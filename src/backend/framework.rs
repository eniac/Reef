type G1 = pasta_curves::pallas::Point;
type G2 = pasta_curves::vesta::Point;
type C1 = NFAStepCircuit<<G1 as Group>::Scalar>;
type C2 = TrivialTestCircuit<<G2 as Group>::Scalar>;
type EE1 = nova_snark::provider::ipa_pc::EvaluationEngine<G1>;
type EE2 = nova_snark::provider::ipa_pc::EvaluationEngine<G2>;
type S1 = nova_snark::spartan::RelaxedR1CSSNARK<G1, EE1>;
type S2 = nova_snark::spartan::RelaxedR1CSSNARK<G2, EE2>;

use crate::backend::{
    commitment::*,
    costs::{logmn, JBatching, JCommit},
    nova::*,
    r1cs::*,
};
use crate::safa::SAFA;
use circ::target::r1cs::wit_comp::StagedWitCompEvaluator;
use circ::target::r1cs::ProverData;
use generic_array::typenum;
use neptune::{
    sponge::vanilla::{Sponge, SpongeTrait},
    Strength,
};
use nova_snark::{
    traits::{circuit::TrivialTestCircuit, Group},
    CompressedSNARK, PublicParams, RecursiveSNARK, StepCounterType, FINAL_EXTERNAL_COUNTER,
};
use rug::Integer;
use std::sync::mpsc;
use std::sync::mpsc::{Receiver, Sender};
use std::sync::{Arc, Mutex};
use std::thread;

struct ProofInfo {
    pp: Arc<Mutex<PublicParams<G1, G2, C1, C2>>>,
    z0_primary: Vec<<G1 as Group>::Scalar>,
    num_steps: usize,
    commit: ReefCommitment<<G1 as Group>::Scalar>,
    table: Vec<Integer>,
    doc_len: usize,
    eval_type: JBatching,
    commit_type: JCommit,
}

#[cfg(feature = "metrics")]
use crate::metrics::{log, log::Component};

// gen R1CS object, commitment, make step circuit for nova
pub fn run_backend(
    safa: SAFA<char>,
    doc: Vec<char>,
    batching_type: Option<JBatching>,
    commit_doctype: Option<JCommit>,
    temp_batch_size: usize, // this may be 0 if not overridden, only use to feed into R1CS object
) {
    let (sender, recv): (
        Sender<NFAStepCircuit<<G1 as Group>::Scalar>>,
        Receiver<NFAStepCircuit<<G1 as Group>::Scalar>>,
    ) = mpsc::channel();

    let (send_setup, recv_setup): (Sender<ProofInfo>, Receiver<ProofInfo>) = mpsc::channel();

    let solver_thread = thread::spawn(move || {
        // we do setup here to avoid unsafe passing
        let sc = Sponge::<<G1 as Group>::Scalar, typenum::U4>::api_constants(Strength::Standard);

        #[cfg(feature = "metrics")]
        log::tic(
            Component::Compiler,
            "R1CS",
            "Optimization Selection, R1CS precomputations",
        );
        let mut r1cs_converter = R1CS::new(
            &safa,
            &doc,
            temp_batch_size,
            sc.clone(),
            batching_type,
            commit_doctype,
        );
        #[cfg(feature = "metrics")]
        log::stop(
            Component::Compiler,
            "R1CS",
            "Optimization Selection, R1CS precomputations",
        );

        #[cfg(feature = "metrics")]
        log::tic(Component::Compiler, "R1CS", "Commitment Generations");
        let reef_commit =
            gen_commitment(r1cs_converter.commit_type, r1cs_converter.udoc.clone(), &sc);
        r1cs_converter.set_commitment(reef_commit.clone());

        #[cfg(feature = "metrics")]
        log::stop(Component::Compiler, "R1CS", "Commitment Generations");

        #[cfg(feature = "metrics")]
        log::tic(Component::Compiler, "R1CS", "To Circuit");

        let (prover_data, _verifier_data) = r1cs_converter.to_circuit();

        #[cfg(feature = "metrics")]
        log::stop(Component::Compiler, "R1CS", "To Circuit");

        #[cfg(feature = "metrics")]
        log::tic(Component::Compiler, "R1CS", "Proof Setup");
        let (num_steps, z0_primary, pp) = setup(&r1cs_converter, &prover_data);

        #[cfg(feature = "metrics")]
        log::stop(Component::Compiler, "R1CS", "Proof Setup");

        send_setup
            .send(ProofInfo {
                pp: Arc::new(Mutex::new(pp)),
                z0_primary,
                num_steps,
                commit: reef_commit,
                table: r1cs_converter.table.clone(),
                doc_len: r1cs_converter.udoc.len(),
                eval_type: r1cs_converter.batching,
                commit_type: r1cs_converter.commit_type,
            })
            .unwrap();

        #[cfg(feature = "metrics")]
        log::stop(Component::Compiler, "Compiler", "Full");

        solve(sender, &r1cs_converter, &prover_data, num_steps);
    });

    //get args
    let proof_info = recv_setup.recv().unwrap();

    prove_and_verify(recv, proof_info);

    // rejoin child
    solver_thread.join().expect("setup/solver thread panicked");
}

fn setup<'a>(
    r1cs_converter: &R1CS<<G1 as Group>::Scalar, char>,
    circ_data: &'a ProverData,
) -> (
    usize,
    Vec<<G1 as Group>::Scalar>,
    PublicParams<G1, G2, C1, C2>,
) {
    let q_len = logmn(r1cs_converter.table.len());
    let qd_len = logmn(r1cs_converter.udoc.len());

    // use "empty" (witness-less) circuit to generate nova F
    let empty_glue = match (r1cs_converter.batching, r1cs_converter.commit_type) {
        (JBatching::NaivePolys, JCommit::HashChain) => {
            vec![
                GlueOpts::PolyHash((
                    <G1 as Group>::Scalar::from(0),
                    <G1 as Group>::Scalar::from(0),
                )),
                GlueOpts::PolyHash((
                    <G1 as Group>::Scalar::from(0),
                    <G1 as Group>::Scalar::from(0),
                )),
            ]
        }
        (JBatching::Nlookup, JCommit::HashChain) => {
            let zero = <G1 as Group>::Scalar::from(0);

            let q = vec![<G1 as Group>::Scalar::from(0); q_len];

            vec![
                GlueOpts::NlHash((zero.clone(), zero.clone(), q.clone(), zero.clone())),
                GlueOpts::NlHash((zero.clone(), zero.clone(), q, zero.clone())),
            ]
        }
        (JBatching::NaivePolys, JCommit::Nlookup) => {
            let q_idx = <G1 as Group>::Scalar::from(0);
            let doc_q = vec![<G1 as Group>::Scalar::from(0); qd_len];

            let doc_v = <G1 as Group>::Scalar::from(0);

            vec![
                GlueOpts::PolyNL((q_idx.clone(), doc_q.clone(), doc_v.clone())),
                GlueOpts::PolyNL((q_idx, doc_q, doc_v)),
            ]
        }
        (JBatching::Nlookup, JCommit::Nlookup) => {
            let q = vec![<G1 as Group>::Scalar::from(0); q_len];

            let v = <G1 as Group>::Scalar::from(0);
            let q_idx = <G1 as Group>::Scalar::from(0);
            let doc_q = vec![<G1 as Group>::Scalar::from(0); qd_len];

            let doc_v = <G1 as Group>::Scalar::from(0);
            vec![
                GlueOpts::NlNl((
                    q.clone(),
                    v.clone(),
                    q_idx.clone(),
                    doc_q.clone(),
                    doc_v.clone(),
                )),
                GlueOpts::NlNl((q, v, q_idx, doc_q, doc_v)),
            ]
        }
    };

    let circuit_primary: NFAStepCircuit<<G1 as Group>::Scalar> = NFAStepCircuit::new(
        circ_data.r1cs.clone(),
        None,
        vec![<G1 as Group>::Scalar::from(0); 2],
        empty_glue,
        <G1 as Group>::Scalar::from(0),
        true,                                                             //false,
        <G1 as Group>::Scalar::from(r1cs_converter.safa.ab.len() as u64), // n chars??
        0,                                                                //nfa.nchars as isize,
        vec![<G1 as Group>::Scalar::from(0); 2],
        r1cs_converter.batch_size,
        r1cs_converter.pc.clone(),
    );

    // trivial circuit
    let circuit_secondary = TrivialTestCircuit::new(StepCounterType::External);

    // produce public parameters
    let pp = PublicParams::<
        G1,
        G2,
        NFAStepCircuit<<G1 as Group>::Scalar>,
        TrivialTestCircuit<<G2 as Group>::Scalar>,
    >::setup(circuit_primary.clone(), circuit_secondary.clone())
    .unwrap();
    #[cfg(feature = "metrics")]
    log::r1cs(
        Component::Prover,
        "add test",
        "Primary Circuit",
        pp.num_constraints().0,
    );
    #[cfg(feature = "metrics")]
    log::r1cs(
        Component::Prover,
        "add test",
        "Secondary Circuit",
        pp.num_constraints().1,
    );

    println!(
        "Number of constraints (primary circuit): {}",
        pp.num_constraints().0
    );
    println!(
        "Number of constraints (secondary circuit): {}",
        pp.num_constraints().1
    );

    println!(
        "Number of variables (primary circuit): {}",
        pp.num_variables().0
    );
    println!(
        "Number of variables (secondary circuit): {}",
        pp.num_variables().1
    );

    let move_0_triple = r1cs_converter.moves.clone().unwrap()[0]; // order?
    let move_0 = (move_0_triple.1, move_0_triple.2);

    // this variable could be two different types of things, which is potentially dicey, but
    // literally whatever
    let blind = match r1cs_converter.reef_commit.clone().unwrap() {
        ReefCommitment::HashChain(hcs) => hcs.blind,
        ReefCommitment::Nlookup(dcs) => dcs.commit_doc_hash,
    };
    // TODO only do this for HC
    let prev_hash = match r1cs_converter.reef_commit.clone().unwrap() {
        ReefCommitment::HashChain(_) => r1cs_converter.prover_calc_hash(blind, true, 0, move_0.0),
        ReefCommitment::Nlookup(_) => <G1 as Group>::Scalar::from(0),
    };

    let current_state = r1cs_converter.safa.get_init().index();

    let z0_primary = match (r1cs_converter.batching, r1cs_converter.commit_type) {
        (JBatching::NaivePolys, JCommit::HashChain) => {
            vec![
                <G1 as Group>::Scalar::from(current_state as u64),
                <G1 as Group>::Scalar::from(move_0.0 as u64),
                prev_hash.clone(),
                <G1 as Group>::Scalar::from(r1cs_converter.prover_accepting_state(current_state)),
            ]
        }
        (JBatching::Nlookup, JCommit::HashChain) => {
            let mut z = vec![
                <G1 as Group>::Scalar::from(current_state as u64),
                <G1 as Group>::Scalar::from(move_0.0 as u64), //<G1 as Group>::Scalar::from(0), //nfa.ab_to_num(&doc[0]) as u64),
                prev_hash.clone(),
            ];
            z.append(&mut vec![<G1 as Group>::Scalar::from(0); q_len]);
            z.push(int_to_ff(r1cs_converter.table[0].clone()));
            z.push(<G1 as Group>::Scalar::from(
                r1cs_converter.prover_accepting_state(current_state),
            ));
            z
        }
        (JBatching::NaivePolys, JCommit::Nlookup) => {
            let mut z = vec![<G1 as Group>::Scalar::from(current_state as u64)];

            z.push(<G1 as Group>::Scalar::from(move_0.0 as u64));

            z.append(&mut vec![<G1 as Group>::Scalar::from(0); qd_len]);
            z.push(<G1 as Group>::Scalar::from(r1cs_converter.udoc[0] as u64));
            z.push(<G1 as Group>::Scalar::from(
                r1cs_converter.prover_accepting_state(current_state),
            ));
            z
        }
        (JBatching::Nlookup, JCommit::Nlookup) => {
            let mut z = vec![<G1 as Group>::Scalar::from(current_state as u64)];

            z.append(&mut vec![<G1 as Group>::Scalar::from(0); q_len]);
            z.push(int_to_ff(r1cs_converter.table[0].clone()));

            z.push(<G1 as Group>::Scalar::from(move_0.0 as u64));
            z.append(&mut vec![<G1 as Group>::Scalar::from(0); qd_len]);
            z.push(<G1 as Group>::Scalar::from(r1cs_converter.udoc[0] as u64));
            z.push(<G1 as Group>::Scalar::from(
                r1cs_converter.prover_accepting_state(current_state),
            ));
            z
        }
    };

    let num_steps = r1cs_converter.moves.clone().unwrap().len();
    assert!(num_steps > 0, "trying to prove something about 0 foldings");

    (num_steps, z0_primary, pp)
}

fn solve<'a>(
    sender: Sender<NFAStepCircuit<<G1 as Group>::Scalar>>, //itness<<G1 as Group>::Scalar>>,
    r1cs_converter: &R1CS<<G1 as Group>::Scalar, char>,
    circ_data: &'a ProverData,
    num_steps: usize,
) {
    let q_len = logmn(r1cs_converter.table.len());
    let qd_len = logmn(r1cs_converter.udoc.len());

    // this variable could be two different types of things, which is potentially dicey, but
    // literally whatever
    let blind = match r1cs_converter.reef_commit.clone().unwrap() {
        ReefCommitment::HashChain(hcs) => hcs.blind,
        ReefCommitment::Nlookup(dcs) => dcs.commit_doc_hash,
    };
    // TODO put this in glue

    let mut wits;
    let mut running_q = None;
    let mut running_v = None;
    let mut next_running_q;
    let mut next_running_v;
    let mut doc_running_q = None;
    let mut doc_running_v = None;
    let mut next_doc_running_q;
    let mut next_doc_running_v;

    let mut start_of_epsilons;
    let mut prev_doc_idx = None;
    let mut next_doc_idx;

    // TODO only do this for HC
    let mut prev_hash = match r1cs_converter.reef_commit.clone().unwrap() {
        ReefCommitment::HashChain(_) => r1cs_converter.prover_calc_hash(
            blind,
            true,
            0,
            r1cs_converter.moves.clone().unwrap()[0].1,
        ),
        ReefCommitment::Nlookup(_) => <G1 as Group>::Scalar::from(0),
    };

    let mut current_state = r1cs_converter.safa.get_init().index();
    // TODO don't recalc :(

    let mut next_state = current_state;

    for i in 0..num_steps {
        #[cfg(feature = "metrics")]
        let test = format!("step {}", i);

        #[cfg(feature = "metrics")]
        log::tic(Component::Solver, &test, "witness generation");
        // allocate real witnesses for round i
        let move_i_triple = r1cs_converter.moves.clone().unwrap()[i]; // order?
        let move_i = (move_i_triple.1, move_i_triple.2);
        (
            wits,
            next_state,
            next_running_q,
            next_running_v,
            next_doc_running_q,
            next_doc_running_v,
            start_of_epsilons,
            next_doc_idx,
        ) = r1cs_converter.gen_wit_i(
            move_i,
            0, // batch == 0 always right now i,
            next_state,
            running_q.clone(),
            running_v.clone(),
            doc_running_q.clone(),
            doc_running_v.clone(),
            prev_doc_idx.clone(),
        );
        #[cfg(feature = "metrics")]
        log::stop(Component::Solver, &test, "witness generation");

        circ_data.check_all(&wits);

        let glue = match (r1cs_converter.batching, r1cs_converter.commit_type) {
            (JBatching::NaivePolys, JCommit::HashChain) => {
                #[cfg(feature = "metrics")]
                log::tic(Component::Solver, &test, "calculate hash");
                let next_hash = r1cs_converter.prover_calc_hash(
                    prev_hash,
                    false,
                    move_i.0, // TODO + (i * r1cs_converter.batch_size),
                    r1cs_converter.batch_size,
                );

                let i_0 = <G1 as Group>::Scalar::from(
                    move_i.0 as u64, //(r1cs_converter.substring.0 + (i * r1cs_converter.batch_size)) as u64,
                );
                let i_last = <G1 as Group>::Scalar::from(
                    (move_i.0 + r1cs_converter.batch_size) as u64, //(r1cs_converter.substring.0 + ((i + 1) * r1cs_converter.batch_size)) as u64,
                );
                let g = vec![
                    GlueOpts::PolyHash((i_0, prev_hash)),
                    GlueOpts::PolyHash((i_last, next_hash)),
                ];
                prev_hash = next_hash;
                #[cfg(feature = "metrics")]
                log::stop(Component::Solver, &test, "calculate hash");
                g
            }
            (JBatching::Nlookup, JCommit::HashChain) => {
                #[cfg(feature = "metrics")]
                log::tic(Component::Solver, &test, "calculate hash");
                let next_hash = r1cs_converter.prover_calc_hash(
                    prev_hash,
                    false,
                    move_i.0, //r1cs_converter.substring.0 + (i * r1cs_converter.batch_size),
                    r1cs_converter.batch_size,
                );

                let q = match running_q {
                    Some(rq) => rq.into_iter().map(|x| int_to_ff(x)).collect(),
                    None => vec![<G1 as Group>::Scalar::from(0); q_len],
                };

                let v = match running_v {
                    Some(rv) => int_to_ff(rv),
                    None => int_to_ff(r1cs_converter.table[0].clone()),
                };

                let next_q = next_running_q
                    .clone()
                    .unwrap()
                    .into_iter()
                    .map(|x| int_to_ff(x))
                    .collect();
                let next_v = int_to_ff(next_running_v.clone().unwrap());

                let i_0 = <G1 as Group>::Scalar::from(
                    move_i.0 as u64, //(r1cs_converter.substring.0 + (i * r1cs_converter.batch_size)) as u64,
                );
                let i_last = <G1 as Group>::Scalar::from(
                    (move_i.0 + r1cs_converter.batch_size) as u64, //(r1cs_converter.substring.0 + ((i + 1) * r1cs_converter.batch_size)) as u64,
                );
                let g = vec![
                    GlueOpts::NlHash((i_0, prev_hash, q, v)),
                    GlueOpts::NlHash((i_last, next_hash, next_q, next_v)),
                ];
                prev_hash = next_hash;
                g
            }
            (JBatching::NaivePolys, JCommit::Nlookup) => {
                // TODO fix
                let q_idx = <G1 as Group>::Scalar::from(move_i.0 as u64);
                println!("Q IDX {:#?}", q_idx);

                let doc_q = match doc_running_q {
                    Some(rq) => rq.into_iter().map(|x| int_to_ff(x)).collect(),
                    None => vec![<G1 as Group>::Scalar::from(0); qd_len],
                };

                let doc_v = match doc_running_v {
                    Some(rv) => int_to_ff(rv),
                    None => <G1 as Group>::Scalar::from(r1cs_converter.udoc[0] as u64),
                };

                let next_q_idx =
                    <G1 as Group>::Scalar::from((move_i.0 + r1cs_converter.batch_size) as u64); //<G1 as Group>::Scalar::from(next_doc_idx.unwrap() as u64);

                println!("NEXT Q IDX {:#?}", next_q_idx);
                let next_doc_q = next_doc_running_q
                    .clone()
                    .unwrap()
                    .into_iter()
                    .map(|x| int_to_ff(x))
                    .collect();
                let next_doc_v = int_to_ff(next_doc_running_v.clone().unwrap());
                vec![
                    GlueOpts::PolyNL((q_idx, doc_q, doc_v)),
                    GlueOpts::PolyNL((next_q_idx, next_doc_q, next_doc_v)),
                ]
            }
            (JBatching::Nlookup, JCommit::Nlookup) => {
                let q = match running_q {
                    Some(rq) => rq.into_iter().map(|x| int_to_ff(x)).collect(),
                    None => vec![<G1 as Group>::Scalar::from(0); q_len],
                };

                let v = match running_v {
                    Some(rv) => int_to_ff(rv),
                    None => int_to_ff(r1cs_converter.table[0].clone()),
                };

                let next_q = next_running_q
                    .clone()
                    .unwrap()
                    .into_iter()
                    .map(|x| int_to_ff(x))
                    .collect();
                let next_v = int_to_ff(next_running_v.clone().unwrap());

                let q_idx = <G1 as Group>::Scalar::from(move_i.0 as u64);

                let next_q_idx =
                    <G1 as Group>::Scalar::from((move_i.0 + r1cs_converter.batch_size) as u64);

                println!("Q IDX {:#?}", q_idx);
                println!("NEXT Q IDX {:#?}", next_q_idx);
                let doc_q = match doc_running_q {
                    Some(rq) => rq.into_iter().map(|x| int_to_ff(x)).collect(),
                    None => vec![<G1 as Group>::Scalar::from(0); qd_len],
                };

                let doc_v = match doc_running_v {
                    Some(rv) => int_to_ff(rv),
                    None => <G1 as Group>::Scalar::from(r1cs_converter.udoc[0] as u64),
                };
                let next_doc_q = next_doc_running_q
                    .clone()
                    .unwrap()
                    .into_iter()
                    .map(|x| int_to_ff(x))
                    .collect();
                let next_doc_v = int_to_ff(next_doc_running_v.clone().unwrap());
                vec![
                    GlueOpts::NlNl((q, v, q_idx, doc_q, doc_v)),
                    GlueOpts::NlNl((next_q, next_v, next_q_idx, next_doc_q, next_doc_v)),
                ]
            }
        };

        let values: Option<Vec<_>> = Some(wits).map(|values| {
            let mut evaluator = StagedWitCompEvaluator::new(&circ_data.precompute);
            let mut ffs = Vec::new();
            ffs.extend(evaluator.eval_stage(values.clone()).into_iter().cloned());
            ffs.extend(
                evaluator
                    .eval_stage(Default::default())
                    .into_iter()
                    .cloned(),
            );
            ffs
        });

        let circuit_primary: NFAStepCircuit<<G1 as Group>::Scalar> = NFAStepCircuit::new(
            circ_data.r1cs.clone(),
            values,
            vec![
                <G1 as Group>::Scalar::from(current_state as u64),
                <G1 as Group>::Scalar::from(next_state as u64),
            ],
            glue,
            blind,
            move_i.0 == 0,
            <G1 as Group>::Scalar::from(r1cs_converter.safa.ab.len() as u64),
            start_of_epsilons,
            vec![
                <G1 as Group>::Scalar::from(r1cs_converter.prover_accepting_state(current_state)),
                <G1 as Group>::Scalar::from(r1cs_converter.prover_accepting_state(next_state)),
            ],
            r1cs_converter.batch_size,
            r1cs_converter.pc.clone(),
        );

        #[cfg(feature = "metrics")]
        log::stop(Component::Solver, &test, "witness generation");

        sender.send(circuit_primary).unwrap(); //witness_i).unwrap();

        // for next i+1 round
        current_state = next_state;
        running_q = next_running_q;
        running_v = next_running_v;
        doc_running_q = next_doc_running_q;
        doc_running_v = next_doc_running_v;
        prev_doc_idx = next_doc_idx;
    }
}

fn prove_and_verify(recv: Receiver<NFAStepCircuit<<G1 as Group>::Scalar>>, proof_info: ProofInfo) {
    println!("Proving thread starting...");

    // recursive SNARK
    let mut recursive_snark: Option<RecursiveSNARK<G1, G2, C1, C2>> = None;
    // trivial circuit
    let circuit_secondary = TrivialTestCircuit::new(StepCounterType::External);
    let z0_secondary = vec![<G2 as Group>::Scalar::zero()];

    // println!("num foldings: {:#?}", proof_info.num_steps);
    for i in 0..proof_info.num_steps {
        #[cfg(feature = "metrics")]
        let test = format!("step {}", i);

        // blocks until we receive first witness
        let circuit_primary = recv.recv().unwrap();

        #[cfg(feature = "metrics")]
        log::tic(Component::Prover, &test, "prove step");

        let result = RecursiveSNARK::prove_step(
            &proof_info.pp.lock().unwrap(),
            recursive_snark,
            circuit_primary.clone(),
            circuit_secondary.clone(),
            proof_info.z0_primary.clone(),
            z0_secondary.clone(),
        );
        println!("prove step {:#?}", i);

        #[cfg(feature = "metrics")]
        log::stop(Component::Prover, &test, "prove step");

        // verify recursive - TODO we can get rid of this verify once everything works
        // PLEASE LEAVE this here for Jess for now - immensely helpful with debugging
        let res = result.clone().unwrap().verify(
            &proof_info.pp.lock().unwrap(),
            FINAL_EXTERNAL_COUNTER,
            proof_info.z0_primary.clone(),
            z0_secondary.clone(),
        );
        println!("Recursive res: {:#?}", res);

        assert!(res.is_ok()); // TODO delete

        recursive_snark = Some(result.unwrap());
    }

    assert!(recursive_snark.is_some());
    let recursive_snark = recursive_snark.unwrap();

    // compressed SNARK
    #[cfg(feature = "metrics")]
    log::tic(Component::Prover, "Proof", "Compressed SNARK");
    let res = CompressedSNARK::<_, _, _, _, S1, S2>::prove(
        &proof_info.pp.lock().unwrap(),
        &recursive_snark,
    );
    #[cfg(feature = "metrics")]
    log::stop(Component::Prover, "Proof", "Compressed SNARK");

    assert!(res.is_ok());
    let compressed_snark = res.unwrap();

    #[cfg(feature = "metrics")]
    log::space(
        Component::Prover,
        "Proof Size",
        "Compressed SNARK size",
        serde_json::to_string(&compressed_snark).unwrap().len(),
    );

    #[cfg(feature = "metrics")]
    log::tic(Component::Verifier, "Verification", "Full");

    verify(
        compressed_snark,
        proof_info.z0_primary,
        proof_info.pp,
        proof_info.commit,
        proof_info.table,
        proof_info.doc_len,
        proof_info.eval_type,
        proof_info.commit_type,
    );

    #[cfg(feature = "metrics")]
    log::stop(Component::Verifier, "Verification", "Full");
}

fn verify(
    compressed_snark: CompressedSNARK<G1, G2, C1, C2, S1, S2>,
    z0_primary: Vec<<G1 as Group>::Scalar>,
    pp: Arc<Mutex<PublicParams<G1, G2, C1, C2>>>,
    reef_commit: ReefCommitment<<G1 as Group>::Scalar>,
    table: Vec<Integer>,
    doc_len: usize,
    eval_type: JBatching,
    commit_type: JCommit,
) {
    let q_len = logmn(table.len());
    let qd_len = logmn(doc_len);

    let z0_secondary = vec![<G2 as Group>::Scalar::zero()];

    #[cfg(feature = "metrics")]
    log::tic(Component::Verifier, "Verification", "Nova Verification");

    let res = compressed_snark.verify(
        &pp.lock().unwrap(),
        FINAL_EXTERNAL_COUNTER,
        z0_primary,
        z0_secondary,
    );
    #[cfg(feature = "metrics")]
    log::stop(Component::Verifier, "Verification", "Nova Verification");

    assert!(res.is_ok());

    #[cfg(feature = "metrics")]
    log::tic(Component::Verifier, "Verification", "Final Clear Checks");

    // state, char, opt<hash>, opt<v,q for eval>, opt<v,q for doc>, accepting
    let zn = res.unwrap().0;

    // eval type, reef commitment, accepting state bool, table, doc, final_q, final_v, final_hash,
    // final_doc_q, final_doc_v
    match (eval_type, commit_type) {
        (JBatching::NaivePolys, JCommit::HashChain) => {
            final_clear_checks(
                eval_type,
                reef_commit,
                zn[3],
                &table, // clones in function?
                doc_len,
                None,
                None,
                Some(zn[2]),
                None,
                None,
            );
        }
        (JBatching::NaivePolys, JCommit::Nlookup) => {
            final_clear_checks(
                eval_type,
                reef_commit,
                zn[3 + qd_len],
                &table,
                doc_len,
                None,
                None,
                None,
                Some(zn[2..(qd_len + 2)].to_vec()),
                Some(zn[2 + qd_len]),
            );
        }
        (JBatching::Nlookup, JCommit::HashChain) => {
            final_clear_checks(
                eval_type,
                reef_commit,
                zn[3 + q_len + 1],
                &table,
                doc_len,
                Some(zn[3..(3 + q_len)].to_vec()),
                Some(zn[3 + q_len]),
                Some(zn[2]),
                None,
                None,
            );
        }
        (JBatching::Nlookup, JCommit::Nlookup) => {
            final_clear_checks(
                eval_type,
                reef_commit,
                zn[2 + q_len + 1 + qd_len + 1],
                &table,
                doc_len,
                Some(zn[1..(q_len + 1)].to_vec()),
                Some(zn[q_len + 1]),
                None,
                Some(zn[(2 + q_len + 1)..(2 + q_len + 1 + qd_len)].to_vec()),
                Some(zn[2 + q_len + 1 + qd_len]),
            );
        }
    }
    #[cfg(feature = "metrics")]
    log::stop(Component::Verifier, "Verification", "Final Clear Checks");
}

#[cfg(test)]
mod tests {

    use crate::backend::framework::*;
    use crate::backend::r1cs_helper::init;
    use crate::nfa::NFA;
    use crate::regex::Regex;

    fn backend_test(
        ab: String,
        rstr: String,
        doc: Vec<String>,
        batching_type: Option<JBatching>,
        commit_docype: Option<JCommit>,
        batch_size: usize,
    ) {
        let r = Regex::new(&rstr);
        let nfa = NFA::new(&ab[..], r);

        init();
        run_backend(
            nfa.clone(),
            doc.clone(),
            batching_type.clone(),
            commit_docype.clone(),
            batch_size,
        );
    }

    #[test]
    fn e2e_q_overflow() {
        backend_test(
            "abcdefg".to_string(),
            "gaa*bb*cc*dd*ee*f".to_string(),
            ("gaaaaaabbbbbbccccccddddddeeeeeef".to_string())
                .chars()
                .map(|c| c.to_string())
                .collect(),
            Some(JBatching::Nlookup),
            Some(JCommit::Nlookup),
            33,
        );
    }

    #[test]
    fn e2e_substring() {
        backend_test(
            "ab".to_string(),
            "bbb".to_string(),
            ("aaabbbaaa".to_string())
                .chars()
                .map(|c| c.to_string())
                .collect(),
            Some(JBatching::Nlookup),
            Some(JCommit::Nlookup),
            2,
        );

        backend_test(
            "ab".to_string(),
            "bbbaaa".to_string(),
            ("aaabbbaaa".to_string())
                .chars()
                .map(|c| c.to_string())
                .collect(),
            Some(JBatching::NaivePolys),
            Some(JCommit::HashChain),
            2,
        );
    }

    #[test]
    fn e2e_poly_hash() {
        backend_test(
            "ab".to_string(),
            "^a*b*$".to_string(),
            ("aaab".to_string())
                .chars()
                .map(|c| c.to_string())
                .collect(),
            Some(JBatching::NaivePolys),
            Some(JCommit::HashChain),
            0,
        );
        /*        backend_test(
                  "ab".to_string(),
                  "^ab*$".to_string(),
                  &("abbbbbbb".to_string())
                      .chars()
                      .map(|c| c.to_string())
                      .collect(),
                  Some(JBatching::NaivePolys),
                  Some(JCommit::HashChain),
                  vec![0, 2],
              );
              backend_test(
                  "ab".to_string(),
                  "^a*$".to_string(),
                  &("aaaaaaaaaaaaaaaa".to_string())
                      .chars()
                      .map(|c| c.to_string())
                      .collect(),
                  Some(JBatching::NaivePolys),
                  Some(JCommit::HashChain),
                  vec![0, 2, 5],
              );
        */
    }

    #[test]
    fn e2e_poly_nl() {
        backend_test(
            "ab".to_string(),
            "^a*b*$".to_string(),
            ("aaab".to_string())
                .chars()
                .map(|c| c.to_string())
                .collect(),
            Some(JBatching::NaivePolys),
            Some(JCommit::Nlookup),
            0,
        );
        /*    backend_test(
                "ab".to_string(),
                "^a*b*$".to_string(),
                &("aa".to_string()).chars().map(|c| c.to_string()).collect(),
                Some(JBatching::NaivePolys),
                Some(JCommit::Nlookup),
                vec![0, 1, 2],
            );
            backend_test(
                "ab".to_string(),
                "^a*b*$".to_string(),
                &("aaab".to_string())
                    .chars()
                    .map(|c| c.to_string())
                    .collect(),
                Some(JBatching::NaivePolys),
                Some(JCommit::Nlookup),
                vec![0, 2],
            );
            backend_test(
                "ab".to_string(),
                "^ab*$".to_string(),
                &("abbbbbbb".to_string())
                    .chars()
                    .map(|c| c.to_string())
                    .collect(),
                Some(JBatching::NaivePolys),
                Some(JCommit::Nlookup),
                vec![0, 2, 5],
            );
            backend_test(
                "ab".to_string(),
                "^a*$".to_string(),
                &("aaaaaaaaaaaaaaaa".to_string())
                    .chars()
                    .map(|c| c.to_string())
                    .collect(),
                Some(JBatching::NaivePolys),
                Some(JCommit::Nlookup),
                vec![0, 2, 5],
            );
        */
    }

    #[test]
    fn e2e_nl_hash() {
        backend_test(
            "ab".to_string(),
            "^a*b*$".to_string(),
            ("aaab".to_string())
                .chars()
                .map(|c| c.to_string())
                .collect(),
            Some(JBatching::Nlookup),
            Some(JCommit::HashChain),
            0,
        );
        /*  backend_test(
                "ab".to_string(),
                "^a*b*$".to_string(),
                &("aa".to_string()).chars().map(|c| c.to_string()).collect(),
                Some(JBatching::Nlookup),
                Some(JCommit::HashChain),
                vec![0, 1, 2],
            );
            backend_test(
                "ab".to_string(),
                "^a*b*$".to_string(),
                &("aaab".to_string())
                    .chars()
                    .map(|c| c.to_string())
                    .collect(),
                Some(JBatching::Nlookup),
                Some(JCommit::HashChain),
                vec![0, 2],
            );
            backend_test(
                "ab".to_string(),
                "^ab*$".to_string(),
                &("abbbbbbb".to_string())
                    .chars()
                    .map(|c| c.to_string())
                    .collect(),
                Some(JBatching::Nlookup),
                Some(JCommit::HashChain),
                vec![0, 2],
            );
            backend_test(
                "ab".to_string(),
                "^a*$".to_string(),
                &("aaaaaaaaaaaaaaaa".to_string())
                    .chars()
                    .map(|c| c.to_string())
                    .collect(),
                Some(JBatching::Nlookup),
                Some(JCommit::HashChain),
                vec![0, 2, 5],
                // [1,2,3,4,5,6,7,8,
            );
        */
    }

    #[test]
    fn e2e_nl_nl() {
        backend_test(
            "ab".to_string(),
            "^a*b*$".to_string(),
            ("aaab".to_string())
                .chars()
                .map(|c| c.to_string())
                .collect(),
            Some(JBatching::Nlookup),
            Some(JCommit::Nlookup),
            0,
        );
        /*  backend_test(
                "ab".to_string(),
                "^a*b*$".to_string(),
                &("aa".to_string()).chars().map(|c| c.to_string()).collect(),
                Some(JBatching::Nlookup),
                Some(JCommit::Nlookup),
                vec![0, 1, 2],
            );
            backend_test(
                "ab".to_string(),
                "^a*b*$".to_string(),
                &("aaab".to_string())
                    .chars()
                    .map(|c| c.to_string())
                    .collect(),
                Some(JBatching::Nlookup),
                Some(JCommit::Nlookup),
                vec![0, 2],
            );
            backend_test(
                "ab".to_string(),
                "^ab*$".to_string(),
                &("abbbbbbb".to_string())
                    .chars()
                    .map(|c| c.to_string())
                    .collect(),
                Some(JBatching::Nlookup),
                Some(JCommit::Nlookup),
                vec![0, 2, 5],
            );
            backend_test(
                "ab".to_string(),
                "^a*$".to_string(),
                &("aaaaaaaaaaaaaaaa".to_string())
                    .chars()
                    .map(|c| c.to_string())
                    .collect(),
                Some(JBatching::Nlookup),
                Some(JCommit::Nlookup),
                vec![0, 2, 5],
                // [1,2,3,4,5,6,7,8,
            );
        */
    }
}

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
use crate::dfa::NFA;
use crate::metrics::{log, log::Component};
use circ::target::r1cs::wit_comp::StagedWitCompEvaluator;
use circ::target::r1cs::ProverData;
use circ::{ir::term::Value, target::r1cs::*};
use core::time;
use ff::PrimeField;
use fxhash::FxHashMap;
use generic_array::typenum;
use neptune::{
    poseidon::PoseidonConstants,
    sponge::vanilla::{Sponge, SpongeTrait},
    Strength,
};
use nova_snark::{
    traits::{circuit::TrivialTestCircuit, Group},
    CompressedSNARK, PublicParams, RecursiveSNARK, StepCounterType, FINAL_EXTERNAL_COUNTER,
};
use rug::Integer;
use serde_json::{Result, Value as SerdeValue};
use std::sync::mpsc;
use std::sync::mpsc::{Receiver, Sender};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::Duration;
use std::time::Instant;

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

// gen R1CS object, commitment, make step circuit for nova
pub fn run_backend(
    dfa: NFA,
    doc: Vec<String>,
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

        log::tic(Component::Compiler, "R1CS", "Optimization Selection");
        let mut r1cs_converter = R1CS::new(
            &dfa,
            &doc,
            temp_batch_size,
            sc.clone(),
            batching_type,
            commit_doctype,
        );
        log::stop(Component::Compiler, "R1CS", "Optimization Selection");

        println!("generate commitment");

        // to get rid clone
        log::tic(Component::Compiler, "R1CS", "Commitment Generations");
        let reef_commit =
            gen_commitment(r1cs_converter.commit_type, r1cs_converter.udoc.clone(), &sc);
        // todo clone
        r1cs_converter.set_commitment(reef_commit.clone());
        log::stop(Component::Compiler, "R1CS", "Commitment Generations");

        log::tic(Component::Compiler, "R1CS", "To Circuit and Setup");
        let (prover_data, _verifier_data) = r1cs_converter.to_circuit();

        let (num_steps, z0_primary, pp) = setup(&r1cs_converter, &prover_data); //, timer);
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
        log::stop(Component::Compiler, "R1CS", "To Circuit and Setup");

        log::stop(Component::Compiler, "Compiler", "Full");

        solve(sender, &r1cs_converter, &prover_data, num_steps); //, timer);
        println!("solver thread finished");
    });

    //get args
    let proof_info = recv_setup.recv().unwrap();

    prove_and_verify(recv, proof_info);

    // rejoin child
    solver_thread.join().expect("setup/solver thread panicked");
}

fn setup<'a>(
    r1cs_converter: &R1CS<<G1 as Group>::Scalar>,
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
            let doc_q = vec![<G1 as Group>::Scalar::from(0); qd_len];

            let doc_v = <G1 as Group>::Scalar::from(0);

            vec![
                GlueOpts::PolyNL((doc_q.clone(), doc_v.clone())),
                GlueOpts::PolyNL((doc_q, doc_v)),
            ]
        }
        (JBatching::Nlookup, JCommit::Nlookup) => {
            let q = vec![<G1 as Group>::Scalar::from(0); q_len];

            let v = <G1 as Group>::Scalar::from(0);
            let doc_q = vec![<G1 as Group>::Scalar::from(0); qd_len];

            let doc_v = <G1 as Group>::Scalar::from(0);
            vec![
                GlueOpts::NlNl((q.clone(), v.clone(), doc_q.clone(), doc_v.clone())),
                GlueOpts::NlNl((q, v, doc_q, doc_v)),
            ]
        }
    };

    let circuit_primary: NFAStepCircuit<<G1 as Group>::Scalar> = NFAStepCircuit::new(
        circ_data.r1cs.clone(),
        None,
        vec![<G1 as Group>::Scalar::from(0); 2],
        empty_glue,
        <G1 as Group>::Scalar::from(0),
        true, //false,
        <G1 as Group>::Scalar::from(r1cs_converter.dfa.nchars() as u64),
        0, //dfa.nchars as isize,
        vec![<G1 as Group>::Scalar::from(0); 2],
        r1cs_converter.batch_size,
        r1cs_converter.pc.clone(),
    );

    // trivial circuit
    let circuit_secondary = TrivialTestCircuit::new(StepCounterType::External);

    // produce public parameters
    println!("Producing public parameters...");
    let pp = PublicParams::<
        G1,
        G2,
        NFAStepCircuit<<G1 as Group>::Scalar>,
        TrivialTestCircuit<<G2 as Group>::Scalar>,
    >::setup(circuit_primary.clone(), circuit_secondary.clone())
    .unwrap();
    log::r1cs(
        Component::Prover,
        "add test",
        "Primary Circuit",
        pp.num_constraints().0,
    );
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

    // this variable could be two different types of things, which is potentially dicey, but
    // literally whatever
    let blind = match r1cs_converter.reef_commit.clone().unwrap() {
        ReefCommitment::HashChain(hcs) => hcs.blind,
        ReefCommitment::Nlookup(dcs) => dcs.commit_doc_hash,
    };
    // TODO only do this for HC
    let prev_hash = match r1cs_converter.reef_commit.clone().unwrap() {
        ReefCommitment::HashChain(_) => {
            r1cs_converter.prover_calc_hash(blind, true, 0, r1cs_converter.substring.0)
        }
        ReefCommitment::Nlookup(_) => <G1 as Group>::Scalar::from(0),
    };

    let current_state = r1cs_converter.dfa.get_init_state();
    let z0_primary = match (r1cs_converter.batching, r1cs_converter.commit_type) {
        (JBatching::NaivePolys, JCommit::HashChain) => {
            vec![
                <G1 as Group>::Scalar::from(current_state as u64),
                <G1 as Group>::Scalar::from(r1cs_converter.substring.0 as u64),
                prev_hash.clone(),
                <G1 as Group>::Scalar::from(
                    r1cs_converter.prover_accepting_state(0, current_state),
                ),
            ]
        }
        (JBatching::Nlookup, JCommit::HashChain) => {
            let mut z = vec![
                <G1 as Group>::Scalar::from(current_state as u64),
                <G1 as Group>::Scalar::from(r1cs_converter.substring.0 as u64), //<G1 as Group>::Scalar::from(0), //dfa.ab_to_num(&doc[0]) as u64),
                prev_hash.clone(),
            ];
            z.append(&mut vec![<G1 as Group>::Scalar::from(0); q_len]);
            z.push(int_to_ff(r1cs_converter.table[0].clone()));
            z.push(<G1 as Group>::Scalar::from(
                r1cs_converter.prover_accepting_state(0, current_state),
            ));
            z
        }
        (JBatching::NaivePolys, JCommit::Nlookup) => {
            let mut z = vec![
                <G1 as Group>::Scalar::from(current_state as u64),
                //<G1 as Group>::Scalar::from(dfa.ab_to_num(&doc[0]) as u64),
            ];

            z.append(&mut vec![<G1 as Group>::Scalar::from(0); qd_len]);
            z.push(<G1 as Group>::Scalar::from(r1cs_converter.udoc[0] as u64));
            z.push(<G1 as Group>::Scalar::from(
                r1cs_converter.prover_accepting_state(0, current_state),
            ));
            z
        }
        (JBatching::Nlookup, JCommit::Nlookup) => {
            let mut z = vec![
                <G1 as Group>::Scalar::from(current_state as u64),
                //<G1 as Group>::Scalar::from(dfa.ab_to_num(&doc[0]) as u64),
            ];

            z.append(&mut vec![<G1 as Group>::Scalar::from(0); q_len]);
            z.push(int_to_ff(r1cs_converter.table[0].clone()));
            z.append(&mut vec![<G1 as Group>::Scalar::from(0); qd_len]);
            z.push(<G1 as Group>::Scalar::from(r1cs_converter.udoc[0] as u64));
            z.push(<G1 as Group>::Scalar::from(
                r1cs_converter.prover_accepting_state(0, current_state),
            ));
            z
        }
    };

    let num_steps = ceil_div(
        r1cs_converter.substring.1 - r1cs_converter.substring.0,
        r1cs_converter.batch_size,
    );
    println!("NUM STEPS {}", num_steps);

    (num_steps, z0_primary, pp)
}

fn solve<'a>(
    sender: Sender<NFAStepCircuit<<G1 as Group>::Scalar>>, //itness<<G1 as Group>::Scalar>>,
    r1cs_converter: &R1CS<<G1 as Group>::Scalar>,
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

    // TODO only do this for HC
    let mut prev_hash = match r1cs_converter.reef_commit.clone().unwrap() {
        ReefCommitment::HashChain(_) => {
            r1cs_converter.prover_calc_hash(blind, true, 0, r1cs_converter.substring.0)
        }
        ReefCommitment::Nlookup(_) => <G1 as Group>::Scalar::from(0),
    };

    let mut current_state = r1cs_converter.dfa.get_init_state();
    // TODO don't recalc :(

    let mut next_state = current_state;

    for i in 0..num_steps {
        println!("WIT GEN STEP {}", i);
        let test = format!("step {}", i);

        // allocate real witnesses for round i
        log::tic(Component::Solver, &test, "witness generation");
        (
            wits,
            next_state,
            next_running_q,
            next_running_v,
            next_doc_running_q,
            next_doc_running_v,
            start_of_epsilons,
        ) = r1cs_converter.gen_wit_i(
            i,
            next_state,
            running_q.clone(),
            running_v.clone(),
            doc_running_q.clone(),
            doc_running_v.clone(),
        );
        log::stop(Component::Solver, &test, "witness generation");

        //circ_data.check_all(&wits);

        let glue = match (r1cs_converter.batching, r1cs_converter.commit_type) {
            (JBatching::NaivePolys, JCommit::HashChain) => {
                log::tic(Component::Solver, &test, "calculate hash");
                let next_hash = r1cs_converter.prover_calc_hash(
                    prev_hash,
                    false,
                    r1cs_converter.substring.0 + (i * r1cs_converter.batch_size),
                    r1cs_converter.batch_size,
                );
                // println!("ph, nh: {:#?}, {:#?}", prev_hash.clone(), next_hash.clone());

                let i_0 = <G1 as Group>::Scalar::from((i * r1cs_converter.batch_size) as u64);
                let i_last =
                    <G1 as Group>::Scalar::from(((i + 1) * r1cs_converter.batch_size) as u64);
                let g = vec![
                    GlueOpts::PolyHash((i_0, prev_hash)),
                    GlueOpts::PolyHash((i_last, next_hash)),
                ];
                prev_hash = next_hash;
                log::stop(Component::Solver, &test, "calculate hash");
                // println!("ph, nh: {:#?}, {:#?}", prev_hash.clone(), next_hash.clone());
                g
            }
            (JBatching::Nlookup, JCommit::HashChain) => {
                log::tic(Component::Solver, &test, "calculate hash");
                let next_hash = r1cs_converter.prover_calc_hash(
                    prev_hash,
                    false,
                    r1cs_converter.substring.0 + (i * r1cs_converter.batch_size),
                    r1cs_converter.batch_size,
                );
                // println!("ph, nh: {:#?}, {:#?}", prev_hash.clone(), next_hash.clone());

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

                let i_0 = <G1 as Group>::Scalar::from((i * r1cs_converter.batch_size) as u64);
                let i_last =
                    <G1 as Group>::Scalar::from(((i + 1) * r1cs_converter.batch_size) as u64);
                let g = vec![
                    GlueOpts::NlHash((i_0, prev_hash, q, v)),
                    GlueOpts::NlHash((i_last, next_hash, next_q, next_v)),
                ];
                prev_hash = next_hash;
                log::stop(Component::Solver, &test, "calculate hash");
                g
            }
            (JBatching::NaivePolys, JCommit::Nlookup) => {
                log::tic(Component::Solver, &test, "calculate running claim");
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
                log::stop(Component::Solver, &test, "calculate running claim");
                vec![
                    GlueOpts::PolyNL((doc_q, doc_v)),
                    GlueOpts::PolyNL((next_doc_q, next_doc_v)),
                ]
            }
            (JBatching::Nlookup, JCommit::Nlookup) => {
                log::tic(Component::Solver, &test, "calculate running claim");
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
                log::stop(Component::Solver, &test, "calculate running claim");
                vec![
                    GlueOpts::NlNl((q, v, doc_q, doc_v)),
                    GlueOpts::NlNl((next_q, next_v, next_doc_q, next_doc_v)),
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
            i == 0,
            <G1 as Group>::Scalar::from(r1cs_converter.dfa.nchars() as u64),
            start_of_epsilons,
            vec![
                <G1 as Group>::Scalar::from(
                    r1cs_converter.prover_accepting_state(i, current_state),
                ),
                <G1 as Group>::Scalar::from(r1cs_converter.prover_accepting_state(i, next_state)),
            ],
            r1cs_converter.batch_size,
            r1cs_converter.pc.clone(),
        );

        //thread::sleep(Duration::from_millis(10000));
        println!("FINISHED WIT STEP {}", i);

        sender.send(circuit_primary).unwrap(); //witness_i).unwrap();

        // for next i+1 round
        current_state = next_state;
        running_q = next_running_q;
        running_v = next_running_v;
        doc_running_q = next_doc_running_q;
        doc_running_v = next_doc_running_v;
    }
}

fn prove_and_verify(
    recv: Receiver<NFAStepCircuit<<G1 as Group>::Scalar>>, //itness<<G1 as Group>::Scalar>>,
    //pp: Arc<Mutex<PublicParams<G1, G2, C1, C2>>>,          //&'a PublicParams<G1, G2, C1, C2>,
    //z0_primary: &Vec<<G1 as Group>::Scalar>,
    //num_steps: usize,
    proof_info: ProofInfo,
) {
    println!("Proving thread starting...");

    // recursive SNARK
    let mut recursive_snark: Option<RecursiveSNARK<G1, G2, C1, C2>> = None;
    // trivial circuit
    let circuit_secondary = TrivialTestCircuit::new(StepCounterType::External);
    let z0_secondary = vec![<G2 as Group>::Scalar::zero()];

    for i in 0..proof_info.num_steps {
        println!("PROVING STEP {}", i);
        let test = format!("step {}", i);

        // blocks until we receive first witness
        let circuit_primary = recv.recv().unwrap();

        //let start = Instant::now();
        //println!("STEP CIRC WIT for i={}: {:#?}", i, circuit_primary);
        log::tic(Component::Prover, &test, "prove step");
        let result = RecursiveSNARK::prove_step(
            &proof_info.pp.lock().unwrap(),
            recursive_snark,
            circuit_primary.clone(),
            circuit_secondary.clone(),
            proof_info.z0_primary.clone(),
            z0_secondary.clone(),
        );
        log::stop(Component::Prover, &test, "prove step");
        //println!("prove step {:#?}", result);

        assert!(result.is_ok());
        println!(
            "RecursiveSNARK::prove_step {}: {:?} ",
            i,
            result.is_ok(),
            //start.elapsed()
        );
        recursive_snark = Some(result.unwrap());
        println!("PROVING FINSIHED STEP {}", i);
    }

    assert!(recursive_snark.is_some());
    let recursive_snark = recursive_snark.unwrap();

    // verify recursive - TODO we can get rid of this verify once everything works
    /*    let res = recursive_snark.verify(
            &pp,
            FINAL_EXTERNAL_COUNTER,
            z0_primary.clone(),
            z0_secondary.clone(),
        );
        // println!("Recursive res: {:#?}", res);

        assert!(res.is_ok()); // TODO delete
    */

    // compressed SNARK
    log::tic(Component::Prover, "Proof", "Compressed SNARK");
    let res = CompressedSNARK::<_, _, _, _, S1, S2>::prove(
        &proof_info.pp.lock().unwrap(),
        &recursive_snark,
    );
    log::stop(Component::Prover, "Proof", "Compressed SNARK");

    assert!(res.is_ok());
    let compressed_snark = res.unwrap();

    log::space(
        Component::Prover,
        "add test",
        "Compressed SNARK size",
        serde_json::to_string(&compressed_snark).unwrap().len(),
    );

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
    let res = compressed_snark.verify(
        &pp.lock().unwrap(),
        FINAL_EXTERNAL_COUNTER,
        z0_primary,
        z0_secondary,
    );
    assert!(res.is_ok());

    // final "in the clear" V checks
    // // state, char, opt<hash>, opt<v,q for eval>, opt<v,q for doc>, accepting
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
                zn[2 + qd_len],
                &table,
                doc_len,
                None,
                None,
                None,
                Some(zn[1..(qd_len + 1)].to_vec()),
                Some(zn[1 + qd_len]),
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
                zn[1 + q_len + 1 + qd_len + 1],
                &table,
                doc_len,
                Some(zn[1..(q_len + 1)].to_vec()),
                Some(zn[q_len + 1]),
                None,
                Some(zn[(1 + q_len + 1)..(1 + q_len + 1 + qd_len)].to_vec()),
                Some(zn[1 + q_len + 1 + qd_len]),
            );
        }
    }
}

#[cfg(test)]
mod tests {

    use crate::backend::framework::*;
    use crate::backend::r1cs_helper::init;
    use crate::dfa::NFA;
    use crate::regex::Regex;

    fn backend_test(
        ab: String,
        rstr: String,
        doc: Vec<String>,
        batching_type: Option<JBatching>,
        commit_docype: Option<JCommit>,
        batch_sizes: Vec<usize>,
    ) {
        let r = Regex::new(&rstr);
        let dfa = NFA::new(&ab[..], r);

        init();
        for b in batch_sizes {
            run_backend(
                dfa.clone(),
                doc.clone(),
                batching_type.clone(),
                commit_docype.clone(),
                b,
            );
        }
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
            vec![0, 2],
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
            vec![0, 2],
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
            vec![0, 2],
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
            vec![0, 2],
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

type G1 = pasta_curves::pallas::Point;
type G2 = pasta_curves::vesta::Point;
type C1 = NFAStepCircuit<<G1 as Group>::Scalar>;
type C2 = TrivialTestCircuit<<G2 as Group>::Scalar>;
type EE1 = nova_snark::provider::ipa_pc::EvaluationEngine<G1>;
type EE2 = nova_snark::provider::ipa_pc::EvaluationEngine<G2>;
type S1 = nova_snark::spartan::RelaxedR1CSSNARK<G1, EE1>;
type S2 = nova_snark::spartan::RelaxedR1CSSNARK<G2, EE2>;

use crate::{
    backend::{
        commitment::*,
        costs::{full_round_cost_model, logmn},
        merkle_tree::{MerkleCommitment, MerkleWit},
        nova::*,
        r1cs::*,
        r1cs_helper::trace_preprocessing,
    },
    frontend::safa::SAFA,
};
use circ::target::r1cs::{wit_comp::StagedWitCompEvaluator, ProverData};
use fxhash::FxHashMap;
use generic_array::typenum;
use neptune::{
    poseidon::PoseidonConstants,
    sponge::vanilla::{Sponge, SpongeTrait},
    Strength,
};
use nova_snark::{
    provider::pedersen::CompressedCommitment,
    traits::{circuit::TrivialTestCircuit, Group},
    CompressedSNARK, PublicParams, RecursiveSNARK, StepCounterType, FINAL_EXTERNAL_COUNTER,
};
use rug::Integer;
use serde::{Deserialize, Serialize};
use std::path::PathBuf;
use std::sync::mpsc;
use std::sync::mpsc::{Receiver, Sender};
use std::sync::{Arc, Mutex};
use std::thread;

pub struct ProverInfo {
    commit: ReefCommitment,
    pc: PoseidonConstants<<G1 as Group>::Scalar, typenum::U4>,
    pp: Arc<Mutex<PublicParams<G1, G2, C1, C2>>>,
    z0_primary: Vec<<G1 as Group>::Scalar>,
    table: Vec<Integer>,
    proj_chunk_idx: Option<Vec<usize>>,
    projections: bool,
    hybrid_len: Option<usize>,
}

#[derive(Deserialize, Serialize)]
pub struct Proofs {
    pub compressed_snark: CompressedSNARK<G1, G2, C1, C2, S1, S2>,
    pub consist_proof: Option<ConsistencyProof>,
}

#[cfg(feature = "metrics")]
use metrics::metrics::{log, log::Component};

pub fn run_committer(doc: &Vec<char>, ab: &String, merkle: bool) -> ReefCommitment {
    let udoc = doc_transform(ab, doc);

    #[cfg(feature = "metrics")]
    log::tic(Component::CommitmentGen, "generation");

    let sc = if !merkle {
        None
    } else {
        Some(Sponge::<<G1 as Group>::Scalar, typenum::U4>::api_constants(
            Strength::Standard,
        ))
    };

    let reef_commit = ReefCommitment::new(udoc.clone(), doc.len(), merkle, sc);

    reef_commit
}

pub fn run_prover(
    reef_commit: ReefCommitment,
    ab: String,
    safa: SAFA<char>,
    doc: Vec<char>,
    temp_batch_size: usize, // this may be 0 if not overridden, only use to feed into R1CS object
    projections: bool,
    hybrid: bool,
    merkle: bool,
    out_write: Option<PathBuf>,
) -> (
    CompressedSNARK<G1, G2, C1, C2, S1, S2>,
    Option<ConsistencyProof>,
) {
    // okay to regen
    let sc = Sponge::<<G1 as Group>::Scalar, typenum::U4>::api_constants(Strength::Standard);

    let (sender, recv): (
        Sender<Option<NFAStepCircuit<<G1 as Group>::Scalar>>>,
        Receiver<Option<NFAStepCircuit<<G1 as Group>::Scalar>>>,
    ) = mpsc::channel();

    let (send_setup, recv_setup): (Sender<ProverInfo>, Receiver<ProverInfo>) = mpsc::channel();

    let (sender_qv, recv_qv): (
        Sender<(Vec<Integer>, Integer)>,
        Receiver<(Vec<Integer>, Integer)>,
    ) = mpsc::channel();

    let solver_thread = thread::spawn(move || {
        let hash_salt = reef_commit.hash_salt();

        let udoc = doc_transform(&ab, &doc);
        let udoc_len = udoc.len();
        let (mut r1cs_converter, circ_data, z0_primary, pp) = pub_setup(
            &sc,
            ab,
            &safa,
            Some(udoc),
            udoc_len,
            doc.len(),
            temp_batch_size,
            projections,
            hybrid,
            merkle,
            hash_salt,
            reef_commit.doc_commit_hash(),
        );

        let mc = reef_commit.merkle.clone();
        send_setup
            .send(ProverInfo {
                pc: sc,
                pp: Arc::new(Mutex::new(pp)),
                z0_primary,
                commit: reef_commit,
                table: r1cs_converter.table.clone(),
                proj_chunk_idx: r1cs_converter.proj_chunk_idx.clone(),
                projections: r1cs_converter.doc_subset.is_some(),
                hybrid_len: r1cs_converter.hybrid_len,
            })
            .unwrap();

        #[cfg(feature = "metrics")]
        log::tic(Component::Prover, "prove+wit");
        solve(
            sender,
            sender_qv,
            &mut r1cs_converter,
            &circ_data,
            &doc,
            hash_salt,
            mc,
        );
    });

    //get args
    let prover_info = recv_setup.recv().unwrap();

    let (compressed_snark, consist_proof) = prove(recv, recv_qv, &prover_info, out_write.clone());

    // rejoin child
    solver_thread.join().expect("setup/solver thread panicked");

    (compressed_snark, consist_proof)
}

fn setup<'a>(
    r1cs_converter: &R1CS<<G1 as Group>::Scalar, char>,
    circ_data: &'a ProverData,
    hash_salt: <G1 as Group>::Scalar,
) -> (Vec<<G1 as Group>::Scalar>, PublicParams<G1, G2, C1, C2>) {
    let current_state = r1cs_converter.safa.get_init().index();
    let mut z = vec![<G1 as Group>::Scalar::from(current_state as u64)];

    let stack_len = r1cs_converter.max_stack;

    // use "empty" (witness-less) circuit to generate nova F
    let stack_ptr = <G1 as Group>::Scalar::zero();
    let stack = vec![<G1 as Group>::Scalar::zero(); stack_len];

    let empty_glue;
    if r1cs_converter.merkle {
        let q_len = logmn(r1cs_converter.table.len());

        let q = vec![<G1 as Group>::Scalar::zero(); q_len];
        let v = <G1 as Group>::Scalar::zero();

        empty_glue = vec![
            GlueOpts::Merkle((q.clone(), v.clone(), stack_ptr.clone(), stack.clone())),
            GlueOpts::Merkle((q, v, stack_ptr, stack)),
        ];
        z.append(&mut vec![<G1 as Group>::Scalar::zero(); q_len]);
        z.push(int_to_ff(r1cs_converter.table[0].clone()));
    } else if r1cs_converter.hybrid_len.is_none() {
        let q_len = logmn(r1cs_converter.table.len());
        let qd_len = logmn(r1cs_converter.doc_len());

        let q = vec![<G1 as Group>::Scalar::zero(); q_len];
        let v = <G1 as Group>::Scalar::zero();
        let doc_q = vec![<G1 as Group>::Scalar::zero(); qd_len];
        let doc_v = <G1 as Group>::Scalar::zero();

        empty_glue = vec![
            GlueOpts::Split((
                q.clone(),
                v.clone(),
                doc_q.clone(),
                doc_v.clone(),
                stack_ptr.clone(),
                stack.clone(),
            )),
            GlueOpts::Split((q, v, doc_q, doc_v, stack_ptr, stack)),
        ];
        z.append(&mut vec![<G1 as Group>::Scalar::zero(); q_len]);
        z.push(int_to_ff(r1cs_converter.table[0].clone()));

        // technically not correct - but I think this is fine as a placeholder
        z.append(&mut vec![<G1 as Group>::Scalar::zero(); qd_len]);
        let d0 = <G1 as Group>::Scalar::zero();

        let d = calc_d(&[d0, hash_salt], &r1cs_converter.pc);
        z.push(d);
    } else {
        let hq_len = logmn(r1cs_converter.hybrid_len.unwrap());
        let hq = vec![<G1 as Group>::Scalar::zero(); hq_len];
        let hv = <G1 as Group>::Scalar::zero();
        empty_glue = vec![
            GlueOpts::Hybrid((hq.clone(), hv.clone(), stack_ptr.clone(), stack.clone())),
            GlueOpts::Hybrid((hq, hv, stack_ptr, stack)),
        ];
        z.append(&mut vec![<G1 as Group>::Scalar::zero(); hq_len]);
        let d = calc_d(
            &[int_to_ff(r1cs_converter.table[0].clone()), hash_salt],
            &r1cs_converter.pc,
        );
        z.push(d);
    }

    z.push(<G1 as Group>::Scalar::from(0 as u64));
    z.append(&mut vec![
        <G1 as Group>::Scalar::from(
            r1cs_converter.kid_padding as u64
        );
        stack_len
    ]);
    z.push(<G1 as Group>::Scalar::from(0 as u64));

    // empty wits
    let merkle_wits = if r1cs_converter.merkle {
        let mut w = vec![];

        for _b in 0..r1cs_converter.batch_size {
            let mut sub_w = vec![];

            sub_w.push(MerkleWit {
                l_or_r: true,
                opposite_idx: Some(<G1 as Group>::Scalar::zero()),
                opposite: <G1 as Group>::Scalar::zero(),
            });

            for _h in 0..(logmn(r1cs_converter.udoc_len) - 1) {
                sub_w.push(MerkleWit {
                    l_or_r: true,
                    opposite_idx: None,
                    opposite: <G1 as Group>::Scalar::zero(),
                });
            }

            w.push(sub_w);
        }

        Some(w)
    } else {
        None
    };

    let circuit_primary: NFAStepCircuit<<G1 as Group>::Scalar> = NFAStepCircuit::new(
        circ_data.r1cs.clone(),
        None,
        r1cs_converter.pc.clone(),
        vec![<G1 as Group>::Scalar::zero(); 2],
        vec![<G1 as Group>::Scalar::zero(); 2],
        empty_glue,
        r1cs_converter.batch_size,
        r1cs_converter.max_branches,
        <G1 as Group>::Scalar::zero(),
        <G1 as Group>::Scalar::zero(),
        <G1 as Group>::Scalar::zero(),
        merkle_wits,
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
    log::r1cs(Component::Prover, "step_circuit", pp.num_constraints().0);
    #[cfg(feature = "metrics")]
    log::r1cs(
        Component::Prover,
        "verifier_circuit",
        pp.num_constraints().1,
    );

    println!(
        "Number of constraints (primary circuit): {}",
        pp.num_constraints().0
    );
    let is_hybrid = match r1cs_converter.hybrid_len {
        Some(_) => true,
        _ => false,
    };
    println!(
        "Estimated Number of constraints: {}",
        full_round_cost_model(
            &r1cs_converter.safa,
            r1cs_converter.batch_size,
            r1cs_converter.udoc_len,
            is_hybrid,
            r1cs_converter.hybrid_len,
            false,
            r1cs_converter.max_offsets,
            r1cs_converter.max_branches,
            r1cs_converter.max_stack
        )
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

    let z0_primary = z;

    (z0_primary, pp)
}

fn solve<'a>(
    sender: Sender<Option<NFAStepCircuit<<G1 as Group>::Scalar>>>,
    sender_qv: Sender<(Vec<Integer>, Integer)>, //itness<<G1 as Group>::Scalar>>,
    r1cs_converter: &mut R1CS<<G1 as Group>::Scalar, char>,
    circ_data: &'a ProverData,
    doc: &Vec<char>,
    hash_salt: <G1 as Group>::Scalar,
    merkle_commit: Option<MerkleCommitment<<G1 as Group>::Scalar>>,
) {
    println!("Solving thread starting...");

    let mut wits;
    let mut running_q: Option<Vec<Integer>> = None;
    let mut running_v: Option<Integer> = None;
    let mut next_running_q: Option<Vec<Integer>>;
    let mut next_running_v: Option<Integer>;
    let mut doc_running_q: Option<Vec<Integer>> = None;
    let mut doc_running_v: Option<Integer> = None;
    let mut next_doc_running_q: Option<Vec<Integer>>;
    let mut next_doc_running_v: Option<Integer>;
    let mut hybrid_running_q: Option<Vec<Integer>> = None;
    let mut hybrid_running_v: Option<Integer> = None;
    let mut next_hybrid_running_q: Option<Vec<Integer>>;
    let mut next_hybrid_running_v: Option<Integer>;
    let mut merkle_lookups: Option<Vec<usize>>;

    let mut prev_cursor = 0;
    let mut next_cursor;
    let mut stack_ptr_0 = 0;
    let mut stack_ptr_popped;
    let mut stack_in = vec![r1cs_converter.kid_padding; r1cs_converter.max_stack];
    let mut stack_out;

    let mut current_state = r1cs_converter.safa.get_init().index();
    let mut next_state = 0;

    #[cfg(feature = "metrics")]
    log::tic(Component::Solver, "fa_solver");

    let trace = r1cs_converter.safa.solve(doc);
    if trace.is_none() {
        panic!("No solution found");
    }
    let mut sols = trace_preprocessing(&trace);

    #[cfg(feature = "metrics")]
    log::stop(Component::Solver, "fa_solver");

    let commit_blind = r1cs_converter.doc_hash;

    let mut i = 0;
    while r1cs_converter.sol_num < sols.len() {
        #[cfg(feature = "metrics")]
        log::tic(
            Component::Solver,
            format!("witness_generation_{}", i).as_str(),
        );
        (
            wits,
            next_state,
            next_running_q,
            next_running_v,
            next_doc_running_q,
            next_doc_running_v,
            next_hybrid_running_q,
            next_hybrid_running_v,
            next_cursor,
            merkle_lookups,
        ) = r1cs_converter.gen_wit_i(
            &mut sols,
            i,
            next_state,
            running_q.clone(),
            running_v.clone(),
            doc_running_q.clone(),
            doc_running_v.clone(),
            hybrid_running_q.clone(),
            hybrid_running_v.clone(),
            prev_cursor.clone(),
        );
        stack_ptr_popped = r1cs_converter.stack_ptr;
        stack_out = vec![];
        for (cur, kid) in &r1cs_converter.stack {
            stack_out.push(cur * r1cs_converter.num_states + kid);
        }

        let sp_0 = <G1 as Group>::Scalar::from(stack_ptr_0 as u64);
        let spp = <G1 as Group>::Scalar::from(stack_ptr_popped as u64);
        let stk_in = stack_in
            .clone()
            .into_iter()
            .map(|x| <G1 as Group>::Scalar::from(x as u64))
            .collect();
        let stk_out = stack_out
            .clone()
            .into_iter()
            .map(|x| <G1 as Group>::Scalar::from(x as u64))
            .collect();

        let glue = if r1cs_converter.merkle {
            let q_len = logmn(r1cs_converter.table.len());

            let q = match running_q {
                Some(rq) => rq.into_iter().map(|x| int_to_ff(x)).collect(),
                None => vec![<G1 as Group>::Scalar::zero(); q_len],
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

            vec![
                GlueOpts::Merkle((q, v, sp_0, stk_in)),
                GlueOpts::Merkle((next_q, next_v, spp, stk_out)),
            ]
        } else if r1cs_converter.hybrid_len.is_none() {
            let q_len = logmn(r1cs_converter.table.len());
            let qd_len = logmn(r1cs_converter.doc_len());

            let q = match running_q {
                Some(rq) => rq.into_iter().map(|x| int_to_ff(x)).collect(),
                None => vec![<G1 as Group>::Scalar::zero(); q_len],
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
                None => vec![<G1 as Group>::Scalar::zero(); qd_len],
            };

            let doc_v = match doc_running_v {
                Some(rv) => int_to_ff(rv),
                None => {
                    if i > 0 {
                        //r1cs_converter.udoc.is_some() {
                        <G1 as Group>::Scalar::from(r1cs_converter.udoc.as_ref().unwrap()[0] as u64)
                    } else {
                        // again, dicey correctness
                        <G1 as Group>::Scalar::zero()
                    }
                }
            };
            let doc_v_hash = calc_d(&[doc_v, hash_salt], &r1cs_converter.pc);

            let next_doc_q = next_doc_running_q
                .clone()
                .unwrap()
                .into_iter()
                .map(|x| int_to_ff(x))
                .collect();
            let next_doc_v: <G1 as Group>::Scalar = int_to_ff(next_doc_running_v.clone().unwrap());
            let next_doc_v_hash = calc_d(&[next_doc_v, hash_salt], &r1cs_converter.pc);

            vec![
                GlueOpts::Split((q, v, doc_q, doc_v_hash, sp_0, stk_in)),
                GlueOpts::Split((next_q, next_v, next_doc_q, next_doc_v_hash, spp, stk_out)),
            ]
        } else {
            let hq_len = logmn(r1cs_converter.hybrid_len.unwrap());

            let hq = match hybrid_running_q {
                Some(hq) => hq.into_iter().map(|x| int_to_ff(x)).collect(),
                None => vec![<G1 as Group>::Scalar::zero(); hq_len],
            };

            let hv: <G1 as Group>::Scalar = match hybrid_running_v {
                Some(hv) => int_to_ff(hv),
                None => int_to_ff(r1cs_converter.table[0].clone()), // table goes first
            };
            let hv_hash = calc_d(&[hv, hash_salt], &r1cs_converter.pc);

            let next_hq = next_hybrid_running_q
                .clone()
                .unwrap()
                .into_iter()
                .map(|x| int_to_ff(x))
                .collect();
            let next_hv: <G1 as Group>::Scalar = int_to_ff(next_hybrid_running_v.clone().unwrap());
            let next_hv_hash = calc_d(&[next_hv, hash_salt], &r1cs_converter.pc);

            vec![
                GlueOpts::Hybrid((hq, hv_hash, sp_0, stk_in)),
                GlueOpts::Hybrid((next_hq, next_hv_hash, spp, stk_out)),
            ]
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

        let mut merkle_root = <G1 as Group>::Scalar::zero();
        let mut merkle_wits = None;
        if merkle_commit.is_some() {
            let mc = merkle_commit.as_ref().unwrap();
            (merkle_root, merkle_wits) =
                (mc.commitment, Some(mc.make_wits(&merkle_lookups.unwrap())));
        }

        let circuit_primary: NFAStepCircuit<<G1 as Group>::Scalar> = NFAStepCircuit::new(
            circ_data.r1cs.clone(),
            values,
            r1cs_converter.pc.clone(),
            vec![
                <G1 as Group>::Scalar::from(current_state as u64),
                <G1 as Group>::Scalar::from(next_state as u64),
            ],
            vec![
                <G1 as Group>::Scalar::from(prev_cursor as u64),
                <G1 as Group>::Scalar::from(next_cursor as u64),
            ],
            glue,
            r1cs_converter.batch_size,
            r1cs_converter.max_branches,
            commit_blind,
            hash_salt,
            merkle_root,
            merkle_wits,
        );

        #[cfg(feature = "metrics")]
        {
            log::stop(
                Component::Solver,
                format!("witness_generation_{}", i).as_str(),
            );
        }

        sender.send(Some(circuit_primary)).unwrap(); //witness_i).unwrap();

        // for next i+1 round
        current_state = next_state;
        running_q = next_running_q;
        running_v = next_running_v;
        doc_running_q = next_doc_running_q;
        doc_running_v = next_doc_running_v;
        hybrid_running_q = next_hybrid_running_q;
        hybrid_running_v = next_hybrid_running_v;
        prev_cursor = next_cursor;
        stack_ptr_0 = stack_ptr_popped;
        stack_in = stack_out;
        i += 1
    }

    sender.send(None).unwrap();

    if r1cs_converter.merkle {
        // do nothing
    } else if r1cs_converter.hybrid_len.is_none() {
        sender_qv
            .send((doc_running_q.unwrap(), doc_running_v.unwrap()))
            .unwrap();
    } else {
        sender_qv
            .send((hybrid_running_q.unwrap(), hybrid_running_v.unwrap()))
            .unwrap();
    }
}

fn prove(
    recv: Receiver<Option<NFAStepCircuit<<G1 as Group>::Scalar>>>,
    recv_qv: Receiver<(Vec<Integer>, Integer)>,
    prover_info: &ProverInfo,
    out_write: Option<PathBuf>,
) -> (
    CompressedSNARK<G1, G2, C1, C2, S1, S2>,
    Option<ConsistencyProof>,
) {
    println!("Proving thread starting...");

    // recursive SNARK
    let mut recursive_snark: Option<RecursiveSNARK<G1, G2, C1, C2>> = None;
    // trivial circuit
    let circuit_secondary = TrivialTestCircuit::new(StepCounterType::External);
    let z0_secondary = vec![<G2 as Group>::Scalar::zero()];

    // blocks until we receive first witness
    let mut circuit_primary = recv.recv().unwrap();

    let mut i = 0;

    while circuit_primary.is_some() {
        #[cfg(feature = "metrics")]
        log::tic(Component::Prover, format!("prove_{}", i).as_str());

        let result = RecursiveSNARK::prove_step(
            &prover_info.pp.lock().unwrap(),
            recursive_snark,
            circuit_primary.clone().unwrap(),
            circuit_secondary.clone(),
            prover_info.z0_primary.clone(),
            z0_secondary.clone(),
        );

        #[cfg(feature = "metrics")]
        {
            log::stop(Component::Prover, format!("prove_{}", i).as_str());
            log::write_csv(&out_write.clone().unwrap().as_path().display().to_string()).unwrap();
        }

        recursive_snark = Some(result.unwrap());

        i += 1;
        circuit_primary = recv.recv().unwrap();
    }

    assert!(recursive_snark.is_some());
    let recursive_snark = recursive_snark.unwrap();

    // compressed SNARK
    #[cfg(feature = "metrics")]
    log::tic(Component::Prover, "compressed_snark");
    let res = CompressedSNARK::<_, _, _, _, S1, S2>::prove(
        &prover_info.pp.lock().unwrap(),
        &recursive_snark,
    );
    #[cfg(feature = "metrics")]
    log::stop(Component::Prover, "compressed_snark");

    assert!(res.is_ok());
    let compressed_snark = res.unwrap();

    let mut consist_proof = None;
    if prover_info.commit.nldoc.is_some() {
        let dc = prover_info.commit.nldoc.as_ref().unwrap();
        let (q, v) = recv_qv.recv().unwrap();

        #[cfg(feature = "metrics")]
        log::tic(Component::Prover, "consistency_proof");
        //Doc dot prod and consistency
        let cp = dc.prove_consistency(
            &prover_info.pc,
            &prover_info.table,
            prover_info.proj_chunk_idx.clone(),
            q,
            v,
            prover_info.projections,
            prover_info.hybrid_len.is_some(),
        );
        #[cfg(feature = "metrics")]
        log::stop(Component::Prover, "consistency_proof");

        consist_proof = Some(cp)
    }

    println!("Proving Finished");

    #[cfg(feature = "metrics")]
    {
        log::stop(Component::Prover, "prove+wit");
    }

    #[cfg(feature = "metrics")]
    log::space(
        Component::Prover,
        "snark_size",
        bincode::serialize(&compressed_snark).unwrap().len(),
    );

    #[cfg(feature = "metrics")]
    {
        let (commit_sz, consistency_proof_size) = proof_size(&consist_proof, &prover_info.commit);
        log::space(
            Component::Prover,
            "consistency_proof",
            consistency_proof_size,
        );
        log::space(Component::CommitmentGen, "commitment", commit_sz);
    }

    (compressed_snark, consist_proof)
}

pub fn run_verifier(
    reef_commit: ReefCommitment,
    ab: &String,
    safa: SAFA<char>,
    temp_batch_size: usize, // this may be 0 if not overridden, only use to feed into R1CS object
    projections: bool,
    hybrid: bool,
    merkle: bool,
    compressed_snark: CompressedSNARK<G1, G2, C1, C2, S1, S2>,
    consist_proof: Option<ConsistencyProof>,
) {
    let sc = Sponge::<<G1 as Group>::Scalar, typenum::U4>::api_constants(Strength::Standard);

    // rederive pp, z0, table information
    let (r1cs_converter, _circ_data, z0_primary, pp) = pub_setup(
        &sc,
        ab.clone(),
        &safa,
        None,
        reef_commit.udoc_len,
        reef_commit.orig_doc_len,
        temp_batch_size,
        projections,
        hybrid,
        merkle,
        reef_commit.hash_salt(),
        reef_commit.doc_commit_hash(),
    );

    let doc_len = r1cs_converter.doc_len(); // projected;

    verify(
        compressed_snark,
        z0_primary,
        pp,
        reef_commit,
        r1cs_converter.table,
        r1cs_converter.exit_state,
        doc_len,
        r1cs_converter.hybrid_len,
        consist_proof,
    );
}

fn verify(
    compressed_snark: CompressedSNARK<G1, G2, C1, C2, S1, S2>,
    z0_primary: Vec<<G1 as Group>::Scalar>,
    pp: PublicParams<G1, G2, C1, C2>,
    reef_commit: ReefCommitment,
    table: Vec<Integer>,
    exit_state: usize,
    proj_doc_len: usize,
    hybrid_len: Option<usize>,
    consist_proof: Option<ConsistencyProof>,
) {
    println!("Verification starting...");

    let z0_secondary = vec![<G2 as Group>::Scalar::zero()];

    #[cfg(feature = "metrics")]
    log::tic(Component::Verifier, "snark_verification");

    let res = compressed_snark.verify(&pp, FINAL_EXTERNAL_COUNTER, z0_primary, z0_secondary);
    #[cfg(feature = "metrics")]
    log::stop(Component::Verifier, "snark_verification");

    assert!(res.is_ok());

    #[cfg(feature = "metrics")]
    log::tic(Component::Verifier, "consistency_verification");

    // [state, <q,v for eval claim>, <q,"v"(hash), for doc claim>, stack_ptr, <stack>]
    let zn = res.unwrap().0;

    let (stack_ptr, eval_q, eval_v) = match (reef_commit.nldoc, reef_commit.merkle) {
        (None, Some(_)) => {
            // merkle
            let q_len = logmn(table.len());

            (
                zn[q_len + 2],
                Some(zn[1..(q_len + 1)].to_vec()),
                Some(zn[q_len + 1]),
            )
        }
        (Some(dc), None) => {
            let cp = consist_proof.unwrap();
            if hybrid_len.is_none() {
                let q_len = logmn(table.len());
                let qd_len = logmn(proj_doc_len);
                assert_eq!(cp.hash_d, zn[2 + q_len + qd_len]);

                dc.verify_consistency(cp);
                (
                    zn[q_len + qd_len + 3],
                    Some(zn[1..(q_len + 1)].to_vec()),
                    Some(zn[q_len + 1]),
                )
            } else {
                let h_len = logmn(hybrid_len.unwrap());
                assert_eq!(cp.hash_d, zn[1 + h_len]);

                dc.verify_consistency(cp);
                (zn[h_len + 2], None, None)
            }
        }
        (_, _) => {
            panic!("weird commitment");
        }
    };

    final_clear_checks(stack_ptr, &table, eval_q, eval_v);

    // final accepting
    assert_eq!(zn[0], <G1 as Group>::Scalar::from(exit_state as u64));

    println!("Verification Finished");

    #[cfg(feature = "metrics")]
    log::stop(Component::Verifier, "consistency_verification");
}

fn proof_size(csp: &Option<ConsistencyProof>, rc: &ReefCommitment) -> (usize, usize) {
    let mut doc_size = 0;
    if rc.nldoc.is_some() {
        let dc = &rc.nldoc.as_ref().unwrap().doc_commit;
        for c in 0..dc.comm.len() {
            let cc: CompressedCommitment<<G1 as Group>::CompressedGroupElement> = dc.comm[c];
            doc_size += bincode::serialize(&cc).unwrap().len();
        }
    };

    let cp = csp.as_ref().unwrap();

    let snark_size = bincode::serialize(&cp.snark).unwrap().len();
    let v_size = bincode::serialize(&cp.v_commit).unwrap().len();
    let vprime_size = if cp.v_prime_commit.is_some() {
        bincode::serialize(&cp.v_prime_commit.unwrap())
            .unwrap()
            .len()
    } else {
        0
    };
    let ipa_size = bincode::serialize(&cp.ipa).unwrap().len();
    let q_size = bincode::serialize(&cp.running_q).unwrap().len();

    let eq_proof_size = bincode::serialize(&cp.eq_proof).unwrap().len();

    (
        doc_size,
        snark_size + v_size + vprime_size + ipa_size + q_size + eq_proof_size,
    )
}

pub fn pub_setup(
    pc: &PoseidonConstants<<G1 as Group>::Scalar, typenum::U4>,
    ab: String,
    safa: &SAFA<char>,
    udoc: Option<Vec<usize>>,
    udoc_len: usize,
    doc_len: usize,
    temp_batch_size: usize, // this may be 0 if not overridden, only use to feed into R1CS object
    projections: bool,
    hybrid: bool,
    merkle: bool,
    hash_salt: <G1 as Group>::Scalar,
    commit_hash: <G1 as Group>::Scalar,
) -> (
    R1CS<<G1 as Group>::Scalar, char>,
    ProverData,
    Vec<<G1 as Group>::Scalar>,
    PublicParams<G1, G2, C1, C2>,
) {
    let batch_size = temp_batch_size;
    let proj = if projections { safa.projection() } else { None };

    #[cfg(feature = "metrics")]
    log::tic(Component::Compiler, "r1cs_init");
    let mut r1cs_converter = R1CS::new(
        &ab,
        safa,
        udoc,
        udoc_len,
        doc_len,
        batch_size,
        proj,
        hybrid,
        merkle,
        pc.clone(),
        commit_hash,
    );

    #[cfg(feature = "metrics")]
    log::stop(Component::Compiler, "r1cs_init");
    println!(
        "Merkle: {} / Hybrid: {} / Projections: {}",
        r1cs_converter.merkle,
        r1cs_converter.hybrid_len.is_some(),
        r1cs_converter.doc_subset.is_some()
    );

    #[cfg(feature = "metrics")]
    {
        log::stop(Component::CommitmentGen, "generation");
        log::tic(Component::Compiler, "constraint_generation");
    }

    let (prover_data, _verifier_data) = r1cs_converter.to_circuit();

    #[cfg(feature = "metrics")]
    {
        log::stop(Component::Compiler, "constraint_generation");
        log::tic(Component::Compiler, "snark_setup");
    }
    let (z0_primary, pp) = setup(&r1cs_converter, &prover_data, hash_salt);

    #[cfg(feature = "metrics")]
    log::stop(Component::Compiler, "snark_setup");

    (r1cs_converter, prover_data, z0_primary, pp)
}

pub fn doc_transform(ab: &String, doc: &Vec<char>) -> Vec<usize> {
    let mut num_ab: FxHashMap<Option<char>, usize> = FxHashMap::default();
    let mut i = 0;
    for c in ab.clone().chars() {
        num_ab.insert(Some(c), i);
        i += 1;
    }
    num_ab.insert(None, i + 1); // EPSILON
    num_ab.insert(Some(26u8 as char), i + 2); // EOF

    let mut udoc = vec![];
    for c in doc.clone().into_iter() {
        if !num_ab.contains_key(&Some(c)) {
            panic!("Character in document that's not in alphabet");
        }
        let u = num_ab[&Some(c)];
        udoc.push(u);
    }

    // EOF
    let u = num_ab[&Some(26u8 as char)];
    udoc.push(u);

    // EPSILON
    let u = num_ab[&None];
    udoc.push(u);

    // extend doc
    let base: usize = 2;
    let ext_len = base.pow(logmn(udoc.len()) as u32) - udoc.len();
    udoc.extend(vec![0; ext_len]);

    udoc
}

#[cfg(test)]
mod tests {

    use crate::backend::framework::*;
    use crate::backend::r1cs_helper::init;
    use crate::frontend::regex::re;
    use crate::frontend::safa::SAFA;
    use std::fs;

    fn backend_test(
        ab: String,
        rstr: String,
        doc: Vec<char>,
        batch_size: usize,
        projections: bool,
        hybrid: bool,
        merkle: bool,
        cmt_name: &str,
    ) {
        let r = re::simpl(re::new(&rstr));
        let safa = SAFA::new(&ab[..], &r);

        init();

        let reef_commit = run_committer(&doc, &ab, merkle);

        let cmt_data = bincode::serialize(&reef_commit).expect("Could not serialize");
        fs::write(format!("{}.cmt", cmt_name), cmt_data).expect("Unable to write file");

        let (compressed_snark, consist_proof) = run_prover(
            reef_commit,
            ab.clone(),
            safa.clone(),
            doc.clone(),
            batch_size,
            projections,
            hybrid,
            merkle,
            None,
        );

        let cmt_data = fs::read(format!("{}.cmt", cmt_name)).expect("Unable to read file");
        let reef_commit_2: ReefCommitment =
            bincode::deserialize(&cmt_data).expect("Could not deserialize");

        run_verifier(
            reef_commit_2,
            &ab,
            safa,
            batch_size,
            projections,
            hybrid,
            merkle,
            compressed_snark,
            consist_proof,
        );
    }

    #[test]
    fn e2e_sub_proj() {
        backend_test(
            "abcd".to_string(),
            "^................aaaaaa$".to_string(),
            ("ddddddddddddddddaaaaaa".to_string()).chars().collect(),
            0,
            false,
            false,
            false,
            "e2e_sub_proj",
        );
    }

    #[test]
    fn e2e_merkle() {
        backend_test(
            "abcd".to_string(),
            "^(?=a)ab(?=c)cd$".to_string(),
            ("abcd".to_string()).chars().collect(),
            0,
            false,
            false,
            true,
            "e2e_merkle",
        );
    }

    #[test]
    fn e2e_hybrid() {
        backend_test(
            "abcd".to_string(),
            "$a*bbbc*d*^".to_string(),
            ("aaabbbcccddd".to_string()).chars().collect(),
            0,
            false,
            true,
            false,
            "e2e_hybrid",
        );
    }

    #[test]
    fn e2e_projections() {
        backend_test(
            "abc".to_string(),
            "^....cc$".to_string(),
            ("aabbcc".to_string()).chars().collect(),
            0,
            false,
            false,
            false,
            "e2e_proj",
        );
    }

    #[test]
    fn e2e_q_overflow() {
        backend_test(
            "abcdefg".to_string(),
            "^gaa*bb*cc*dd*ee*f$".to_string(),
            ("gaaaaaabbbbbbccccccddddddeeeeeef".to_string())
                .chars()
                .collect(),
            33,
            false,
            false,
            false,
            "e2e_q_overflow",
        );
    }

    #[test]
    fn e2e_nest_forall() {
        backend_test(
            "abcd".to_string(),
            "^(?=a)ab(?=c)cd$".to_string(),
            ("abcd".to_string()).chars().collect(),
            0,
            false,
            false,
            false,
            "e2e_nest_forall",
        );
    }

    #[test]
    fn e2e_nl_nl() {
        backend_test(
            "ab".to_string(),
            "^a*b*$".to_string(),
            ("aaab".to_string())
                .chars()
                //.map(|c| c.to_string())
                .collect(),
            0,
            false,
            false,
            false,
            "e2e_nl",
        );
    }
}

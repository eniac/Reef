type G1 = pasta_curves::pallas::Point;
type G2 = pasta_curves::vesta::Point;
type C1 = NFAStepCircuit<<G1 as Group>::Scalar>;
type C2 = TrivialTestCircuit<<G2 as Group>::Scalar>;
type EE1 = nova_snark::provider::ipa_pc::EvaluationEngine<G1>;
type EE2 = nova_snark::provider::ipa_pc::EvaluationEngine<G2>;
type S1 = nova_snark::spartan::RelaxedR1CSSNARK<G1, EE1>;
type S2 = nova_snark::spartan::RelaxedR1CSSNARK<G2, EE2>;

use crate::backend::r1cs_helper::trace_preprocessing;
use crate::backend::{commitment::*, costs::logmn, nova::*, r1cs::*};
use crate::frontend::safa::SAFA;
use circ::target::r1cs::wit_comp::StagedWitCompEvaluator;
use circ::target::r1cs::{self, ProverData};
use ff::Field;
use generic_array::typenum;
use neptune::{
    sponge::vanilla::{Sponge, SpongeTrait},
    Strength,
};
use nova_snark::provider::ipa_pc::{InnerProductArgument, InnerProductInstance};
use nova_snark::spartan::direct::*;
use nova_snark::{
    provider::pedersen::Commitment,
    traits::{
        circuit::TrivialTestCircuit,
        commitment::{CommitmentEngineTrait, CommitmentTrait},
        evaluation::GetGeneratorsTrait,
        Group,
    },
    CompressedSNARK, PublicParams, RecursiveSNARK, StepCounterType, FINAL_EXTERNAL_COUNTER,
};
use rand::rngs::OsRng;
use rug::Integer;
use std::sync::mpsc;
use std::sync::mpsc::{Receiver, Sender};
use std::sync::{Arc, Mutex};
use std::thread;

struct ProofInfo {
    pp: Arc<Mutex<PublicParams<G1, G2, C1, C2>>>,
    z0_primary: Vec<<G1 as Group>::Scalar>,
    commit: ReefCommitment,
    table: Vec<Integer>,
    doc_len: usize,
    proj_doc_len: usize,
    exit_state: usize,
    projections: bool,
    hybrid_len: Option<usize>,
}

#[cfg(feature = "metrics")]
use metrics::metrics::{log, log::Component};

// gen R1CS object, commitment, make step circuit for nova
pub fn run_backend(
    safa: SAFA<char>,
    doc: Vec<char>,
    temp_batch_size: usize, // this may be 0 if not overridden, only use to feed into R1CS object
    projections: bool,
    hybrid: bool,
) {
    let (sender, recv): (
        Sender<Option<NFAStepCircuit<<G1 as Group>::Scalar>>>,
        Receiver<Option<NFAStepCircuit<<G1 as Group>::Scalar>>>,
    ) = mpsc::channel();

    let (send_setup, recv_setup): (Sender<ProofInfo>, Receiver<ProofInfo>) = mpsc::channel();

    let (sender_qv, recv_qv): (
        Sender<(Vec<Integer>, Integer)>,
        Receiver<(Vec<Integer>, Integer)>,
    ) = mpsc::channel();

    let solver_thread = thread::spawn(move || {
        // we do setup here to avoid unsafe passing

        // stop gap for cost model - don't need to time >:)
        let mut batch_size = if temp_batch_size == 0 {
            let trace = safa.solve(&doc);
            println!("post solve");
            let mut sols = trace_preprocessing(&trace, &safa);
            println!("post trace");

            let mut paths = vec![];
            let mut path_len = 1;

            for sol in sols {
                for elt in sol {
                    if safa.g[elt.from_node].is_and() {
                        if path_len > 1 {
                            paths.push(path_len);
                        }
                        path_len = 1;
                    } else if safa.accepting().contains(&elt.to_node) {
                        path_len += 1;
                        paths.push(path_len);
                    } else {
                        path_len += 1;
                    }
                }
            }

            if paths.len() == 1 {
                paths.len() / 2
            } else {
                //average(paths)
                (paths.iter().sum::<usize>() as f32 / paths.len() as f32).ceil() as usize
            }
        } else {
            temp_batch_size
        };
        batch_size += 1; // to last

        if batch_size < 2 {
            batch_size = 2;
        }
        println!("BATCH SIZE {:#?}", batch_size);

        #[cfg(feature = "metrics")]
        log::tic(Component::Compiler, "R1CS", "R1CS precomputations");

        let sc = Sponge::<<G1 as Group>::Scalar, typenum::U4>::api_constants(Strength::Standard);

        let proj = if projections { safa.projection() } else { None };
        println!("hybrid: {}", hybrid);
        let mut r1cs_converter = R1CS::new(&safa, &doc, batch_size, proj, hybrid, sc.clone());

        #[cfg(feature = "metrics")]
        log::stop(Component::Compiler, "R1CS", "R1CS precomputations");

        #[cfg(feature = "metrics")]
        log::tic(Component::Compiler, "R1CS", "Commitment Generations");
        let reef_commit =
            ReefCommitment::new(r1cs_converter.udoc.clone(), r1cs_converter.hybrid_len, &sc);
        r1cs_converter.doc_hash = Some(reef_commit.doc_commit_hash);
        let hash_salt = reef_commit.hash_salt.clone();

        #[cfg(feature = "metrics")]
        log::stop(Component::Compiler, "R1CS", "Commitment Generations");

        #[cfg(feature = "metrics")]
        log::tic(Component::Compiler, "R1CS", "To Circuit");

        let (prover_data, _verifier_data) = r1cs_converter.to_circuit();

        #[cfg(feature = "metrics")]
        log::stop(Component::Compiler, "R1CS", "To Circuit");

        #[cfg(feature = "metrics")]
        log::tic(Component::Compiler, "R1CS", "Proof Setup");
        let (z0_primary, pp) = setup(&r1cs_converter, &prover_data, hash_salt);

        #[cfg(feature = "metrics")]
        log::stop(Component::Compiler, "R1CS", "Proof Setup");

        send_setup
            .send(ProofInfo {
                pp: Arc::new(Mutex::new(pp)),
                z0_primary,
                commit: reef_commit,
                table: r1cs_converter.table.clone(),
                doc_len: r1cs_converter.udoc.len(),     // real
                proj_doc_len: r1cs_converter.doc_len(), // projected
                exit_state: r1cs_converter.exit_state,
                projections: r1cs_converter.doc_subset.is_some(),
                hybrid_len: r1cs_converter.hybrid_len,
            })
            .unwrap();

        #[cfg(feature = "metrics")]
        log::stop(Component::Compiler, "Compiler", "Full");

        #[cfg(feature = "metrics")]
        log::tic(Component::Solver, "Solve", "Framework Solve");
        solve(
            sender,
            sender_qv,
            &mut r1cs_converter,
            &prover_data,
            &doc,
            hash_salt,
        );

        #[cfg(feature = "metrics")]
        log::stop(Component::Solver, "Solve", "Framework Solve");
    });

    //get args
    let proof_info = recv_setup.recv().unwrap();

    prove_and_verify(recv, recv_qv, proof_info);

    // rejoin child
    solver_thread.join().expect("setup/solver thread panicked");
}

fn setup<'a>(
    r1cs_converter: &R1CS<<G1 as Group>::Scalar, char>,
    circ_data: &'a ProverData,
    claim_blind: <G1 as Group>::Scalar,
) -> (Vec<<G1 as Group>::Scalar>, PublicParams<G1, G2, C1, C2>) {
    let current_state = r1cs_converter.safa.get_init().index();

    let mut z = vec![<G1 as Group>::Scalar::from(current_state as u64)];

    let stack_len = r1cs_converter.max_stack;

    // use "empty" (witness-less) circuit to generate nova F
    let stack_ptr = <G1 as Group>::Scalar::zero();
    let stack = vec![<G1 as Group>::Scalar::zero(); stack_len];

    let empty_glue;
    if r1cs_converter.hybrid_len.is_none() {
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
        z.append(&mut vec![<G1 as Group>::Scalar::zero(); qd_len]);
        let d = calc_d_clear(
            &r1cs_converter.pc,
            claim_blind,
            Integer::from(r1cs_converter.udoc[0] as u64),
        );
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
        let d = calc_d_clear(
            &r1cs_converter.pc,
            claim_blind,
            r1cs_converter.table[0].clone(), // start with table
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

    // println!("Z LEN {:#?}", z.len());

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

    let z0_primary = z;

    (z0_primary, pp)
}

fn solve<'a>(
    sender: Sender<Option<NFAStepCircuit<<G1 as Group>::Scalar>>>,
    sender_qv: Sender<(Vec<Integer>, Integer)>, //itness<<G1 as Group>::Scalar>>,
    r1cs_converter: &mut R1CS<<G1 as Group>::Scalar, char>,
    circ_data: &'a ProverData,
    doc: &Vec<char>,
    claim_blind: <G1 as Group>::Scalar,
) {
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

    let mut prev_cursor = 0;
    let mut next_cursor;
    let mut stack_ptr_0 = 0;
    let mut stack_ptr_popped;
    let mut stack_in = vec![r1cs_converter.kid_padding; r1cs_converter.max_stack];
    let mut stack_out;

    let mut current_state = r1cs_converter.safa.get_init().index();
    // TODO don't recalc :(

    let mut next_state = 0;

    //measure safa solve
    let trace = r1cs_converter.safa.solve(doc);
    let mut sols = trace_preprocessing(&trace, &r1cs_converter.safa);
    //end safa solve

    let commit_blind = r1cs_converter.doc_hash.unwrap();

    let mut i = 0;
    while r1cs_converter.sol_num < sols.len() {
        #[cfg(feature = "metrics")]
        log::tic(
            Component::Solver,
            "Witness Generation",
            format!("step_{}", i).as_str(),
        );
        // allocate real witnesses for round i

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

        // TODO
        // just for debugging :)
        //circ_data.check_all(&wits);

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

        let glue = if r1cs_converter.hybrid_len.is_none() {
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
                Some(rv) => rv,
                None => Integer::from(r1cs_converter.udoc[0] as u64),
            };
            let doc_v_hash = calc_d_clear(&r1cs_converter.pc, claim_blind, doc_v.clone());

            let next_doc_q = next_doc_running_q
                .clone()
                .unwrap()
                .into_iter()
                .map(|x| int_to_ff(x))
                .collect();
            let next_doc_v = next_doc_running_v.clone().unwrap();
            let next_doc_v_hash = calc_d_clear(&r1cs_converter.pc, claim_blind, next_doc_v.clone());

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

            let hv = match hybrid_running_v {
                Some(hv) => hv,
                None => Integer::from(r1cs_converter.table[0].clone()), // table goes first
            };
            let hv_hash = calc_d_clear(&r1cs_converter.pc, claim_blind, hv.clone());

            let next_hq = next_hybrid_running_q
                .clone()
                .unwrap()
                .into_iter()
                .map(|x| int_to_ff(x))
                .collect();
            let next_hv = next_hybrid_running_v.clone().unwrap();
            let next_hv_hash = calc_d_clear(&r1cs_converter.pc, claim_blind, next_hv.clone());

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
            claim_blind,
        );

        #[cfg(feature = "metrics")]
        log::stop(
            Component::Solver,
            "Witness Generation",
            format!("step_{}", i).as_str(),
        );

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

    if r1cs_converter.hybrid_len.is_none() {
        sender_qv
            .send((doc_running_q.unwrap(), doc_running_v.unwrap()))
            .unwrap();
    } else {
        sender_qv
            .send((hybrid_running_q.unwrap(), hybrid_running_v.unwrap()))
            .unwrap();
    }
}

fn prove_and_verify(
    recv: Receiver<Option<NFAStepCircuit<<G1 as Group>::Scalar>>>,
    recv_qv: Receiver<(Vec<Integer>, Integer)>,
    mut proof_info: ProofInfo,
) {
    println!("Proving thread starting...");

    // recursive SNARK
    let mut recursive_snark: Option<RecursiveSNARK<G1, G2, C1, C2>> = None;
    // trivial circuit
    let circuit_secondary = TrivialTestCircuit::new(StepCounterType::External);
    let z0_secondary = vec![<G2 as Group>::Scalar::zero()];

    // blocks until we receive first witness
    let mut circuit_primary = recv.recv().unwrap();

    let cp_clone = circuit_primary.clone().unwrap();
    let pc = cp_clone.pc;
    let claim_blind = cp_clone.claim_blind;

    let mut i = 0;
    while circuit_primary.is_some() {
        #[cfg(feature = "metrics")]
        log::tic(Component::Prover, "prove", format!("prove_{}", i).as_str());

        let result = RecursiveSNARK::prove_step(
            &proof_info.pp.lock().unwrap(),
            recursive_snark,
            circuit_primary.clone().unwrap(),
            circuit_secondary.clone(),
            proof_info.z0_primary.clone(),
            z0_secondary.clone(),
        );

        #[cfg(feature = "metrics")]
        log::stop(Component::Prover, "prove", format!("prove_{}", i).as_str());
        /*
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
        */
        recursive_snark = Some(result.unwrap());

        i += 1;
        circuit_primary = recv.recv().unwrap();
    }

    assert!(recursive_snark.is_some());
    let recursive_snark = recursive_snark.unwrap();

    println!("post recurisve snark");

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

    let (q, v) = recv_qv.recv().unwrap();

    println!("post compress");

    #[cfg(feature = "metrics")]
    log::tic(Component::Prover, "Proof", "Consistency Proofs");
    //Doc dot prod and consistency
    let consist_proof = proof_info.commit.prove_consistency(
        &proof_info.table,
        proof_info.proj_doc_len,
        q,
        v,
        proof_info.projections,
        proof_info.hybrid_len.is_some(),
    );
    #[cfg(feature = "metrics")]
    log::stop(Component::Prover, "Proof", "Consistency Proofs");

    println!("post cp");

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
        proof_info.exit_state,
        proof_info.doc_len,
        proof_info.proj_doc_len,
        proof_info.hybrid_len,
        consist_proof,
    );

    println!("post verify");

    #[cfg(feature = "metrics")]
    log::stop(Component::Verifier, "Verification", "Full");
}

fn verify(
    compressed_snark: CompressedSNARK<G1, G2, C1, C2, S1, S2>,
    z0_primary: Vec<<G1 as Group>::Scalar>,
    pp: Arc<Mutex<PublicParams<G1, G2, C1, C2>>>,
    reef_commit: ReefCommitment,
    table: Vec<Integer>,
    exit_state: usize,
    doc_len: usize,
    proj_doc_len: usize,
    hybrid_len: Option<usize>,
    consist_proof: ConsistencyProof,
) {
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
    log::tic(
        Component::Verifier,
        "Verification",
        "Final Checks Consistency Verification",
    );

    // [state, <q,v for eval claim>, <q,"v"(hash), for doc claim>, stack_ptr, <stack>]
    let zn = res.unwrap().0;

    let (stack_ptr, eval_q, eval_v, hybrid_q) = if hybrid_len.is_none() {
        let q_len = logmn(table.len());
        let qd_len = logmn(proj_doc_len);
        assert_eq!(consist_proof.hash_d, zn[2 + q_len + qd_len]);

        (
            zn[(q_len + qd_len + 3)],
            Some(zn[1..(q_len + 1)].to_vec()),
            Some(zn[q_len + 1]),
            None,
        )
    } else {
        let h_len = logmn(hybrid_len.unwrap());
        assert_eq!(consist_proof.hash_d, zn[1 + h_len]);

        (
            zn[(h_len + 2)],
            None,
            None,
            Some(zn[1..(1 + h_len)].to_vec()),
        )
    };

    let (t, q_0) = final_clear_checks(stack_ptr, &table, eval_q, eval_v, hybrid_q);

    //CAP verify
    reef_commit.verify_consistency(consist_proof, t, q_0);

    // final accepting
    assert_eq!(zn[0], <G1 as Group>::Scalar::from(exit_state as u64));

    #[cfg(feature = "metrics")]
    log::stop(
        Component::Verifier,
        "Verification",
        "Final Checks Consistency Verification",
    );
}

#[cfg(test)]
mod tests {

    use crate::backend::framework::*;
    use crate::backend::r1cs_helper::init;
    use crate::frontend::regex::re;
    use crate::frontend::safa::SAFA;

    fn backend_test(
        ab: String,
        rstr: String,
        doc: Vec<char>,
        batch_size: usize,
        projections: bool,
        hybrid: bool,
    ) {
        let r = re::simpl(re::new(&rstr));
        let safa = SAFA::new(&ab[..], &r);

        init();
        run_backend(safa.clone(), doc.clone(), batch_size, projections, hybrid);
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
        );
    }

    #[test]
    fn e2e_projections() {
        backend_test(
            "abc".to_string(),
            "^....cc$".to_string(),
            ("aabbcc".to_string()).chars().collect(),
            0,
            true,
            false,
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
        );
        /* backend_test(
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

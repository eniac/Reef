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
    commit: ReefCommitment<<G1 as Group>::Scalar>,
    table: Vec<Integer>,
    doc_len: usize,
    num_states: usize,
}

#[cfg(feature = "metrics")]
use crate::metrics::{log, log::Component};

// gen R1CS object, commitment, make step circuit for nova
pub fn run_backend(
    safa: SAFA<char>,
    doc: Vec<char>,
    temp_batch_size: usize, // this may be 0 if not overridden, only use to feed into R1CS object
    projections: bool,
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
        let sc = Sponge::<<G1 as Group>::Scalar, typenum::U4>::api_constants(Strength::Standard);

        #[cfg(feature = "metrics")]
        log::tic(
            Component::Compiler,
            "R1CS",
            "Optimization Selection, R1CS precomputations",
        );
        // TODO feed in proj data here
        let mut r1cs_converter = R1CS::new(&safa, &doc, temp_batch_size, None, false, sc.clone());
        #[cfg(feature = "metrics")]
        log::stop(
            Component::Compiler,
            "R1CS",
            "Optimization Selection, R1CS precomputations",
        );

        #[cfg(feature = "metrics")]
        log::tic(Component::Compiler, "R1CS", "Commitment Generations");
        let reef_commit = gen_commitment(r1cs_converter.udoc.clone(), &sc);
        r1cs_converter.reef_commit = Some(reef_commit.clone());

        #[cfg(feature = "metrics")]
        log::stop(Component::Compiler, "R1CS", "Commitment Generations");

        #[cfg(feature = "metrics")]
        log::tic(Component::Compiler, "R1CS", "To Circuit");

        let (prover_data, _verifier_data) = r1cs_converter.to_circuit();

        #[cfg(feature = "metrics")]
        log::stop(Component::Compiler, "R1CS", "To Circuit");

        #[cfg(feature = "metrics")]
        log::tic(Component::Compiler, "R1CS", "Proof Setup");
        let (z0_primary, pp) = setup(&r1cs_converter, &prover_data);

        #[cfg(feature = "metrics")]
        log::stop(Component::Compiler, "R1CS", "Proof Setup");

        send_setup
            .send(ProofInfo {
                pp: Arc::new(Mutex::new(pp)),
                z0_primary,
                commit: reef_commit,
                table: r1cs_converter.table.clone(),
                doc_len: r1cs_converter.udoc.len(),
                num_states: r1cs_converter.num_states,
            })
            .unwrap();

        #[cfg(feature = "metrics")]
        log::stop(Component::Compiler, "Compiler", "Full");

        solve(sender, sender_qv, &mut r1cs_converter, &prover_data, &doc);
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
) -> (Vec<<G1 as Group>::Scalar>, PublicParams<G1, G2, C1, C2>) {
    let q_len = logmn(r1cs_converter.table.len());
    let qd_len = logmn(r1cs_converter.udoc.len());
    let stack_len = r1cs_converter.max_stack;

    // use "empty" (witness-less) circuit to generate nova F
    let q = vec![<G1 as Group>::Scalar::from(0); q_len];
    let v = <G1 as Group>::Scalar::from(0);
    let doc_q = vec![<G1 as Group>::Scalar::from(0); qd_len];
    let doc_v = <G1 as Group>::Scalar::from(0);
    let stack_ptr = <G1 as Group>::Scalar::from(0);
    let stack = vec![<G1 as Group>::Scalar::from(0); stack_len];

    let empty_glue = vec![
        Glue {
            q: q.clone(),
            v: v.clone(),
            doc_q: doc_q.clone(),
            doc_v: doc_v.clone(),
            stack_ptr: stack_ptr.clone(),
            stack: stack.clone(),
        },
        Glue {
            q: q,
            v: v,
            doc_q: doc_q,
            doc_v: doc_v,
            stack_ptr: stack_ptr,
            stack: stack,
        },
    ];

    let circuit_primary: NFAStepCircuit<<G1 as Group>::Scalar> = NFAStepCircuit::new(
        circ_data.r1cs.clone(),
        None,
        vec![<G1 as Group>::Scalar::from(0); 2],
        empty_glue,
        <G1 as Group>::Scalar::from(0),
        r1cs_converter.batch_size,
        r1cs_converter.max_branches,
        r1cs_converter.pc.clone(),
        <G1 as Group>::Scalar::from(0),
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

    let commit_blind = r1cs_converter.reef_commit.clone().unwrap().commit_doc_hash;
    let claim_blind = r1cs_converter.reef_commit.clone().unwrap().s;

    let current_state = r1cs_converter.safa.get_init().index();

    let mut z = vec![<G1 as Group>::Scalar::from(current_state as u64)];

    z.append(&mut vec![<G1 as Group>::Scalar::from(0); q_len]);
    z.push(int_to_ff(r1cs_converter.table[0].clone()));

    z.append(&mut vec![<G1 as Group>::Scalar::from(0); qd_len]);
    let d = calc_d_clear(
        r1cs_converter.pc.clone(),
        claim_blind,
        Integer::from(r1cs_converter.udoc[0] as u64),
    );
    //z.push(<G1 as Group>::Scalar::from(r1cs_converter.udoc[0] as u64));
    z.push(d);

    z.push(<G1 as Group>::Scalar::from(0 as u64));
    z.append(&mut vec![<G1 as Group>::Scalar::from(0); stack_len]);
    let z0_primary = z;

    (z0_primary, pp)
}

fn solve<'a>(
    sender: Sender<Option<NFAStepCircuit<<G1 as Group>::Scalar>>>,
    sender_qv: Sender<(Vec<Integer>, Integer)>, //itness<<G1 as Group>::Scalar>>,
    r1cs_converter: &mut R1CS<<G1 as Group>::Scalar, char>,
    circ_data: &'a ProverData,
    doc: &Vec<char>,
) {
    let q_len = logmn(r1cs_converter.table.len());
    let qd_len = logmn(r1cs_converter.udoc.len());

    let commit_blind = r1cs_converter.reef_commit.clone().unwrap().commit_doc_hash;
    let claim_blind = r1cs_converter.reef_commit.clone().unwrap().s;

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

    let mut prev_cursor_0 = 0;
    let mut next_cursor_0;
    let mut stack_ptr_0 = 0;
    let mut stack_ptr_popped;
    let mut stack_in = vec![0; r1cs_converter.max_stack];
    let mut stack_out;

    let mut current_state = r1cs_converter.safa.get_init().index();
    // TODO don't recalc :(

    let mut next_state;

    let trace = r1cs_converter.safa.solve(doc);
    let mut sols = trace_preprocessing(&trace, &r1cs_converter.safa);

    let mut i = 0;
    while r1cs_converter.sol_num < sols.len() {
        #[cfg(feature = "metrics")]
        let test = format!("step {}", i);

        #[cfg(feature = "metrics")]
        log::tic(Component::Solver, &test, "witness generation");
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
            next_cursor_0,
        ) = r1cs_converter.gen_wit_i(
            &mut sols,
            i,
            running_q.clone(),
            running_v.clone(),
            doc_running_q.clone(),
            doc_running_v.clone(),
            hybrid_running_q.clone(),
            hybrid_running_v.clone(),
            prev_cursor_0.clone(),
        );
        stack_ptr_popped = r1cs_converter.stack_ptr;
        stack_out = vec![];
        for (cur, kid) in &r1cs_converter.stack {
            stack_out.push(cur * r1cs_converter.num_states + kid);
        }

        #[cfg(feature = "metrics")]
        log::stop(Component::Solver, &test, "witness generation");

        circ_data.check_all(&wits);

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

        /*let doc_v = match doc_running_v {
            Some(rv) => int_to_ff(rv),
            None => <G1 as Group>::Scalar::from(r1cs_converter.udoc[0] as u64),
        };*/
        let doc_v = match doc_running_v {
            Some(rv) => rv,
            None => Integer::from(r1cs_converter.udoc[0] as u64),
        };
        let doc_v_hash = calc_d_clear(r1cs_converter.pc.clone(), claim_blind, doc_v.clone());

        let next_doc_q = next_doc_running_q
            .clone()
            .unwrap()
            .into_iter()
            .map(|x| int_to_ff(x))
            .collect();
        let next_doc_v = next_doc_running_v.clone().unwrap();
        let next_doc_v_hash =
            calc_d_clear(r1cs_converter.pc.clone(), claim_blind, next_doc_v.clone());

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

        let glue = vec![
            Glue {
                q: q,
                v: v,
                doc_q: doc_q,
                doc_v: doc_v_hash,
                stack_ptr: sp_0,
                stack: stk_in,
            },
            Glue {
                q: next_q,
                v: next_v,
                doc_q: next_doc_q,
                doc_v: next_doc_v_hash,
                stack_ptr: spp,
                stack: stk_out,
            },
        ];

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
            commit_blind,
            r1cs_converter.batch_size,
            r1cs_converter.max_branches,
            r1cs_converter.pc.clone(),
            claim_blind,
        );

        #[cfg(feature = "metrics")]
        log::stop(Component::Solver, &test, "witness generation");

        sender.send(Some(circuit_primary)).unwrap(); //witness_i).unwrap();

        // for next i+1 round
        current_state = next_state;
        running_q = next_running_q;
        running_v = next_running_v;
        doc_running_q = next_doc_running_q;
        doc_running_v = next_doc_running_v;
        prev_cursor_0 = next_cursor_0;
        stack_ptr_0 = stack_ptr_popped;
        stack_in = stack_out;
        i += 1
    }

    sender.send(None).unwrap();
    sender_qv
        .send((doc_running_q.unwrap(), doc_running_v.unwrap()))
        .unwrap();
}

fn prove_and_verify(
    recv: Receiver<Option<NFAStepCircuit<<G1 as Group>::Scalar>>>,
    recv_qv: Receiver<(Vec<Integer>, Integer)>,
    proof_info: ProofInfo,
) {
    println!("Proving thread starting...");

    // recursive SNARK
    let mut recursive_snark: Option<RecursiveSNARK<G1, G2, C1, C2>> = None;
    // trivial circuit
    let circuit_secondary = TrivialTestCircuit::new(StepCounterType::External);
    let z0_secondary = vec![<G2 as Group>::Scalar::zero()];

    let mut i = 0;

    // blocks until we receive first witness
    let mut circuit_primary = recv.recv().unwrap();

    let cp_clone = circuit_primary.clone().unwrap();
    let pc = cp_clone.pc;
    let claim_blind = cp_clone.claim_blind;

    while circuit_primary.is_some() {
        #[cfg(feature = "metrics")]
        let test = format!("step {}", i);

        #[cfg(feature = "metrics")]
        log::tic(Component::Prover, &test, "prove step");

        let result = RecursiveSNARK::prove_step(
            &proof_info.pp.lock().unwrap(),
            recursive_snark,
            circuit_primary.clone().unwrap(),
            circuit_secondary.clone(),
            proof_info.z0_primary.clone(),
            z0_secondary.clone(),
        );

        #[cfg(feature = "metrics")]
        log::stop(Component::Prover, &test, "prove step");
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
        circuit_primary = recv.recv().unwrap()
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

    let (q, v) = recv_qv.recv().unwrap();

    //Doc dot prod

    let (ipi, ipa, v_commit, v_decommit) = proof_dot_prod_prover(
        &proof_info.commit,
        q.into_iter().map(|x| int_to_ff(x)).collect(),
        int_to_ff(v.clone()),
        proof_info.doc_len,
    );

    //CAP Proving
    let cap_d = calc_d_clear(pc.clone(), claim_blind, v.clone());

    // CAP circuit
    let cap_circuit: ConsistencyCircuit<<G1 as Group>::Scalar> =
        ConsistencyCircuit::new(pc, cap_d, int_to_ff(v.clone()), claim_blind);

    // produce CAP keys
    let (cap_pk, cap_vk) =
        SpartanSNARK::<G1, EE1, ConsistencyCircuit<<G1 as Group>::Scalar>>::setup(
            cap_circuit.clone(),
        )
        .unwrap();

    let cap_blind_v = <G1 as Group>::Scalar::random(&mut OsRng);
    let cap_com_v = <G1 as Group>::CE::commit(
        cap_pk.pk.gens.get_scalar_gen(),
        &[int_to_ff(v.clone())],
        &cap_blind_v,
    );

    let cap_z = vec![cap_d];

    let cap_res = SpartanSNARK::cap_prove(
        &cap_pk,
        cap_circuit.clone(),
        &cap_z,
        &cap_com_v.compress(),
        &int_to_ff(v),
        &cap_blind_v,
    );
    assert!(cap_res.is_ok());

    let cap_snark = cap_res.unwrap();

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
        proof_info.num_states,
        proof_info.doc_len,
        ipi,
        ipa,
        cap_d,
        cap_circuit,
        cap_snark,
        cap_vk,
        cap_com_v,
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
    num_states: usize,
    doc_len: usize,
    ipi: InnerProductInstance<G1>,
    ipa: InnerProductArgument<G1>,
    cap_d: <G1 as Group>::Scalar,
    cap_circuit: ConsistencyCircuit<<G1 as Group>::Scalar>,
    cap_snark: SpartanSNARK<G1, EE1, ConsistencyCircuit<<G1 as Group>::Scalar>>,
    cap_vk: SpartanVerifierKey<G1, EE1>,
    cap_v_commit: Commitment<G1>,
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

    //CAP verify
    let cap_res = cap_verifier(cap_d, cap_snark, cap_circuit, cap_vk, cap_v_commit);
    assert!(cap_res.is_ok());

    // state, char, opt<hash>, opt<v,q for eval>, opt<v,q for doc>, accepting
    let zn = res.unwrap().0;

    // eval type, reef commitment, accepting state bool, table, doc, final_q, final_v, final_hash,
    // final_doc_q, final_doc_v

    final_clear_checks(
        reef_commit,
        &table,
        doc_len,
        Some(zn[1..(q_len + 1)].to_vec()),
        Some(zn[q_len + 1]),
        Some(zn[(2 + q_len)..(2 + q_len + qd_len)].to_vec()),
        Some(zn[2 + q_len + qd_len]),
        None, // TODO
        Some(cap_d),
        ipi,
        ipa,
    );

    // final accepting
    assert_eq!(zn[0], <G1 as Group>::Scalar::from(num_states as u64));

    #[cfg(feature = "metrics")]
    log::stop(Component::Verifier, "Verification", "Final Clear Checks");
}

#[cfg(test)]
mod tests {

    use crate::backend::framework::*;
    use crate::backend::r1cs_helper::init;
    use crate::frontend::regex::{re, Regex};
    use crate::frontend::safa::SAFA;

    fn backend_test(
        ab: String,
        rstr: String,
        doc: Vec<char>,
        batch_size: usize,
        projections: bool,
    ) {
        let r = re::new(&rstr);
        let safa = SAFA::new(&ab[..], &r);

        init();
        run_backend(safa.clone(), doc.clone(), batch_size, projections);
    }

    #[test]
    fn e2e_projections() {
        backend_test(
            "ab".to_string(),
            "^a*b*$".to_string(),
            ("aaab".to_string())
                .chars()
                //.map(|c| c.to_string())
                .collect(),
            0,
            true,
        );
    }

    #[test]
    fn e2e_q_overflow() {
        backend_test(
            "abcdefg".to_string(),
            "gaa*bb*cc*dd*ee*f".to_string(),
            ("gaaaaaabbbbbbccccccddddddeeeeeef".to_string())
                .chars()
                //.map(|c| c.to_string())
                .collect(),
            33,
            false,
        );
    }

    #[test]
    fn e2e_substring() {
        backend_test(
            "ab".to_string(),
            "bbb".to_string(),
            ("aaabbbaaa".to_string())
                .chars()
                //.map(|c| c.to_string())
                .collect(),
            2,
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

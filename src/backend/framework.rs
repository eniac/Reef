type G1 = pasta_curves::pallas::Point;
type G2 = pasta_curves::vesta::Point;
use crate::backend::costs::{JBatching, JCommit};
use crate::backend::{nova::*, r1cs::*};
use crate::dfa::DFA;
use circ::cfg;
use circ::cfg::CircOpt;
use circ::target::r1cs::ProverData;
use generic_array::typenum;
use neptune::{
    sponge::api::{IOPattern, SpongeAPI, SpongeOp},
    sponge::vanilla::{Mode, Sponge, SpongeTrait},
    Strength,
};
use nova_snark::{
    traits::{circuit::TrivialTestCircuit, Group},
    CompressedSNARK, PublicParams, RecursiveSNARK, StepCounterType, FINAL_EXTERNAL_COUNTER,
};
use std::time::{Duration, Instant};

// gen R1CS object, commitment, make step circuit for nova
pub fn run_backend(
    dfa: &DFA,
    doc: &Vec<String>,
    batching_type: Option<JBatching>,
    commit_type: Option<JCommit>,
    batch_size: usize,
) {
    let sc = Sponge::<<G1 as Group>::Scalar, typenum::U2>::api_constants(Strength::Standard);

    let mut r1cs_converter =
        R1CS::new(dfa, doc, batch_size, sc.clone(), batching_type, commit_type);
    //let parse_ms = p_time.elapsed().as_millis();

    let c_time = Instant::now();
    println!("generate commitment");
    r1cs_converter.gen_commitment();
    let commit_ms = c_time.elapsed().as_millis();

    let r_time = Instant::now();
    let (prover_data, _verifier_data) = r1cs_converter.to_circuit();
    let r1cs_ms = r_time.elapsed().as_millis();

    let s_time = Instant::now();
    // use "empty" (witness-less) circuit to generate nova F
    let circuit_primary: DFAStepCircuit<<G1 as Group>::Scalar> = DFAStepCircuit::new(
        &prover_data,
        None,
        vec![<G1 as Group>::Scalar::from(0); 2],
        vec![<G1 as Group>::Scalar::from(0); 2],
        vec![<G1 as Group>::Scalar::from(0); 2],
        batch_size,
        sc.clone(),
        false,
    );

    // trivial circuit
    let circuit_secondary = TrivialTestCircuit::new(StepCounterType::External);

    // produce public parameters
    println!("Producing public parameters...");
    let pp = PublicParams::<
        G1,
        G2,
        DFAStepCircuit<<G1 as Group>::Scalar>,
        TrivialTestCircuit<<G2 as Group>::Scalar>,
    >::setup(circuit_primary.clone(), circuit_secondary.clone())
    .unwrap();
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

    let mut current_state = dfa.get_init_state();
    let z0_primary = vec![
        <G1 as Group>::Scalar::from(current_state as u64),
        <G1 as Group>::Scalar::from(dfa.ab_to_num(&doc[0]) as u64),
        <G1 as Group>::Scalar::from(0),
    ];

    let z0_secondary = vec![<G2 as Group>::Scalar::zero()];

    // PROVER fold up recursive proof and prove compressed snark
    type C1<'a> = DFAStepCircuit<'a, <G1 as Group>::Scalar>;
    type C2 = TrivialTestCircuit<<G2 as Group>::Scalar>;

    // recursive SNARK
    let mut recursive_snark: Option<RecursiveSNARK<G1, G2, C1, C2>> = None;

    // TODO check "ingrained" bool out
    let mut prev_hash = <G1 as Group>::Scalar::from(0);

    //let setup_ms = s_time.elapsed().as_millis();

    // TODO deal with time bs

    let n_time = Instant::now();
    let parameter = IOPattern(vec![SpongeOp::Absorb(2), SpongeOp::Squeeze(1)]);

    let num_steps = doc.len() / r1cs_converter.batch_size;
    let mut wits;
    let mut next_state;
    let mut running_q = None;
    let mut running_v = None;
    let mut doc_running_q = None;
    let mut doc_running_v = None;

    let mut current_state = 0; //dfa.get init state ??
    for i in 0..num_steps {
        println!("STEP {}", i);

        // allocate real witnesses for round i
        (
            wits,
            next_state,
            running_q,
            running_v,
            doc_running_q,
            doc_running_v,
        ) = r1cs_converter.gen_wit_i(
            i,
            current_state,
            running_q.clone(),
            running_v.clone(),
            doc_running_q.clone(),
            doc_running_v.clone(),
        );
        //println!("prover_data {:#?}", prover_data.clone());
        //println!("wits {:#?}", wits.clone());
        //let extended_wit = prover_data.precomp.eval(&wits);
        //println!("extended wit {:#?}", extended_wit);

        //prover_data.check_all(&extended_wit);
        prover_data.check_all(&wits);

        let current_char = doc[i * batch_size].clone();
        let mut next_char: String = String::from("");
        if i + 1 < num_steps {
            next_char = doc[(i + 1) * batch_size].clone();
        };
        //println!("next char = {}", next_char);

        // todo put this in r1cs
        let mut next_hash = <G1 as Group>::Scalar::from(0);
        let mut intm_hash = prev_hash;
        for b in 0..batch_size {
            // expected poseidon
            let mut sponge = Sponge::new_with_constants(&sc, Mode::Simplex);
            let acc = &mut ();

            sponge.start(parameter.clone(), None, acc);
            SpongeAPI::absorb(
                &mut sponge,
                2,
                &[
                    intm_hash,
                    <G1 as Group>::Scalar::from(
                        dfa.ab_to_num(&doc[i * batch_size + b].clone()) as u64
                    ),
                ],
                acc,
            );
            let expected_next_hash = SpongeAPI::squeeze(&mut sponge, 1, acc);
            println!(
                "prev, expected next hash in main {:#?} {:#?}",
                prev_hash, expected_next_hash
            );
            sponge.finish(acc).unwrap(); // assert expected hash finished correctly

            next_hash = expected_next_hash[0];
            intm_hash = next_hash;
        }

        let circuit_primary: DFAStepCircuit<<G1 as Group>::Scalar> = DFAStepCircuit::new(
            &prover_data,
            Some(wits),
            vec![
                <G1 as Group>::Scalar::from(current_state as u64),
                <G1 as Group>::Scalar::from(next_state as u64),
            ],
            vec![
                <G1 as Group>::Scalar::from(dfa.ab_to_num(&current_char) as u64),
                <G1 as Group>::Scalar::from(dfa.ab_to_num(&next_char) as u64),
            ],
            vec![
                <G1 as Group>::Scalar::from(prev_hash),
                <G1 as Group>::Scalar::from(next_hash),
            ],
            batch_size,
            sc.clone(),
            false,
        );
        // trivial circuit
        let circuit_secondary = TrivialTestCircuit::new(StepCounterType::External);

        //println!("STEP CIRC WIT for i={}: {:#?}", i, circuit_primary);
        // snark
        let result = RecursiveSNARK::prove_step(
            &pp,
            recursive_snark,
            circuit_primary.clone(),
            circuit_secondary.clone(),
            z0_primary.clone(),
            z0_secondary.clone(),
        );
        //println!("prove step {:#?}", result);

        assert!(result.is_ok());
        println!("RecursiveSNARK::prove_step {}: {:?}", i, result.is_ok());
        recursive_snark = Some(result.unwrap());

        // for next i+1 round
        current_state = next_state;
        prev_hash = next_hash;
    }

    assert!(recursive_snark.is_some());
    let recursive_snark = recursive_snark.unwrap();

    // verify recursive - TODO we can get rid of this verify once everything works
    let res = recursive_snark.verify(
        &pp,
        FINAL_EXTERNAL_COUNTER,
        z0_primary.clone(),
        z0_secondary.clone(),
    );
    //println!("Recursive res: {:#?}", res);

    assert!(res.is_ok());

    // compressed SNARK
    type EE1 = nova_snark::provider::ipa_pc::EvaluationEngine<G1>;
    type EE2 = nova_snark::provider::ipa_pc::EvaluationEngine<G2>;
    type S1 = nova_snark::spartan::RelaxedR1CSSNARK<G1, EE1>;
    type S2 = nova_snark::spartan::RelaxedR1CSSNARK<G2, EE2>;
    let res = CompressedSNARK::<_, _, _, _, S1, S2>::prove(&pp, &recursive_snark);
    assert!(res.is_ok());
    let compressed_snark = res.unwrap();

    let nova_prover_ms = n_time.elapsed().as_millis();

    println!("nova prover ms {:#?}", nova_prover_ms);

    // VERIFIER verify compressed snark
    let n_time = Instant::now();
    let res = compressed_snark.verify(&pp, FINAL_EXTERNAL_COUNTER, z0_primary, z0_secondary);
    assert!(res.is_ok());
    let nova_verifier_ms = n_time.elapsed().as_millis();

    println!("nova verifier ms {:#?}", nova_verifier_ms);
}

// tests that need setup

#[cfg(test)]
mod tests {

    use crate::backend::costs;
    use crate::backend::framework::*;
    use crate::backend::r1cs::*;
    use crate::dfa::DFA;
    use crate::regex::Regex;
    use circ::cfg;
    use circ::cfg::CircOpt;
    use serial_test::serial;
    type G1 = pasta_curves::pallas::Point;

    fn backend_test(
        ab: String,
        rstr: String,
        doc: String,
        batch_type: JBatching,
        commit_type: JCommit,
        batch_sizes: Vec<usize>,
    ) {
        let r = Regex::new(&rstr);
        let dfa = DFA::new(&ab[..], r);
        let chars: Vec<String> = doc.chars().map(|c| c.to_string()).collect();

        init();
        for b in batch_sizes {
            run_backend(
                &dfa,
                &doc.chars().map(|c| c.to_string()).collect(),
                Some(batch_type.clone()),
                Some(commit_type.clone()),
                b,
            );
        }
    }

    #[test]
    fn e2e_simple() {
        backend_test(
            "ab".to_string(),
            "a*b*".to_string(),
            "aaabbb".to_string(),
            JBatching::NaivePolys,
            JCommit::HashChain,
            vec![1, 2],
        );
    }

    #[test]
    fn e2e_nlookup() {
        backend_test(
            "ab".to_string(),
            "a*b*".to_string(),
            "aaabbb".to_string(),
            JBatching::Nlookup,
            JCommit::HashChain,
            vec![2],
        );
        /*
              backend_test(
                  "ab".to_string(),
                  "a*b*".to_string(),
                  "aaabbb".to_string(),
                  JBatching::Nlookup,
                  JCommit::Nlookup,
                  vec![2],
              );
        */
    }
}

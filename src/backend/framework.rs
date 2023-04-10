type G1 = pasta_curves::pallas::Point;
type G2 = pasta_curves::vesta::Point;
use crate::backend::{
    costs::{logmn, JBatching, JCommit},
    nova::*,
    r1cs::*,
};
use crate::dfa::NFA;
use circ::cfg;
use circ::cfg::CircOpt;
use circ::target::r1cs::ProverData;
use ff::{Field, PrimeField};
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
//use rand::rngs::OsRng;
use rug::{
    integer::Order,
    ops::{RemRounding, RemRoundingAssign},
    Assign, Integer,
};
use std::time::{Duration, Instant};

// gen R1CS object, commitment, make step circuit for nova
pub fn run_backend(
    dfa: &NFA,
    doc: &Vec<String>,
    batching_type: Option<JBatching>,
    commit_type: Option<JCommit>,
    temp_batch_size: usize, // this may be 0 if not overridden, only use to feed into R1CS object
) {
    let sc = Sponge::<<G1 as Group>::Scalar, typenum::U2>::api_constants(Strength::Standard);

    let mut r1cs_converter = R1CS::new(
        dfa,
        doc,
        temp_batch_size,
        sc.clone(),
        batching_type,
        commit_type,
    );
    //let parse_ms = p_time.elapsed().as_millis();
    let q_len = logmn(r1cs_converter.table.len());
    let qd_len = logmn(r1cs_converter.doc.len());

    let c_time = Instant::now();
    println!("generate commitment");
    r1cs_converter.gen_commitment();
    let commit_ms = c_time.elapsed().as_millis();

    let r_time = Instant::now();
    let (prover_data, _verifier_data) = r1cs_converter.to_circuit();
    let r1cs_ms = r_time.elapsed().as_millis();

    let s_time = Instant::now();
    // use "empty" (witness-less) circuit to generate nova F
    let empty_glue = match (r1cs_converter.batching, r1cs_converter.commit_type) {
        (JBatching::NaivePolys, JCommit::HashChain) => {
            vec![
                GlueOpts::Poly_Hash(<G1 as Group>::Scalar::from(0)),
                GlueOpts::Poly_Hash(<G1 as Group>::Scalar::from(0)),
            ]
        }
        (JBatching::Nlookup, JCommit::HashChain) => {
            let h = <G1 as Group>::Scalar::from(0);

            let q = vec![<G1 as Group>::Scalar::from(0); q_len];

            let v = <G1 as Group>::Scalar::from(0);

            vec![
                GlueOpts::Nl_Hash((h.clone(), q.clone(), v.clone())),
                GlueOpts::Nl_Hash((h, q, v)),
            ]
        }
        _ => todo!(),
    };

    let circuit_primary: NFAStepCircuit<<G1 as Group>::Scalar> = NFAStepCircuit::new(
        &prover_data,
        None,
        vec![<G1 as Group>::Scalar::from(0); 2],
        vec![<G1 as Group>::Scalar::from(0); 2],
        empty_glue,
        vec![<G1 as Group>::Scalar::from(0); 2],
        r1cs_converter.batch_size,
        sc.clone(),
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
    type C1<'a> = NFAStepCircuit<'a, <G1 as Group>::Scalar>;
    type C2 = TrivialTestCircuit<<G2 as Group>::Scalar>;

    // recursive SNARK
    let mut recursive_snark: Option<RecursiveSNARK<G1, G2, C1, C2>> = None;

    //let setup_ms = s_time.elapsed().as_millis();

    // TODO deal with time bs

    let n_time = Instant::now();
    let parameter = IOPattern(vec![SpongeOp::Absorb(2), SpongeOp::Squeeze(1)]);

    let num_steps =
        (r1cs_converter.substring.1 - r1cs_converter.substring.0) / r1cs_converter.batch_size;
    let mut wits;
    let mut running_q = None;
    let mut running_v = None;
    let mut next_running_q = None;
    let mut next_running_v = None;
    let mut doc_running_q = None;
    let mut doc_running_v = None;
    let mut next_doc_running_q = None;
    let mut next_doc_running_v = None;

    let mut next_state = 0; //dfa.get init state ??
    let mut prev_hash = <G1 as Group>::Scalar::from(0);
    for i in 0..num_steps {
        println!("STEP {}", i);

        // allocate real witnesses for round i
        (
            wits,
            next_state,
            next_running_q,
            next_running_v,
            next_doc_running_q,
            next_doc_running_v,
        ) = r1cs_converter.gen_wit_i(
            i,
            next_state,
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

        let current_char = doc[i * r1cs_converter.batch_size].clone();
        let mut next_char: String = String::from("");
        if i + 1 < num_steps {
            next_char = doc[(i + 1) * r1cs_converter.batch_size].clone();
        };
        //println!("next char = {}", next_char);

        // todo put this in r1cs
        let mut next_hash = <G1 as Group>::Scalar::from(0);
        /*for b in 0..r1cs_converter.batch_size {
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
                        dfa.ab_to_num(&doc[i * r1cs_converter.batch_size + b].clone()) as u64,
                    ),
                ],
                acc,
            );
            let expected_next_hash = SpongeAPI::squeeze(&mut sponge, 1, acc);
            println!(
                "prev, expected next hash in main {:#?} {:#?}",
                intm_hash, expected_next_hash
            );
            sponge.finish(acc).unwrap(); // assert expected hash finished correctly

            next_hash = expected_next_hash[0];
            intm_hash = next_hash;
        }*/

        let glue = match (r1cs_converter.batching, r1cs_converter.commit_type) {
            (JBatching::NaivePolys, JCommit::HashChain) => {
                let next_hash = r1cs_converter.prover_calc_hash(prev_hash, i);
                println!("ph, nh: {:#?}, {:#?}", prev_hash.clone(), next_hash.clone());
                let g = vec![
                    GlueOpts::Poly_Hash(prev_hash),
                    GlueOpts::Poly_Hash(next_hash),
                ];
                prev_hash = next_hash;
                println!("ph, nh: {:#?}, {:#?}", prev_hash.clone(), next_hash.clone());
                g
            }
            (JBatching::Nlookup, JCommit::HashChain) => {
                let next_hash = r1cs_converter.prover_calc_hash(prev_hash, i);

                let q = match running_q {
                    Some(rq) => rq.into_iter().map(|x| int_to_ff(x)).collect(),
                    None => vec![<G1 as Group>::Scalar::from(0); q_len],
                };

                let v = match running_v {
                    Some(rv) => int_to_ff(rv),
                    None => <G1 as Group>::Scalar::from(0),
                };

                let next_q = next_running_q
                    .clone()
                    .unwrap()
                    .into_iter()
                    .map(|x| int_to_ff(x))
                    .collect();
                let next_v = int_to_ff(next_running_v.clone().unwrap());

                let g = vec![
                    GlueOpts::Nl_Hash((prev_hash, q, v)),
                    GlueOpts::Nl_Hash((next_hash, next_q, next_v)),
                ];
                prev_hash = next_hash;

                g
            }
            _ => todo!(),
        };

        let circuit_primary: NFAStepCircuit<<G1 as Group>::Scalar> = NFAStepCircuit::new(
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
            glue,
            vec![
                <G1 as Group>::Scalar::from(
                    r1cs_converter.prover_accepting_state(i, current_state),
                ),
                <G1 as Group>::Scalar::from(r1cs_converter.prover_accepting_state(i, next_state)),
            ],
            r1cs_converter.batch_size,
            sc.clone(),
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
        running_q = next_running_q;
        running_v = next_running_v;
        doc_running_q = next_doc_running_q;
        doc_running_v = next_doc_running_v;
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

    assert!(res.is_ok()); // TODO delete

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
    use crate::dfa::NFA;
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
        let dfa = NFA::new(&ab[..], r);
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

    //    #[test]
    fn e2e_poly_hash() {
        backend_test(
            "ab".to_string(),
            "^a*b*$".to_string(),
            "aaabbb".to_string(),
            JBatching::NaivePolys,
            JCommit::HashChain,
            vec![1, 2],
        );
    }

    #[test]
    fn e2e_poly_nl() {
        backend_test(
            "ab".to_string(),
            "^a*b*$".to_string(),
            "aaabbb".to_string(),
            JBatching::NaivePolys,
            JCommit::Nlookup,
            vec![2],
        );
    }

    #[test]
    fn e2e_nl_hash() {
        backend_test(
            "ab".to_string(),
            "^a*b*$".to_string(),
            "aaabbb".to_string(),
            JBatching::Nlookup,
            JCommit::HashChain,
            vec![2],
        );
    }

    #[test]
    fn e2e_nl_nl() {
        backend_test(
            "ab".to_string(),
            "^a*b*$".to_string(),
            "aaabbb".to_string(),
            JBatching::Nlookup,
            JCommit::Nlookup,
            vec![2],
        );
    }
}

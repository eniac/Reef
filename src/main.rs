#![allow(missing_docs, non_snake_case)]
type G1 = pasta_curves::pallas::Point;
type G2 = pasta_curves::vesta::Point;
use circ::cfg;
use circ::cfg::CircOpt;
use circ::target::r1cs::nova::*;
use generic_array::typenum;
use clap::{Args, Parser, Subcommand};
use std::path::PathBuf;

use neptune::{
    poseidon::{Arity, HashMode, Poseidon, PoseidonConstants},
    sponge::api::{IOPattern, SpongeAPI, SpongeOp},
    sponge::vanilla::{Mode, Sponge, SpongeTrait},
    Strength,
};
use nova_snark::{
    traits::{circuit::TrivialTestCircuit, Group},
    CompressedSNARK, PublicParams, RecursiveSNARK, StepCounterType, FINAL_EXTERNAL_COUNTER,
};

pub mod deriv;
pub mod dfa;
pub mod parser;
pub mod r1cs;
pub mod config;

use crate::dfa::DFA;
use crate::r1cs::*;
use crate::config::*;

#[cfg(feature = "plot")]
pub mod plot;

fn main() {
    let opt = Options::parse();

    // Alphabet
    let ab = String::from_iter(opt.config.alphabet());

    // Regular expresion parser and convert the Regex to a DFA
    let dfa = opt.config.compile_dfa();
    println!("dfa: {:#?}", dfa);

    // Input document
    let doc: Vec<String> = opt.config.read_doc().into_iter().map(|c|c.to_string()).collect();

    // set up CirC library
    let mut circ: CircOpt = Default::default();
    circ.field.custom_modulus =
        "28948022309329048855892746252171976963363056481941647379679742748393362948097".into(); // vesta (fuck???)
                                                                                                //"28948022309329048855892746252171976963363056481941560715954676764349967630337".into(); // pallas curve (i think?)
    cfg::set(&circ);


    #[cfg(feature = "plot")]
    plot::plot_dfa(&dfa).expect("Failed to plot DFA to a pdf file");

    let num_steps = doc.len();
    println!("Doc len is {}", num_steps);

    let sc = Sponge::<<G1 as Group>::Scalar, typenum::U2>::api_constants(Strength::Standard);

    let mut r1cs_converter = R1CS::new(&dfa, &doc, 1, sc.clone());
    println!("generate commitment");
    r1cs_converter.gen_commitment();
    let (prover_data, _verifier_data) = r1cs_converter.to_r1cs();

    // use "empty" (witness-less) circuit to generate nova F
    let circuit_primary: DFAStepCircuit<<G1 as Group>::Scalar> = DFAStepCircuit::new(
        &prover_data.r1cs,
        None,
        <G1 as Group>::Scalar::zero(),
        <G1 as Group>::Scalar::zero(),
        <G1 as Group>::Scalar::zero(),
        <G1 as Group>::Scalar::zero(),
        <G1 as Group>::Scalar::zero(),
        <G1 as Group>::Scalar::zero(),
        <G1 as Group>::Scalar::zero(),
        sc.clone(),
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

    // trivial
    let z0_secondary = vec![<G2 as Group>::Scalar::zero()];

    type C1 = DFAStepCircuit<<G1 as Group>::Scalar>;
    type C2 = TrivialTestCircuit<<G2 as Group>::Scalar>;
    // recursive SNARK
    let mut recursive_snark: Option<RecursiveSNARK<G1, G2, C1, C2>> = None;

    let mut current_state = dfa.get_init_state();
    let z0_primary = vec![
        <G1 as Group>::Scalar::from(current_state),
        <G1 as Group>::Scalar::from(dfa.ab_to_num(&doc[0])),
        <G1 as Group>::Scalar::from(0),
        <G1 as Group>::Scalar::from(0),
    ];
    // TODO check "ingrained" bool out
    let mut prev_hash = <G1 as Group>::Scalar::from(0);
    let precomp = prover_data.clone().precompute;

    // for expected hash
    /*
    let mut sponge = Sponge::new_with_constants(&sc, Mode::Simplex);
    let acc = &mut ();
    */
    /*let mut seq = vec![];
    for i in 0..num_steps {
        seq.push(SpongeOp::Absorb(2));
        seq.push(SpongeOp::Squeeze(1));
    }*/
    let parameter = IOPattern(vec![SpongeOp::Absorb(2), SpongeOp::Squeeze(1)]);

    //sponge.start(parameter, None, acc);

    for i in 0..num_steps {
        println!("STEP {}", i);

        // allocate real witnesses for round i
        let (wits, next_state) = r1cs_converter.gen_wit_i(i, current_state);
        //println!("prover_data {:#?}", prover_data.clone());
        //println!("wits {:#?}", wits.clone());
        let extended_wit = precomp.eval(&wits);
        //println!("extended wit {:#?}", extended_wit);

        prover_data.r1cs.check_all(&extended_wit);

        let current_char = doc[i].clone();
        let mut next_char: String = String::from("");
        if i + 1 < num_steps {
            next_char = doc[i+1].clone();
        };
        //println!("next char = {}", next_char);

        // expected poseidon
        let mut sponge = Sponge::new_with_constants(&sc, Mode::Simplex);
        let acc = &mut ();

        sponge.start(parameter.clone(), None, acc);
        SpongeAPI::absorb(
            &mut sponge,
            2,
            &[
                prev_hash,
                <G1 as Group>::Scalar::from(dfa.ab_to_num(&current_char)),
            ],
            acc,
        );
        let expected_next_hash = SpongeAPI::squeeze(&mut sponge, 1, acc);

        println!("expected next hash in main {:#?}", expected_next_hash);
        sponge.finish(acc).unwrap(); // assert expected hash finished correctly

        let circuit_primary: DFAStepCircuit<<G1 as Group>::Scalar> = DFAStepCircuit::new(
            &prover_data.r1cs,
            Some(extended_wit),
            <G1 as Group>::Scalar::from(current_state),
            <G1 as Group>::Scalar::from(next_state),
            <G1 as Group>::Scalar::from(dfa.ab_to_num(&current_char)),
            <G1 as Group>::Scalar::from(dfa.ab_to_num(&next_char)),
            <G1 as Group>::Scalar::from(prev_hash),
            <G1 as Group>::Scalar::from(expected_next_hash[0]),
            <G1 as Group>::Scalar::from(i as u64),
            sc.clone(),
        );

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
        prev_hash = expected_next_hash[0];
    }

    assert!(recursive_snark.is_some());
    let recursive_snark = recursive_snark.unwrap();

    // verify recursive
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

    // verify compressed
    let res = compressed_snark.verify(&pp, FINAL_EXTERNAL_COUNTER, z0_primary, z0_secondary);
    assert!(res.is_ok());
}

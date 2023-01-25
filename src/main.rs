#![allow(missing_docs)]
use structopt::StructOpt;
type G1 = pasta_curves::pallas::Point;
type G2 = pasta_curves::vesta::Point;
use ::bellperson::{gadgets::num::AllocatedNum, LinearCombination, SynthesisError};
use circ::cfg;
use circ::cfg::CircOpt;
use circ::target::r1cs::{nova::*, R1cs};
use ff::PrimeField;
use nova_snark::{
    traits::{
        circuit::{StepCircuit, TrivialTestCircuit},
        Group,
    },
    CompressedSNARK, PublicParams, RecursiveSNARK,
};
use std::collections::HashMap;

pub mod deriv;
pub mod dfa;
pub mod parser;

use crate::deriv::mk_dfa;
use crate::dfa::DFA;
use crate::parser::regex_parser;

fn type_of<T>(_: &T) {
    println!("{}", std::any::type_name::<T>())
}

#[derive(Debug, StructOpt)]
#[structopt(name = "rezk", about = "Rezk: The regex to circuit compiler")]
struct Options {
    #[structopt(short = "ab", long = "alphabet", parse(from_str))]
    alphabet: String,

    /// regular expression
    #[structopt(short = "r", long = "regex", parse(from_str))]
    regex: String,

    #[structopt(short = "i", long = "input", parse(from_str))]
    input: String,
}

fn main() {
    let opt = Options::from_args();
    // Alphabet
    let ab = opt.alphabet;

    // Regular expresion
    let r = regex_parser(&opt.regex, &ab);

    // Input document
    let doc = opt.input;

    // set up CirC library
    let mut circ: CircOpt = Default::default();
    circ.field.custom_modulus =
        "28948022309329048855892746252171976963363056481941647379679742748393362948097".into(); // vesta (fuck???)
                                                                                                //"28948022309329048855892746252171976963363056481941560715954676764349967630337".into(); // pallas curve (i think?)
    cfg::set(&circ);

    // Convert the Regex to a DFA
    let mut dfa = DFA::new(&ab[..]);
    mk_dfa(&r, &ab, &mut dfa);
    println!("dfa: {:#?}", dfa);

    let (prover_data, verifier_data) = dfa.to_lookup_comp();
    println!("r1cs: {:#?}", prover_data.r1cs);

    // use "empty" (witness-less) circuit to generate nova F
    let circuit_primary = DFAStepCircuit::new(&prover_data.r1cs);

    // iterations
    let num_steps = doc.chars().count(); // len of document
    println!("Doc len is {}", num_steps);
    let mut chars = doc.chars();

    let mut current_state = dfa.get_init_state();
    for i in 0..num_steps {
        // allocate real witnesses for round i
        let (wits, next_state) = dfa.gen_wit_i(i, chars.next().unwrap(), current_state);
        let precomp = prover_data.clone().precompute;
        println!("prover_data {:#?}", prover_data.clone());
        println!("wits {:#?}", wits.clone());
        let extended_wit = precomp.eval(&wits);
        println!("extended wit {:#?}", extended_wit);

        prover_data.r1cs.check_all(&extended_wit);

        // generate nova witness vector i
        // wits as F in z = vec![*xx, *xxx, *xx];

        // translate wit to nova, fold

        // for next i+1 round
        current_state = next_state;
    }

    // TODO: check conversion is good

    // trivial circuit
    let circuit_secondary = TrivialTestCircuit::default();

    // produce public parameters
    println!("Producing public parameters...");
    let pp = PublicParams::<
        G1,
        G2,
        DFAStepCircuit<<G1 as Group>::Scalar>,
        TrivialTestCircuit<<G2 as Group>::Scalar>,
    >::setup(circuit_primary.clone(), circuit_secondary.clone());
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

    //println!("{:#?}", circuit_primary.clone());

    // circuit
    /*let (z0_primary, circuits_primary) = DFAStepCircuit::new(
        num_steps,
        <G1 as Group>::Scalar::one() + <G1 as Group>::Scalar::one(),
    );
    */

    // trivial
    let z0_secondary = vec![<G2 as Group>::Scalar::zero()];

    type C1 = DFAStepCircuit<<G1 as Group>::Scalar>;
    type C2 = TrivialTestCircuit<<G2 as Group>::Scalar>;
    /*
        // recursive SNARK
        let mut recursive_snark: Option<RecursiveSNARK<G1, G2, C1, C2>> = None;

        for (i, circuit_primary) in circuits_primary.iter().take(num_steps).enumerate() {
            let result = RecursiveSNARK::prove_step(
                &pp,
                recursive_snark,
                circuit_primary.clone(),
                circuit_secondary.clone(),
                z0_primary.clone(),
                z0_secondary.clone(),
            );
            assert!(result.is_ok());
            println!("RecursiveSNARK::prove_step {}: {:?}", i, result.is_ok());
            recursive_snark = Some(result.unwrap());
        }

        assert!(recursive_snark.is_some());
        let recursive_snark = recursive_snark.unwrap();

        // verify recursive
        let res = recursive_snark.verify(&pp, num_steps, z0_primary.clone(), z0_secondary.clone());
        assert!(res.is_ok());

        // compressed SNARK
        type S1 = nova_snark::spartan_with_ipa_pc::RelaxedR1CSSNARK<G1>;
        type S2 = nova_snark::spartan_with_ipa_pc::RelaxedR1CSSNARK<G2>;
        let res = CompressedSNARK::<_, _, _, _, S1, S2>::prove(&pp, &recursive_snark);
        assert!(res.is_ok());
        let compressed_snark = res.unwrap();

        // verify compressed
        let res = compressed_snark.verify(&pp, num_steps, z0_primary, z0_secondary);
        assert!(res.is_ok());
    */
}

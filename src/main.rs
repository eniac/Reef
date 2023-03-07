#![allow(missing_docs)]
use structopt::StructOpt;

type G1 = pasta_curves::pallas::Point;
type G2 = pasta_curves::vesta::Point;
use circ::cfg;
use circ::cfg::CircOpt;
use circ::target::r1cs::nova::*;
use generic_array::typenum;
use neptune::{
    poseidon::{Arity, HashMode, Poseidon, PoseidonConstants},
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

use crate::deriv::*;
use crate::dfa::DFA;
use crate::parser::regex_parser;
use crate::r1cs::*;

/*
fn type_of<T>(_: &T) {
    println!("{}", std::any::type_name::<T>())
}
*/

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

    let num_steps = doc.chars().count(); // len of document
    println!("Doc len is {}", num_steps);

    let pc = PoseidonConstants::<<G1 as Group>::Scalar, typenum::U2>::new_with_strength(
        Strength::Standard,
    );
    let mut r1cs_converter = R1CS::new(&dfa, doc.clone(), 1, pc.clone());
    println!("generate commitment");
    r1cs_converter.gen_commitment();
    let (prover_data, _verifier_data) = r1cs_converter.to_r1cs(num_steps);

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
        pc.clone(),
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
        <G1 as Group>::Scalar::from(dfa.ab_to_num(doc.chars().nth(0).unwrap())),
        <G1 as Group>::Scalar::from(0),
        <G1 as Group>::Scalar::from(0),
    ];
    // TODO check "ingrained" bool out
    let mut prev_hash = <G1 as Group>::Scalar::from(0);
    let precomp = prover_data.clone().precompute;
    for i in 0..num_steps {
        println!("STEP {}", i);

        // allocate real witnesses for round i
        let (wits, next_state) = r1cs_converter.gen_wit_i(i, current_state);
        //println!("prover_data {:#?}", prover_data.clone());
        //println!("wits {:#?}", wits.clone());
        let extended_wit = precomp.eval(&wits);
        //println!("extended wit {:#?}", extended_wit);

        prover_data.r1cs.check_all(&extended_wit);

        let current_char = doc.chars().nth(i).unwrap();
        let mut next_char = '#';
        if i + 1 < num_steps {
            next_char = doc.chars().nth(i + 1).unwrap();
        };
        //println!("next char = {}", next_char);

        // expected poseidon
        let mut data = vec![
            prev_hash,
            <G1 as Group>::Scalar::from(dfa.ab_to_num(current_char)),
        ];
        let mut p = Poseidon::<<G1 as Group>::Scalar, typenum::U2>::new_with_preimage(&data, &pc);
        let expected_next_hash: <G1 as Group>::Scalar = p.hash();

        //println!("expected next hash in main {:#?}", expected_next_hash);

        let circuit_primary: DFAStepCircuit<<G1 as Group>::Scalar> = DFAStepCircuit::new(
            &prover_data.r1cs,
            Some(extended_wit),
            <G1 as Group>::Scalar::from(current_state),
            <G1 as Group>::Scalar::from(next_state),
            <G1 as Group>::Scalar::from(dfa.ab_to_num(current_char)),
            <G1 as Group>::Scalar::from(dfa.ab_to_num(next_char)),
            <G1 as Group>::Scalar::from(prev_hash),
            <G1 as Group>::Scalar::from(expected_next_hash),
            <G1 as Group>::Scalar::from(i as u64),
            pc.clone(),
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
        prev_hash = expected_next_hash;
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

#![allow(missing_docs)]
use structopt::StructOpt;
type G1 = pasta_curves::pallas::Point;
type G2 = pasta_curves::vesta::Point;
use ::bellperson::{gadgets::num::AllocatedNum, ConstraintSystem, SynthesisError};
use ff::PrimeField;
use nova_snark::{
    traits::{
        circuit::{StepCircuit, TrivialTestCircuit},
        Group,
    },
    CompressedSNARK, PublicParams, RecursiveSNARK,
};

pub mod deriv;
pub mod parser;
pub mod poly;

use crate::parser::regex_parser;
use crate::poly::mk_poly;

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

#[derive(Clone, Debug)]
struct DFAStepWitness<F: PrimeField> {
    x_i: F,
    x_i_plus_1: F,
}

impl<F: PrimeField> DFAStepWitness<F> {
    // sample witness
    fn new(num_iters: uszie, hash_0: &F, x_0: &F) -> (Vec<F>, Vec<Self>) {
        let mut vars = Vec::new();

        let mut hash_i = *hash_0;
        let mut x_i = *x_0;

        for i in 0..num_iters {
            let x_i_plus_1 = x_i * 2;

            wit.push(Self { x_i, x_i_plus_1 });

            x_i = x_i_plus_1;
        }

        let z0 = vec![*hash_0, *x_0];

        (z0, wit)
    }
}

// sample F: x_{i+1} = 2 * x_i

fn main() {
    let opt = Options::from_args();
    /*
      let ab = opt.alphabet;
      let r = regex_parser(&opt.regex, &ab);
      let pdfa = mk_poly(&r, &ab);

      let doc = opt.input;
      println!("Your regex {:?} matches input {}: {}", r, doc, pdfa.is_match(&doc));
    */

    let num_iters = 2; // len of document

    // main circuit F w/empty witness
    let circuit_primary = DFAStepCircuit {
        seq: vec![
            DFAStepWitness {
                x_i: <G1 as Group>::Scalar::zero(),
                y_i: <G1 as Group>::Scalar::zero(),
                x_i_plus_1: <G1 as Group>::Scalar::zero(),
                y_i_plus_1: <G1 as Group>::Scalar::zero(),
            };
            num_iters
        ],
    };

    // trivial circuit
    let circuit_secondary = TrivialTestCircuit::default();

    // produce public parameters
    println!("Producing public parameters...");
    let pp = PublicParams::<
        G1,
        G2,
        DFAStepCircuit<<G1 as Group>::Scalar>,
        TrivialTestCircuit<<G2 as Group>::Scalar>,
    >::setup(circuit_primary, circuit_secondary.clone());
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

    // produce witnesses

    // recursive SNARK
    type C1 = ChainCircuit<<G1 as Group>::Scalar>;
    type C2 = TrivialTestCircuit<<G2 as Group>::Scalar>;

    let mut recursive_snark: Option<RecursiveSNARK<G1, G2, C1, C2>> = None;

    for (i, circuit_primary) in circuits_primary.iter().take(num_links).enumerate() {
        let result = RecursiveSNARK::prove_step(
            &pp,
            recursive_snark,
            circuit_primary.clone(),
            circuit_secondary.clone(),
            z0_primary,
            z0_secondary,
        );
        assert!(result.is_ok());
        println!("RecursiveSNARK::prove_step {}: {:?}", i, result.is_ok());
        recursive_snark = Some(result.unwrap());
    }

    assert!(recursive_snark.is_some());
    let recursive_snark = recursive_snark.unwrap();

    // verify recursive
    let res = recursive_snark.verify(&pp, num_links, z0_primary, z0_secondary);
    assert!(res.is_ok());

    // compressed SNARK
    let res = CompressedSNARK::<_, _, _, _, S1, S2>::prove(&pp, &recursive_snark);
    assert!(res.is_ok());
    let compressed_snark = res.unwrap();

    // verify compressed
    let res = compressed_snark.verify(&pp, num_links, z0_primary, z0_secondary);
    assert!(res.is_ok());
}

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
    fn new(x_0: &F) -> (Vec<F>, Self) {
        //Vec<Self>) {
        //let mut vars = Vec::new();

        //let mut hash_i = *hash_0;
        let mut x_i = *x_0;

        // note in final version, we will likely do many iters per step
        let x_i_plus_1 = x_i * x_i;

        //vars.push(
        let vars = Self { x_i, x_i_plus_1 };

        //x_i = x_i_plus_1;

        let z_0 = vec![*x_0];

        (z_0, vars)
    }
}

#[derive(Clone, Debug)]
struct DFAStepCircuit<F: PrimeField> {
    wit: DFAStepWitness<F>, // later this will be an array
}

// sample F: x_{i+1} = 2 * x_i
impl<F> StepCircuit<F> for DFAStepCircuit<F>
where
    F: PrimeField,
{
    // return # inputs or outputs of each step
    // synthesize() and output() take as input and output a vec of len = arity()
    fn arity(&self) -> usize {
        1
    }

    // make circuit for a computation step
    // return variable corresponding to output of step z_{i+1}
    fn synthesize<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        z: &[AllocatedNum<F>],
    ) -> Result<Vec<AllocatedNum<F>>, SynthesisError> {
        let mut z_out: Result<Vec<AllocatedNum<F>>, SynthesisError> =
            Err(SynthesisError::AssignmentMissing);

        // starting inputs
        let x_0 = z[0].clone();

        // variables to hold running x_i and y_i
        // let mut hash_i = hash_0;
        let mut x_i = x_0;

        // non deterministic advice
        let x_i_plus_1 = AllocatedNum::alloc(cs.namespace(|| format!("x_i_plus_1")), || {
            Ok(self.wit.x_i_plus_1)
        })?;

        // check conditions hold:
        // x_i_plus_1 = x_i^2
        cs.enforce(
            || format!("x_i * x_i = x_i_plus_1"),
            |lc| lc + x_i.get_variable(),
            |lc| lc + x_i.get_variable(),
            |lc| lc + x_i_plus_1.get_variable(),
        );

        // return hash(x_i_plus_1, ...TODO) since Nova circuits expect a single output
        z_out = Ok(vec![x_i_plus_1.clone()]); // # outputs??

        // update x_i and hash_i for the next iteration
        // x_i = x_i_plus_1;

        z_out
    }

    // return output of step when provided with step's input
    fn output(&self, z: &[F]) -> Vec<F> {
        // sanity check
        debug_assert_eq!(z[0], self.wit.x_i);

        // compute output using advice
        vec![self.wit.x_i_plus_1]
    }
}

fn main() {
    let opt = Options::from_args();
    /*
      let ab = opt.alphabet;
      let r = regex_parser(&opt.regex, &ab);
      let pdfa = mk_poly(&r, &ab);

      let doc = opt.input;
      println!("Your regex {:?} matches input {}: {}", r, doc, pdfa.is_match(&doc));
    */

    // nova recursions
    let num_steps = 3; // len of document

    // main circuit F w/empty witness
    let circuit_primary = DFAStepCircuit {
        wit: DFAStepWitness {
            x_i: <G1 as Group>::Scalar::zero(),
            x_i_plus_1: <G1 as Group>::Scalar::zero(),
        },
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

    // circuit
    let mut circuits_primary = Vec::new();

    // witness #0
    let (z0_primary, dfa_witness) = DFAStepWitness::new(
        // &<G1 as Group>::Scalar::zero(), //hash_0
        &(<G1 as Group>::Scalar::one() + <G1 as Group>::Scalar::one()), //x_0 = 2
    );
    for i in 0..num_steps {
        // witnesses
        if i != 0 {
            let (_z0_primary, dfa_witness) = DFAStepWitness::new(
                // &<G1 as Group>::Scalar::zero(), //hash_0
                &dfa_witness.x_i_plus_1, //x_0
            );
        }
        println!("{:#?}\n{:#?}", z0_primary, dfa_witness);
        // fill circuit w/wit
        let circuit = DFAStepCircuit {
            wit: DFAStepWitness {
                x_i: dfa_witness.x_i,
                x_i_plus_1: dfa_witness.x_i_plus_1,
            },
        };
        circuits_primary.push(circuit);
    }

    // trivial
    let z0_secondary = vec![<G2 as Group>::Scalar::zero()];

    type C1 = DFAStepCircuit<<G1 as Group>::Scalar>;
    type C2 = TrivialTestCircuit<<G2 as Group>::Scalar>;

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
}

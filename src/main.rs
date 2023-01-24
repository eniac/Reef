#![allow(missing_docs)]
use structopt::StructOpt;
type G1 = pasta_curves::pallas::Point;
type G2 = pasta_curves::vesta::Point;
use ::bellperson::{gadgets::num::AllocatedNum, SynthesisError};
use circ::cfg;
use circ::cfg::CircOpt;
use ff::PrimeField;
use nova_snark::{
    traits::{
        circuit::{StepCircuit, TrivialTestCircuit},
        Group,
    },
    CompressedSNARK, PublicParams, RecursiveSNARK,
};

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
    wit: DFAStepWitness<F>,
    //arkcs:
}

impl<F> DFAStepCircuit<F>
where
    F: PrimeField,
{
    fn new(num_steps: usize, x0: F) -> (Vec<F>, Vec<Self>) {
        let z0 = vec![x0];
        let mut circuits = Vec::new();
        let (mut zi, mut dfa_witness) = DFAStepWitness::new(&x0);
        let circuit = DFAStepCircuit {
            wit: dfa_witness.clone(),
        };
        // println!("{:#?}", circuit);
        circuits.push(circuit);

        for i in 1..num_steps {
            (zi, dfa_witness) = DFAStepWitness::new(&dfa_witness.x_i_plus_1);

            let circuit = DFAStepCircuit {
                wit: dfa_witness.clone(),
            };
            // println!("{:#?}", circuit);
            circuits.push(circuit);
        }

        (z0, circuits)
    }

    // helper methods here (?)
}

// sample F: x_{i+1} = x_i * x_i
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
    fn synthesize<CS: bellperson::ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        z: &[AllocatedNum<F>],
    ) -> Result<Vec<AllocatedNum<F>>, SynthesisError> {
        let mut z_out: Result<Vec<AllocatedNum<F>>, SynthesisError> =
            Err(SynthesisError::AssignmentMissing);

        // let mut hash_i = hash_0;
        // let mut x_i = z[0].clone();;

        // non deterministic advice
        let x_i = AllocatedNum::alloc(cs.namespace(|| format!("x_i")), || Ok(self.wit.x_i))?;
        let x_i_plus_1 = AllocatedNum::alloc(cs.namespace(|| format!("x_i_plus_1")), || {
            Ok(self.wit.x_i_plus_1)
        })?;

        // check conditions hold:
        // x_i_plus_1 = x_i^2

        cs.enforce(
            || format!("x_i * x_i = x_i_plus_1"),
            |lc| lc + CS::one() + CS::one(),
            |lc| lc + CS::one() + CS::one(),
            |lc| lc + CS::one() + CS::one() + CS::one() + CS::one(),
        );

        //println!("TESTING {:#?}", cs);

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
/*
pub fn ark_mat_to_nova<F>(mat: ark_relations::r1cs::Matrix<F>) {
    println!("SCALAR {:#?}", type_of(&<G1 as Group>::Scalar::one()));
    for cs in mat {
        // rows = constraints
        for col in cs {
            let num = col.0;
            let slot = col.1;
        }
    }

    /*println!("mat len {:#?}", mat.len());
    for row in mat {
        println!("len row {:#?}", row.len());
        for col in row {
            println!("{:#?}", col.1);
        }
        println!("\n");
    }
    */
}
*/
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
    circ.field.custom_modulus = "17".to_owned(); //TODO
    cfg::set(&circ);

    // Convert the Regex to a DFA
    let mut dfa = DFA::new(&ab[..]);
    mk_dfa(&r, &ab, &mut dfa);
    println!("dfa: {:#?}", dfa);

    dfa.to_lookup_comp();

    // use "empty" (witness-less) circuit to generate nova F

    // iterations
    let num_steps = doc.chars().count(); // len of document
    println!("Doc len is {}", num_steps);
    let mut chars = doc.chars();

    for i in 0..num_steps {
        // allocate real witnesses for round i

        // regenerate circuit (only needed for validation, not for nova)
        //let next_state = dfa.cond_delta(civar, curr_state.clone()).value().unwrap();

        // generate nova witness vector i

        // translate wit to nova, fold

        // for next i+1 round
    }

    // TEST
    /*
    let circuit_primary = DFAStepCircuit {
        wit: DFAStepWitness {
            x_i: <G1 as Group>::Scalar::one(),
            x_i_plus_1: <G1 as Group>::Scalar::zero(),
        },
    };

    println!("TEST {:#?}", type_of(&circuit_primary.wit.x_i));

    // fold + compile nova

    // TODO: check conversion is good
    // NOVA

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

    println!("{:#?}", circuit_primary.clone());

    // circuit
    let (z0_primary, circuits_primary) = DFAStepCircuit::new(
        num_steps,
        <G1 as Group>::Scalar::one() + <G1 as Group>::Scalar::one(),
    );

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
    */
}

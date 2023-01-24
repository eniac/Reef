use itertools::Itertools;
use std::collections::HashMap;
use std::collections::HashSet;
use std::io::{Error, ErrorKind, Result};

use crate::deriv::nullable;
use crate::parser::re::Regex;

use circ::cfg::cfg;
use circ::ir::opt::*;
use circ::ir::proof::Constraints;
use circ::ir::term::*;
use circ::target::r1cs::opt::reduce_linearities;
use circ::target::r1cs::trans::to_r1cs;

use rug::Integer;

fn new_field<I>(i: I) -> Term
where
    Integer: From<I>,
{
    leaf_term(Op::Const(Value::Field(cfg().field().new_v(i))))
}

#[derive(Debug)]
pub struct DFA<'a> {
    /// Alphabet
    pub ab: &'a str,
    /// Set of states (and their index)
    pub states: HashMap<Regex, u64>,
    /// Transition relation from [state -> state], given [char]
    pub trans: HashSet<(Regex, char, Regex)>,
}

impl<'a> DFA<'a> {
    pub fn new(ab: &'a str) -> Self {
        Self {
            ab,
            states: HashMap::new(),
            trans: HashSet::new(),
        }
    }

    pub fn ab_to_num(&self, c: char) -> u64 {
        let sorted_ab = self.ab.chars().sorted().collect::<String>();
        let num = sorted_ab.chars().position(|x| x == c).unwrap();
        num as u64
    }

    pub fn nstates(&self) -> usize {
        self.states.len()
    }

    pub fn add_transition(&mut self, from: &Regex, c: char, to: &Regex) {
        self.trans.insert((from.clone(), c, to.clone()));
    }

    pub fn add_state(&mut self, new_state: &Regex) {
        self.states.insert(new_state.clone(), self.nstates() as u64);
    }

    pub fn contains_state(&self, state: &Regex) -> bool {
        self.states.contains_key(state)
    }

    pub fn get_state_num(&self, state: &Regex) -> u64 {
        self.states[state]
    }

    /// Initial state
    pub fn get_init_state(&self) -> u64 {
        0
    }

    /// Final state
    pub fn get_final_states(&self) -> HashSet<u64> {
        self.states
            .clone()
            .into_iter()
            .filter_map(|(k, v)| if nullable(&k) { Some(v) } else { None })
            .collect()
    }

    /// DFA step function [delta(s, c) = s'] function
    fn delta(&self, state: u64, ch: char) -> Result<u64> {
        let res: Vec<u64> = self
            .deltas()
            .clone()
            .into_iter()
            .filter_map(|(s, c, t)| if s == state && c == ch { Some(t) } else { None })
            .collect();

        if res.len() == 1 {
            Ok(res[0])
        } else {
            Err(Error::new(
                ErrorKind::InvalidInput,
                "Invalidated DFA invariant",
            ))
        }
    }

    fn deltas(&self) -> Vec<(u64, char, u64)> {
        self.trans
            .clone()
            .into_iter()
            .map(|(a, b, c)| (self.get_state_num(&a), b, self.get_state_num(&c)))
            .collect()
    }

    pub fn to_lookup_comp(&self) {
        let ite = term(
            Op::Eq,
            vec![
                leaf_term(Op::Var(
                    "next_state".to_owned(),
                    Sort::Field(cfg().field().clone()),
                )),
                term(
                    Op::Ite,
                    vec![
                        term(
                            Op::Eq,
                            vec![
                                leaf_term(Op::Var(
                                    "char".to_owned(),
                                    Sort::Field(cfg().field().clone()),
                                )),
                                new_field(0),
                            ],
                        ),
                        new_field(1),
                        new_field(2),
                    ],
                ),
            ],
        );

        let assertions = vec![ite];
        let pub_inputs = vec![];

        let cs = Computation::from_constraint_system_parts(assertions, pub_inputs);

        let mut css = Computations::new();
        css.comps.insert("main".to_string(), cs);

        let opt_css = opt(
            css,
            vec![
                Opt::ScalarizeVars,
                Opt::Flatten,
                Opt::Sha,
                Opt::ConstantFold(Box::new([])),
                // Tuples must be eliminated before oblivious array elim
                Opt::Tuple,
                Opt::ConstantFold(Box::new([])),
                Opt::Obliv,
                // The obliv elim pass produces more tuples, that must be eliminated
                Opt::Tuple,
                Opt::LinearScan,
                // The linear scan pass produces more tuples, that must be eliminated
                Opt::Tuple,
                Opt::Flatten,
                Opt::ConstantFold(Box::new([])),
            ],
        );

        let (mut prover_data, verifier_data) = to_r1cs(opt_css.get("main").clone(), cfg());

        println!(
            "Pre-opt R1cs size: {}",
            prover_data.r1cs.constraints().len()
        );
        prover_data.r1cs = reduce_linearities(prover_data.r1cs, cfg());

        println!("Final R1cs size: {}", prover_data.r1cs.constraints().len());
    }

    /*

        pub fn to_poly(&self, p: BigInt) -> Vec<BigInt> {
            let coefs = Vec::new();

            for i in 0..n {
                let mut term = f[i].y;
                // A good old nested for loop :)
                for j in 0..n {
                    if i != j {
                        // X's should be unique
                        assert!(f[i].x - f[j].x != 0.0);
                        let denominator = f[i].x - f[j].x;
                        let numerator = - f[j].x;
                        term = term * (numerator/denominator);
                    }
                }
                result += term;
                result = result.mod_euc(p)
            }
    */
    /*
        /// Make a DFA delta function into a circuit
        /// Both [c] and [state] are in index
        /// form in a [DomainRadix2] in [src/domain.rs]
        pub fn cond_delta(&self, c: FpVar<Fr>, state: FpVar<Fr>) -> FpVar<Fr> {
            /* println!(
                "state {:#?}, c {:#?}, len {:#?}",
                state.value().unwrap(),
                c.value().unwrap(),
                frth(self.ab.len() as u64)
            ); */

    //        let index = (state * frth(self.ab.len() as u64) + c)

            // println!("index {:#?}", index.value().unwrap());

            let mut bits = Vec::new();
            for i in 0..num_bits(self.deltas().len() as u64) {
                bits.push(index[i as usize].clone());
            }
            // println!("Bits {:#?}", bits.value().unwrap());

            // Sort so indexing by (state, char) works correctly in the CondGadget
            let mut ds: Vec<FpVar<Fr>> = self
                .deltas()
                .into_iter()
                .sorted()
    //            .map(|(_, _, c)| FpVar::constant(frth(c)))
                .collect();

            // println!("Deltas {:#?}", self.deltas().into_iter().sorted());

            // pad ds
            let dummy = FpVar::constant(Fr::zero());
            while ds.len() < (1 << num_bits(self.deltas().len() as u64)) {
                ds.push(dummy.clone());
            }

            CondSelectGadget::conditionally_select_power_of_two_vector(&bits, &ds).unwrap()

            //let b = Boolean::new_witness(
            //CondSelectGadget::conditionally_select(b, FpVar::constant(frth(1)), FpVar::constant(frth(2)));
        }

    */
}

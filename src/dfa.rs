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

fn new_const<I>(i: I) -> Term
where
    Integer: From<I>,
{
    leaf_term(Op::Const(Value::Field(cfg().field().new_v(i))))
}

fn new_var(name: String) -> Term {
    leaf_term(Op::Var(name, Sort::Field(cfg().field().clone())))
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
        let sorted_ab = self.ab.chars().sorted();

        let mut char_bottom = new_const(self.nstates()); //TODO
        let mut i = 0; // position of char
        for c in sorted_ab {
            // for each char
            let mut state_bottom = new_const(self.nstates()); //TODO dummy state that is returned in case of no match
                                                              // perhaps better way todo
                                                              // make each state ite
            for (s, ch, t) in self.deltas() {
                if ch == c {
                    // if this char is transition
                    state_bottom = term(
                        Op::Ite,
                        vec![
                            term(
                                Op::Eq,
                                vec![new_var("current state".to_owned()), new_const(s)],
                            ), // if match on this state
                            new_const(t), // true (??)
                            state_bottom, // false
                        ],
                    );
                }
            }

            // add to char ite (outer)
            char_bottom = term(
                Op::Ite,
                vec![
                    term(Op::Eq, vec![new_var("char".to_owned()), new_const(i)]),
                    state_bottom,
                    char_bottom,
                ],
            );
            i += 1;
        }

        let ite = term(Op::Eq, vec![new_var("next_state".to_owned()), char_bottom]);

        //println!("ITE {:#?}", ite);

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
}

#[cfg(test)]
mod tests {

    use crate::deriv::{mk_dfa, nullable};
    use crate::dfa::DFA;
    use crate::domain::{frth, num_bits, DomainRadix2};
    use crate::parser::regex_parser;
    use itertools::Itertools;
    use std::collections::HashMap;
    use std::collections::HashSet;
    use std::io::{Error, ErrorKind, Result};

    fn set_up_delta_test(r: &str, alpha: &str, tocheck: &str) -> bool {
        let ab = String::from(alpha);
        let regex = regex_parser(&String::from(r), &ab);
        let input = String::from(tocheck);

        let mut dfa = DFA::new(&ab[..]);
        mk_dfa(&regex, &ab, &mut dfa);
        let mut s = dfa.get_init_state();

        for i in 0..input.len() {
            s = dfa.delta(s, input.chars().nth(i).unwrap()).unwrap();
        }
        let re_match = dfa.get_final_states().contains(&s);
        return re_match;
    }

    #[test]
    fn test_dfa_delta_non_circuit_basic() {
        let re_match = set_up_delta_test("a", "ab", "a");
        assert!(re_match);
    }

    #[test]
    fn test_dfa_delta_non_circuit_basic_nonmatch() {
        let re_match = set_up_delta_test("a", "ab", "b");
        assert!(!re_match);
    }

    #[test]
    fn test_dfa_delta_non_circuit() {
        let re_match = set_up_delta_test("aba", "ab", "aba");
        assert!(re_match);
    }

    #[test]
    fn test_dfa_delta_non_circuit_nonmatch() {
        let re_match = set_up_delta_test("aba", "ab", "ab");
        assert!(!re_match);
    }

    #[test]
    fn test_dfa_delta_non_circuit_star() {
        let re_match = set_up_delta_test("a.*a", "ab", "abba");
        assert!(re_match);
    }

    #[test]
    fn test_dfa_delta_non_circuit_stat_nonmatch() {
        let re_match = set_up_delta_test("a.*a", "ab", "abb");
        assert!(!re_match);
    }
}

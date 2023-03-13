use itertools::Itertools;
use std::collections::HashMap;
use std::collections::HashSet;
use std::io::{Error, ErrorKind, Result};

use crate::deriv::{deriv, nullable};
use crate::parser::re::Regex;

#[derive(Debug)]
pub struct DFA {
    /// Alphabet
    pub ab: Vec<String>,
    /// Set of states (and their index)
    pub states: HashMap<Regex, u64>,
    /// Transition relation from [state -> state] given an input
    pub trans: HashMap<(Regex, String), Regex>,
}

impl DFA {
    pub fn new<'a>(ab: &'a str, re: Regex) -> Self {

        let mut d = Self {
            ab: ab.chars().sorted().map(|c| c.to_string()).collect(),
            states: HashMap::new(),
            trans: HashMap::new(),
        };

        // Recursive funtion
        fn mk_dfa(d: &mut DFA, q: &Regex) {
          // Add to DFA if not already there
          d.add_state(q);

          // Explore derivatives
          for c in d.ab.clone().into_iter() {
              let q_c = deriv(&c, q);
              d.add_transition(q, &c, &q_c);
              if d.contains_state(&q_c) {
                  continue;
              } else {
                  mk_dfa(d, &q_c);
              }
          }
        }

        // Recursively build transitions
        mk_dfa(&mut d, &re);
        d
    }

    pub fn ab_to_num(&self, c: &String) -> u64 {
        /*let sorted_ab = self.ab.chars().sorted().collect::<String>();
        let num = sorted_ab.chars().position(|x| x == c).unwrap();
        num as u64
        */
        if c == "" {
            self.ab.len() as u64 // TODO better solution
        } else {
            self.ab.iter().position(|x| x == c).unwrap() as u64
        }
    }

    pub fn nstates(&self) -> usize {
        self.states.len()
    }

    pub fn add_transition(&mut self, from: &Regex, c: &String, to: &Regex) {
        self.trans.insert((from.clone(), c.clone()), to.clone());
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

    pub fn get_state_regex(&self, n: &u64) -> Option<Regex> {
        self.states
            .iter()
            .find_map(|(&k, v)| if v == n { Some(k) } else { None })
    }

    /// Initial state
    pub fn get_init_state(&self) -> u64 {
        0
    }

    /// Final states
    pub fn get_final_states(&self) -> HashSet<u64> {
        self.states
            .clone()
            .into_iter()
            .filter_map(|(k, v)| if nullable(&k) { Some(v) } else { None })
            .collect()
    }

    /// Non final states
    pub fn get_non_final_states(&self) -> HashSet<u64> {
        self.states
            .clone()
            .into_iter()
            .filter_map(|(k, v)| if nullable(&k) { None } else { Some(v) })
            .collect()
    }

    /// All states
    pub fn get_states(&self) -> HashSet<u64> {
        self.states.clone().into_values().collect()
    }

    /// DFA step function [delta(s, c) = s'] function
    pub fn delta(&self, state: &u64, ch: &String) -> Result<u64> {
        self.get_state_regex(&state)
            .and_then(|r| self.trans.get(&(r, *ch)))
            .map(|s| self.get_state_num(s))
            .ok_or(Error::new(ErrorKind::InvalidInput,
                    "Invalidated DFA invariant (determinism)"))
    }

    pub fn deltas(&self) -> Vec<(u64, String, u64)> {
        self.trans
            .clone()
            .into_iter()
            .map(|((a, b), c)| (self.get_state_num(&a), b, self.get_state_num(&c)))
            .collect()
    }

    pub fn is_match(&self, doc: &Vec<String>) -> bool {
        let mut s = self.get_init_state();
        for c in doc.iter() {
            s = self.delta(&s, c).unwrap();
        }
        // If it is in the final states, then success
        self.get_final_states().contains(&s)
    }

    /// Double the stride of the DFA, can be nested k-times
    /// TODO: Figure out accepting states
    ///       Figure out O(|ab|*n^2) algorithm
    pub fn double_stride(&mut self) {
        let mut ab = Vec::new();
        let mut ntrans = HashMap::new();
        for c0 in self.ab {
            for c1 in self.ab {
                for a in self.states.keys() {
                    let b = self.trans.get(&(*a, c0)).unwrap();
                    let c = self.trans.get(&(*b, c1)).unwrap();
                    ntrans.insert((*a, c0 + &c1), *c);
                    ab.push(c0 + &c1);
                }
            }
        }

        self.trans = ntrans;
        self.ab = ab;
    }

    /// Compute equivalence classes from the DFA
    /// and output for each character its equivalence class
    /// TODO: Make algorithm O(|ab|*n)
    pub fn equiv_classes(&self) -> HashMap<String, HashSet<String>> {
        let mut char_classes: HashMap<String, HashSet<String>> = HashMap::new();

        for a in self.ab {
            for b in self.ab {
                if !char_classes.contains_key(&a) {
                    char_classes.insert(a, HashSet::from([a]));
                }
                if !char_classes.contains_key(&b) {
                    char_classes.insert(b, HashSet::from([b]));
                }
                let mut equivalent = true;
                for s in self.get_states() {
                    if self.delta(&s, &a).unwrap() != self.delta(&s, &b).unwrap() {
                        equivalent = false;
                    }
                }
                // Merge equivalence classes
                if equivalent {
                    let union: HashSet<String> =
                        char_classes[&a].union(&char_classes[&b]).cloned().collect();
                    char_classes.insert(a, union.clone());
                    char_classes.insert(b, union);
                }
            }
        }

        char_classes
    }
}

#[cfg(test)]
mod tests {

    use crate::dfa::DFA;
    use crate::parser::regex_parser;

    fn set_up_delta_test(r: &str, alpha: &str, tocheck: &str) -> bool {
        let ab = String::from(alpha);
        let regex = regex_parser(&String::from(r), &ab);
        let input : Vec<String> = tocheck.chars().map(|c| c.to_string()).collect();

        let mut dfa = DFA::new(&ab[..], regex);
        let mut s = dfa.get_init_state();

        for i in 0..input.len() {
            s = dfa.delta(&s, &input[i]).unwrap();
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

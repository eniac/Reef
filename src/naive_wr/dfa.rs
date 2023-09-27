use itertools::Itertools;
use std::collections::HashMap;
use std::collections::HashSet;
use std::io::{Error, ErrorKind, Result};

use crate::naive_wr::naive_regex::{re,Regex};
// use crate::regex::*;

#[derive(Debug)]
pub struct DFA<'a> {
    /// Alphabet
    pub ab: &'a str,
    /// map of alphabet -> u64
    pub chars: HashMap<char, u64>,
    /// Set of states (and their index)
    pub states: HashMap<Regex, u64>,
    /// Transition relation from [state -> state], given [char]
    pub trans: HashSet<(Regex, char, Regex)>,
}

impl<'a> DFA<'a> {
    pub fn new(ab: &'a str, re: Regex) -> Self {
        let mut char_map = HashMap::new();
        for (i, c) in ab.chars().sorted().enumerate() {
            char_map.insert(c, i as u64);
        }

        let mut d = Self {
            ab,
            chars: char_map,
            states: HashMap::new(),
            trans: HashSet::new(),
        };

        // Recursive funtion
        fn mk_dfa(d: &mut DFA, q: &Regex) {
          // Add to DFA if not already there
          d.add_state(q);

          // Explore derivatives
          //d.ab.chars()
          for c in d.ab.chars()  {
              let q_c = re::deriv(q, &c);
              d.add_transition(q, c, &q_c);
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

    pub fn ab_to_num(&self, c: char) -> u64 {
        /*let sorted_ab = self.ab.chars().sorted().collect::<String>();
        let num = sorted_ab.chars().position(|x| x == c).unwrap();
        num as u64
        */
        match c {
            '#' => self.chars.len() as u64, // TODO better solution
            _ => self.chars[&c],
        }
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

    /// Final states
    pub fn get_final_states(&self) -> HashSet<u64> {
        self.states
            .clone()
            .into_iter()
            .filter_map(|(k, v)| if re::nullable(&k) { Some(v) } else { None })
            .collect()
    }

    /// Non final states
    pub fn get_non_final_states(&self) -> HashSet<u64> {
        self.states
            .clone()
            .into_iter()
            .filter_map(|(k, v)| if re::nullable(&k) { None } else { Some(v) })
            .collect()
    }

    /// All states
    pub fn get_states(&self) -> HashSet<u64> {
        self.states.clone().into_values().collect()
    }

    /// DFA step function [delta(s, c) = s'] function
    pub fn delta(&self, state: u64, ch: char) -> Result<u64> {
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
                "Invalidated DFA invariant (determinism)",
            ))
        }
    }

    pub fn deltas(&self) -> Vec<(u64, char, u64)> {
        self.trans
            .clone()
            .into_iter()
            .map(|(a, b, c)| (self.get_state_num(&a), b, self.get_state_num(&c)))
            .collect()
    }

    pub fn is_match(&self, doc: &String) -> bool {
        let mut s = self.get_init_state();
        for c in doc.chars() {
            s = self.delta(s, c).unwrap();
        }
        // If it is in the final states, then success
        self.get_final_states().contains(&s)
    }

    pub fn solve(&self, doc: &String) -> Vec<(u32,u32,u32)> {
        let mut solution = vec![];
        let mut cur = self.get_init_state() as u32;
        for c in doc.chars() {
            let next = self.delta(cur as u64, c).unwrap() as u32;
            solution.push((cur,c as u32,next));
            cur = next;
        }
        // If it is in the final states, then success
        solution
    }

    pub fn equiv_classes(&self) -> HashMap<char, HashSet<char>> {
        let mut char_classes: HashMap<char, HashSet<char>> = HashMap::new();

        for a in self.ab.chars() {
            for b in self.ab.chars() {
                if !char_classes.contains_key(&a) {
                    char_classes.insert(a, HashSet::from([a]));
                }
                if !char_classes.contains_key(&b) {
                    char_classes.insert(b, HashSet::from([b]));
                }
                let mut equivalent = true;
                for s in self.get_states() {
                    if self.delta(s, a).unwrap() != self.delta(s, b).unwrap() {
                        equivalent = false;
                    }
                }
                // Merge equivalence classes
                if equivalent {
                    let union: HashSet<char> =
                        char_classes[&a].union(&char_classes[&b]).cloned().collect();
                    char_classes.insert(a, union.clone());
                    char_classes.insert(b, union);
                }
            }
        }

        char_classes
    }

}

// #[cfg(test)]
// mod tests {

//     use crate::naive::dfa::DFA;
//     use crate::naive::naive_parser::regex_parser;

//     fn set_up_delta_test(r: &str, alpha: &str, tocheck: &str) -> bool {
//         let ab = String::from(alpha);
//         let regex = regex_parser(&String::from(r), &ab);
//         let input = String::from(tocheck);

//         let mut dfa = DFA::new(&ab[..], regex);
//         let mut s = dfa.get_init_state();

//         for i in 0..input.len() {
//             s = dfa.delta(s, input.chars().nth(i).unwrap()).unwrap();
//         }
//         let re_match = dfa.get_final_states().contains(&s);
//         return re_match;
//     }

//     #[test]
//     fn test_dfa_delta_non_circuit_basic() {
//         let re_match = set_up_delta_test("a", "ab", "a");
//         assert!(re_match);
//     }

//     #[test]
//     fn test_dfa_delta_non_circuit_basic_nonmatch() {
//         let re_match = set_up_delta_test("a", "ab", "b");
//         assert!(!re_match);
//     }

//     #[test]
//     fn test_dfa_delta_non_circuit() {
//         let re_match = set_up_delta_test("aba", "ab", "aba");
//         assert!(re_match);
//     }

//     #[test]
//     fn test_dfa_delta_non_circuit_nonmatch() {
//         let re_match = set_up_delta_test("aba", "ab", "ab");
//         assert!(!re_match);
//     }

//     #[test]
//     fn test_dfa_delta_non_circuit_star() {
//         let re_match = set_up_delta_test("a.*a", "ab", "abba");
//         assert!(re_match);
//     }

//     #[test]
//     fn test_dfa_delta_non_circuit_stat_nonmatch() {
//         let re_match = set_up_delta_test("a.*a", "ab", "abb");
//         assert!(!re_match);
//     }
// }
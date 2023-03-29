use itertools::Itertools;
use std::collections::HashMap;
use std::collections::HashSet;
use std::io::{Error, ErrorKind, Result};

use crate::regex::Regex;

#[derive(Debug)]
pub struct DFA {
    /// Alphabet
    pub ab: Vec<String>,
    /// Set of states (and their index)
    pub states: HashMap<Regex, usize>,
    /// Transition relation from [state -> state] given an input
    pub trans: HashMap<(Regex, String), Regex>,
    /// Must match from the begining of the document (default: false)
    pub anchor_start: bool,
    /// Must match until the end of the document (default: false)
    pub anchor_end: bool
}

impl DFA {
    pub fn new<'a>(alphabet: &'a str, re: Regex) -> Self {
        let ab: Vec<String> = alphabet.chars().sorted().map(|c| c.to_string()).collect();

        let mut trans: HashMap<(Regex, String), Regex> = HashMap::new();
        let mut states: HashMap<Regex, usize> = HashMap::new();

        // Recursive funtion
        fn build_trans(
            states: &mut HashMap<Regex, usize>,
            trans: &mut HashMap<(Regex, String), Regex>,
            ab: &Vec<String>,
            q: &Regex,
        ) {
            // Add to DFA if not already there
            states.insert(q.clone(), states.len() as usize);

            // Explore derivatives
            for c in &ab[..] {
                let q_c = q.deriv(&c);
                trans.insert((q.clone(), c.clone()), q_c.clone());
                if states.contains_key(&q_c) {
                    continue;
                } else {
                    build_trans(states, trans, ab, &q_c);
                }
            }
        }

        // Recursively build transitions
        build_trans(&mut states, &mut trans, &ab, &re);
        Self { ab, states, trans, anchor_start: re.is_start_anchored(), anchor_end: re.is_end_anchored() }
    }

    pub fn ab_to_num(&self, c: &String) -> usize {
        /*let sorted_ab = self.ab.chars().sorted().collect::<String>();
        let num = sorted_ab.chars().position(|x| x == c).unwrap();
        num as usize
        */
        if c == "" {
            self.ab.len() as usize // TODO better solution
        } else {
            self.ab.iter().position(|x| x == c).unwrap() as usize
        }
    }

    pub fn nstates(&self) -> usize {
        self.states.len()
    }

    pub fn nchars(&self) -> usize {
        self.ab.len()
    }

    pub fn is_exact_match(&self) -> bool {
        self.anchor_start && self.anchor_end
    }

    pub fn contains_state(&self, state: &Regex) -> bool {
        self.states.contains_key(state)
    }

    pub fn get_state_num(&self, state: &Regex) -> Option<usize> {
        self.states.get(state).map(|c| c.clone())
    }

    pub fn get_state_regex(&self, n: &usize) -> Option<Regex> {
        self.states
            .iter()
            .find_map(|(k, v)| if v == n { Some(k.clone()) } else { None })
    }

    /// Initial state
    pub fn get_init_state(&self) -> usize {
        0
    }

    /// Final states
    pub fn get_final_states(&self) -> HashSet<usize> {
        self.states
            .clone()
            .into_iter()
            .filter_map(|(k, v)| if k.nullable() { Some(v) } else { None })
            .collect()
    }

    /// Non final states
    pub fn get_non_final_states(&self) -> HashSet<usize> {
        self.states
            .clone()
            .into_iter()
            .filter_map(|(k, v)| if k.nullable() { None } else { Some(v) })
            .collect()
    }

    /// All states
    pub fn get_states(&self) -> HashSet<usize> {
        self.states.clone().into_values().collect()
    }

    /// DFA step function [delta(s, c) = s'] function
    pub fn delta(&self, state: &usize, ch: &String) -> Option<usize> {
        self.get_state_regex(&state)
            .and_then(|r| self.trans.get(&(r, ch.clone())))
            .and_then(|s| self.get_state_num(s))
    }

    pub fn deltas(&self) -> Vec<(usize, String, usize)> {
        self.trans
            .clone()
            .into_iter()
            .map(|((a, b), c)| {
                (
                    self.get_state_num(&a).unwrap(),
                    b,
                    self.get_state_num(&c).unwrap(),
                )
            })
            .collect()
    }

    pub fn is_match(&self, doc: &Vec<String>) -> bool {
        let mut s = self.get_init_state();
        let mut start_idxs = Vec::new();
        let mut j = 0;
        let mut res = false;
        let accepting = &self.get_final_states();

        // Iterate over all postfixes of doc
        if self.anchor_start {
            start_idxs.push(0);
        } else {
            for i in 0..doc.len() {
                start_idxs.push(i)
            }
        }

        // For every postfix
        for i in start_idxs {
            res = false;
            for j in i..doc.len() {
                // Apply transition relation
                s = self.delta(&s, &doc[j]).unwrap();
                //
                if accepting.contains(&s) {
                    // If we found a substring (prefix) or exact match
                    if !self.anchor_end || j == doc.len() - 1 {
                        res = true;
                        break;
                    }
                }
            }
            // Found an accepting state
            if res {
                break;
            }
        }
        res
    }

    /// Double the stride of the DFA, can be nested k-times
    /// TODO: Figure out accepting states
    ///       Figure out O(|ab|*n^2) algorithm
    pub fn double_stride(&self) -> Self {
        let mut ab = Vec::new();
        let mut trans = HashMap::new();
        for c0 in &self.ab {
            for c1 in &self.ab {
                for (a, _) in &self.states {
                    let b = self.trans.get(&(a.clone(), c0.clone())).unwrap();
                    let c = self.trans.get(&(b.clone(), c1.clone())).unwrap();
                    trans.insert((a.clone(), c0.clone() + &c1), c.clone());
                    ab.push(c0.clone() + &c1);
                }
            }
        }

        // TODO: Accepting states
        let states = self.states.clone();
        Self { ab, states, trans, anchor_start: self.anchor_start, anchor_end: self.anchor_end }
    }

    /// Compute equivalence classes from the DFA
    /// and output for each character its equivalence class
    /// TODO: Make algorithm O(|ab|*n)
    pub fn equiv_classes(&self) -> HashMap<String, HashSet<String>> {
        let mut char_classes: HashMap<String, HashSet<String>> = HashMap::new();

        for a in &self.ab {
            for b in &self.ab {
                if !char_classes.contains_key(a) {
                    char_classes.insert(a.clone(), HashSet::from([a.clone()]));
                }
                if !char_classes.contains_key(b) {
                    char_classes.insert(b.clone(), HashSet::from([b.clone()]));
                }
                // Merge equivalence classes
                if self
                    .states
                    .iter()
                    .all(|(_, s)| self.delta(&s, &a).unwrap() == self.delta(&s, &b).unwrap())
                {
                    let union: HashSet<String> =
                        char_classes[a].union(&char_classes[b]).cloned().collect();
                    char_classes.insert(a.clone(), union.clone());
                    char_classes.insert(b.clone(), union);
                }
            }
        }

        char_classes
    }
}

#[cfg(test)]
mod tests {
    use crate::dfa::DFA;
    use crate::regex::Regex;

    fn set_up_delta_test(r: &str, alpha: &str, tocheck: &str) -> bool {
        let ab = String::from(alpha);
        let regex = Regex::new(r);
        let input: Vec<String> = tocheck.chars().map(|c| c.to_string()).collect();

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

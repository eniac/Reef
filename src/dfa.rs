use itertools::Itertools;
use std::collections::HashMap;
use std::collections::HashSet;
use std::io::{Error, ErrorKind, Result};

use crate::deriv::nullable;
use crate::parser::re::Regex;

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
    pub fn new(ab: &'a str) -> Self {
        let mut char_map = HashMap::new();
        for (i, c) in ab.chars().sorted().enumerate() {
            char_map.insert(c, i as u64);
        }

        Self {
            ab,
            chars: char_map,
            states: HashMap::new(),
            trans: HashSet::new(),
        }
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

    /// Final state
    pub fn get_final_states(&self) -> HashSet<u64> {
        self.states
            .clone()
            .into_iter()
            .filter_map(|(k, v)| if nullable(&k) { Some(v) } else { None })
            .collect()
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
                "Invalidated DFA invariant",
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
}

#[cfg(test)]
mod tests {

    use crate::deriv::{mk_dfa, nullable};
    use crate::dfa::DFA;
    use crate::parser::re::Regex;
    use crate::parser::regex_parser;

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

    use itertools::Itertools;
    use std::fmt::{Display, Error, Formatter};
    use std::fs::File;

    #[test]
    fn dot_dfa() {
        let ab = String::from("ab");
        let regex = regex_parser(&String::from(".*ab"), &ab);

        let mut dfa = DFA::new(&ab[..]);
        mk_dfa(&regex, &ab, &mut dfa);

        // Output file
        let mut buffer = File::create("graphs/dfa.dot").unwrap();

        dot::render(&dfa, &mut buffer).unwrap()
    }

    type Ed = (Regex, Vec<char>, Regex);

    impl<'a> dot::Labeller<'a, Regex, Ed> for DFA<'a> {
        fn graph_id(&'a self) -> dot::Id<'a> {
            dot::Id::new("example").unwrap()
        }
        fn node_id(&'a self, n: &Regex) -> dot::Id<'a> {
            dot::Id::new(format!("N{}", self.states[n])).unwrap()
        }
        fn node_label<'b>(&'b self, r: &Regex) -> dot::LabelText<'b> {
            dot::LabelText::LabelStr(format!("{}", r).into())
        }
        fn edge_label<'b>(&'b self, e: &Ed) -> dot::LabelText<'b> {
            let mut comma_separated = String::new();

            for num in &e.1[0..e.1.len() - 1] {
                comma_separated.push_str(&num.to_string());
                comma_separated.push_str(", ");
            }

            comma_separated.push_str(&e.1[e.1.len() - 1].to_string());

            dot::LabelText::LabelStr(format!("{}", comma_separated).into())
        }
    }

    impl<'a> dot::GraphWalk<'a, Regex, Ed> for DFA<'a> {
        fn nodes(&'a self) -> dot::Nodes<'a, Regex> {
            self.states.clone().into_keys().collect()
        }
        fn edges(&'a self) -> dot::Edges<'a, Ed> {
            self.trans
                .clone()
                .into_iter()
                .map(|(a, c, b)| ((a, b), c))
                .into_group_map()
                .into_iter()
                .map(|((a, b), c)| (a, c, b))
                .collect()
        }

        fn source(&self, e: &Ed) -> Regex {
            e.0.clone()
        }
        fn target(&self, e: &Ed) -> Regex {
            e.2.clone()
        }
    }
}

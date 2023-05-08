use itertools::Itertools;
use std::collections::HashMap;
use std::collections::{BTreeSet, HashSet};

use crate::regex::Regex;

#[derive(Debug)]
pub struct NFA {
    /// Alphabet
    pub ab: Vec<String>,
    /// Set of states (and their index)
    pub n: usize,
    /// Accepting states
    pub accepting: HashSet<usize>,
    /// Regular expressions (for printing)
    pub expressions: HashMap<usize, Regex>,
    /// Transition relation from [state -> char -> state] given an input
    pub trans: HashMap<(usize, String), usize>,
    /// Must match from the begining of the document (default: false)
    pub anchor_start: bool,
    /// Must match until the end of the document (default: false)
    pub anchor_end: bool,
}

// Null transition character
pub const EPSILON: &String = &String::new();

impl NFA {
    pub fn new<'a>(alphabet: &'a str, re: Regex) -> Self {
        let ab = alphabet.chars().sorted().collect();

        let mut trans = HashMap::new();
        let mut states: HashMap<Regex, usize> = HashMap::new();
        // Recursive funtion
        fn build_trans(
            states: &mut HashMap<Regex, usize>,
            trans: &mut HashMap<(usize, String), usize>,
            ab: &Vec<char>,
            q: &Regex,
            n: usize,
        ) {
            // Add to DFA if not already there
            states.insert(q.clone(), n);
            // The reflexive step
            trans.insert((states[q], EPSILON.clone()), states[q]);

            // Explore derivatives
            for c in &ab[..] {
                let q_c = q.deriv(&c);
                // Non-reflexive step
                if states.contains_key(&q_c) {
                    trans.insert((states[q], c.to_string()), states[&q_c]);
                } else {
                    let n_c = states.len();
                    trans.insert((states[q], c.to_string()), n_c);
                    build_trans(states, trans, ab, &q_c, n_c);
                }
            }
        }

        // Recursively build transitions
        build_trans(&mut states, &mut trans, &ab, &re, 0);

        // Return DFA
        Self {
            ab: ab.into_iter().map(|c| c.to_string()).collect(),
            n: states.len(),
            accepting: states
                .clone()
                .into_iter()
                .filter_map(|(k, v)| if k.nullable() { Some(v) } else { None })
                .collect(),
            expressions: states.into_iter().map(|(k, v)| (v, k)).collect(),
            trans,
            anchor_start: re.is_start_anchored(),
            anchor_end: re.is_end_anchored(),
        }
    }

    /// Fails when document not well-formed
    pub fn well_formed(&self, doc: &Vec<String>) -> () {
        for d in doc {
            if !self.ab.contains(d) {
                panic!(
                    "Found {} in the document but not in the alphabet {:?}",
                    d, self.ab
                )
            }
        }
    }

    pub fn ab_to_num(&self, c: &String) -> usize {
        if c == EPSILON {
            self.ab.len() as usize
        } else {
            self.ab.iter().position(|x| x == c).unwrap() as usize
        }
    }

    pub fn nstates(&self) -> usize {
        self.n
    }

    pub fn nchars(&self) -> usize {
        self.ab.len()
    }

    pub fn is_exact_match(&self) -> bool {
        self.anchor_start && self.anchor_end
    }

    /// Initial state
    pub fn get_init_state(&self) -> usize {
        0
    }

    /// All states
    pub fn get_states(&self) -> HashSet<usize> {
        (0..self.n).collect()
    }

    /// Final states
    pub fn get_final_states(&self) -> HashSet<usize> {
        self.accepting.clone()
    }

    /// Non final states
    pub fn get_non_final_states(&self) -> HashSet<usize> {
        self.get_states()
            .difference(&self.accepting)
            .map(|c| c.clone())
            .collect()
    }

    pub fn delta(&self, state: usize, c: &String) -> Option<usize> {
        let res = self.trans.get(&(state, c.clone())).map(|c| c.clone());

        // println!("{} --[ {} ]--> {}", state, c, res.map(|c|c.to_string()).unwrap_or(String::from("NONE")));
        res
    }

    /// Transition relation as a vector
    pub fn deltas(&self) -> Vec<(usize, String, usize)> {
        self.trans
            .clone()
            .into_iter()
            .map(|((a, b), c)| (a, b, c))
            .collect()
    }

    /// Returns (begin match index, end index) if a match is found in the doc
    pub fn is_match(&self, doc: &Vec<String>) -> Option<(usize, usize)> {
        let mut start_idxs = Vec::new();
        let accepting = &self.get_final_states();

        // Iterate over all postfixes of doc
        if self.anchor_start {
            start_idxs.push(0);
        } else {
            for i in 0..doc.len() {
                start_idxs.push(i)
            }
        }

        // Initial state is also accepting
        if accepting.contains(&self.get_init_state()) && (!self.anchor_end || doc.len() == 0) {
            return Some((0, 0));
        }
        // For every postfix of doc (O(n^2))
        start_idxs.into_iter().find_map(|i| {
            // .into_par_iter()
            // .find_map_any(|i| {
            let mut s = self.get_init_state();
            for j in i..doc.len() {
                // Apply transition relation
                s = self.delta(s, &doc[j]).unwrap();

                // found a substring match or exact match
                if accepting.contains(&s) && (!self.anchor_end || j == doc.len() - 1) {
                    return Some((i, j + 1)); // Return an interval [i, j)
                }
            }
            None
        })
    }

    /// Get the 2^k stride DFA
    pub fn k_stride(&mut self, k: usize, doc: &Vec<String>) -> Vec<String> {
        let mut d = doc.clone();
        for _ in 0..k {
            d = self.double_stride(&d);
        }
        d
    }

    /// Double the stride of the DFA
    pub fn double_stride(&mut self, doc: &Vec<String>) -> Vec<String> {
        let mut ab: HashSet<(String, String)> = HashSet::new();
        let mut classes: HashMap<BTreeSet<(usize, usize)>, BTreeSet<String>> = HashMap::new();
        // S' := S + S*S (cartesian product)
        for c0 in self.ab.iter() {
            ab.insert((c0.clone(), EPSILON.clone()));
            for c1 in self.ab.clone() {
                ab.insert((c0.clone(), c1));
            }
        }

        // Result transition will be t1 -[a+b]-> t3
        for (a, b) in ab {
            // All the pairs (t1, t3) such that t1 -[a+b]-> t3
            let mut trans_clos: BTreeSet<(usize, usize)> = BTreeSet::new();
            for t1 in self.get_states() {
                let t2 = self.delta(t1, &a).unwrap();
                // Epsilon does not transition
                let t3 = self.delta(t2, &b).unwrap();
                // Transitively close over all states
                trans_clos.insert((t1, t3));
            }

            let s = a + &b;

            // Equivalence classes have the same transitive closure
            match classes.get_mut(&trans_clos) {
                Some(class) => {
                    class.insert(s.clone());
                }
                None => {
                    classes.insert(trans_clos, BTreeSet::from([s.clone()]));
                }
            }
        }

        // Find a representative string from an eqivalence class
        fn find_representative(class: &BTreeSet<String>) -> String {
            let size = class
                .iter()
                .max_by(|a, b| a.len().cmp(&b.len()))
                .unwrap()
                .len();
            class
                .iter()
                .find(|c| c.len() >= size)
                .map(|c| c.clone())
                .expect("No equivalence classes found")
        }

        // Find a equivalent string from an eqivalence class
        fn find_equivalent(c: String, classes: &Vec<BTreeSet<String>>) -> String {
            let mut rep = None;
            for class in classes {
                if class.contains(&c) {
                    rep = Some(find_representative(class))
                }
            }
            rep.expect("No equivalence classes found")
        }

        // Translate doc into equivalent doc
        let equiv_classes = classes.clone().into_values().collect();

        // Clear the old alphabet
        let mut abset = HashSet::new();

        // Build transition relation from classes
        self.trans = self
            .trans
            .clone()
            .into_iter()
            .filter(|((t, c), u)| if t == u && c == EPSILON { true } else { false })
            .collect();

        for (set, class) in classes {
            for (t, u) in set {
                self.trans.insert((t, find_representative(&class)), u);
                abset.insert(find_representative(&class));
            }
        }
        self.ab = abset.into_iter().collect();

        // Return new document (modulo equiv classes)
        doc.chunks(2)
            .filter_map(|c| match c {
                [a, b] => Some(find_equivalent(a.clone() + b, &equiv_classes)),
                [a] => Some(find_equivalent(a.clone() + &EPSILON, &equiv_classes)),
                _ => None,
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use crate::dfa::NFA;
    use crate::regex::Regex;

    fn setup_nfa(r: &str, alpha: &str) -> NFA {
        let ab = String::from(alpha);
        let regex = Regex::new(r);
        let nfa = NFA::new(&ab[..], regex);
        nfa
    }

    fn vs(s: &str) -> Vec<String> {
        s.chars().map(|c| c.to_string()).collect()
    }

    fn check(nfa: &NFA, doc: &Vec<String>, res: Option<(usize, usize)>) {
        assert_eq!(nfa.is_match(doc), res)
    }

    #[test]
    fn test_nfa_delta_circuit_basic() {
        check(&setup_nfa("a", "ab"), &vs("a"), Some((0, 1)))
    }

    #[test]
    fn test_nfa_delta_non_circuit_basic_nonmatch() {
        check(&setup_nfa("a", "ab"), &vs("b"), None)
    }

    #[test]
    fn test_nfa_delta_circuit() {
        check(&setup_nfa("aba", "ab"), &vs("aba"), Some((0, 3)))
    }

    #[test]
    fn test_nfa_delta_non_circuit_nonmatch() {
        check(&setup_nfa("aba", "ab"), &vs("ab"), None)
    }

    #[test]
    fn test_nfa_delta_circuit_star() {
        check(&setup_nfa("a.*a", "ab"), &vs("abba"), Some((0, 4)))
    }

    #[test]
    fn test_nfa_delta_empty_match() {
        check(&setup_nfa(".*", "ab"), &vs(""), Some((0, 0)))
    }

    #[test]
    fn test_nfa_delta_circuit_star_anchor() {
        check(&setup_nfa("^a.*a$", "ab"), &vs("abba"), Some((0, 4)))
    }

    #[test]
    fn test_nfa_delta_non_circuit_star_anchor() {
        check(&setup_nfa("^a.*a$", "ab"), &vs("abbab"), None)
    }

    #[test]
    fn test_nfa_delta_non_circuit_stat_nonmatch() {
        check(&setup_nfa("a.*a", "ab"), &vs("abb"), None)
    }

    #[test]
    fn test_nfa_delta_middle_match() {
        check(
            &setup_nfa("abba", "ab"),
            &vs("aaaaaaaaaabbaaaaaaa"),
            Some((9, 13)),
        )
    }

    #[test]
    fn test_nfa_double_stride() {
        let mut nfa = setup_nfa("a.*a", "ab");
        let doc = nfa.double_stride(&vs("abbbba"));
        check(&nfa, &doc, Some((0, 3)))
    }

    #[test]
    fn test_nfa_double_stride_2() {
        let mut nfa = setup_nfa("^.*a$", "ab");
        let doc = nfa.double_stride(&vs("aabbaaa"));
        check(&nfa, &doc, Some((0, 4)))
    }
}

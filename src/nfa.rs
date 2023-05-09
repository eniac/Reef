use itertools::Itertools;
use std::collections::HashMap;
use std::collections::{BTreeSet, HashSet};
use std::process::Command;

use petgraph::{Direction, Graph};
use petgraph::graph::NodeIndex;
use petgraph::visit::*;
use petgraph::dot::Dot;
use petgraph::algo;

use crate::regex::Regex;

#[derive(Debug, Clone)]
pub struct NFA {
    /// Alphabet
    pub ab: Vec<String>,
    /// Accepting states
    accepting: HashSet<usize>,
    /// Transition relation from [state -> char -> state] given an input
    g: Graph<Regex, String>,
    /// Must match from the begining of the document (default: false)
    anchor_start: bool,
    /// Must match until the end of the document (default: false)
    anchor_end: bool,
}

// Null transition character
pub const EPSILON: &String = &String::new();


impl PartialEq for NFA {
    fn eq(&self, other: &Self) -> bool {
        self.ab == other.ab &&
            self.g[self.get_init_nodeidx()] == other.g[other.get_init_nodeidx()]
    }
}

impl NFA {
    pub fn new<'a>(alphabet: &'a str, re: Regex) -> Self {
        let ab = alphabet.chars().sorted().collect();
        let mut graph: Graph<Regex, String> = Graph::new();

        // Recursive funtion
        fn build_trans(
            g: &mut Graph<Regex, String>,
            ab: &Vec<char>,
            q: &Regex,
            n: NodeIndex<u32>) {

            println!("Adding trans {}, {}", q, n.index());
            // Explore derivatives
            for c in &ab[..] {
                let q_c = q.deriv(&c);

                if let Some(n_c) = g.node_indices().find(|i| g[*i] == q_c) {
                    g.add_edge(n, n_c, c.to_string());
                } else {
                    // Add to DFA if not already there
                    let n_c = g.add_node(q_c.clone());
                    // Reflexive step
                    g.add_edge(n_c, n_c, EPSILON.clone());
                    g.add_edge(n, n_c, c.to_string());
                    build_trans(g, ab, &q_c, n_c);
                }
            }
        }

        let n = graph.add_node(re.clone());
        graph.add_edge(n, n, EPSILON.clone());
        // Recursively build transitions
        build_trans(&mut graph, &ab, &re, n);

        // Return DFA
        Self {
            ab: ab.into_iter().map(|c| c.to_string()).collect(),
            accepting: graph.node_indices()
                .filter(|&k| graph[k].nullable())
                .map(|i| i.index())
                .collect(),
            g: graph,
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
        self.g.node_count()
    }

    pub fn nchars(&self) -> usize {
        self.ab.len()
    }

    pub fn nedges(&self) -> usize {
        self.g.edge_count()
    }

    pub fn is_exact_match(&self) -> bool {
        self.anchor_start && self.anchor_end
    }

    /// Initial state
    pub fn get_init_state(&self) -> usize {
        0
    }

    pub fn get_init_nodeidx(&self) -> NodeIndex<u32> {
        NodeIndex::new(0)
    }

    /// All states
    pub fn get_states(&self) -> HashSet<usize> {
        self.g.node_indices().map(|i|i.index()).collect()
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

    /// Single step transition
    pub fn delta(&self, state: usize, c: &String) -> Option<usize> {
        let res = self.g.edges_directed(NodeIndex::new(state), Direction::Outgoing)
                        .find(|e| e.weight() == c)
                        .map(|e| e.target().index());

        println!("{} --[ {} ]--> {}", state, c, res.map(|c|c.to_string()).unwrap_or(String::from("NONE")));
        res
    }

    /// Transition relation as a vector
    pub fn deltas(&self) -> HashSet<(usize, String, usize)> {
        self.g.node_indices()
            .flat_map(|i| self.g.edges(i))
            .map(|e| (e.source().index(), e.weight().clone(), e.target().index()))
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
        start_idxs.into_par_iter().find_map_any(|i| {
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

    /// Compute the strongly connected components of the DFA
    pub fn scc_loops(&self) -> Vec<Self> {
        algo::tarjan_scc(&self.g)
            .into_iter()
            .map(|v| NFA::new(&self.ab.join(""),
                self.g[*v.iter().min_by_key(|i| i.index()).unwrap()].clone()))
            .filter(|v| v.has_accepting_cycle() && v != self)
            .collect()
    }

    /// Is the DFA a sink (has no accepting states)
    pub fn is_sink(&self) -> bool {
        self.accepting.is_empty()
    }

    pub fn find_node(&self, r: &Regex) -> Option<NodeIndex<u32>> {
        self.g.node_indices().find(|i| &self.g[*i] == r)
    }

    pub fn to_regex(&self) -> Regex {
        self.g[self.get_init_nodeidx()].clone()
    }

    /// Does this DFA has an infintely accepting cycle - or - does this DFA accept arbitrary length prefixes
    pub fn has_accepting_cycle(&self) -> bool {
        fn is_cycle(p: &Vec<NodeIndex<u32>>) -> bool {
            let s: HashSet<&NodeIndex<u32>> = p.into_iter().collect();
            println!("SET {:?} and VEC {:?}", s, p);
            s.len() != p.len()
        }
        fn has_accepting(g: &Graph<Regex, String>, p: &Vec<NodeIndex<u32>>) -> bool {
            p.into_iter().any(|i| g[*i].nullable())
        }

        // algo::is_cyclic_directed(&self.g)
        let mut dfs = Dfs::new(&self.g, self.get_init_nodeidx());
        while let Some(node) = dfs.next(&self.g) {
            println!("Visiting node {}", self.g[node]);
            if algo::all_simple_paths::<Vec<_>, _>(&self.g, node, node, 1, None)
                .any(|p| is_cycle(&p) && has_accepting(&self.g, &p)) {
                return true;
            }
        }
        return false;
    }

    /// Remove all outgoing edges and visited nodes out of [i]
    pub fn remove_outgoing_edges(&mut self, i: NodeIndex<u32>) {
        let mut dfs = Dfs::new(&self.g, i);
        let mut nodes = HashSet::new();
        while let Some(node) = dfs.next(&self.g) {
            // use a detached neighbors walker
            let mut edges = self.g.neighbors_directed(node, Direction::Outgoing).detach();
            while let Some(edge) = edges.next_edge(&self.g) {
                if let Some((_, dst)) = self.g.edge_endpoints(edge) {
                    if dst != i {
                        nodes.insert(dst);
                    }
                }
                self.g.remove_edge(edge);
            }
        }
        for n in nodes {
            self.g.remove_node(n);
        }
    }

    /// Substitute any sub-DFA with another DFA while maintaining transitions
    pub fn to_epsilon(&mut self, i: NodeIndex<u32>) -> bool {
        // Remove children
        self.remove_outgoing_edges(i);

        // Update node to epsilon
        self.g.add_edge(i, i, EPSILON.clone());
        if let Some(xr) = self.g.node_weight_mut(i) {
            *xr = Regex::nil();
            true
        } else {
            false
        }
    }

    /// Split NFA in .*
    pub fn split_dot_star(&mut self) -> std::io::Result<()> {

        self.write_pdf("original")?;
        let sccs = self.scc_loops();

        let mut files: Vec<String> = Vec::from(["original.pdf".to_string(), "reduced.pdf".to_string()]);

        for i in 0..sccs.len() {
            let fout = format!("scc-{}", i);
            let xi = self.find_node(&sccs[i].to_regex()).unwrap();
            self.to_epsilon(xi);
            sccs[i].write_pdf(fout.as_str())?;
            files.push(format!("{}.pdf", fout));
        }

        self.write_pdf("reduced")?;
        Command::new("pdfjam")
            .args(files.clone())
            .arg("-o")
            .arg("scc.pdf")
            .spawn()
            .expect("[dot] CLI failed to convert dfa to [pdf] file")
            .wait()?;

        for fout in files.clone() {
            std::fs::remove_file(fout)?;
        }

        Ok(())
    }

    /// Dot file
    pub fn write_dot(&self, filename: &str) -> std::io::Result<()> {
        let s: String = Dot::new(&self.g).to_string();
        let fout = filename.to_string() + ".dot";
        println!("Wrote DOT file {}.", fout);
        std::fs::write(fout, s)
    }

    /// PDF file
    pub fn write_pdf(&self, filename: &str) -> std::io::Result<()> {
        self.write_dot(filename)?;

        // Convert to pdf
        Command::new("dot")
            .arg("-Tpdf")
            .arg(filename.to_string() + ".dot")
            .arg("-o")
            .arg(filename.to_string() + ".pdf")
            .spawn()
            .expect("[dot] CLI failed to convert dfa to [pdf] file")
            .wait()?;

        Ok(())
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
    fn double_stride(&mut self, doc: &Vec<String>) -> Vec<String> {
        assert!(self.anchor_start && self.anchor_end, "k-stride only works for exact match");
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

        // ((a | b) .* c) | d) =
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
        self.g.clear_edges();

        for (set, class) in classes {
            for (t, u) in set {
                self.g.add_edge(NodeIndex::new(t), NodeIndex::new(u), find_representative(&class));
                abset.insert(find_representative(&class));
            }
        }
        self.ab = abset.into_iter().collect();

        // Add reflexive steps again
        for i in self.g.node_indices() {
            self.g.add_edge(i, i, EPSILON.clone());
        }

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
    use crate::nfa::NFA;
    use crate::regex::Regex;

    fn setup_nfa(r: &str, alpha: &str) -> NFA {
        let ab = String::from(alpha);
        let regex = Regex::new(r);
        NFA::new(&ab[..], regex)
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
        let doc = nfa.k_stride(1, &vs("abbbba"));
        check(&nfa, &doc, Some((0, 3)))
    }

    #[test]
    fn test_nfa_double_stride_2() {
        let mut nfa = setup_nfa("^.*a$", "ab");
        let doc = nfa.k_stride(1, &vs("aabbaaa"));
        check(&nfa, &doc, Some((0, 4)))
    }

    #[test]
    fn test_nfa_split() {
        let mut nfa = setup_nfa("((c.*b) | (a.*b))*b", "abc");
        nfa.split_dot_star().unwrap();
    }
}

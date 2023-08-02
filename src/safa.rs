use itertools::Itertools;
use std::collections::{BTreeSet, LinkedList};
use std::process::Command;

use petgraph::dot::Dot;
use petgraph::graph::{EdgeReference, NodeIndex};
use petgraph::visit::*;
use petgraph::Graph;

use std::result::Result;

use crate::openset::OpenSet;
use crate::quantifier::Quant;
use crate::regex::{re, Regex, RegexF};
use crate::trace::{Trace, TraceElem};
use rayon::iter::*;

use core::fmt;
use core::fmt::{Display, Formatter};
use std::fmt::Debug;
use std::hash::Hash;

#[derive(Debug, Clone, Hash, PartialOrd, Ord, PartialEq, Eq)]
pub struct Either<A, B>(pub Result<A, B>);

impl<A, B> Either<A, B> {
    fn left(a: A) -> Self {
        Self(Ok(a))
    }
    fn right(b: B) -> Self {
        Self(Err(b))
    }
    fn test_left<F>(&self, f: F) -> bool
    where
        F: Fn(&A) -> bool,
    {
        match self.0 {
            Ok(ref a) => f(a),
            _ => false,
        }
    }
    fn test_right<F>(&self, f: F) -> bool
    where
        F: Fn(&B) -> bool,
    {
        match self.0 {
            Err(ref b) => f(b),
            _ => false,
        }
    }
}

impl<A: Display, B: Display> Display for Either<A, B> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            Ok(ref a) => write!(f, "{}", a),
            Err(ref b) => write!(f, "{}", b),
        }
    }
}

/// A skip is a set of ranges
pub type Skip = OpenSet<usize>;

#[derive(Debug, Clone)]
pub struct SAFA<C: Clone> {
    /// Alphabet
    pub ab: Vec<C>,

    /// A graph
    pub g: Graph<Quant<Regex>, Either<C, Skip>>,

    /// Is a positive or negative SAFA (inverse match)
    pub positive: bool
}

impl PartialEq for SAFA<char> {
    fn eq(&self, other: &Self) -> bool {
        self.ab == other.ab &&
        self.positive == other.positive &&
        self.deltas() == other.deltas()
    }
}

impl Eq for SAFA<char> {}

impl SAFA<char> {
    /// Deep Constructor
    pub fn new<'a>(alphabet: &'a str, re: &Regex) -> Self {
        let ab = alphabet.chars().sorted().collect();
        // Add root
        let mut g: Graph<Quant<Regex>, Either<char, Skip>> = Graph::new();
        let n_init = g.add_node(Quant::or(re.clone()));
        g.add_edge(n_init, n_init, SAFA::epsilon());
        let mut s = Self {
            ab,
            g,
            positive: true
        };
        // Recursively build graph
        s.add(n_init);
        s
    }

    /// Add a regex to position [from]
    fn add_skip(&mut self, n: NodeIndex<u32>, skip: Skip, q_c: &Regex) {
        let recurse = !self.exists(q_c, false);
        let n_c = self.find_or_add(q_c, false);
        self.g.add_edge(n, n_c, Either::right(skip.clone()));
        // Also add the complement skip since we know it always fails
        if !skip.is_full() && !skip.is_nil() {
            let n_empty = self.find_or_add(&re::empty(), false);
            self.g.add_edge(n, n_empty, Either::right(skip.negate().diff(&OpenSet::nil())));
        }
        if recurse {
            self.add(n_c);
        }
    }

    /// Find if a regex exists in the nodes of the graph
    pub fn exists(&self, r: &Regex, is_and: bool) -> bool {
        self.g.node_indices().any(|i| &self.g[i].get() == r && self.g[i].is_and() == is_and)
    }

    /// Find a node from a regex
    pub fn find(&self, r: &Regex) -> Option<NodeIndex<u32>> {
        self.g.node_indices()
              .find(|i| &self.g[*i].get() == r)
    }

    /// Find a node from a regex, or add it and return a new node id
    pub fn find_or_add(&mut self, r: &Regex, is_and: bool) -> NodeIndex<u32> {
        self.g.node_indices()
              .find(|i| self.g[*i] == Quant::new(r.clone(), is_and))
              .unwrap_or_else(|| {
                let n_q = self.g.add_node(Quant::new(r.clone(), is_and));
                // Reflexive step
                self.g.add_edge(n_q, n_q, SAFA::epsilon());
                n_q
              })
    }

    /// Add derivative of a node in the graph
    fn add_derivatives(&mut self, from: NodeIndex<u32>) {
        // Take all the single character steps
        for c in self.ab.clone().iter() {
            let q_c = re::deriv(&self.g[from].get(), &c);
            let recurse = !self.exists(&q_c, false);
            let n_c = self.find_or_add(&q_c, false);
            self.g.add_edge(from, n_c, Either::left(*c));
            if recurse {
                self.add(n_c);
            }
        }
    }

    /// Insert an [and] or [alt] fork in the safa
    fn add_fork(&mut self, is_and: bool, from: NodeIndex<u32>) -> Option<()> {
        fn to_set(r: &Regex, is_and: bool) -> BTreeSet<Regex> {
            match **r {
                // (r | r' | ...) => [r, r', ...]
                RegexF::And(ref a, ref b) if is_and => {
                    let mut l = to_set(a, is_and);
                    let mut r = to_set(b, is_and);
                    l.append(&mut r);
                    l
                },
                RegexF::Alt(ref a, ref b) if !is_and => {
                    let mut l = to_set(a, is_and);
                    let mut r = to_set(b, is_and);
                    l.append(&mut r);
                    l
                },
                RegexF::Star(ref a) if !is_and =>
                    BTreeSet::from([re::nil(), re::app(a.clone(), re::star(a.clone()))]),
                _ => BTreeSet::from([r.clone()]),
            }
        }

        let children = to_set(&self.g[from].get(), is_and);
        if children.len() > 1 {
            self.g[from] = Quant::new(self.g[from].get(), is_and);
            children
                .into_iter()
                .for_each(|q_c| self.add_skip(from, Skip::nil(), &q_c));
            Some(())
        } else {
            None
        }
    }

    /// Add a new regex starting at [from]
    fn add(&mut self, from: NodeIndex<u32>) {
        re::extract_skip(&self.g[from].get())
            .map(|(skip, rem)| self.add_skip(from, skip, &rem))
            .or_else(|| self.add_fork(true, from)) // Add [and] fork
            .or_else(|| self.add_fork(false, from)) // Add [or] fork
            .or_else(|| Some(self.add_derivatives(from))); // Catch-all
    }

    /// Is this node a fork ([alt, and] with epsilon children)
    pub fn is_fork(&self, from: NodeIndex<u32>) -> bool {
        self.edges(from).iter().all(|e| e.weight() == &SAFA::epsilon())
    }

    /// Number of states
    pub fn nstates(&self) -> usize {
        self.g.node_indices().len()
    }

    /// Negation of SAFAs
    pub fn negate(&self) -> Self {
        // Clone graph (immutable negate)
        let mut safa = self.clone();

        // Negate sign (for accepting)
        safa.positive = !safa.positive;

        safa.g = safa.g.map(
            |i, b| if safa.is_fork(i) { b.negate() } else { b.clone() },
            |_, e| e.clone());
        safa
    }

    /// To regular expression (root = s.g[nx] iode)
    pub fn to_regex(&self) -> Regex {
        self.g[self.get_init()].get()
    }

    /// An epsilon transition
    fn epsilon() -> Either<char, Skip> {
        Either::right(Skip::nil())
    }

    /// Get initial state
    pub fn get_init(&self) -> NodeIndex<u32> {
        NodeIndex::new(0)
    }

    /// All edges (quantified) in the graph
    pub fn deltas(&self) -> BTreeSet<(Quant<NodeIndex<u32>>, Either<char, Skip>, NodeIndex<u32>)> {
        self.g
            .node_indices()
            .flat_map(|n| {
                self.g.edges(n).filter_map(|e| {
                    // Filter out sink state transitions
                    if self.is_sink(e.source()) || self.is_sink(e.target()) {
                        None
                    } else if self.g[e.source()].is_and() {
                        Some((Quant::and(e.source()), e.weight().clone(), e.target()))
                    } else {
                        Some((Quant::or(e.source()), e.weight().clone(), e.target()))
                    }
                })
            })
            .collect()
    }

    /// A sink is a self-looping node that is not accepting
    pub fn is_sink(&self, n: NodeIndex<u32>) -> bool {
        self.g
            .edges(n)
            .all(|e| e.target() == n && self.non_accepting().contains(&n))
    }

    /// Accepting criterion for a node, document and cursor
    pub fn is_accept(&self, n: NodeIndex<u32>, i: usize, doc: &Vec<char>) -> bool {
        self.accepting().contains(&n) && i == doc.len()
    }

    /// Non accepting states
    pub fn non_accepting(&self) -> BTreeSet<NodeIndex<u32>> {
        self.g.node_indices()
            .filter(|i| !self.accepting().contains(i))
            .collect()
    }

    /// Accepting states
    pub fn accepting(&self) -> BTreeSet<NodeIndex<u32>> {
        if self.positive {
            self.g.node_indices()
                .filter(|i| self.g[*i].get().nullable())
                .collect()
        } else {
            self.g.node_indices()
                .filter(|i| !self.g[*i].get().nullable())
                .collect()
        }
    }

    /// Recursively solve an edge and all the children coming off of it
    fn solve_edge(
        &self,
        e: &Either<char, Skip>,
        from: NodeIndex<u32>,
        to: NodeIndex<u32>,
        i: usize,
        doc: &Vec<char>,
    ) -> Option<Trace<char>> {
        match e.0.clone() {
            // Sink state, cannot succeed
            Ok(_) if self.is_sink(to) => None,
            // Character match
            Ok(c) if c == doc[i] => Trace::prepend(
                self.solve_rec(to, i + 1, doc),
                TraceElem::new(from.index(), e, to.index(), i, i + 1),
            ),
            // Character non-match
            Ok(_) => None,
            Err(skip) => skip
                .clone()
                .into_iter()
                .take_while(|n| i + n <= doc.len())
                .find_map(|n| {
                    Trace::prepend(
                        self.solve_rec(to, i + n, doc),
                        TraceElem::new(from.index(), e, to.index(), i, i + n),
                    )
                }),
        }
    }

    /// Neighbors of [n]
    pub fn edges(&self, n: NodeIndex<u32>) -> Vec<EdgeReference<'_, Either<char, Skip>>> {
        self.g
            .edges(n)
            .filter(|e| e.source() != e.target() || !e.weight().test_right(|c| c.is_nil()))
            .collect()
    }

    /// Find a non-empty list of continuous matching document strings
    fn solve_rec(&self, n: NodeIndex<u32>, i: usize, doc: &Vec<char>) -> Option<Trace<char>> {
        // Check accepting condition
        if self.is_accept(n, i, doc) {
            return Some(Trace::empty());
        } else if i >= doc.len() {
            return None;
        }
        if self.g[n].is_and() {
            // All of the next entries must have solutions
            let subsolutions: Vec<_> =
                self.edges(n)
                    .into_iter()
                    .map(|e| self.solve_edge(e.weight(), e.source(), e.target(), i, doc))
                    .collect();
            // All of them need to be set
            if subsolutions.iter().all(Option::is_some) {
                Some(Trace(
                    subsolutions
                        .into_iter()
                        .flat_map(|c| c.unwrap().0)
                        .collect(),
                ))
            } else {
                None
            }
        } else {
            // One of the next entries must has a solution
            self.edges(n).into_par_iter()
                .find_map_any(|e| self.solve_edge(e.weight(), e.source(), e.target(), i, doc))
        }
    }

    /// Solve at the root
    pub fn solve(&self, doc: &Vec<char>) -> Option<Trace<char>> {
        self.solve_rec(self.get_init(), 0, doc)
    }

    /// Produce a graph of the SAFA in a PDF file with [filename]
    pub fn write_pdf(&self, filename: &str) -> std::io::Result<()> {
        // Graph [g]
        let strg = self.g.map(
            |_, b|
                if self.positive {
                    if b.get().nullable() {
                        format!("{} ✓", b)
                    } else { b.to_string() }
                } else {
                    if b.get().nullable() {
                        format!("{} ✗", b)
                    } else { format!("{} ¬", b) }
                },
            |_, e| Either(e.clone().0.map(|c| c.to_string())),
        );

        let s: String = Dot::new(&strg).to_string();
        let fdot = format!("{}.dot", filename.to_string());
        std::fs::write(fdot.clone(), s)?;

        let fpdf = format!("{}.pdf", filename.to_string());

        // Convert to pdf
        Command::new("dot")
            .arg("-Tpdf")
            .arg(fdot.clone())
            .arg("-o")
            .arg(fpdf.clone())
            .spawn()
            .expect("[dot] CLI failed to convert dfa to [pdf] file")
            .wait()?;

        // Remove DOT file
        std::fs::remove_file(fdot)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::regex::re;
    use crate::safa::Skip;
    use crate::safa::{Either, Trace, TraceElem, SAFA};
    use std::collections::HashSet;
    use std::collections::LinkedList;
    use std::fmt::Display;

    /// Helper function to output states
    fn print_states<C: Display + Clone + Eq>(safa: &SAFA<C>) {
        safa.g
            .node_indices()
            .for_each(|i| println!("({}) -> {}", i.index(), safa.g[i]))
    }

    /// Equivalent solutions up to epsilon steps
    fn equiv_upto_epsilon(test: &Option<Trace<char>>, control: &Trace<char>) {
        if let Some(t) = test {
            let mut ia = t.0.iter();
            let mut ib = control.0.iter();
            let mut res = LinkedList::new();
            while let Some(x) = ia.next() {
                if !x.is_nil() {
                    while let Some(y) = ib.next() {
                        if !y.is_nil() {
                            if x == y {
                                res.push_back(x.clone());
                                break;
                            } else {
                                assert!(
                                    false,
                                    "\nTraceAssert: Assertion failed,
                                        \nMatch {} = \n\ntest : {}\ncontrol := {}\n",
                                    Trace(res),
                                    t,
                                    control
                                );
                            }
                        }
                    }
                }
            }
        } else {
            assert!(
                false,
                "\nTraceAssert: Assertion failed,
                                \n test: NONE\ncontrol: {}\n",
                control
            );
        }
    }

    #[test]
    fn test_safa_match_exact() {
        let r = re::simpl(re::new("^baa$"));
        let safa = SAFA::new("ab", &r);
        let strdoc = "baa";
        let doc = strdoc.chars().collect();

        equiv_upto_epsilon(
            &safa.solve(&doc),
            &Trace::new(&[
                TraceElem::new(0, &Either(Ok('b')), 2, 0, 1),
                TraceElem::new(2, &Either(Ok('a')), 3, 1, 2),
                TraceElem::new(3, &Either(Ok('a')), 4, 2, 3),
            ]),
        );
    }

    #[test]
    fn test_safa_match_partial() {
        let r = re::simpl(re::new("baa"));
        let safa = SAFA::new("ab", &r);
        let strdoc = "ababbbaa";
        let doc: Vec<_> = strdoc.chars().collect();
        equiv_upto_epsilon(
            &safa.solve(&doc),
            &Trace::new(&[
                TraceElem::new(0, &Either(Err(Skip::star())), 1, 0, 5),
                TraceElem::new(1, &Either(Ok('b')), 3, 5, 6),
                TraceElem::new(3, &Either(Ok('a')), 4, 6, 7),
                TraceElem::new(4, &Either(Ok('a')), 5, 7, 8),
            ]),
        );
    }

    #[test]
    fn test_safa_match_star() {
        let r = re::simpl(re::new("^a*$"));
        let safa = SAFA::new("ab", &r);
        let strdoc = "aa";
        let doc: Vec<_> = strdoc.chars().collect();
        equiv_upto_epsilon(
            &safa.solve(&doc),
            &Trace::new(&[
                TraceElem::new(0, &Either::left('a'), 0, 0, 1),
                TraceElem::new(0, &Either::left('a'), 0, 1, 2),
            ]),
        )
    }

    #[test]
    fn test_safa_alt_pure() {
        let r = re::simpl(re::new("baa(a|c)$"));
        let safa = SAFA::new("abc", &r);
        let strdoc = "abababaac";
        let doc: Vec<_> = strdoc.chars().collect();
        equiv_upto_epsilon(
            &safa.solve(&doc),
            &Trace::new(&[
                TraceElem::new(0, &Either(Err(Skip::star())), 1, 0, 5),
                TraceElem::new(1, &Either(Ok('b')), 3, 5, 6),
                TraceElem::new(3, &Either(Ok('a')), 4, 6, 7),
                TraceElem::new(4, &Either(Ok('a')), 5, 7, 8),
                TraceElem::new(5, &Either(Ok('c')), 6, 8, 9),
            ]),
        )
    }

    #[test]
    fn test_safa_alt_merge() {
        let r = re::simpl(re::new("^.*baa(a|b)$"));
        let safa = SAFA::new("ab", &r);
        let strdoc = "abababaab";
        let doc: Vec<_> = strdoc.chars().collect();
        equiv_upto_epsilon(
            &safa.solve(&doc),
            &Trace::new(&[
                TraceElem::new(0, &Either(Err(Skip::star())), 1, 0, 5),
                TraceElem::new(1, &Either(Ok('b')), 3, 5, 6),
                TraceElem::new(3, &Either(Ok('a')), 4, 6, 7),
                TraceElem::new(4, &Either(Ok('a')), 5, 7, 8),
                TraceElem::new(5, &Either(Ok('b')), 6, 8, 9),
            ]),
        )
    }

    #[test]
    fn test_safa_range_exact() {
        let r = re::simpl(re::new("^.{3}b$"));
        let safa = SAFA::new("ab", &r);
        let doc: Vec<_> = "aaab".chars().collect();
        equiv_upto_epsilon(
            &safa.solve(&doc),
            &Trace::new(&[
                TraceElem::new(0, &Either(Err(Skip::single(3))), 1, 0, 3),
                TraceElem::new(1, &Either(Ok('b')), 3, 3, 4),
            ]),
        )
    }

    #[test]
    fn test_safa_range_interval() {
        let r = re::simpl(re::new("^.{1,3}b$"));
        let safa = SAFA::new("ab", &r);
        let doc: Vec<_> = "aaab".chars().collect();
        equiv_upto_epsilon(
            &safa.solve(&doc),
            &Trace::new(&[
                TraceElem::new(0, &Either(Err(Skip::closed(1, 3))), 1, 0, 3),
                TraceElem::new(1, &Either(Ok('b')), 3, 3, 4),
            ]),
        )
    }

    #[test]
    fn test_safa_range_starplus() {
        let r = re::simpl(re::new("^.{2,}b$"));
        let safa = SAFA::new("ab", &r);
        let doc: Vec<_> = "aaab".chars().collect();
        equiv_upto_epsilon(
            &safa.solve(&doc),
            &Trace::new(&[
                TraceElem::new(0, &Either(Err(Skip::open(2))), 1, 0, 3),
                TraceElem::new(1, &Either(Ok('b')), 3, 3, 4),
            ]),
        )
    }

    #[test]
    fn test_safa_range_nested() {
        // unsafe { backtrace_on_stack_overflow::enable() };
        let r = re::simpl(re::new("^(.{1,3}){1,2}b$"));
        let safa = SAFA::new("ab", &r);
        let doc: Vec<_> = "aaaab".chars().collect();
        equiv_upto_epsilon(
            &safa.solve(&doc),
            &Trace::new(&[
                TraceElem::new(
                    0,
                    &Either(Err(Skip::closed(1, 6))),
                    1,
                    0,
                    4,
                ),
                TraceElem::new(1, &Either(Ok('b')), 3, 4, 5),
            ]),
        )
    }

    #[test]
    fn test_safa_range_alt() {
        let r = re::simpl(re::new("^((.{1,2}.)|(.{4,5}b))$"));
        let safa = SAFA::new("ab", &r);
        let doc: Vec<_> = "aaaab".chars().collect();
        equiv_upto_epsilon(
            &safa.solve(&doc),
            &Trace::new(&[
                TraceElem::new(
                    4,
                    &Either(Err(Skip::closed(4, 5))),
                    5,
                    0,
                    4,
                ),
                TraceElem::new(5, &Either(Ok('b')), 2, 4, 5),
            ]),
        )
    }

    #[test]
    fn test_safa_lookahead_weird() {
        let r = re::simpl(re::new(r"^(?=a).*b$"));
        let safa = SAFA::new("ab", &r);
        let doc: Vec<_> = "ab".chars().collect();
        equiv_upto_epsilon(
            &safa.solve(&doc),
            &Trace::new(&[
                TraceElem::new(0, &SAFA::epsilon(), 5, 0, 0),
                TraceElem::new(5, &Either(Err(Skip::open(0))), 6, 0, 1),
                TraceElem::new(6, &Either(Ok('b')), 3, 1, 2),
                TraceElem::new(0, &SAFA::epsilon(), 1, 0, 0),
                TraceElem::new(1, &Either(Ok('a')), 2, 0, 1),
                TraceElem::new(2, &Either(Err(Skip::open(0))), 3, 1, 2)
            ]),
        )
    }

    #[test]
    fn test_safa_validate() {
        let abvec: Vec<char> = (0..128).filter_map(std::char::from_u32).collect();
        let ab: String = abvec.iter().collect();
        let r = re::new(r"\.");
        println!("{:#?}", r);
    }

    #[test]
    fn test_safa_basic_lookahead() {
        for s in vec![r"(?=a.*).*ed$"] {
            let r = re::simpl(re::new(s));
            let safa = SAFA::new("abcde", &r);
            println!{"Regex: {:#?}",r};

            print_states(&safa);
            println!("DELTAS");
            for d in safa.deltas() {
                println!("{}, {}, {}", d.0, d.1, d.2.index());
            }

            let strdoc = "aed";
            let doc = strdoc.chars().collect();

            let sol = safa.solve(&doc);

            println!("SOLUTION for: {}", strdoc);
            println!("{:?}", sol);
            assert_ne!(sol,None);
        }
    }

    #[test]
    fn test_safa_lookahead_loop() {
        let s = r"^((?=a.*).*a)*$";
        let r = re::simpl(re::new(s));
        let safa = SAFA::new("ab", &r);
        assert_eq!(safa.nstates(), 8);
    }

    #[test]
    fn test_safa_double_negate() {
        let r = re::simpl(re::new("(a|b).{1,3}a"));
        let safa = SAFA::new("ab", &r);
        assert_eq!(safa, safa.negate().negate());
    }

    #[test]
    fn test_safa_double_negate_alt() {
        let r = re::simpl(re::new("(a.*|.*b)a"));
        let safa = SAFA::new("ab", &r);
        // safa.write_pdf("pos").unwrap();
        // safa.negate().write_pdf("neg").unwrap();
        // safa.negate().negate().write_pdf("dneg").unwrap();
        assert_eq!(safa, safa.negate().negate());
    }

    #[test]
    fn test_safa_double_negate_and() {
        let r = re::simpl(re::new("^(?=ab)ba$"));
        let safa = SAFA::new("ab", &r);
        // safa.write_pdf("pos").unwrap();
        // safa.negate().write_pdf("neg").unwrap();
        // safa.negate().negate().write_pdf("dneg").unwrap();
        assert_eq!(safa, safa.negate().negate());
    }

    #[test]
    fn test_safa_negate_range_interval() {
        let r = re::simpl(re::new("^.{1,3}b$"));
        let safa = SAFA::new("ab", &r).negate();
        let doc: Vec<_> = "aaaa".chars().collect();
        equiv_upto_epsilon(
            &safa.solve(&doc),
            &Trace::new(&[
                TraceElem::new(0, &Either(Err(Skip::open(4))), 2, 0, 4)
            ]),
        )
    }

    #[test]
    fn test_safa_negative() {
        for s in vec![
            r"^(A|BCD).{3}hello$"
            //r"abcd",r"a.*bd"
        ] {
            let r = re::simpl(re::new(s));
            let safa = SAFA::new("ACBDhello", &r);
            println! {"Regex: {:#?}",s};
            print_states(&safa);
            println!("DELTAS");
                for d in safa.deltas() {
                    println!("{}, {}, {}", d.0, d.1, d.2.index());
            }
            let strdoc = "abbb";
            let doc = strdoc.chars().collect();

            let sol = safa.solve(&doc);

            println!("SOLUTION for: {}", strdoc);
            println!("{:?}", sol);
            assert_ne!(sol, None);
        }
    }

    #[test]
    fn test_safa_negative_password() {
        let abvec: Vec<char> = (0..128).filter_map(std::char::from_u32).collect();
        let ab: String = abvec.iter().collect();
        for s in vec![
            r"(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$",
        ] {
            let r = re::simpl(re::new(s));
            let safa = (SAFA::new(&ab, &r)).negate();
            println! {"Regex: {:#?}",s};
            // let mut states = HashSet::new();
            // let mut ntrans: usize = 0;
            // for d in safa.deltas() {
            //     states.insert(d.0);
            //     ntrans = ntrans + 1;
            // }
            // println! {"N States: {:#?}",states.len()};
            // println! {"N Trans: {:#?}",ntrans};

            let strdoc = "password123";
            let doc = strdoc.chars().collect();

            let sol = safa.solve(&doc);

            println!("SOLUTION for: {}", strdoc);
            println!("{:?}", sol);
            assert_ne!(sol, None);
        }
    }
    #[test]
    fn test_safa_validate_password() {
        let abvec: Vec<char> = (0..128).filter_map(std::char::from_u32).collect();
        let ab: String = abvec.iter().collect();
        for s in vec![
            r"(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$",
        ] {
            let r = re::simpl(re::new(s));
            let safa = SAFA::new(&ab, &r);
            println! {"Regex: {:#?}",s};
            let mut states = HashSet::new();
            let mut ntrans: usize = 0;
            for d in safa.deltas() {
                states.insert(d.0);
                ntrans = ntrans + 1;
            }
            println! {"N States: {:#?}",states.len()};
            println! {"N Trans: {:#?}",ntrans};

            let strdoc = "MaJ@*n%!vx24";
            let doc = strdoc.chars().collect();

            let sol = safa.solve(&doc);

            println!("SOLUTION for: {}", strdoc);
            println!("{:?}", sol);
            assert_ne!(sol, None);
        }
    }

    #[test]
    fn test_safa_validate_pihole_syntax() {
        let abvec: Vec<char> = (0..128).filter_map(std::char::from_u32).collect();
        let ab: String = abvec.iter().collect();
        for s in vec![
            r"^ad([sxv]?[0-9]*|system)[_.-]([^.[:space:]]+[.]){1,}|[_.-]ad([sxv]?[0-9]*|system)[_.-]",
            "^(.+[_.-])?adse?rv(er?|ice)?s?[0-9]*[_.-]",
            "^(.+[_.-])?telemetry[_.-]",
            "^adim(age|g)s?[0-9]*[_.-]",
            "^adtrack(er|ing)?[0-9]*[_.-]",
            "^advert(s|is(ing|ements?))?[0-9]*[_.-]",
            "^aff(iliat(es?|ion))?[_.-]",
            "^analytics?[_.-]",
            "^banners?[_.-]",
            "^beacons?[0-9]*[_.-]",
            "^count(ers?)?[0-9]*[_.-]",
            r"^mads\.",
            "^pixels?[-.]",
            "^stat(s|istics)?[0-9]*[_.-]",
        ] {
            let r = re::simpl(re::new(s));
            println!("PIHOLE {}",r);
            let safa = SAFA::new(&ab, &r);
            println! {"Regex: {:#?}",s};
            let mut states = HashSet::new();
            let mut ntrans: usize = 0;
            for d in safa.deltas() {
                states.insert(d.0);
                ntrans = ntrans + 1;
            }
            println! {"N States: {:#?}",states.len()};
            println! {"N Trans: {:#?}",ntrans};
        }
    }

    #[test]
    fn test_safa_validate_dns() {
        let abvec: Vec<char> = (0..128).filter_map(std::char::from_u32).collect();
        let ab: String = abvec.iter().collect();
        for s in vec![r"^(?!you).*tube\.", r"\.ir\.{5}$", "porn|sex|xxx"] {
            let r = re::simpl(re::new(s));
            let safa = SAFA::new(&ab, &r);
            // let safa = SAFA::new("abcdefghijklmnopqrstuvwxyz", &r);
            println! {"Regex: {:#?}",s};
            let mut states = HashSet::new();
            let mut ntrans: usize = 0;
            for d in safa.deltas() {
                states.insert(d.0);
                ntrans = ntrans + 1;
            }
            println! {"N States: {:#?}",states.len()};
            println! {"N Trans: {:#?}",ntrans};

            let strdoc = "sadtube.com";
            let doc = strdoc.chars().collect();

            println!("SOLUTION for: {}", strdoc);
            println!("{:?}", safa.solve(&doc));
        }
    }

    #[test]
    fn test_safa_validate_pii() {
        let abvec: Vec<char> = (0..128).filter_map(std::char::from_u32).collect();
        let ab: String = abvec.iter().collect();
        for s in vec![
            ",[1-9][0-9]{9},",
            r"[0-9]{1,6}\ [a-zA-z\ ]*\ (CT|BLVD|ST|DR|AVE|PL|COURT|BOULEVARD)[a-zA-z0-9\ ]*,[A-Z0-9a-z]*,[A-Z]*,[A-Z\ ]*,[A-Z]{2},[A-Z]*,[1-9][0-9]{8},",
        ] {
            let r = re::simpl(re::new(s));
            let safa: SAFA<char> = SAFA::new(&ab, &r);
            println! {"Regex: {:#?}",s};
            let mut states = HashSet::new();
            let mut ntrans: usize = 0;
            for d in safa.deltas() {
                states.insert(d.0);
                ntrans = ntrans + 1;
            }
            println! {"N States: {:#?}",states.len()};
            println! {"N Trans: {:#?}",ntrans};
        }
    }

    #[test]
    fn test_safa_validate_dna() {
        for s in vec![".{8210}ATGGGCTACAGAAACCGTGCCAAAAGACTTCTACAGAGTGAACCCGAAAATCCTTCCTTG",
        ".{5841}ATGCTGAAACTTCTCAACCAGAAGAAAGGGCCTTCACAGTGTCCTTTATGTAAGAATGATATAACCAAAAG
        .*AGCCTACAAGAAAGTACGAGATTTAGTCAACTTGTTGAAGAGCTATTGAAAATCATTTGTGCTTTTCAGCTTGACACAGGTTTGGAGT.*ATGCAAACAGCTATAATTTTGCAAAAAAGGAAAATAACTCTCCTGAACATCTAAAAGATGAAGTTTCTATCATCCAAAGTATGGGCTACAGAAACCGTGCCAAAAGACTTCTACAGAGTGAACCCGAAAATCCTTCCTTG",
        ".{1989}CACAACTAAGGAACGTCAAGAGATACAGAATCCAAATTTTACCGCACCTGGTCAAGAATTTCTGTCTAAATCTCATTTGTATGAACATCTGACTTTGGAAAAATCTTCAAGCAATTTAGCAGTTTCAGGACATCCATTTTATCAAGTTTCTGCTACAAGAAATGAAAAAATGAGACACTTGATTACTACAGGCAGACCAACCAAAGTCTTTGTTCCACCTTTTAAAACTAAATCACATTTTCACAGAGTTGAACAGTGTGTTAGGAATATTAACTTGGAGGAAAACAGACAAAAGCAAAACATTGATGGACATGGCTCTGATGATAGTAA
        AAATAAGATTAATGACAATGAGATTCATCAGTTTAACAAAAACAACTCCAATCAAGCAGTAGCTGTAACTTTCACAAAGTGTGAAGAAGAACCTTTAG.*
        ATTTAATTACAAGTCTTCAGAATGCCAGAGATATACAGGATATGCGAATTAAGAAGAAACAAAGGCAACGCGTCTTTCCACAGCCAGGCAGTCTGTATCTTGCAAAAACATCCACTCTGCCTCGAATCTCTCTGAAAGCAGCAGTAGGAGGCCAAGTTCCCTCTGCGTGTTCTCATAAACAG.*CTGTATACGTATGGCGTTTCTAAACATTGCATAAAAATTAACAGCAAAA
        ATGCAGAGTCTTTTCAGTTTCACACTGAAGATTATTTTGGTAAGGAAAGTTTATGGACTGGAAAAGGAATACAGTTGGCTGATGGTGGATGGCTCATACC
        CTCCAATGATGGAAAGGCTGGAAAAGAAGAATTTTATAG.*GGCTCTGTGTGACACTCCAGGTGTGGATCCAAAGCTTATTTCTAGAATTTGGGTTTATAATCACTATA
        GATGGATCATATGGAAACTGGCAGCTATGGAATGTGCCTTTCCTAAGGAATTTGCTAATAGATGCCTAAGCCCAGAAAGGGTGCTTCTTCAACTAAAATA
        CAG"] {
            let r = re::simpl(re::new(s));
            let safa: SAFA<char> = SAFA::new("ACTGactg", &r);
            println!{"Regex: {:#?}",s};
            let mut states = HashSet::new();
            let mut ntrans: usize = 0;
            for d in safa.deltas() {
               states.insert(d.0);
               ntrans = ntrans + 1;
             }
            println!{"N States: {:#?}",states.len()};
            println!{"N Trans: {:#?}",ntrans};
        }
    }

    #[test]
    fn test_running_problems() {
        let list_of_failures = ["^a{3}|((?=b).{2})$","ab{1,3}"];
        for l in list_of_failures {
            let r = re::simpl(re::new(l));
            let mut safa = SAFA::new("ab", &r);
        }
    }

    #[cfg(feature = "plot")]
    #[test]
    fn test_safa_pdf() {
        let r = re::simpl(re::new("^a{3}|((?=b).{2})$"));
        let mut safa = SAFA::new("ab", &r);
        // safa = safa.negate();
        safa.write_pdf("safa_alt").unwrap();
        // let strdoc = "baababab";
        // let doc = strdoc.chars().collect();

        // println!("DELTAS");
        // for d in safa.deltas() {
        //     println!("{}, {}, {}", d.0, d.1, d.2.index());
        // }
        // println!("SOLUTION for: {}", strdoc);
        // println!("{:?}", safa.solve(&doc));
    }
}

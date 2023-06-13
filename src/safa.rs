use itertools::Itertools;
use std::collections::{BTreeSet, LinkedList};
use std::process::Command;

use petgraph::dot::Dot;
use petgraph::graph::NodeIndex;
use petgraph::visit::*;
use petgraph::Graph;

use std::result::Result;

use crate::quantifier::Quant;
use crate::regex::{re, Regex};
use crate::skip::Skip;

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
}

impl<A: Display, B: Display> Display for Either<A, B> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            Ok(ref a) => write!(f, "{}", a),
            Err(ref b) => write!(f, "{}", b),
        }
    }
}

#[derive(Debug, Clone)]
pub struct SAFA<C: Clone> {
    /// Alphabet
    pub ab: Vec<C>,

    /// A graph
    pub g: Graph<Quant<Regex>, Either<C, Skip>>,

    /// Set of accepting states
    pub accepting: BTreeSet<NodeIndex<u32>>,
}

impl SAFA<char> {
    /// Deep Constructor
    pub fn new<'a>(alphabet: &'a str, re: &Regex) -> Self {
        let ab = alphabet.chars().sorted().collect();
        // Add root
        let mut g: Graph<Quant<Regex>, Either<char, Skip>> = Graph::new();
        let n_init = g.add_node(Quant::and(re.clone()));
        g.add_edge(n_init, n_init, SAFA::epsilon());
        let mut s = Self {
            ab,
            g,
            accepting: BTreeSet::new(),
        };
        // Recursively build graph
        s.add(n_init, re);
        // Accepting states
        for n in s.g.node_indices() {
            if s.g[n].get().nullable() {
                s.accepting.insert(n);
            }
        }
        s
    }

    /// Add a regex to position [from] (an Or by default)
    fn add_skip(&mut self, n: NodeIndex<u32>, skip: Skip, q_c: &Regex) {
        if let Some(n_c) = self.find_or(q_c) {
            self.g.add_edge(n, n_c, Either::right(skip));
        } else {
            // Add to graph if not already there
            let n_c = self.g.add_node(Quant::or(q_c.clone()));
            // Reflexive step
            self.g.add_edge(n_c, n_c, SAFA::epsilon());
            self.g.add_edge(n, n_c, Either::right(skip));
            // Recurse on child [q_c]
            self.add(n_c, &q_c);
        }
    }

    /// Find an [or] node
    pub fn find_or(&self, r: &Regex) -> Option<NodeIndex<u32>> {
        self.g
            .node_indices()
            .find(|i| self.g[*i] == Quant::or(r.clone()))
    }

    /// Find an [and] node
    pub fn find_and(&self, r: &Regex) -> Option<NodeIndex<u32>> {
        self.g
            .node_indices()
            .find(|i| self.g[*i] == Quant::and(r.clone()))
    }

    /// Add derivative of a node in the graph
    fn add_derivatives(&mut self, from: NodeIndex<u32>, q: &Regex) {
        let mut cached_node = from;
        if let Some(n) = self.find_or(q) {
            if n != from {
                self.g.add_edge(from, n, SAFA::epsilon());
                cached_node = n;
            }
        } else {
            if !self.g[from].is_or() {
                // Add an OR node to graph if not already there
                cached_node = self.g.add_node(Quant::or(q.clone()));
                self.g.add_edge(cached_node, cached_node, SAFA::epsilon());
                // Reflexive step
                self.g.add_edge(from, cached_node, SAFA::epsilon());
            }
        };

        // Take all the single character steps
        for c in self.ab.clone().iter() {
            let q_c = re::deriv(q, &c);
            if let Some(n_c) = self.find_or(&q_c) {
                self.g.add_edge(cached_node, n_c, Either::left(*c));
            } else {
                // Add to graph if not already there
                let n_c = self.g.add_node(Quant::or(q_c.clone()));
                // Reflexive step
                self.g.add_edge(n_c, n_c, SAFA::epsilon());
                self.g.add_edge(cached_node, n_c, Either::left(*c));
                self.add(n_c, &q_c);
            }
        }
    }

    fn to_and(&mut self, from: NodeIndex<u32>) {
        self.g[from] = Quant::and(self.g[from].get());
    }

    fn to_or(&mut self, from: NodeIndex<u32>) {
        self.g[from] = Quant::or(self.g[from].get());
    }

    fn add(&mut self, from: NodeIndex<u32>, q: &Regex) {
        re::extract_skip(q, &self.ab)
            .map(|(skip, rem)| self.add_skip(from, skip, &rem))
            .or_else(|| {
                let children = re::extract_and(q)?;
                self.to_and(from);
                children
                    .into_iter()
                    .for_each(|q_c| self.add_skip(from, Skip::epsilon(), &q_c));
                Some(())
            })
            .or_else(|| {
                let children = re::extract_alt(q)?;
                self.to_or(from);
                children
                    .into_iter()
                    .for_each(|q_c| self.add_skip(from, Skip::epsilon(), &q_c));
                Some(())
            })
            .or_else(|| Some(self.add_derivatives(from, q))); // Catch-all
    }

    /// From SAFA<char> -> SAFA<String>
    pub fn as_str_safa(&self) -> SAFA<String> {
        SAFA {
            ab: self.ab.iter().map(|c| c.to_string()).collect(),
            g: self.g.map(
                |_, b| b.clone(),
                |_, e| Either(e.clone().0.map(|c| c.to_string())),
            ),
            accepting: self.accepting.clone(),
        }
    }
    pub fn write_pdf(&self, fout: &str) -> std::io::Result<()> {
        self.as_str_safa().write_pdf(fout)
    }
}

#[derive(Debug, Clone, Hash, PartialOrd, Ord, PartialEq, Eq)]
pub struct TraceElem<C> {
    pub from_node: NodeIndex<u32>,
    pub edge: Either<C, Skip>,
    pub to_node: NodeIndex<u32>,
    pub from_cur: usize,
    pub to_cur: usize,
}

impl<C: Clone> TraceElem<C> {
    pub fn new(
        from: NodeIndex<u32>,
        e: &Either<C, Skip>,
        to: NodeIndex<u32>,
        i: usize,
        j: usize,
    ) -> Self {
        Self {
            from_node: from,
            edge: e.clone(),
            to_node: to,
            from_cur: i,
            to_cur: j,
        }
    }

    pub fn is_epsilon(&self) -> bool {
        match self.edge.0 {
            Ok(_) => false,
            Err(ref e) => e.is_epsilon(),
        }
    }
}

impl<C: Display> Display for TraceElem<C> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{{{} -[ {} ]-> {} @ Doc[{} - {}]}}",
            self.from_node.index(),
            self.edge,
            self.to_node.index(),
            self.from_cur,
            self.to_cur
        )
    }
}

/// Type of solver result, a matchign [Trace]
pub type Trace<C> = LinkedList<TraceElem<C>>;

impl<C: Clone + Eq + Ord + Debug + Display + Hash + Sync + Send> SAFA<C> {
    /// To regular expression (root node)
    pub fn to_regex(&self) -> Regex {
        self.g[NodeIndex::new(0)].get()
    }

    /// An epsilon transition
    fn epsilon() -> Either<C, Skip> {
        Either::right(Skip::offset(0))
    }

    /// Get initial state
    pub fn get_init(&self) -> NodeIndex<u32> {
        NodeIndex::new(0)
    }

    /// Find regular expression in graph [i]
    pub fn find_regex(&self, re: &Regex) -> Option<NodeIndex<u32>> {
        self.g.node_indices().find(|x| &self.g[*x].get() == re)
    }

    /// All edges (quantified) in the graph
    pub fn deltas(&self) -> BTreeSet<(Quant<NodeIndex<u32>>, Either<C, Skip>, NodeIndex<u32>)> {
        self.g
            .node_indices()
            .flat_map(|n| {
                self.g.edges(n).map(|e| {
                    if self.g[e.source()].is_and() {
                        (Quant::and(e.source()), e.weight().clone(), e.target())
                    } else {
                        (Quant::or(e.source()), e.weight().clone(), e.target())
                    }
                })
            })
            .collect()
    }

    /// A sink is a self-looping node that is not accepting
    pub fn is_sink(&self, n: NodeIndex<u32>) -> bool {
        self.g
            .edges(n)
            .all(|e| e.target() == n && !self.accepting.contains(&e.target()))
    }

    fn prepend<'a, A: Clone + Debug>(v: &'a mut LinkedList<A>, a: A) -> Option<LinkedList<A>> {
        v.push_front(a.clone());
        Some(v.clone())
    }

    /// Accepting criterion for a node, document and cursor
    pub fn is_accept(&self, n: NodeIndex<u32>, i: usize, doc: &Vec<C>) -> bool {
        self.accepting.contains(&n) && i == doc.len()
    }

    /// Non accepting states
    pub fn non_accepting(&self) -> BTreeSet<NodeIndex<u32>> {
        let mut s: BTreeSet<_> = self.g.node_indices().collect();
        for x in self.accepting.clone() {
            s.remove(&x);
        }
        s
    }

    /// Recursively solve an edge and all the children coming off of it
    fn solve_edge(
        &self,
        e: &Either<C, Skip>,
        from: NodeIndex<u32>,
        to: NodeIndex<u32>,
        i: usize,
        doc: &Vec<C>,
    ) -> Option<Trace<C>> {
        let res = match e.0.clone() {
            // Sink state, cannot succeed
            Ok(_) if self.is_sink(to) => None,
            // Character match
            Ok(c) if c == doc[i] => Self::prepend(
                &mut self.solve_rec(to, i + 1, doc)?,
                TraceElem::new(from, e, to, i, i + 1),
            ),
            // Character non-match
            Ok(_) => None,
            Err(Skip::Choice(ref ns)) => ns.into_par_iter().find_map_any(|n| {
                Self::prepend(
                    &mut self.solve_rec(to, i + n, doc)?,
                    TraceElem::new(from, e, to, i, i + n),
                )
            }),
            Err(Skip::Star(n)) => (i + n..=doc.len()).into_par_iter().find_map_any(|j| {
                Self::prepend(
                    &mut self.solve_rec(to, j, doc)?,
                    TraceElem::new(from, e, to, i, j),
                )
            }),
        };
        res
    }

    /// Find a non-empty list of continuous matching document strings,
    /// as well as the sub-automaton that matched them
    fn solve_rec(&self, n: NodeIndex<u32>, i: usize, doc: &Vec<C>) -> Option<Trace<C>> {
        // Check accepting condition
        if self.is_accept(n, i, doc) {
            return Some(LinkedList::new());
        } else if i >= doc.len() {
            return None;
        }
        // Next nodes to visit
        let next: Vec<_> = self
            .g
            .edges(n)
            .filter(|e| e.source() != e.target() || e.weight() != &SAFA::epsilon())
            .collect();
        if self.g[n].is_and() {
            // All of the next entries must have solutions
            let subsolutions: Vec<_> = next
                .into_iter()
                .map(|e| self.solve_edge(e.weight(), e.source(), e.target(), i, doc))
                .collect();

            // All of them need to be set
            if subsolutions.iter().all(Option::is_some) {
                Some(subsolutions.into_iter().flat_map(Option::unwrap).collect())
            } else {
                None
            }
        } else {
            // One of the next entries must has a solution
            next.into_par_iter()
                .find_map_any(|e| self.solve_edge(e.weight(), e.source(), e.target(), i, doc))
        }
    }

    /// Solve at the root
    pub fn solve(&self, doc: &Vec<C>) -> Option<Trace<C>> {
        self.solve_rec(self.get_init(), 0, doc)
    }
}

impl SAFA<String> {
    /// Write DOT -> PDF file
    pub fn write_pdf(&self, filename: &str) -> std::io::Result<()> {
        let s: String = Dot::new(&self.g).to_string();
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
    use crate::regex::{re, Regex};
    use crate::safa::{Either, Trace, TraceElem, SAFA};
    use crate::skip::Skip;
    use std::fmt::Display;
    use petgraph::graph::NodeIndex;
    use std::collections::LinkedList;
    use std::collections::HashSet;

    fn print_states<C: Display + Clone>(safa: &SAFA<C>) {
        safa.g.node_indices().for_each(|i|
            println!("({}) -> {}", i.index(), safa.g[i])
        )
    }

    /// Equivalent solutions up to epsilon steps
    fn equiv_upto_epsilon(oa: &Option<Trace<char>>, ob: &Option<Trace<char>>) {
        fn fmt_trace(t: &Trace<char>) -> String {
            let mut s = Vec::new();
            for x in t {
                s.push(format!("{}", x));
            }
            s.join(", ")
        }

        if let Some(a) = oa {
            if let Some(b) = ob {
                let mut ia = a.iter();
                let mut ib = b.iter();
                let mut res = LinkedList::new();
                while let Some(x) = ia.next() {
                    if !x.is_epsilon() {
                        while let Some(y) = ib.next() {
                            if !y.is_epsilon() {
                                if x == y {
                                    res.push_back(x.clone());
                                    break;
                                } else {
                                    assert!(
                                        false,
                                        "\nTraceAssert: {} != {},
                                            \nMatch {} = \n\nleft := {}\nright := {}\n",
                                        x,
                                        y,
                                        fmt_trace(&res),
                                        fmt_trace(a),
                                        fmt_trace(b)
                                    );
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn test_safa_match_exact() {
        let r = re::new("^baa$");
        let safa = SAFA::new("ab", &r);
        let strdoc = "baa";
        let doc = strdoc.chars().collect();

        equiv_upto_epsilon(
            &safa.solve(&doc),
            &Some(LinkedList::from([
                TraceElem::new(NodeIndex::new(0), &SAFA::epsilon(), NodeIndex::new(1), 0, 0),
                TraceElem::new(NodeIndex::new(1), &Either(Ok('b')), NodeIndex::new(3), 0, 1),
                TraceElem::new(NodeIndex::new(3), &Either(Ok('a')), NodeIndex::new(4), 1, 2),
                TraceElem::new(NodeIndex::new(4), &Either(Ok('a')), NodeIndex::new(5), 2, 3),
            ])),
        );
    }

    #[test]
    fn test_safa_match_partial() {
        let r = re::new("baa");
        let safa = SAFA::new("ab", &r);
        let strdoc = "ababbbaa";
        let doc: Vec<_> = strdoc.chars().collect();
        equiv_upto_epsilon(
            &safa.solve(&doc),
            &Some(LinkedList::from([
                TraceElem::new(
                    NodeIndex::new(0),
                    &Either(Err(Skip::star())),
                    NodeIndex::new(1),
                    0,
                    5,
                ),
                TraceElem::new(NodeIndex::new(1), &Either(Ok('b')), NodeIndex::new(3), 5, 6),
                TraceElem::new(NodeIndex::new(3), &Either(Ok('a')), NodeIndex::new(4), 6, 7),
                TraceElem::new(NodeIndex::new(4), &Either(Ok('a')), NodeIndex::new(5), 7, 8),
            ])),
        );
    }

    #[test]
    fn test_safa_match_star() {
        let r = re::new("^a*$");
        let safa = SAFA::new("ab", &r);
        let strdoc = "aa";
        let doc: Vec<_> = strdoc.chars().collect();
        assert_eq!(
            safa.solve(&doc),
            Some(LinkedList::from([
                TraceElem::new(NodeIndex::new(0), &SAFA::epsilon(), NodeIndex::new(1), 0, 0),
                TraceElem::new(
                    NodeIndex::new(1),
                    &Either::left('a'),
                    NodeIndex::new(1),
                    0,
                    1
                ),
                TraceElem::new(
                    NodeIndex::new(1),
                    &Either::left('a'),
                    NodeIndex::new(1),
                    1,
                    2
                )
            ]))
        )
    }

    #[test]
    fn test_safa_alt_pure() {
        let r = re::new("baa(a|c)$");
        let safa = SAFA::new("abc", &r);
        let strdoc = "abababaac";
        let doc: Vec<_> = strdoc.chars().collect();
        equiv_upto_epsilon(
            &safa.solve(&doc),
            &Some(LinkedList::from([
                TraceElem::new(
                    NodeIndex::new(0),
                    &Either(Err(Skip::star())),
                    NodeIndex::new(1),
                    0,
                    5,
                ),
                TraceElem::new(NodeIndex::new(1), &Either(Ok('b')), NodeIndex::new(3), 5, 6),
                TraceElem::new(NodeIndex::new(3), &Either(Ok('a')), NodeIndex::new(4), 6, 7),
                TraceElem::new(NodeIndex::new(4), &Either(Ok('a')), NodeIndex::new(5), 7, 8),
                TraceElem::new(NodeIndex::new(5), &Either(Ok('c')), NodeIndex::new(6), 8, 9),
            ])),
        )
    }

    #[test]
    fn test_safa_alt_merge() {
        let r = re::new("^.*baa(a|b)$");
        let safa = SAFA::new("ab", &r);
        let strdoc = "abababaab";
        let doc: Vec<_> = strdoc.chars().collect();
        equiv_upto_epsilon(
            &safa.solve(&doc),
            &Some(LinkedList::from([
                TraceElem::new(
                    NodeIndex::new(0),
                    &Either(Err(Skip::star())),
                    NodeIndex::new(1),
                    0,
                    5
                ),
                TraceElem::new(NodeIndex::new(1), &Either(Ok('b')), NodeIndex::new(3), 5, 6),
                TraceElem::new(NodeIndex::new(3), &Either(Ok('a')), NodeIndex::new(4), 6, 7),
                TraceElem::new(NodeIndex::new(4), &Either(Ok('a')), NodeIndex::new(5), 7, 8),
                TraceElem::new(NodeIndex::new(5), &Either(Ok('b')), NodeIndex::new(6), 8, 9)
            ]))
        )
    }

    #[test]
    fn test_safa_range_exact() {
        let r = re::new("^.{3}b$");
        let safa = SAFA::new("ab", &r);
        let doc: Vec<_> = "aaab".chars().collect();
        equiv_upto_epsilon(
            &safa.solve(&doc),
            &Some(LinkedList::from([
                TraceElem::new(
                    NodeIndex::new(0),
                    &Either(Err(Skip::offset(3))),
                    NodeIndex::new(1),
                    0,
                    3
                ),
                TraceElem::new(NodeIndex::new(1), &Either(Ok('b')), NodeIndex::new(3), 3, 4)
            ]))
        )
    }

    #[test]
    fn test_safa_range_interval() {
        let r = re::new("^.{1,3}b$");
        let safa = SAFA::new("ab", &r);
        safa.write_pdf("safa").unwrap();
        print_states(&safa);
        let doc: Vec<_> = "aaab".chars().collect();
        equiv_upto_epsilon(
            &safa.solve(&doc),
            &Some(LinkedList::from([
                TraceElem::new(
                    NodeIndex::new(0),
                    &Either(Err(Skip::range(1,3))),
                    NodeIndex::new(1),
                    0,
                    3
                ),
                TraceElem::new(NodeIndex::new(1), &Either(Ok('b')), NodeIndex::new(3), 3, 4)
            ]))
        )
    }


    #[test]
    fn test_safa_range_starplus() {
        let r = re::new("^.{2,}b$");
        let safa = SAFA::new("ab", &r);
        let doc: Vec<_> = "aaab".chars().collect();
        equiv_upto_epsilon(
            &safa.solve(&doc),
            &Some(LinkedList::from([
                TraceElem::new(
                    NodeIndex::new(0),
                    &Either(Err(Skip::starplus(2))),
                    NodeIndex::new(1),
                    0,
                    3
                ),
                TraceElem::new(NodeIndex::new(1), &Either(Ok('b')), NodeIndex::new(3), 3, 4)
            ]))
        )
    }

    #[test]
    fn test_safa_range_nested() {
        // unsafe { backtrace_on_stack_overflow::enable() };
        let r = re::new("^(.{1,3}){1,2}b$");
        let safa = SAFA::new("ab", &r);
        let doc: Vec<_> = "aaaab".chars().collect();
        equiv_upto_epsilon(
            &safa.solve(&doc),
            &Some(LinkedList::from([
                TraceElem::new(
                    NodeIndex::new(0),
                    &Either(Err(Skip::choice(&[1, 2, 3, 4, 6]))),
                    NodeIndex::new(1),
                    0,
                    4
                ),
                TraceElem::new(NodeIndex::new(1), &Either(Ok('b')), NodeIndex::new(3), 4, 5)
            ]))
        )
    }

    #[test]
    fn test_safa_range_alt() {
        unsafe { backtrace_on_stack_overflow::enable() };
        let r = re::new("^((.{1,2}.)|(.{4,5}b))$");
        let safa = SAFA::new("ab", &r);
        print_states(&safa);
        let doc: Vec<_> = "aaaab".chars().collect();
        equiv_upto_epsilon(
            &safa.solve(&doc),
            &Some(LinkedList::from([
                TraceElem::new(
                    NodeIndex::new(4),
                    &Either(Err(Skip::choice(&[4, 5]))),
                    NodeIndex::new(5),
                    0,
                    4
                ),
                TraceElem::new(NodeIndex::new(5), &Either(Ok('b')), NodeIndex::new(2), 4, 5)
            ]))
        )
    }

    #[test]
    fn test_safa_validate() {
        let abvec: Vec<char>= (0..128).filter_map(std::char::from_u32).collect();
        let ab: String = abvec.iter().collect();
        let r = re::new(r"\.");
        println!("{:#?}",r);
    }

    #[test]
    fn test_safa_validate_password() {
        let abvec: Vec<char>= (0..128).filter_map(std::char::from_u32).collect();
        let ab: String = abvec.iter().collect();
        for s in vec![r"(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$"] {
            let r = re::new(s);
            let safa = SAFA::new(&ab, &r);
            println!{"Regex: {:#?}",s};
            let mut states = HashSet::new();
            let mut ntrans: usize = 0;
            for d in safa.deltas() {
               states.insert(d.0);
               ntrans = ntrans + 1; 
             }
            println!{"N States: {:#?}",states.len()};
            println!{"N Trans: {:#?}",ntrans};

            let strdoc = "MaJ@*n%!vx24";
            let doc = strdoc.chars().collect();

            println!("SOLUTION for: {}", strdoc);
            println!("{:?}", safa.solve(&doc));
        }
    }


    #[test]
    fn test_safa_validate_pihole_syntax() {
        let abvec: Vec<char>= (0..128).filter_map(std::char::from_u32).collect();
        let ab: String = abvec.iter().collect();
        for s in vec![r"^ad([sxv]?[0-9]*|system)[_.-]([^.[:space:]]+[.]){1,}|[_.-]ad([sxv]?[0-9]*|system)[_.-]",
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
        "^stat(s|istics)?[0-9]*[_.-]"] {
            let r = re::new(s);
            let safa = SAFA::new(&ab, &r);
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
    fn test_safa_validate_dns() {
        let abvec: Vec<char>= (0..128).filter_map(std::char::from_u32).collect();
        let ab: String = abvec.iter().collect();
        for s in vec![r"^(?!you).*tube\.",r"\.ir\.{5}$","porn|sex|xxx"] {
            let r = re::new(s);
            let safa = SAFA::new(&ab, &r);
            // let safa = SAFA::new("abcdefghijklmnopqrstuvwxyz", &r);
            println!{"Regex: {:#?}",s};
            let mut states = HashSet::new();
            let mut ntrans: usize = 0;
            for d in safa.deltas() {
               states.insert(d.0);
               ntrans = ntrans + 1; 
             }
            println!{"N States: {:#?}",states.len()};
            println!{"N Trans: {:#?}",ntrans};

            let strdoc = "sadtube.com";
            let doc = strdoc.chars().collect();

            println!("SOLUTION for: {}", strdoc);
            println!("{:?}", safa.solve(&doc));
        }
    }

    #[test]
    fn test_safa_validate_pii() {
        let abvec: Vec<char>= (0..128).filter_map(std::char::from_u32).collect();
        let ab: String = abvec.iter().collect();
        for s in vec![",[1-9][0-9]{9},",r"[0-9]{1,6}\ [a-zA-z\ ]*\ (CT|BLVD|ST|DR|AVE|PL|COURT|BOULEVARD)[a-zA-z0-9\ ]*,[A-Z0-9a-z]*,[A-Z]*,[A-Z\ ]*,[A-Z]{2},[A-Z]*,[1-9][0-9]{8},"] {
            let r = re::new(s);
            let safa: SAFA<char> = SAFA::new(&ab, &r);
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
            let r = re::new(s);
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

    #[cfg(feature = "plot")]
    #[test]
    fn test_safa_pdf() {
        let r = re::new("^[a-c]*b$");
        let safa = SAFA::new("abcd", &r);
        safa.write_pdf("safa2").unwrap();
        let strdoc = "baababab";
        let doc = strdoc.chars().collect();

        println!("DELTAS");
        for d in safa.deltas() {
            println!("{}, {}, {}", d.0, d.1, d.2.index());
        }
        println!("SOLUTION for: {}", strdoc);
        println!("{:?}", safa.solve(&doc));
    }
}

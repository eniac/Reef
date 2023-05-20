use itertools::Itertools;
use std::collections::{HashSet, HashMap, BTreeSet, LinkedList};
use std::process::Command;

use petgraph::Graph;
use petgraph::graph::NodeIndex;
use petgraph::dot::Dot;
use petgraph::visit::*;

use std::fs::File;
use std::io::BufWriter;
use std::result::Result;

use crate::regex::{Regex, RegexF};
use crate::nfa::EPSILON;
use rayon::iter::*;

use core::fmt;
use core::fmt::{Display,Formatter};

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Skip {
    Offset(usize),
    Choice(BTreeSet<usize>),
    Star
}

impl Skip {
    pub fn range(i: usize, j: usize) -> Self {
        if i == j {
            Skip::Offset(i)
        } else {
            Skip::Choice((i..=j).collect())
        }
    }

    pub fn epsilon() -> Self {
        Skip::Offset(0)
    }
    /// Sequential composition of two jumps is a jump
    pub fn then(&self, a: &Skip) -> Skip {
        match (self, a) {
            (Skip::Offset(0), _) => a.clone(),
            (Skip::Offset(i), Skip::Offset(j)) => Skip::Offset(i+j),
            (Skip::Offset(i), Skip::Choice(x)) | (Skip::Choice(x), Skip::Offset(i)) =>
                Skip::Choice(x.into_iter().map(|x| x + i).collect()),
            (Skip::Choice(x), Skip::Choice(y)) => {
                let mut s = BTreeSet::new();
                for i in x.into_iter() {
                    for j in y.into_iter() {
                        s.insert(i + j);
                    }
                }
                Skip::Choice(s)
            },
            (Skip::Star, _) | (_, Skip::Star) => Skip::Star
        }
    }
}

impl fmt::Display for Skip {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Skip::Offset(u) if *u == 0 => write!(f, "ε"),
            Skip::Offset(u) => write!(f, "+{}", u),
            Skip::Choice(us) => write!(f, "{:?}", us),
            Skip::Star => write!(f, "*")
        }
    }
}

#[derive(Debug, Clone, Hash, PartialOrd, Ord, PartialEq, Eq)]
pub struct Either<A, B>(Result<A, B>);

impl<A, B> Either<A, B> {
    fn left(a: A) -> Self {
        Self(Ok(a))
    }
    fn right(b: B) -> Self {
        Self(Err(b))
    }
    fn is_left(&self) -> bool {
        self.0.is_ok()
    }
    fn is_right(&self) -> bool {
        self.0.is_err()
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Quant<A>(A, bool);

impl<A: Clone> Quant<A> {
    fn and(a: A) -> Self {
        Self(a, true)
    }
    fn or(a: A) -> Self {
        Self(a, false)
    }
    fn is_and(&self) -> bool {
        self.1
    }
    fn is_or(&self) -> bool {
        !self.1
    }
    fn get(&self) -> A {
        self.0.clone()
    }
}

impl<A: Display, B: Display> Display for Either<A, B> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            Ok(ref a) => write!(f, "{}", a),
            Err(ref b) => write!(f, "{}", b)
        }
    }
}

impl Display for Quant<Regex> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if self.1 {
            write!(f, "∀ {}", self.0)
        } else {
            write!(f, "∃ {}", self.0)
        }
    }
}

impl Display for Quant<NodeIndex<u32>> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if self.1 {
            write!(f, "∀ {}", self.0.index())
        } else {
            write!(f, "∃ {}", self.0.index())
        }
    }
}


#[derive(Debug, Clone)]
pub struct SAFA<C: Clone> {
    /// Alphabet
    pub ab: Vec<C>,

    /// A graph
    pub g: Graph<Quant<Regex>, Either<C, Skip>>,
}

impl SAFA<char> {
    /// Shallow constructor
    pub fn new<'a>(alphabet: &'a str, re: &Regex) -> Self {
        let ab = alphabet.chars().sorted().collect();
        let mut g: Graph<Quant<Regex>, Either<char, Skip>> = Graph::new();
        let n_init = g.add_node(Quant::and(re.clone()));
        g.add_edge(n_init, n_init, SAFA::epsilon());
        let mut s = Self { ab, g };
        s.add(n_init, re);
        s
    }

    /// Add a regex to position [from] (an Or by default)
    fn add_skip(&mut self, n: NodeIndex<u32>, skip: Skip, q_c: &Regex) {
        if let Some(n_c) = self.g.node_indices().find(|i|
                                &self.g[*i].get() == q_c && self.g[*i].is_or()) {
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

    /// Add derivative of a node in the graph
    fn add_derivatives(&mut self, from: NodeIndex<u32>, q: &Regex) {
      let n =
        if let Some(n) = self.g.node_indices().find(|i| self.g[*i] == Quant::or(q.clone())) {
            if n != from {
                self.g.add_edge(from, n, SAFA::epsilon());
            }
            n
        } else {
            if self.g[from].is_or() {
              from
            } else {
              // Add an OR node to graph if not already there
              let n = self.g.add_node(Quant::or(q.clone()));
              self.g.add_edge(n, n, SAFA::epsilon());
              // Reflexive step
              self.g.add_edge(from, n, SAFA::epsilon());
              n
            }
        };

        // Take all the single character steps
        for c in self.ab.clone().iter() {
            let q_c = q.deriv(&c);
            if let Some(n_c) = self.g.node_indices().find(|i| self.g[*i] == Quant::or(q_c.clone())) {
                self.g.add_edge(n, n_c, Either::left(*c));
            } else {
                // Add to graph if not already there
                let n_c = self.g.add_node(Quant::or(q_c.clone()));
                // Reflexive step
                self.g.add_edge(n_c, n_c, SAFA::epsilon());
                self.g.add_edge(n, n_c, Either::left(*c));
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
        match *q.0 {
            // .*
            RegexF::Star(ref a) if a.accepts_any(&self.ab) =>
              self.add_skip(from, Skip::Star, &Regex::nil()),
            // .{i,j}
            RegexF::Range(ref a, x, y) if a.accepts_any(&self.ab) && !a.nullable() =>
              self.add_skip(from, Skip::range(x, y), &Regex::nil()),
            // (?=r)
            RegexF::Lookahead(ref a) => {
              self.to_and(from);
              self.add_skip(from, Skip::epsilon(), a)
            },
            // (r | r')
            RegexF::Alt(_, _) => {
              self.to_or(from);
              q.to_alt_list()
               .into_iter()
               .for_each(|q_c| self.add_skip(from, Skip::epsilon(), &q_c));
            },
            // r1r2
            RegexF::App(ref a, ref b) => {
              match *a.0 {
                  // .*r
                  RegexF::Star(ref a) if a.accepts_any(&self.ab) =>
                      self.add_skip(from, Skip::Star, b),
                  // .{i,j}r
                  RegexF::Range(ref a, x, y) if a.accepts_any(&self.ab) =>
                      self.add_skip(from, Skip::range(x, y), b),
                  // (?=r1)r2
                  RegexF::Lookahead(ref a) => {
                      self.to_and(from);
                      self.add_skip(from, Skip::epsilon(), a);
                      self.add_skip(from, Skip::epsilon(), b);
                  },
                  // Distributivity with alt
                  RegexF::Alt(ref x, ref y) => {
                    self.add(from,
                        &Regex::alt(
                            Regex::app(x.clone(), b.clone()),
                            Regex::app(y.clone(), b.clone())));
                    self.to_or(from);
                  }
                  // Some other kind of app
                  _ => self.add_derivatives(from, q)
              }
            },
            // Other (derivative)
            _ => self.add_derivatives(from, q)
        }
    }

    /// From SAFA<char> -> SAFA<String>
    pub fn as_str_safa(&self) -> SAFA<String> {
        SAFA {
            ab: self.ab.iter().map(|c| c.to_string()).collect(),
            g: self.g.map(|_, b| b.clone(),
                          |_, e| Either(e.clone().0.map(|c| c.to_string())))
        }
    }
}


impl<C: Clone + Eq + Ord + std::fmt::Debug + Display + std::hash::Hash + Sync> SAFA<C> {
    /// To regular expression (root node)
    pub fn to_regex(&self) -> Regex {
        self.g[NodeIndex::new(0)].get()
    }

    pub fn is_start_anchored(&self, from: NodeIndex<u32>) -> bool {
        self.g[from].get().is_start_anchored()
    }

    pub fn is_end_anchored(&self, from: NodeIndex<u32>) -> bool {
        self.g[from].get().is_end_anchored()
    }

    /// An epsilon transition
    fn epsilon() -> Either<C, Skip> {
        Either::right(Skip::Offset(0))
    }

    /// Return a vector of (NFA id, node) of all accepting states
    pub fn accepting(&self) -> Vec<NodeIndex<u32>> {
        let mut res: Vec<_> = Vec::new();

        for n in self.g.node_indices() {
            if self.g[n].get().nullable() {
                res.push(n);
            }
        }
        res
    }

    /// Get initial state
    pub fn get_init(&self) -> NodeIndex<u32> {
        NodeIndex::new(0)
    }

    /// Find regular expression in graph [i]
    pub fn find_regex(&self, re: &Regex) -> Option<NodeIndex<u32>> {
        self.g.node_indices().find(|x| &self.g[*x].get() == re)
    }

    pub fn deltas(&self) -> BTreeSet<(Quant<NodeIndex<u32>>, Either<C, Skip>, NodeIndex<u32>)> {
        self.g.node_indices().flat_map(|n|
            self.g.edges(n).map(|e|
                if self.g[e.source()].is_and() {
                    (Quant::and(e.source()), e.weight().clone(), e.target())
                } else {
                    (Quant::or(e.source()), e.weight().clone(), e.target())
                })).collect()
    }

    fn safe_get(v: &Vec<C>, i: usize) -> String {
        if i == v.len() {
            "NaN".to_string()
        } else {
            v[i].to_string()
        }
    }

    /// Find the largest continuous matching string of characters
    /// exclusive both in [node index] and [usize] that didn't match
    pub fn solve_char(&self, from: NodeIndex<u32>, i: usize, doc: &Vec<C>) ->
        (NodeIndex<u32>, Option<(usize, usize)>) {
        let accepting = &self.accepting();

        // Initial state is also accepting
        if accepting.contains(&self.get_init()) &&
            (!self.is_end_anchored(from) || doc.len() == 0) {
            return (from, Some((0, 0)));
        }

        // For every postfix of doc (O(n^2))
        let mut s = from;
        for j in i..doc.len() {
            // Apply transition relation
            if let Some(x) =
                self.g.edges(s)
                      .find(|e| e.source() != e.target() &&
                                e.weight() == &Either::left(doc[j].clone()))
                      .map(|e| e.target()) {
                // found a substring match or exact match
                if self.is_accept(x, j, doc) {
                    return (x, Some((i, j + 1)));
                }
                s = x;
            } else {
                // Non-character transition found
                return (s, Some((i, j)));
            }
        }
        (s, None)
    }

    pub fn is_sink(&self, n: NodeIndex<u32>) -> bool {
        self.g.edges(n).all(|e| e.target() == n)
    }

    /// Recursively solve an edge and all the children coming off of it
    fn solve_edge(&self, e: &Either<C, Skip>, from: NodeIndex<u32>,
        to: NodeIndex<u32>, i: usize, doc: &Vec<C>) ->
        Option<Vec<(NodeIndex<u32>, usize, usize)>> {
        match e.0 {
            Ok(_) =>
                match self.solve_char(from, i, doc) {
                  (n, Some((a,b))) if self.is_accept(n, b, doc) =>
                      Some(vec![(from, a, b)]),
                  (n, Some(_)) if self.is_sink(n) => None,
                  (n, Some((a,b))) => {
                      let mut sols = self.solve_rec(n, b, doc)?;
                      sols.insert(0, (from, a, b));
                      Some(sols)
                  },
                  (_, None) => None
                },
            Err(Skip::Offset(n)) => self.solve_rec(to, i+n, doc),
            Err(Skip::Choice(ref ns)) =>
                ns.into_iter()
                  .find_map(|n| self.solve_rec(to, i+n, doc)),
            Err(Skip::Star) =>
                (i..doc.len())
                    .into_iter()
                    .find_map(|n| self.solve_rec(to, i, doc))
        }
    }

    fn is_accept(&self, n: NodeIndex<u32>, i: usize, doc: &Vec<C>) -> bool {
        // Initial state is also accepting
        if self.accepting().contains(&n) && (!self.is_end_anchored(n) || i == doc.len() - 1) {
            true
        } else {
            false
        }
    }

    /// Find a non-empty list of continuous matching document strings,
    /// as well as the sub-AFA that matched them
    fn solve_rec(&self, n: NodeIndex<u32>, i: usize,
        doc: &Vec<C>) -> Option<Vec<(NodeIndex<u32>, usize, usize)>> {

        // Check accepting condition
        if self.is_accept(n, i, doc) {
            return Some(vec![]);
        }

        // Iterate over all postfixes of doc
        let mut start_idxs = Vec::new();
        if self.is_start_anchored(n) {
            start_idxs.push(i);
        } else {
            start_idxs.append(&mut (i..doc.len()).collect());
        }

        // For every postfix of doc (O(n^2))
        start_idxs.into_iter().find_map(|i| {
            let mut next = self.g.edges(n).filter(|e| e.source() != e.target());
            if self.g[n].is_and() {
                // All of the next entries must have solutions
                let subsolutions : Vec<_> = next.into_iter()
                    .map(|e| self.solve_edge(e.weight(), e.source(), e.target(), i, doc))
                    .collect();

                // All of them need to be
                if subsolutions.iter().all(Option::is_some) {
                    Some(subsolutions.into_iter().flat_map(Option::unwrap).collect())
                } else {
                    None
                }
            } else {
                // One of the next entries must has a solution
                next.find_map(|e|
                    self.solve_edge(e.weight(), e.source(), e.target(), i, doc))
            }
        })
    }

    pub fn solve(&self, doc: &Vec<C>) -> Option<Vec<(NodeIndex<u32>, usize, usize)>> {
        self.solve_rec(self.get_init(), 0, doc)
    }
}

impl SAFA<String> {
    /// Write DOT -> PDF file
    pub fn write_pdf(&self,  filename: &str) -> std::io::Result<()> {
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
    use crate::safa::SAFA;
    use crate::regex::Regex;
    use petgraph::graph::NodeIndex;

    #[test]
    fn test_safa_match_exact() {
        // unsafe { backtrace_on_stack_overflow::enable() };
        let r = Regex::new("^baa$");
        let safa = SAFA::new("ab", &r);
        let strdoc = "baa";
        let doc = strdoc.chars().collect();
        assert_eq!(safa.solve(&doc), Some(vec![(NodeIndex::new(1), 0, 3)]));

    }

    #[test]
    fn test_safa_match_partial() {
        // unsafe { backtrace_on_stack_overflow::enable() };
        let r = Regex::new("baa");
        let safa = SAFA::new("ab", &r);
        let strdoc = "abababaaba";
        let doc = strdoc.chars().collect();
        assert_eq!(safa.solve(&doc), Some(vec![(NodeIndex::new(1), 5, 8)]));
    }

    #[test]
    fn test_safa_alt() {
        // unsafe { backtrace_on_stack_overflow::enable() };
        let r = Regex::new(".*baa(b|a)");
        let safa = SAFA::new("ab", &r);
        safa.as_str_safa().write_pdf("safa").unwrap();
        let strdoc = "abababaab";
        let doc = strdoc.chars().collect();
        assert_eq!(safa.solve(&doc),
            Some(vec![(NodeIndex::new(1), 5, 8),
                      (NodeIndex::new(6), 8, 9)]));
    }

    #[test]
    fn test_safa_pdf() {
        // unsafe { backtrace_on_stack_overflow::enable() };
        let r = Regex::new("(?=a).*baa(b|a)");
        let safa = SAFA::new("ab", &r);
        safa.as_str_safa().write_pdf("safa").unwrap();
        let strdoc = "abababaab";
        let doc = strdoc.chars().collect();

        println!("DELTAS");
        for d in safa.deltas() {
           println!("{}, {}, {}", d.0, d.1, d.2.index());
        }
        println!("SOLUTION for: {}", strdoc);
        println!("{:?}", safa.solve(&doc));
    }

}

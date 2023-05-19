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

impl<A: Display> Display for Quant<A> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if self.1 {
            write!(f, "∀ {}", self.0)
        } else {
            write!(f, "∃ {}", self.0)
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
                  RegexF::Alt(ref x, ref y) =>
                    self.add(from,
                        &Regex::alt(
                            Regex::app(x.clone(), b.clone()),
                            Regex::app(y.clone(), b.clone()))),
                  // Some other kind of app
                  _ => self.add_derivatives(from, q)
              }
            },
            // Other (derivative)
            _ => self.add_derivatives(from, q)
        }
    }

    /// From SAFA<char> -> SAFA<String>
    pub fn as_str_snfa(&self) -> SAFA<String> {
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

    /// Find the largest continuous matching string of characters
    /// exclusive both in [node index] and [usize] that didn't match
    pub fn solve_char(&self, c: C, next: NodeIndex<u32>, i: usize, doc: &Vec<C>) -> Option<(NodeIndex<u32>, usize, usize)> {
        if c == doc[i] {
            if let Some((nn, a, b)) =
                self.g.edges(next)
                      .find_map(|e| self.solve_char(e.weight().0.clone().ok()?, e.target(), i+1, doc)) {
                Some((nn, a-1, b))
            } else { Some((next, i, i+1)) }
        } else {
            None
        }
    }

    /// Recursively solve an edge and all the children coming off of it
    fn solve_edge(&self, e: &Either<C, Skip>, from: NodeIndex<u32>, to: NodeIndex<u32>, i: usize, doc: &Vec<C>) ->
        Option<Vec<(NodeIndex<u32>, usize, usize)>> {
        match e.0 {
            Ok(ref c) => {
                let (n, a, b) = self.solve_char(c.clone(), to, i, doc)?;
                let mut sols = self.solve_rec(n, b, doc)?;
                sols.insert(0, (from, a, b));
                Some(sols)
            },
            Err(Skip::Offset(n)) => self.solve_rec(to, i+n, doc),
            Err(Skip::Choice(ref ns)) =>
                ns.into_par_iter()
                  .find_map_any(|n| self.solve_rec(to, i+n, doc)),
            Err(Skip::Star) =>
                (i..doc.len())
                    .into_par_iter()
                    .find_map_any(|n| self.solve_rec(to, i+n, doc))
        }
    }

    /// Find a non-empty list of continuous matching document strings, as well as the sub-AFA that matched them
    fn solve_rec(&self, n: NodeIndex<u32>, i: usize, doc: &Vec<C>) -> Option<Vec<(NodeIndex<u32>, usize, usize)>> {
        let mut start_idxs = Vec::new();

        // Iterate over all postfixes of doc
        if self.is_start_anchored(n) {
            start_idxs.push(i);
        } else {
            start_idxs.append(&mut (i..doc.len()).collect());
        }

        let accepting = &self.accepting();

        // Initial state is also accepting
        if accepting.contains(&n) && (!self.is_end_anchored(n) || doc.len() == 0) {
            return Some(vec![(n, 0, 0)]);
        }

        // For every postfix of doc (O(n^2))
        start_idxs.into_par_iter().find_map_any(|i| {
            let mut next = self.g.edges(n);
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
    /*

    /// Is this a state with jumps
    fn is_jump_pad(&self, from: Coord) -> bool {
        self.hg[from.0].edges(from.1)
                       .filter(|e| e.target() != from.1)
                       .all(|e| self.hg[from.0][e.target()].0.is_err() && e.weight().is_none())
    }

    /// Is this a state with derivatives
    fn is_deriv_pad(&self, from: Coord) -> bool {
        self.hg[from.0].edges(from.1)
                       .filter(|e| e.target() != from.1)
                       .all(|e| self.hg[from.0][e.target()].0.is_ok() && e.weight().is_some())
    }

    /// Match the SAFA on a document (backtracking)
    pub fn solve(&self, doc: &Vec<C>) -> LinkedList<Moves> {
        self.solve_rec((0, NodeIndex::new(0)), doc, 0).unwrap_or(LinkedList::new())
    }

    /// Is the state [from] accepting
    fn is_accepting(&self, from: Coord) -> bool {
        match self.hg[from.0][from.1].0.clone() {
            Ok(re) if re.nullable() => true,
            Err(Jump(Skip::Offset(offset), nfa_dest)) if offset == 0 =>
                self.is_accepting((nfa_dest, NodeIndex::new(0))),
            Err(Jump(Skip::Choice(offsets), nfa_dest)) if offsets.contains(&0) =>
                self.is_accepting((nfa_dest, NodeIndex::new(0))),
            Err(Jump(Skip::Star, nfa_dest)) =>
                self.is_accepting((nfa_dest, NodeIndex::new(0))),
            _ => false
        }
    }

    fn solve_jump(&self, jmp: &Jump, doc: &Vec<C>, i: usize) -> Option<LinkedList<Moves>> {
        match jmp {
            Jump(Skip::Offset(offset), nfa_dest) =>
                self.solve_rec((*nfa_dest, NodeIndex::new(0)), doc, i + offset),
            Jump(Skip::Choice(offsets), nfa_dest) =>
                // Parallelize this
                offsets.into_par_iter()
                       .filter(|&o| i + o < doc.len())
                       .find_map_any(|o| self.solve_rec((*nfa_dest, NodeIndex::new(0)), doc, i + o)),
            Jump(Skip::Star, nfa_dest) =>
                (i..doc.len())
                    .into_par_iter()
                    .find_map_any(|j| self.solve_rec((*nfa_dest, NodeIndex::new(0)), doc, j))
        }
    }

    fn solve_rec(&self, from: Coord, doc: &Vec<C>, i: usize) -> Option<LinkedList<Moves>> {
        println!("SOLVE: i = {}, doc[i] = {}, from = ({},{}), from(re) = {}",
            i, doc.get(i).map(|a|a.to_string()).unwrap_or("NaN".to_string()), from.0, from.1.index(), self.hg[from.0][from.1]);

        // Acceptance criteria
        if self.is_accepting(from) && !self.is_end_anchored(from) {
            return Some(LinkedList::from([LinkedList::from([(from, i)])]));
        } else if self.is_accepting(from) && (i == doc.len()) {
            return Some(LinkedList::from([LinkedList::from([(from, i)])]));
        } else if i == doc.len() {
            return None;
        }
        if self.is_jump_pad(from) {
            // All the children are jumps
            let paths_opt: Vec<Option<LinkedList<Moves>>> =
              self.hg[from.0]
                .edges(from.1)
                .filter(|e| e.target() != from.1)
                .map(|e| match self.hg[from.0][e.target()].0 {
                    Err(ref jmp) => self.solve_jump(jmp, doc, i),
                    Ok(_) => panic!("Invariant: Jumping pad {} should not have derivative {}",
                                        self.hg[from.0][from.1],
                                        self.hg[from.0][e.target()])
                }).collect();
            // All jumps must successfully match
            if paths_opt.iter().all(Option::is_some) {
                Some(paths_opt.into_iter().flat_map(Option::unwrap).collect())
            } else {
                None
            }
        } else {
            // All the children are derivative steps
            let mut paths: LinkedList<Moves> =
              self.hg[from.0]
                .edges(from.1)
                .find(|e| e.weight().as_ref() == Some(&doc[i]))
                .and_then(|e| self.solve_rec((from.0, e.target()), doc, i+1))?;

            for path in paths.iter_mut() {
                path.push_front((from,i))
            }
            Some(paths)
        }
    } */
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

    #[test]
    fn test_snfa() {
        let r = Regex::new("(?=b)(?=a?)(baa|.*b)(.?){1,2}");
        let safa = SAFA::new("ab", &r);
        safa.as_str_snfa().write_pdf("safa").unwrap();
        let strdoc = "baaaaab";
        let doc = strdoc.chars().collect();

        println!("DELTAS");
        for d in safa.deltas() {
           println!("{:?}", d);
        }
        println!("SOLUTION for: {}", strdoc);
        println!("{:?}", safa.solve(&doc));
    }

}

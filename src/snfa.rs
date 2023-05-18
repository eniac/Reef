use itertools::Itertools;
use std::collections::{HashSet, LinkedList};
use std::process::Command;

use petgraph::Graph;
use petgraph::graph::NodeIndex;
use petgraph::dot::Dot;
use petgraph::visit::*;

use printpdf::*;
use std::fs::File;
use std::io::BufWriter;
use std::result::Result;

use crate::regex::{Regex, RegexF, JumpType};
use crate::nfa::EPSILON;
use rayon::iter::*;

use core::fmt;
use core::fmt::{Display,Formatter};

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Jump(JumpType, usize);

#[derive(Debug, Clone)]
pub struct SNFA<C: Clone> {
    /// Alphabet
    pub ab: Vec<C>,

    /// A hypergraph
    pub hg: Vec<Graph<Either<Regex, Jump>, Option<C>>>,
}

impl Display for Jump {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "Jump({} -> {})", self.0, self.1)
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Either<A,B>(Result<A, B>);

impl<A,B> Either<A,B> {
    fn left(a: A) -> Self {
        Either(Ok(a))
    }
    fn right(b: B) -> Self {
        Either(Err(b))
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

type Coord = (usize, NodeIndex<u32>);

impl SNFA<char> {

    pub fn new<'a>(alphabet: &'a str, re: &Regex) -> Self {
        let ab = alphabet.chars().sorted().collect();
        let mut s = Self {
            ab,
            hg: Vec::new(),
        };
        let n = s.add_re(0, re.clone());
        s.build((0, n), re.clone());
        s
    }

    pub fn build_deriv(&mut self, from: Coord, q: Regex) {
        // Take all the single character steps
        for c in self.ab.clone() {
            let q_c = q.deriv(&c);
            if let Some(n_c) = self.find_re(from.0, &q_c) {
                // State [q_c] exists already, add edge
                self.hg[from.0].add_edge(from.1, n_c, Some(c));
            } else if let Some(n_o) = self.find_edge_endpoint(from, c) {
                // State[q_c] is new, but if transition from q-[c]> n_o exists
                let mw_o = self.hg[from.0].node_weight_mut(n_o)
                            .expect("Getting mutable reference to [n_o]");
                let re_o = mw_o.0.clone()
                            .expect("Expecting a regex from a char transition");
                let new_re = Regex::alt(re_o, q_c);
                *mw_o = Either::left(new_re.clone());
                self.build((from.0, n_o), new_re);
            } else {
                // Add to NFA if not already there
                let n_c = self.add_re(from.0, q_c.clone());
                // Reflexive step
                self.hg[from.0].add_edge(from.1, n_c, Some(c));
                self.build((from.0, n_c), q_c);
            }
        }
    }

    /// Mutually recursive, build hypergraph
    pub fn build(&mut self, from: Coord, q: Regex) {
        let ab = &self.ab;
        match *q.0 {
            // .*
            RegexF::Star(ref a) if a.accepts_any(ab) =>
                self.add_jump(from, JumpType::Star, Regex::nil()),
            // .{i,j}
            RegexF::Range(ref a, x, y) if a.accepts_any(ab) && !a.nullable() =>
                self.add_jump(from, JumpType::range(x, y), Regex::nil()),
            // (?=r)
            RegexF::Lookahead(ref a) =>
                self.add_jump(from, JumpType::Offset(0), a.clone()),
            RegexF::Alt(ref a, ref b) => {
                self.build(from, a.clone());
                self.build(from, b.clone());
            },
            RegexF::App(ref a, ref b) => {
                match *a.0 {
                    // .*r
                    RegexF::Star(ref a) if a.accepts_any(ab) =>
                        self.add_jump(from, JumpType::Star, b.clone()),
                    // .{i,j}r
                    RegexF::Range(ref a, x, y) if a.accepts_any(ab) =>
                        self.add_jump(from, JumpType::range(x, y), b.clone()),
                    // (?=r1)r2
                    RegexF::Lookahead(ref a) => {
                        self.add_jump(from, JumpType::Offset(0), a.clone());
                        self.add_jump(from, JumpType::Offset(0), b.clone());
                    },
                    RegexF::Alt(ref x, ref y) => {
                        self.build(from, x.clone());
                        self.build(from, y.clone());
                        self.build(from, b.clone());
                    },
                    // Re-associate [app] right if needed
                    RegexF::App(ref x, ref y) =>
                        self.build(from, Regex::app(x.clone(), Regex::app(y.clone(), b.clone()))),
                    // Some other kind of app, use derivatives
                    _ => self.build_deriv(from, q)
                }},
            // Other (derivative)
            _ => self.build_deriv(from, q)
        }
    }

    /// Add a jump node to the graph at position [Coord]
    pub fn add_jump(&mut self, from: Coord, jt: JumpType, re: Regex) {
        // the new graph is hg[m]
        let m = self.hg.len();
        let root = (m, self.add_re(m, re.clone()));
        // Add the jump hg[from.0] -> hg[m]
        let n_jmp = self.hg[from.0].add_node(Either::right(Jump(jt, m)));
        self.hg[from.0].add_edge(from.1, n_jmp, None);
        // Recursively build the new graph hg[m]
        self.build(root, re);
    }

    /// From SNFA<char> -> SNFA<String>
    pub fn as_str_snfa(&self) -> SNFA<String> {
        SNFA {
            ab: self.ab.iter().map(|c| c.to_string()).collect(),
            hg: self.hg.iter()
                    .map(|g| g.map(|_, b| b.clone(),
                        |_,e| e.map(|c| c.to_string())))
                    .collect::<Vec<Graph<Either<Regex, Jump>, Option<String>>>>(),
        }
    }
}

type Moves = LinkedList<(Coord, usize)>;

impl<C: Clone + Eq + Ord + std::fmt::Debug + Display + std::hash::Hash + Sync> SNFA<C> {
    pub fn add_re(&mut self, i: usize, re: Regex) -> NodeIndex<u32> {
        while i >= self.hg.len() {
            self.hg.push(Graph::new());
        }
        let n_k = self.hg[i].add_node(Either::left(re));
        self.hg[i].add_edge(n_k, n_k, None);
        n_k
    }

    pub fn is_start_anchored(&self, from: Coord) -> bool {
        match self.hg[from.0][from.1].0 {
            Ok(ref re) => re.is_start_anchored(),
            Err(Jump(_, ref to)) => self.is_start_anchored((*to, NodeIndex::new(0)))
        }
    }

    pub fn is_end_anchored(&self, from: Coord) -> bool {
        match self.hg[from.0][from.1].0 {
            Ok(ref re) => re.is_end_anchored(),
            Err(Jump(_, ref to)) => self.is_end_anchored((*to, NodeIndex::new(0)))
        }
    }


    /// Find regular expression in graph [i]
    pub fn find_re(&self, i: usize, re: &Regex) -> Option<NodeIndex<u32>> {
        self.hg[i].node_indices().find(|x| self.hg[i][*x].0 == Ok(re.clone()))
    }

    /// If an edge [c] exists from [from] returns the other endpoint
    pub fn find_edge_endpoint(&self, from: Coord, c: C) -> Option<NodeIndex<u32>> {
        self.hg[from.0].edges(from.1)
            .find_map(|e| if e.weight().as_ref() == Some(&c) { Some(e.target()) } else { None })
    }

    fn deltas_one_step(&self, from: Coord) -> HashSet<(Coord, Option<C>, Coord, Option<JumpType>)> {
        match self.hg[from.0][from.1].0 {
            Err(Jump(ref j1, next)) => {
                self.deltas_one_step((next, NodeIndex::new(0)))
                    .into_iter()
                    .map(|(a,w,b,j)| match j {
                        Some(j2) => (a,w,b,Some(j1.then(&j2))),
                        None => (a,w,b,Some(j1.clone()))
                    }).collect()
            },
            Ok(_) =>
                Some((from, None, from, None))
                    .into_iter()
                    .chain(self.hg[from.0]
                            .edges(from.1) // epsilon transitions
                            .filter(|e| e.target() != from.1 && e.weight().is_none())
                            .flat_map(|e| self.deltas_one_step((from.0, e.target())))
                            .map(|(_, w, x, j)| (from, w, x, j))
                    ).chain(self.hg[from.0]
                            .edges(from.1) // Non-epsilon transitions
                            .filter(|e| e.target() != from.1 && e.weight().is_some())
                            .map(|e| (from, e.weight().clone(), (from.0, e.target()), None))
                    ).collect::<HashSet<_>>()
        }
    }

    pub fn deltas(&self) -> Vec<(Coord, Option<C>, Coord, Option<JumpType>)> {
        let mut i: usize = 0;
        let mut res: HashSet<(Coord, Option<C>, Coord, Option<JumpType>)> = HashSet::new();

        for g in self.hg.iter() {
            for j in g.node_indices() {
                if let Ok(_) = g[j].0.clone() {
                    for x in self.deltas_one_step((i, j)) {
                        res.insert(x);
                    }
                }
            }
            i += 1;
        }
        res.into_iter().sorted().collect()
    }

    /// Is this a state with jumps
    pub fn is_jump_pad(&self, from: Coord) -> bool {
        self.hg[from.0].edges(from.1)
                       .filter(|e| e.target() != from.1)
                       .all(|e| self.hg[from.0][e.target()].0.is_err() && e.weight().is_none())
    }

    /// Is this a state with derivatives
    pub fn is_deriv_pad(&self, from: Coord) -> bool {
        self.hg[from.0].edges(from.1)
                       .filter(|e| e.target() != from.1)
                       .all(|e| self.hg[from.0][e.target()].0.is_ok() && e.weight().is_some())
    }

    /// Return a vector of (NFA id, node) of all accepting states
    pub fn accepting(&self) -> Vec<Coord> {
        let mut i: usize = 0;
        let mut res: Vec<Coord> = Vec::new();

        for g in self.hg.iter() {
            for j in g.node_indices() {
                if let Ok(re) = g[j].0.clone() {
                    if re.nullable() {
                        res.push((i, j))
                    }
                }
            }
            i += 1;
        }
        res
    }

    pub fn get_init(&self) -> Coord {
        (0, NodeIndex::new(0))
    }

    pub fn get_node(&self, i: Coord) -> Result<Regex, Jump> {
        self.hg[i.0][i.1].0.clone()
    }

    /// Match the SNFA on a document (backtracking)
    pub fn solve(&self, doc: &Vec<C>) -> LinkedList<Moves> {
        self.solve_rec((0, NodeIndex::new(0)), doc, 0).unwrap_or(LinkedList::new())
    }

    /// Is the state [from] accepting
    fn is_accepting(&self, from: Coord) -> bool {
        match self.hg[from.0][from.1].0.clone() {
            Ok(re) if re.nullable() => true,
            Err(Jump(JumpType::Offset(offset), nfa_dest)) if offset == 0 =>
                self.is_accepting((nfa_dest, NodeIndex::new(0))),
            Err(Jump(JumpType::Choice(offsets), nfa_dest)) if offsets.contains(&0) =>
                self.is_accepting((nfa_dest, NodeIndex::new(0))),
            Err(Jump(JumpType::Star, nfa_dest)) =>
                self.is_accepting((nfa_dest, NodeIndex::new(0))),
            _ => false
        }
    }

    fn solve_jump(&self, jmp: &Jump, doc: &Vec<C>, i: usize) -> Option<LinkedList<Moves>> {
        match jmp {
            Jump(JumpType::Offset(offset), nfa_dest) =>
                self.solve_rec((*nfa_dest, NodeIndex::new(0)), doc, i + offset),
            Jump(JumpType::Choice(offsets), nfa_dest) =>
                // Parallelize this
                offsets.into_par_iter()
                       .filter(|&o| i + o < doc.len())
                       .find_map_any(|o| self.solve_rec((*nfa_dest, NodeIndex::new(0)), doc, i + o)),
            Jump(JumpType::Star, nfa_dest) =>
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
    }
}

impl SNFA<String> {
    /// Write DOT -> PDF files for all graphs
    pub fn write_pdf(&self,  filename: &str) -> std::io::Result<()> {
        fn write_text_pdf(s: &String, f: &str) {
            let (doc, page1, layer1) = PdfDocument::new(s, Mm(210.0), Mm(297.0), "Layer 1");
            let current_layer = doc.get_page(page1).get_layer(layer1);

            // Add some text to the document
            let font = doc.add_builtin_font(BuiltinFont::HelveticaBold).unwrap();
            current_layer.set_font(&font, 32.0);
            current_layer.set_line_height(20.0);
            current_layer.use_text(s, 32.0, Mm(10.0), Mm(100.0), &font);
            current_layer.end_text_section();

            let file = File::create(f).unwrap();
            let mut buf_writer = BufWriter::new(file);
            doc.save(&mut buf_writer).unwrap();
        }

        let mut files: Vec<String> = Vec::new();
        let mut i = 0;
        for g in self.hg.iter() {
          let pg = g.map(|_, b| b.clone(),
                         |_, e| e.clone().unwrap_or(EPSILON.clone()));

          let s: String = Dot::new(&pg).to_string();
          let fdot = format!("{}-{}.dot", filename.to_string(), i);
          std::fs::write(fdot.clone(), s)?;

          let fpdf = format!("{}-{}.pdf", filename.to_string(), i);
          let ftxt = format!("text-{}-{}.pdf", filename.to_string(), i);

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

          write_text_pdf(&format!("Graph {}", i), &ftxt);
          files.push(ftxt);
          files.push(fpdf);
          i += 1;
        }

        let fout = format!("{}.pdf", filename.to_string());
        Command::new("pdfjam")
            .args(files.clone())
            .arg("-o")
            .arg(fout.clone())
            .spawn()
            .expect("[dot] CLI failed to convert dfa to [pdf] file")
            .wait()?;

        println!("Wrote PDF file {}.", fout);
        for fout in files.clone() {
            std::fs::remove_file(fout)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::snfa::SNFA;
    use crate::regex::Regex;

    #[test]
    fn test_snfa() {
        let r = Regex::new("((?=b)(?=.))b.{1,2}ab");
        let snfa = SNFA::new("ab", &r);
        snfa.as_str_snfa().write_pdf("snfa").unwrap();
        let doc = "baab".chars().collect();
        let sol = snfa.solve(&doc);
        println!("DELTAS");
        for d in snfa.deltas() {
            println!("{:?}", d);
        }
        println!("SOLUTION: ");
        for s in sol {
            println!("{:?}", s);
        }
    }

}

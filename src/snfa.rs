use itertools::Itertools;
use std::collections::{BTreeSet, HashMap, HashSet};
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

    /// A hypergraph?
    pub hg: Vec<Graph<Either<Regex, Jump>, Option<C>>>,

    /// Must match from the begining of the document (default: false)
    anchor_start: bool,

    /// Must match until the end of the document (default: false)
    anchor_end: bool,
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
            anchor_start: re.is_start_anchored(),
            anchor_end: re.is_end_anchored()
        };
        let n = s.add_re(0, re.clone());
        s.build((0, n), re.clone());
        s
    }


    pub fn add_re(&mut self, i: usize, re: Regex) -> NodeIndex<u32> {
        while i >= self.hg.len() {
            self.hg.push(Graph::new());
        }
        let n_k = self.hg[i].add_node(Either::left(re));
        self.hg[i].add_edge(n_k, n_k, None);
        n_k
    }

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

    pub fn find_re(&self, i: usize, re: &Regex) -> Option<NodeIndex<u32>> {
        self.hg[i].node_indices().find(|x| self.hg[i][*x].0 == Ok(re.clone()))
    }

    pub fn build_deriv(&mut self, from: Coord, q: Regex) {
        // Take all the single character steps
        for c in self.ab.clone() {
            let q_c = q.deriv(&c);
            // State [q_c] exists already, add edge
            if let Some(n_c) = self.find_re(from.0, &q_c) {
                self.hg[from.0].add_edge(from.1, n_c, Some(c));
            } else {
                // Add to NFA if not already there
                let n_c = self.add_re(from.0, q_c.clone());
                // Reflexive step
                self.hg[from.0].add_edge(n_c, n_c, None);
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
            RegexF::Range(ref a, x, y) if a.accepts_any(ab) =>
                self.add_jump(from, JumpType::range(x, y), Regex::nil()),
            // (?=r)
            RegexF::Lookahead(ref a) =>
                self.add_jump(from, JumpType::Offset(0), a.clone()),
            RegexF::Alt(ref a, ref b) => {
                self.build(from, a.clone());
                self.build(from, b.clone());
            },
            RegexF::App(ref a, ref b) => {
                println!("Now exploring {:?}", a);
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
                        self.build(from, b.clone())
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

    /// Return a vector of (NFA id, node, Dest NFA id) of all jumps
    pub fn jumps(&self) -> Vec<Coord> {
        let mut i: usize = 0;
        let mut res: Vec<Coord> = Vec::new();

        for g in self.hg.iter() {
            for j in g.node_indices() {
                if let Err(Jump(_, dst)) = g[j].0 {
                    res.push((i, j));
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

    pub fn as_str_snfa(&self) -> SNFA<String> {
        SNFA {
            ab: self.ab.iter().map(|c| c.to_string()).collect(),
            hg: self.hg.iter()
                    .map(|g| g.map(|_, b| b.clone(),
                        |_,e| e.map(|c| c.to_string())))
                    .collect::<Vec<Graph<Either<Regex, Jump>, Option<String>>>>(),
            anchor_start: self.anchor_start,
            anchor_end: self.anchor_end
        }
    }
    /// All epsilon adjacent states outgoing from [from], including [from]
    fn epsilons_rec(&self, from: Coord, visited: &mut HashSet<Coord>) -> HashSet<Coord> {
        if visited.contains(&from) {
            return HashSet::from([from.clone()]);
        }

        self.hg[from.0]
            .edges(from.1)
            .filter(|e| *e.weight() == None)
            .flat_map(|e| {
                visited.insert((from.0, e.target()));
                self.epsilons_rec((from.0, e.target()), visited)
            }).collect()
    }

    /*
    /// Starting at [from] and [i] position of [doc], take a single non-det step
    fn delta_rec(&self, from: Coord, doc: &Vec<String>, i: usize, visited: &mut HashSet<Coord>) -> HashSet<Vec<Coord>> {
        if visited.contains(&from) {
            return HashSet::new();
        }
        let mut from_set = self.epsilons_rec(from, &mut visited);
        // all of these need to match
        from_set.into_iter().map(|from| {
            visited.insert(from);
            match self.hg[from.0][from.1].0 {
                // A normal character transition, consume the character in this NFA
                Ok(_) => self.hg[from.0]
                          .edges(from.1)
                          .filter(|e| e.weight() == &doc[i])
                          .map(|e| (from.0, e.target()))
                          .collect::<Vec<Coord>>(),
                // A jump
                Err(Jump(JumpType::Offset(offset), nfa_dest)) =>
                    self.delta_rec((nfa_dest, NodeIndex::new(0)), doc, i + offset, visited),
                Err(Jump(JumpType::Choice(offsets), nfa_dest)) =>
                    // At least one of these needs to match
                    offsets.into_iter().flat_map(|offset| self.delta_rec((nfa_dest, NodeIndex::new(0)), doc, i + offset, visited)),
                Err(Jump(JumpType::Star, nfa_dest)) =>
                    // At least one of these needs to match
                    (i..doc.len()).flat_map(|i| self.delta_rec((nfa_dest, NodeIndex::new(0)), doc, i, visited))
            }
        })
    } */
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
        let r = Regex::new("((?=b)(?=.)|.{5})a(?=ba).{4,10}ab");
        let snfa = SNFA::new("ab", &r);
        snfa.as_str_snfa().write_pdf("snfa").unwrap();
    }

}

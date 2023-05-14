use itertools::Itertools;
use std::collections::{BTreeSet, HashMap, HashSet};
use std::process::Command;

use petgraph::{Direction, Graph};
use petgraph::graph::NodeIndex;
use petgraph::dot::Dot;

use printpdf::*;
use std::fs::File;
use std::io::BufWriter;
use std::result::Result;

use crate::regex::{Regex, JumpType};
use crate::nfa::EPSILON;

use core::fmt;
use core::fmt::{Display,Formatter};

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Jump(JumpType, usize);

#[derive(Debug, Clone)]
pub struct SNFA {
    /// Alphabet
    pub ab: Vec<String>,

    /// A hypergraph?
    pub hg: Vec<Graph<Either<Regex, Jump>, String>>,

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

impl SNFA {
    pub fn new<'a>(alphabet: &'a str, re: Regex) -> Self {
        let ab = alphabet.chars().sorted().collect();

        fn get_next(r: &Regex, ab: &Vec<char>) -> Either<Vec<(char, Regex)>,(JumpType, Option<Regex>, Regex)> {
            if let Some((j, k, c)) = r.split(ab) {
                Either::right((j, k, c))
            } else {
                let mut v: Vec<(char, Regex)> = Vec::with_capacity(ab.len());
                for c in &ab[..] {
                    let q_c = r.deriv(&c);
                    v.push((*c, q_c));
                }
                Either::left(v)
            }
        }

        fn build_hg(
            hg: &mut Vec<Graph<Either<Regex, Jump>, String>>,
            ab: &Vec<char>,
            i: usize,
            j: NodeIndex<u32>,
            q: &Regex) {
        println!("========= HG {:#?}", hg);
            match get_next(q, ab).0 {
              Ok(ds) => // Take all the single character steps
                for (c, q_c) in ds {
                    if let Some(n_c) = hg[i].node_indices().find(|x| hg[i][*x].0 == Ok(q_c.clone())) {
                        hg[i].add_edge(j, n_c, c.to_string());
                    } else {
                        // Add to DFA if not already there
                        let n_c = hg[i].add_node(Either::left(q_c.clone()));
                        // Reflexive step
                        hg[i].add_edge(n_c, n_c, EPSILON.clone());
                        println!("J {:?}", j);
                        hg[i].add_edge(j, n_c, c.to_string());
                        build_hg(hg, ab, i, n_c, &q_c);
                    }
                },
              Err((jmp, kopt, c)) => { // Jump ahead
                let mut cg: Graph<Either<Regex,Jump>, String> = Graph::new();
                let n_c = cg.add_node(Either::left(c.clone()));
                cg.add_edge(n_c, n_c, EPSILON.clone());
                // Add [jmp] to [g]
                let m = hg.len();
                let n_jmp = hg[i].add_node(Either::right(Jump(jmp, m)));
                hg[i].add_edge(j, n_jmp, EPSILON.clone());
                // The landing pad [cg]
                hg.push(cg);
                build_hg(hg, ab, m, n_c, &c);
                if let Some(k) = kopt {
                    build_hg(hg, ab, i, j, &k);
                }
              },
            }
        }

        let mut hg: Vec<Graph<Either<Regex, Jump>, String>> = Vec::new();
        hg.push(Graph::new());
        let n = hg[0].add_node(Either::left(re.clone()));
        hg[0].add_edge(n, n, EPSILON.clone());
        // Recursively build transitions
        build_hg(&mut hg, &ab, 0, n, &re);

        // Return DFA
        Self {
            ab: ab.into_iter().map(|c| c.to_string()).collect(),
            hg,
            anchor_start: re.is_start_anchored(),
            anchor_end: re.is_end_anchored(),
        }
    }

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
          let s: String = Dot::new(&g).to_string();
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
        let r = Regex::new(".*a.*b");
        let snfa = SNFA::new("ab", r);
        snfa.write_pdf("snfa").unwrap();
        println!("SNFA {:#?}", snfa);
    }
}

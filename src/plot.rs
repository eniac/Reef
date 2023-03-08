use itertools::Itertools;
use std::fmt::{Display, Error, Formatter};
use std::fs::File;
use std::process::{Command, ExitStatus};
use std::io::Result;

use crate::dfa::DFA;
use crate::parser::re::Regex;

type Ed = (Regex, Vec<char>, Regex);

#[cfg(feature = "plot")]
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
    fn node_style(&'a self, n: &Regex) -> dot::Style {
        let init = self.get_init_state();
        let finals = self.get_final_states();
        let s = self.get_state_num(&n);
        if s == init && finals.contains(&s) {
            dot::Style::Filled
        } else if finals.contains(&s) {
            dot::Style::Bold
        } else if s == init {
            dot::Style::Dashed
        } else {
            dot::Style::None
        }
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

#[cfg(feature = "plot")]
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

#[cfg(feature = "plot")]
pub fn plot_dfa<'a>(dfa: &'a DFA) -> Result<ExitStatus> {
    let dotfile = "dfa.dot";

    // Output file
    let mut buffer = File::create(dotfile).unwrap();

    // render .dot file
    dot::render(dfa, &mut buffer).unwrap();
    println!("Wrote DOT file {}.", dotfile);

    // Convert to pdf
    let mut child = Command::new("dot")
                        .arg("-Tpdf")
                        .arg(dotfile)
                        .arg("-o")
                        .arg("dfa.pdf")
                        .spawn()
                        .expect("[dot] CLI failed to convert dfa to [pdf] file");
    child.wait()
}

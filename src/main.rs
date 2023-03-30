#![allow(missing_docs, non_snake_case)]
type G1 = pasta_curves::pallas::Point;
type G2 = pasta_curves::vesta::Point;
use clap::{Args, Parser, Subcommand};
use std::time::{Duration, Instant};

pub mod backend;
pub mod config;
pub mod dfa;
pub mod regex;

use crate::backend::{framework::*, r1cs::init};
use crate::config::*;
use crate::dfa::NFA;

#[cfg(feature = "plot")]
pub mod plot;

fn main() {
    let p_time = Instant::now();
    let opt = Options::parse();

    // Alphabet
    let ab = String::from_iter(opt.config.alphabet());

    // Regular expresion parser and convert the Regex to a DFA
    let nfa = opt.config.compile_nfa();
    println!("dfa: {:#?}", nfa);

    // Input document
    let doc: Vec<String> = opt.config.read_doc().iter().map(|c|c.to_string()).collect();

    #[cfg(feature = "plot")]
    plot::plot_nfa(&nfa).expect("Failed to plot DFA to a pdf file");

    let num_steps = doc.len();
    println!("Doc len is {}", num_steps);

    init();

    run_backend(&nfa, &doc, opt.eval_type, opt.commit_type, opt.batch_size); // auto select batching/commit

    //println!("parse_ms {:#?}, commit_ms {:#?}, r1cs_ms {:#?}, setup_ms {:#?}, precomp_ms {:#?}, nova_ms {:#?},",parse_ms, commit_ms, r1cs_ms, setup_ms, precomp_ms, nova_ms);
}

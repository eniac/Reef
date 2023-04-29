#![allow(missing_docs, non_snake_case)]
use clap::{Args, Parser};
use std::time::{Duration, Instant};

use reef::backend::{framework::*, r1cs_helper::init};
use reef::config::*;

#[cfg(feature = "plot")]
use reef::plot;

use reef::dfa::NFA;

fn main() {
    let p_time = Instant::now();
    let opt = Options::parse();

    // Alphabet
    let ab = String::from_iter(opt.config.alphabet());

    // Regular expresion parser and convert the Regex to a DFA
    let mut doc = opt
        .config
        .read_file(&opt.input)
        .iter()
        .map(|c| c.to_string())
        .collect();

    // Input document
    let mut nfa = NFA::new(&ab, opt.re);

    // Try to use k-stride
    opt.k_stride.map(|k| {
        doc = nfa.k_stride(k, &doc);
    });

    // Is document well-formed
    nfa.well_formed(&doc);

    println!("NFA: {:#?}", nfa);

    #[cfg(feature = "plot")]
    plot::plot_nfa(&nfa).expect("Failed to plot NFA to a pdf file");

    println!("Doc len is {}", doc.len());
    println!(
        "Match: {}",
        nfa.is_match(&doc)
            .map(|c| format!("{:?}", c))
            .unwrap_or(String::from("NONE"))
    );
    init();

    run_backend(&nfa, &doc, opt.eval_type, opt.commit_type, opt.batch_size); // auto select batching/commit

    //println!("parse_ms {:#?}, commit_ms {:#?}, r1cs_ms {:#?}, setup_ms {:#?}, precomp_ms {:#?}, nova_ms {:#?},",parse_ms, commit_ms, r1cs_ms, setup_ms, precomp_ms, nova_ms);
}

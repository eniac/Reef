#![allow(missing_docs, non_snake_case)]
use clap::Parser;

use reef::backend::{framework::*, r1cs_helper::init};
use reef::config::*;

#[cfg(feature = "metrics")]
use reef::metrics::{log, log::Component};

#[cfg(feature = "plot")]
use reef::plot;

use reef::dfa::NFA;

fn main() {
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

    #[cfg(feature = "metrics")]
    log::tic(Component::Compiler, "Compiler", "Full");

    #[cfg(feature = "metrics")]
    log::tic(Component::Compiler, "DFA", "DFA");

    let mut nfa = NFA::new(&ab, opt.re);

    #[cfg(feature = "metrics")]
    log::stop(Component::Compiler, "DFA", "DFA");

    // Try to use k-stride
    if let Some(k) = opt.k_stride {
        #[cfg(feature = "metrics")]
        log::tic(Component::Compiler, "DFA", "K Stride");

        doc = nfa.k_stride(k, &doc);

        #[cfg(feature = "metrics")]
        log::stop(Component::Compiler, "DFA", "K Stride");
    };

    // Is document well-formed
    nfa.well_formed(&doc);

    #[cfg(feature = "plot")]
    plot::plot_nfa(&nfa).expect("Failed to plot NFA to a pdf file");

    println!("Doc len is {}", doc.len());

    #[cfg(feature = "metrics")]
    log::tic(Component::Solver, "DFA Solving", "Clear Match");
    println!(
        "Match: {}",
        nfa.is_match(&doc)
            .map(|c| format!("{:?}", c))
            .unwrap_or(String::from("NONE"))
    );

    #[cfg(feature = "metrics")]
    log::stop(Component::Solver, "DFA Solving", "Clear Match");
    init();

    run_backend(
        nfa,
        doc,
        opt.eval_type,
        opt.commit_type,
        opt.batch_size
    ); // auto select batching/commit

    #[cfg(feature = "metrics")]
    log::write_csv(opt.output.to_str().unwrap()).unwrap();

    //println!("parse_ms {:#?}, commit_ms {:#?}, r1cs_ms {:#?}, setup_ms {:#?}, precomp_ms {:#?}, nova_ms {:#?},",parse_ms, commit_ms, r1cs_ms, setup_ms, precomp_ms, nova_ms);
}

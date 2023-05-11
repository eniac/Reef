#![allow(missing_docs, non_snake_case)]
use clap::Parser;

use reef::backend::{framework::*, r1cs_helper::init};
use reef::config::*;
use reef::regex::Regex;
use reef::nfa::NFA;
use csv::Writer;
use std::fs::OpenOptions;
use std::path::PathBuf;

#[cfg(feature = "metrics")]
use reef::metrics::{log, log::Component};

fn main() {
    let opt = Options::parse();

    // Alphabet
    let ab = String::from_iter(opt.config.alphabet());

    // Input document
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

    let mut nfa = NFA::new(&ab, Regex::new(&opt.re));

    // Is document well-formed
    nfa.well_formed(&doc);

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
    #[cfg(feature = "plot")]
    nfa.write_pdf("nfa").expect("Failed to plot NFA to a pdf file");

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
        nfa.clone(),
        doc,
        opt.eval_type,
        opt.commit_type,
        opt.batch_size
    ); // auto select batching/commit


    let file = OpenOptions::new().write(true).append(true).create(true).open(opt.output.clone()).unwrap();
    let mut wtr = Writer::from_writer(file);
    let _ = wtr.write_record(&[opt.input.as_path().display().to_string(),opt.re,nfa.nedges().to_string(),nfa.nstates().to_string()]);
    let spacer = "---------";
    let _ = wtr.write_record(&[spacer, spacer, spacer, spacer]);
    wtr.flush();
    #[cfg(feature = "metrics")]
    log::write_csv(opt.output.to_str().unwrap()).unwrap();

    //println!("parse_ms {:#?}, commit_ms {:#?}, r1cs_ms {:#?}, setup_ms {:#?}, precomp_ms {:#?}, nova_ms {:#?},",parse_ms, commit_ms, r1cs_ms, setup_ms, precomp_ms, nova_ms);
}

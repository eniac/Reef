#![allow(missing_docs, non_snake_case)]
use clap::Parser;

use reef::backend::{framework::*, r1cs_helper::init};
use reef::config::*;
use reef::metrics::*;

#[cfg(feature = "plot")]
use reef::plot;

use reef::dfa::NFA;

fn main() {
    let mut timer: Timer = Timer::new();
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

    timer.tic(Component::Compiler, "Compiler", "Full");
    timer.tic(Component::Compiler, "DFA", "DFA");
    let mut nfa = NFA::new(&ab, opt.re);
    timer.stop(Component::Compiler, "DFA", "DFA");

    // Try to use k-stride
    timer.tic(Component::Compiler, "DFA", "K Stride");
    opt.k_stride.map(|k| {
        doc = nfa.k_stride(k, &doc);
    });
    timer.stop(Component::Compiler, "DFA", "K Stride");

    // Is document well-formed
    nfa.well_formed(&doc);

    // println!("NFA: {:#?}", nfa);

    #[cfg(feature = "plot")]
    plot::plot_nfa(&nfa).expect("Failed to plot NFA to a pdf file");

    println!("Doc len is {}", doc.len());

    timer.tic(Component::Solver, "DFA Solving", "Clear Match");
    println!(
        "Match: {}",
        nfa.is_match(&doc)
            .map(|c| format!("{:?}", c))
            .unwrap_or(String::from("NONE"))
    );
    timer.stop(Component::Solver, "DFA Solving", "Clear Match");
    init();

    run_backend(
        &nfa,
        &doc,
        opt.eval_type,
        opt.commit_type,
        opt.batch_size,
        &mut timer,
    ); // auto select batching/commit

    if let Err(e) = timer.write_csv(opt.output.to_str().unwrap()) {
        eprintln!("Error writing to file: {}", e);
        panic!("exiting");
    }

    //println!("parse_ms {:#?}, commit_ms {:#?}, r1cs_ms {:#?}, setup_ms {:#?}, precomp_ms {:#?}, nova_ms {:#?},",parse_ms, commit_ms, r1cs_ms, setup_ms, precomp_ms, nova_ms);
}

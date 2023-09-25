#![allow(missing_docs, non_snake_case)]
use clap::Parser;
use csv::Writer;
use reef::backend::{framework::*, r1cs_helper::init};
use reef::config::*;
use reef::regex::re;
use reef::safa::SAFA;
// use reef::naive::*;
use std::fs::OpenOptions;
use std::path::Path;
use std::path::PathBuf;

#[cfg(all(not(windows), not(target_env = "musl")))]
#[global_allocator]
static ALLOC: jemallocator::Jemalloc = jemallocator::Jemalloc;

#[cfg(feature = "metrics")]
use reef::metrics::{log, log::Component};

fn main() {
    let opt = Options::parse();

    // Alphabet
    let ab = String::from_iter(opt.config.alphabet());

    // Input document
    let doc = if Path::exists(Path::new(&opt.input)) {
        opt.config
            .read_file(&PathBuf::from(&opt.input))
            .iter()
            .map(|c| c.clone()) //to_string())
            .collect()
    } else {
        opt.input.chars().collect()
    };

    #[cfg(feature = "metrics")]
    log::tic(Component::Compiler, "Compiler", "Full");

    #[cfg(feature = "metrics")]
    log::tic(Component::Compiler, "DFA", "DFA");

    let r = re::new(&opt.re);
    //    println!("REGEX: {:#?}", r));

    // Compile regex to SAFA
    let safa = if opt.negate {
        SAFA::new(&ab, &r).negate()
    } else {
        SAFA::new(&ab, &r)
    };

    // Is document well-formed
    // nfa.well_formed(&doc);

    #[cfg(feature = "metrics")]
    log::stop(Component::Compiler, "DFA", "DFA");

    #[cfg(feature = "plot")]
    safa.write_pdf("main")
        .expect("Failed to plot NFA to a pdf file");

    #[cfg(feature = "metrics")]
    log::tic(Component::Solver, "DFA Solving", "Clear Match");

    /*
    println!(
        "Match: {}",
        nfa.is_match(&doc)
            .map(|c| format!("{:?}", c))
            .unwrap_or(String::from("NONE"))
    );*/
    // TODO solving here, pass result to R1CS

    #[cfg(feature = "metrics")]
    log::stop(Component::Solver, "DFA Solving", "Clear Match");

    init();

    run_backend(safa.clone(), doc, opt.batch_size, opt.projections); // auto select batching/commit

    let file = OpenOptions::new()
        .write(true)
        .append(true)
        .create(true)
        .open(opt.output.clone())
        .unwrap();
    let mut wtr = Writer::from_writer(file);
    let _ = wtr.write_record(&[
        opt.input,
        opt.re,
        safa.g.edge_count().to_string(), //nedges().to_string(),
        safa.g.node_count().to_string(), //nstates().to_string(),
    ]);
    let spacer = "---------";
    let _ = wtr.write_record(&[spacer, spacer, spacer, spacer]);
    wtr.flush();
    #[cfg(feature = "metrics")]
    log::write_csv(opt.output.to_str().unwrap()).unwrap();

    //println!("parse_ms {:#?}, commit_ms {:#?}, r1cs_ms {:#?}, setup_ms {:#?}, precomp_ms {:#?}, nova_ms {:#?},",parse_ms, commit_ms, r1cs_ms, setup_ms, precomp_ms, nova_ms);
}

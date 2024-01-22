#![allow(missing_docs, non_snake_case)]
use clap::Parser;
use csv::Writer;
use reef::backend::{framework::*, r1cs_helper::init};
use reef::config::*;
use reef::frontend::regex::re;
use reef::frontend::safa::SAFA;
use std::fs::OpenOptions;
use std::path::Path;
use std::path::PathBuf;
use std::time::SystemTime;

#[cfg(feature = "metrics")]
use metrics::metrics::{log, log::Component};

fn main() {
    let opt = Options::parse();

    // Alphabet
    let ab = String::from_iter(opt.config.alphabet());

    // Input document
    let doc: Vec<char> = if Path::exists(Path::new(&opt.input)) {
        opt.config
            .read_file(&PathBuf::from(&opt.input))
            .iter()
            .map(|c| c.clone())
            .collect()
    } else {
        opt.input.chars().collect()
    };
    println!("reef");

    #[cfg(feature = "metrics")]
    log::tic(Component::Compiler, "regex_normalization");

    let r = re::simpl(re::new(&opt.re));

    #[cfg(feature = "metrics")]
    {
        log::stop(Component::Compiler, "regex_normalization");
        log::tic(Component::Compiler, "fa_builder");
    }

    // Compile regex to SAFA
    let safa = if opt.negate {
        SAFA::new(&ab, &r).negate()
    } else {
        SAFA::new(&ab, &r)
    };

    // Is document well-formed
    // nfa.well_formed(&doc);

    #[cfg(feature = "metrics")]
    log::stop(Component::Compiler, "fa_builder");

    #[cfg(feature = "plot")]
    safa.write_pdf("main")
        .expect("Failed to plot NFA to a pdf file");

    init();

    let file = OpenOptions::new()
        .write(true)
        .append(true)
        .create(true)
        .open(opt.output.clone())
        .unwrap();
    let mut wtr = Writer::from_writer(file);
    let mut title = opt.input.clone();
    if title.len() > 10 {
        title = title[..10].to_string();
    }
    let test_type;
    if opt.hybrid | opt.projections {
        test_type = "reef";
    } else {
        test_type = "safa+nlookup";
    };
    let _ = wtr.write_record(&[
        format!("{}_{}", title, doc.len()),
        test_type.to_string(),
        SystemTime::now()
            .duration_since(SystemTime::UNIX_EPOCH)
            .unwrap()
            .as_secs()
            .to_string(),
        opt.re,
        safa.g.edge_count().to_string(), //nedges().to_string(),
        safa.g.node_count().to_string(), //nstates().to_string(),
    ]);
    let spacer = "---------";
    let _ = wtr.write_record(&[spacer, spacer, spacer, spacer, "\n"]);
    let _ = wtr.flush();
    #[cfg(feature = "metrics")]
    log::write_csv(opt.output.to_str().unwrap()).unwrap();

    let hybrid_len = None; // TODO!! JESS
    let (reef_commit, sc, udoc) = run_committer(&doc, &ab, hybrid_len, opt.merkle);

    let (compressed_snark, proof_info, consist_proof) = run_prover(
        reef_commit,
        sc,
        safa,
        doc,
        udoc,
        opt.batch_size,
        opt.projections,
        opt.hybrid,
        opt.merkle,
        Some(opt.output.clone()),
    );
    run_verifier(compressed_snark, proof_info, consist_proof);
}

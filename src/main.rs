#![allow(missing_docs, non_snake_case)]
use clap::Parser;
use csv::Writer;
use reef::backend::{framework::*, r1cs_helper::init};
use reef::config::*;
use reef::frontend::regex::re;
use reef::frontend::safa::SAFA;
use reef::naive::naive;
use reef::naive::naive_wr;
// use reef::naive::*;
use std::fs::OpenOptions;
use std::path::Path;
use std::path::PathBuf;

// #[cfg(all(not(windows), not(target_env = "musl")))]
// #[global_allocator]
// static ALLOC: jemallocator::Jemalloc = jemallocator::Jemalloc;

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
            .map(|c| c.clone()) //to_string())
            .collect()
    } else {
        opt.input.chars().collect()
    };

    #[cfg(feature = "nwr")]
    naive_wr::naive_bench(opt.re, ab, doc.iter().collect::<String>(), opt.output);

    #[cfg(feature = "naive")]
    naive::naive_bench(opt.re, ab, doc.iter().collect::<String>(), opt.output);

    #[cfg(feature = "reef")]
    {
        println!("reef");
        #[cfg(feature = "metrics")]
        log::tic(Component::Compiler, "Compiler", "Full");

        #[cfg(feature = "metrics")]
        log::tic(Component::Compiler, "SAFA", "SAFA");

        let r = re::simpl(re::new(&opt.re));
        println!("make r");

        // Compile regex to SAFA
        let safa = if opt.negate {
            SAFA::new(&ab, &r).negate()
        } else {
            SAFA::new(&ab, &r)
        };
        println!("make safa");
        println!("safa states: {}",safa.num_states());
        println!("safa size: {}", safa.num_edges());

        // Is document well-formed
        // nfa.well_formed(&doc);

        #[cfg(feature = "metrics")]
        log::stop(Component::Compiler, "SAFA", "SAFA");

        #[cfg(feature = "plot")]
        safa.write_pdf("main")
            .expect("Failed to plot NFA to a pdf file");

        #[cfg(feature = "metrics")]
        log::tic(Component::Solver, "SAFA Solving", "Clear Match");

        /*
            println!(
            "Match: {}",
            nfa.is_match(&doc)
                .map(|c| format!("{:?}", c))
                .unwrap_or(String::from("NONE"))
        );*/

        #[cfg(feature = "metrics")]
        log::stop(Component::Solver, "SAFA Solving", "Clear Match");

        init();

        run_backend(
            safa.clone(),
            doc.clone(),
            opt.batch_size,
            opt.projections,
            opt.hybrid,
        );

        let file = OpenOptions::new()
            .write(true)
            .append(true)
            .create(true)
            .open(opt.output.clone())
            .unwrap();
        let mut wtr = Writer::from_writer(file);
        let mut title = opt.input.clone();
        if title.len() > 10 {
            title = opt.input[..10].to_string();
        }
        let _ = wtr.write_record(&[
            format!("{}_{}", &title, doc.len()),
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
}

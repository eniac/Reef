#![allow(missing_docs, non_snake_case)]

use clap::Parser;
use csv::Writer;
use reef::backend::{commitment::ReefCommitment, framework::*, r1cs_helper::init};
use reef::config::*;
use reef::frontend::regex::re;
use reef::frontend::safa::SAFA;
use std::fs;
use std::fs::OpenOptions;
use std::path::Path;
use std::path::PathBuf;
use std::time::SystemTime;
use reef::naive::naive;
use reef::naive::naive_wr;

#[cfg(feature = "metrics")]
use metrics::metrics::{log, log::Component};

fn main() {
    let opt = Options::parse();
    println!("reef");

    // read alphabet
    let config = opt.config.expect("No alphabet found");
    let ab = String::from_iter(config.alphabet());

    if opt.baselines{
        let doc_string = opt.doc.as_ref().expect("No document found");
        let doc = read_doc(&doc_string, &config);
        #[cfg(feature = "nwr")]
        naive_wr::naive_bench(opt.re, ab, doc.iter().collect::<String>(), opt.output,opt.batch_size.clone());
        
        #[cfg(feature = "naive")]
        naive::naive_bench(opt.re, ab, doc.iter().collect::<String>(), opt.output);
    } else {
        if opt.e2e || opt.commit {
            // read doc
            let doc_string = opt.doc.as_ref().expect("No document found");
            let doc = read_doc(&doc_string, &config);

            #[cfg(feature = "metrics")]
            metrics_file(opt.metrics.clone(), opt.hybrid, opt.projections, doc_string);

            let reef_commit = run_committer(&doc, &ab, opt.merkle);

            // write commitment
            let cmt_data = bincode::serialize(&reef_commit).expect("Could not serialize");
            fs::write(get_name(opt.cmt_name.clone(), &doc_string, true), cmt_data)
                .expect("Unable to write file");
        }

        if opt.e2e || opt.prove {
            // read doc
            let doc_string = opt.doc.as_ref().expect("No document found");
            let doc = read_doc(&doc_string, &config);

            // read commitment
            let cmt_data = fs::read(get_name(opt.cmt_name.clone(), &doc_string, true))
                .expect("Unable to read file");
            let reef_commit: ReefCommitment =
                bincode::deserialize(&cmt_data).expect("Could not deserialize");

            // read re
            #[cfg(feature = "metrics")]
            log::tic(Component::Compiler, "regex_normalization");

            let r = re::simpl(re::new(
                &opt.re.clone().expect("Regular Expression not found"),
            ));

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

            #[cfg(feature = "metrics")]
            log::stop(Component::Compiler, "fa_builder");

            #[cfg(feature = "plot")]
            safa.write_pdf("main")
                .expect("Failed to plot NFA to a pdf file");

            init();
            let (compressed_snark, consist_proof) = run_prover(
                reef_commit, // replace -> only need doc hash
                ab.clone(),
                safa,
                doc.clone(),
                opt.batch_size,
                opt.projections,
                opt.hybrid,
                opt.merkle,
                opt.metrics.clone(),
            );

            // write snark, consistency
            let proofs = Proofs {
                compressed_snark,
                consist_proof,
            };
            let proof_data = bincode::serialize(&proofs).expect("Could not serialize");
            fs::write(
                get_name(
                    opt.proof_name.clone(),
                    opt.re.as_ref().expect("Regular Expression not found"),
                    false,
                ),
                proof_data,
            )
            .expect("Unable to write file");
        }

        if opt.e2e || opt.verify {
            // read commitment
            let file_name = if opt.verify {
                format!("{}", &opt.cmt_name.clone().unwrap())
            } else {
                let doc_string = opt.doc.expect("No document found");
                get_name(opt.cmt_name.clone(), &doc_string, true)
            };

            let cmt_data = fs::read(file_name).expect("Unable to read file");
            let reef_commit: ReefCommitment =
                bincode::deserialize(&cmt_data).expect("Could not deserialize");

            // read re
            let r = re::simpl(re::new(
                opt.re.as_ref().expect("Regular Expression not found"),
            ));

            // Compile regex to SAFA
            let safa = if opt.negate {
                SAFA::new(&ab, &r).negate()
            } else {
                SAFA::new(&ab, &r)
            };

            // read proofs
            let proof_data = fs::read(get_name(
                opt.proof_name.clone(),
                opt.re.as_ref().expect("Regular Expression not found"),
                false,
            ))
            .expect("Unable to read file");
            let proofs: Proofs = bincode::deserialize(&proof_data).expect("Could not deserialize");

            if opt.verify {
                init();
            }
            run_verifier(
                reef_commit,
                &ab,
                safa,
                opt.batch_size,
                opt.projections,
                opt.hybrid,
                opt.merkle,
                proofs.compressed_snark,
                proofs.consist_proof,
            );
        }
    }
}

fn read_doc(doc_string: &String, config: &Config) -> Vec<char> {
    let doc = if Path::exists(Path::new(doc_string)) {
        config
            .read_file(&PathBuf::from(doc_string))
            .iter()
            .map(|c| c.clone())
            .collect()
    } else {
        doc_string.chars().collect()
    };

    doc
}

fn get_name(opt_1: Option<String>, rgx_or_doc: &str, cmt_or_prf: bool) -> String {
    if opt_1.is_some() {
        format!("{}", opt_1.unwrap())
    } else {
        if cmt_or_prf {
            format!("{}.cmt", rgx_or_doc)
        } else {
            format!("reg_{}.proof", rgx_or_doc)
        }
    }
}

fn metrics_file(metrics: Option<PathBuf>, hybrid: bool, projections: bool, doc: &String) {
    assert!(metrics.is_some());
    let file = OpenOptions::new()
        .write(true)
        .append(true)
        .create(true)
        .open(metrics.clone().unwrap())
        .unwrap();
    let mut wtr = Writer::from_writer(file);
    let mut title = doc.clone();
    if title.len() > 10 {
        title = title[..10].to_string();
    }
    let test_type;
    if hybrid | projections {
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
        format!("--"), //opt.re,
        format!("--"), //safa.g.edge_count().to_string(), //nedges().to_string(),
        format!("--"), //safa.g.node_count().to_string(), //nstates().to_string(),
    ]);
    let spacer = "---------";
    let _ = wtr.write_record(&[spacer, spacer, spacer, spacer, "\n"]);
    let _ = wtr.flush();
    #[cfg(feature = "metrics")]
    log::write_csv(metrics.unwrap().to_str().unwrap()).unwrap();
}

#![allow(missing_docs, non_snake_case)]

type G1 = pasta_curves::pallas::Point;
type G2 = pasta_curves::vesta::Point;
type C1 = NFAStepCircuit<<G1 as Group>::Scalar>;
type C2 = TrivialTestCircuit<<G2 as Group>::Scalar>;
type EE1 = nova_snark::provider::ipa_pc::EvaluationEngine<G1>;
type EE2 = nova_snark::provider::ipa_pc::EvaluationEngine<G2>;
type S1 = nova_snark::spartan::RelaxedR1CSSNARK<G1, EE1>;
type S2 = nova_snark::spartan::RelaxedR1CSSNARK<G2, EE2>;

use bincode;
use clap::Parser;
use csv::Writer;
use nova_snark::{
    provider::pedersen::CompressedCommitment,
    traits::{circuit::TrivialTestCircuit, Group},
    CompressedSNARK, PublicParams, RecursiveSNARK, StepCounterType, FINAL_EXTERNAL_COUNTER,
};
use reef::backend::{
    commitment::ConsistencyProof, framework::*, nova::NFAStepCircuit, r1cs_helper::init,
};
use reef::config::*;
use reef::frontend::regex::re;
use reef::frontend::safa::SAFA;
use serde::{Deserialize, Serialize};
use std::fs::{File, OpenOptions};
use std::path::Path;
use std::path::PathBuf;
use std::time::SystemTime;

#[cfg(feature = "metrics")]
use metrics::metrics::{log, log::Component};

fn main() {
    let opt = Options::parse();
    println!("reef");

    // read alphabet
    let config = opt.config.expect("No alphabet found");
    let ab = String::from_iter(config.alphabet());

    // TODO DELETE
    let doc_string = opt.doc.expect("No document found");
    let doc = read_doc(doc_string, &config);

    let hybrid_len = None; // TODO!! JESS

    if opt.e2e || opt.commit {
        #[cfg(feature = "metrics")]
        metrics_file(opt, doc);

        // read doc
        let doc_string = opt.doc.expect("No document found");
        let doc = read_doc(doc_string, &config);

        let reef_commit = run_committer(&doc, &ab, hybrid_len, opt.merkle);

        // write commitment
        write(
            &reef_commit,
            &get_name(opt.file_name.clone(), &doc_string, "cmt"),
        );
    }

    if opt.e2e || opt.prove {
        // read doc
        let doc_string = opt.doc.expect("No document found");
        let doc = read_doc(doc_string, &config);

        // read commitment
        let reef_commit = read(&get_name(opt.file_name.clone(), &doc_string, "cmt"));

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
        write(
            &proofs,
            &get_name(
                opt.file_name.clone(),
                opt.re.as_ref().expect("Regular Expression not found"),
                "proof",
            ),
        );
    }

    if opt.e2e || opt.verify {
        // read commitment
        let reef_commit = read(&get_name(opt.file_name.clone(), &doc_string, "cmt"));

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
        let proofs: Proofs = read(&get_name(
            opt.file_name.clone(),
            opt.re.as_ref().expect("Regular Expression not found"),
            "proof",
        ));

        run_verifier(
            reef_commit,
            &ab,
            safa,
            doc,
            opt.batch_size,
            opt.projections,
            opt.hybrid,
            opt.merkle,
            proofs.compressed_snark,
            proofs.consist_proof,
        );
    }
}

#[derive(Deserialize, Serialize)]
pub struct Proofs {
    compressed_snark: CompressedSNARK<G1, G2, C1, C2, S1, S2>,
    consist_proof: Option<ConsistencyProof>,
}

fn read_doc(doc_string: String, config: &Config) -> Vec<char> {
    let doc = if Path::exists(Path::new(&doc_string)) {
        config
            .read_file(&PathBuf::from(&doc_string))
            .iter()
            .map(|c| c.clone())
            .collect()
    } else {
        doc_string.chars().collect()
    };

    doc
}

fn get_name(opt_1: Option<String>, rgx_or_doc: &str, ending: &str) -> String {
    if opt_1.is_some() {
        format!("{}.{}", opt_1.unwrap(), ending)
    } else {
        format!("{}.{}", rgx_or_doc, ending)
    }
}

fn metrics_file(opt: Options, doc: String) {
    assert!(opt.metrics.is_some());
    let file = OpenOptions::new()
        .write(true)
        .append(true)
        .create(true)
        .open(opt.metrics.clone().unwrap())
        .unwrap();
    let mut wtr = Writer::from_writer(file);
    let mut title = doc.clone();
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
        format!("--"), //opt.re,
        format!("--"), //safa.g.edge_count().to_string(), //nedges().to_string(),
        format!("--"), //safa.g.node_count().to_string(), //nstates().to_string(),
    ]);
    let spacer = "---------";
    let _ = wtr.write_record(&[spacer, spacer, spacer, spacer, "\n"]);
    let _ = wtr.flush();
    #[cfg(feature = "metrics")]
    log::write_csv(opt.metrics.unwrap().to_str().unwrap()).unwrap();
}

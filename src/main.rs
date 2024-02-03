#![allow(missing_docs, non_snake_case)]

use clap::Parser;
use csv::Writer;
use nova_snark::{
    traits::{circuit::TrivialTestCircuit, Group},
    CompressedSNARK,
};
use reef::backend::{
    commitment::ReefCommitment, framework::*, nova::NFAStepCircuit, r1cs_helper::init,
};
use reef::config::*;
use reef::frontend::regex::re;
use reef::frontend::safa::SAFA;
use serde::{Deserialize, Serialize};
use std::fs::OpenOptions;
use std::path::Path;
use std::path::PathBuf;
use std::time::SystemTime;

#[cfg(feature = "metrics")]
use metrics::metrics::{log, log::Component};

use nova_snark::provider::hyrax_pc::PolyCommit;
use reef::backend::commitment::NLDocCommitment;
type G1 = pasta_curves::pallas::Point;
use generic_array::typenum;
use neptune::poseidon::PoseidonConstants;
use nova_snark::provider::pedersen::CommitmentGens;
use nova_snark::spartan::direct::SpartanProverKey;
use nova_snark::spartan::polynomial::MultilinearPolynomial;
use std::fs;
use std::fs::File;
use std::io::BufReader;
use std::io::BufWriter;
use std::io::Write;
type EE1 = nova_snark::provider::ipa_pc::EvaluationEngine<G1>;

#[derive(Deserialize, Serialize)]
#[serde(bound = "")]
pub struct Fake {
    // commitment to doc
    single_gens: CommitmentGens<G1>,
    /*    hyrax_gen: HyraxPC<G1>,
        doc_poly: MultilinearPolynomial<<G1 as Group>::Scalar>,
        pub doc_commit: PolyCommit<G1>,
        doc_decommit: PolyCommitBlinds<G1>,
        pub doc_commit_hash: <G1 as Group>::Scalar,
        pub hash_salt: <G1 as Group>::Scalar,
        // consistency verification
        cap_pk: SpartanProverKey<G1, EE1>,
        cap_vk: SpartanVerifierKey<G1, EE1>,
        q_len: usize,
    */
}

fn main() {
    let opt = Options::parse();
    println!("reef");

    // read alphabet
    let config = opt.config.expect("No alphabet found");
    let ab = String::from_iter(config.alphabet());

    if opt.e2e || opt.commit {
        #[cfg(feature = "metrics")]
        metrics_file(opt, doc);

        // read doc
        let doc_string = opt.doc.as_ref().expect("No document found");
        let doc = read_doc(&doc_string, &config);

        let reef_commit = run_committer(&doc, &ab, opt.merkle);

        // write commitment
        let cmt_data = bincode::serialize(&reef_commit).expect("Could not serialize");
        fs::write(get_name(opt.cmt_name.clone(), &doc_string, "cmt"), cmt_data)
            .expect("Unable to write file");
    }

    if opt.e2e || opt.prove {
        // read doc
        let doc_string = opt.doc.as_ref().expect("No document found");
        let doc = read_doc(&doc_string, &config);

        // read commitment
        let cmt_data = fs::read(get_name(opt.cmt_name.clone(), &doc_string, "cmt"))
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
                "proof",
            ),
            proof_data,
        )
        .expect("Unable to write file");
    }

    if opt.e2e || opt.verify {
        // read commitment
        let file_name = if opt.verify {
            format!("{}.cmt", &opt.cmt_name.clone().unwrap())
        } else {
            let doc_string = opt.doc.expect("No document found");
            get_name(opt.cmt_name.clone(), &doc_string, "cmt")
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
            "proof",
        ))
        .expect("Unable to read file");
        let proofs: Proofs = bincode::deserialize(&proof_data).expect("Could not deserialize");

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

fn get_name(opt_1: Option<String>, rgx_or_doc: &str, ending: &str) -> String {
    if opt_1.is_some() {
        format!("{}", opt_1.unwrap())
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

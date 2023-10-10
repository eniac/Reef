#![allow(missing_docs, non_snake_case)]

type G1 = pasta_curves::pallas::Point;
type G2 = pasta_curves::vesta::Point;
type EE1 = nova_snark::provider::ipa_pc::EvaluationEngine<G1>;
type EE2 = nova_snark::provider::ipa_pc::EvaluationEngine<G2>;

use crate::naive::naive_wr_circom_writer::*;
use crate::naive::naive_wr_nova::*;
use std::{env::current_dir};
use std::path::PathBuf;
use std::fs::{File,remove_file};
use std::io::prelude::*;
use crate::naive::dfa::*; 
use crate::naive::naive_regex::*;
use itertools::Itertools;
use neptune::{
    poseidon::PoseidonConstants,
    sponge::api::{IOPattern, SpongeAPI, SpongeOp},
    sponge::circuit::SpongeCircuit,
    sponge::vanilla::{SpongeTrait,Sponge},
    Strength,
};
use generic_array::typenum;
use nova_scotia::circom::circuit::*;
// use nova_scotia::compute_witness;
use nova_snark::{
    PublicParams,
    traits::{circuit::StepCircuit, Group},
    spartan::*,
    CompressedSNARK,
};
use ff::PrimeField;
use pasta_curves::Fq;
use serde_json::json;
use nova_scotia::{
    circom::reader::load_r1cs, create_public_params, create_recursive_circuit, FileLocation, F,
};
use std::fs::OpenOptions;
use csv::Writer;
use memory_stats::memory_stats;
use std::process::{Command, Stdio};
use execute::{Execute, shell};
use std::{collections::HashMap};

#[cfg(feature = "metrics")]
use metrics::metrics::{log, log::Component};

pub fn get_folded_cost(circuit_size: usize, n_foldings: usize) -> usize {
    let cost_folding = 2 * circuit_size * n_foldings;
    let cost_snark = (((circuit_size) as f32) * 128.0).log2().ceil() as usize;
    let total_cost = cost_folding + cost_snark;
    total_cost
}

pub fn naive_bench(r: String, alpha: String, doc: String, out_write:PathBuf) {
    println!("nwr");
    println!("doc len: {}",doc.len());
    println!("{}",r);
    let doc_vec: Vec<u32> = doc.chars().map(|x| x as u32).collect();
    let doc_len = doc_vec.len();

    #[cfg(feature = "metrics")]
    log::tic(Component::Compiler, "DFA","DFA");
    let regex = re::simpl(re::new(&(r.clone())));

    let dfa = DFA::new(&alpha[..],regex);
    let dfa_ndelta = dfa.deltas().len();
    let dfa_nstate = dfa.nstates();

    #[cfg(feature = "metrics")]
    log::stop(Component::Compiler, "DFA","DFA");

    println!("N States: {:#?}",dfa_nstate);

    #[cfg(feature = "metrics")]
    log::tic(Component::Solver,"DFA Solving", "Clear Match");

    let is_match = dfa.is_match(&doc);
    let solution = dfa.solve(&doc);
    let mut prover_states: Vec<u32> = solution.clone().into_iter().map(|(a,b,c)| a).collect_vec();
    if let Some(last) = solution.last().map(|(a,b,c)| (*c).clone()) {
        prover_states.push(last);
    }
    println!("solution length: {}",prover_states.len());
    println!("doc length: {}",doc_len);
   
    let is_match_g = <G1 as Group>::Scalar::from(is_match as u64);
    #[cfg(feature = "metrics")]
    log::stop(Component::Solver, "DFA Solving", "Clear Match");

    #[cfg(feature = "metrics")]
    log::tic(Component::Compiler, "R1CS", "Commitment Gen");

    let pc: PoseidonConstants<<G1 as Group>::Scalar, typenum::U4> = Sponge::<<G1 as Group>::Scalar, typenum::U4>::api_constants(Strength::Standard);
    let commitment = gen_commitment(doc_vec.clone(), &pc);

    #[cfg(feature = "metrics")]
    log::stop(Component::Compiler, "R1CS", "Commitment Gen");

    let _ = make_circom(&dfa, doc_len, alpha.len());

    let mut command = shell("circom match.circom --r1cs --sym --wasm --prime vesta");

    #[cfg(feature = "metrics")]
    log::tic(Component::Compiler, "R1CS", "Circom");
    let mut output  = command.execute_output().unwrap();
    #[cfg(feature = "metrics")]
    log::stop(Component::Compiler, "R1CS", "Circom");

    println!("{}", String::from_utf8(output.stdout).unwrap());

    remove_file("match.circom");

    println!("post circom");

    let circuit_filepath = "match.r1cs";
    let witness_gen_filepath = "match_js/match.wasm";

    let root = current_dir().unwrap();

    let circuit_file = root.join(circuit_filepath);
    let witness_generator_file = root.join(witness_gen_filepath);
    let witness_generator_output = root.join("circom_witness.wtns");

    #[cfg(feature = "metrics")]
    log::tic(Component::Compiler, "R1CS", "Loading");
    let r1cs = load_r1cs::<G1, G2>(&FileLocation::PathBuf(circuit_file));

    #[cfg(feature = "metrics")]
    log::stop(Component::Compiler,"R1CS", "Loading");

    println!("R1CS loaded" );

    let start_public_input = [
        F::<G1>::from(0),
        gen_hash(vec![commitment.blind], &pc),
        F::<G1>::from(1),
        gen_hash(vec![F::<G1>::from(prover_states[0] as u64)], &pc),
    ];

    let mut private_inputs: Vec<HashMap<String, serde_json::Value>> = Vec::new();

    for i in 0..doc_len {
        let mut private_input = HashMap::new();
        private_input.insert("cur_state".to_string(), json!(prover_states[i]));
        private_input.insert("next_state".to_string(), json!(prover_states[i+1]));
        private_input.insert("char".to_string(),json!(doc_vec[i]));
        private_inputs.push(private_input);

    }

    #[cfg(feature = "metrics")]
    log::tic(Component::Compiler, "R1CS","Public Params");

    let pp = create_public_params::<G1, G2>(r1cs.clone());
    
    #[cfg(feature = "metrics")]
    log::stop(Component::Compiler, "R1CS","Public Params");
 
    println!(
        "Number of constraints per step (primary circuit): {}",
        pp.num_constraints().0
    );
    println!(
        "Number of constraints per step (secondary circuit): {}",
        pp.num_constraints().1
    );

    println!(
        "total n constraints: {}",
        get_folded_cost(pp.num_constraints().0,doc_len)
    );


    #[cfg(feature = "metrics")]
    log::r1cs(Component::Compiler, "R1CS", "Size", pp.num_constraints().0);

    println!(
        "Number of variables per step (primary circuit): {}",
        pp.num_variables().0
    );
    println!(
        "Number of variables per step (secondary circuit): {}",
        pp.num_variables().1
    );

    let recursive_snark = create_recursive_circuit(
        FileLocation::PathBuf(witness_generator_file),
        r1cs,
        private_inputs,
        start_public_input.to_vec(),
        &pp,
    ).unwrap();

    let z0_secondary = [<G2 as Group>::Scalar::zero()];

    // produce a compressed SNARK
    println!("Generating a CompressedSNARK using Spartan with IPA-PC...");
    type S1 = nova_snark::spartan::RelaxedR1CSSNARK<G1, EE1>;
    type S2 = nova_snark::spartan::RelaxedR1CSSNARK<G2, EE2>;

    #[cfg(feature = "metrics")]
    log::tic(Component::Prover, "Prove","Prove Compressed");

    let res = CompressedSNARK::<_, _, _, _, S1, S2>::prove(&pp, &recursive_snark);

    #[cfg(feature = "metrics")]
    log::stop(Component::Prover, "Prove","Prove Compressed");

    assert!(res.is_ok());
    let compressed_snark = res.unwrap();


    // // verify the compressed SNARK
    println!("Verifying a CompressedSNARK...");

    #[cfg(feature = "metrics")]
    log::tic(Component::Verifier, "Verifier","Verify");
    let res = compressed_snark.verify(
        &pp,
        doc_len,
        start_public_input.to_vec().clone(),
        z0_secondary.to_vec(),
    );

    #[cfg(feature = "metrics")]
    log::stop(Component::Verifier, "Verifier","Verify");

    println!(
        "CompressedSNARK::verify: {:?}",
        res,
    );
    assert!(res.is_ok());

    // index,hash.out, valid_match.out,next_state_hash.out;
    println!(
        "zn? {:?}",
        res.unwrap().0,
    );

    println!(
        "commitment {:?}",
        commitment,
    );

    #[cfg(feature = "metrics")]
    log::space(
        Component::Prover,
        "Proof Size",
        "Spartan SNARK size",
        serde_json::to_string(&compressed_snark).unwrap().len(),
    );


    let file = OpenOptions::new().write(true).append(true).create(true).open(out_write.clone()).unwrap();
    let mut wtr = Writer::from_writer(file);
    let _ = wtr.write_record(&[
    format!("{}_{}",&doc[..10],doc.len()),
    r,
    dfa_ndelta.to_string(), //nedges().to_string(),
    dfa_nstate.to_string(), //nstates().to_string(),
    ]);
    let spacer = "---------";
    let _ = wtr.write_record(&[spacer, spacer, spacer, spacer]);
    wtr.flush();

    #[cfg(feature = "metrics")]
    log::write_csv(&out_write.as_path().display().to_string()).unwrap();

    remove_file("match.sym");
    remove_file("match.r1cs");
    remove_file("circom_witness.wtns");

    return   
}


#[test]
fn test_1() {
    let r  = "abc";
    //"Message-ID: .*\nDate: Tue, 8 May 2001 09:16:00 -0700 \(PDT\)\nFrom: .*\nTo: .*\nSubject: Re:\nMime-Version: 1\.0\nContent-Type: text\/plain; charset=us-ascii\nContent-Transfer-Encoding: 7bit\nX-From: Mike Maggi\nX-To: Amanda Huble\nX-cc: \nX-bcc: \nX-Folder: \\Michael_Maggi_Jun2001\\Notes Folders\\Sent\nX-Origin: Maggi-M\nX-FileName: mmaggi\.nsf\n\nat 5:00".to_string();
    //let abvec: Vec<char> = (0..256).filter_map(std::char::from_u32).collect();
    let ab: String = "abc".to_string();
    //let ab = abvec.iter().collect();
    let doc = "abc".to_owned();
    naive_bench(r.to_string(),ab, doc, PathBuf::from("out_test"));
}

#![allow(missing_docs, non_snake_case)]

type G1 = pasta_curves::pallas::Point;
type G2 = pasta_curves::vesta::Point;
type EE = nova_snark::provider::ipa_pc::EvaluationEngine<G1>;

// use crate::backend::{r1cs_helper::init};
use crate::naive::naive_circom_writer::*;
use crate::naive::naive_nova::gen_commitment;
use std::env::current_dir;
use std::path::PathBuf;
use std::fs::File;
use std::io::prelude::*;
use crate::naive::dfa::*; 
use crate::regex::re;
use crate::naive::naive_parser as naive_re;
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
use nova_scotia::compute_witness;
use nova_snark::{
    PublicParams,
    traits::{circuit::StepCircuit, Group},
    spartan::direct::*,
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
use crate::metrics::{log, log::Component};

pub fn naive_bench(r: String, alpha: String, doc: String, out_write:PathBuf) {
    let doc_vec: Vec<u32> = doc.chars().map(|x| x as u32).collect();
    let doc_len = doc_vec.len();

    let regex = re::simpl(re::new(&(r.clone())));

    let dfa = DFA::new(&alpha[..],naive_re::re::translate(&regex, &alpha[..]));
    let dfa_ndelta = dfa.deltas().len();
    let dfa_nstate = dfa.nstates();

    println!("N States: {:#?}",dfa_nstate);
    println!("N Delta: {:#?}",dfa_ndelta);


    let is_match = dfa.is_match(&doc);
    let solution = dfa.solve(&doc);
    let mut prover_states: Vec<u32> = solution.clone().into_iter().map(|(a,b,c)| a).collect_vec();
    if let Some(last) = solution.last().map(|(a,b,c)| (*c).clone()) {
        prover_states.push(last);
    }
   
    let is_match_g = <G1 as Group>::Scalar::from(is_match as u64);

    let pc: PoseidonConstants<<G1 as Group>::Scalar, typenum::U4> = Sponge::<<G1 as Group>::Scalar, typenum::U4>::api_constants(Strength::Standard);
    let commitment = gen_commitment(doc_vec.clone(), &pc);

    let _ = make_circom(&dfa, doc_len, alpha.len());

    let mut command = shell("circom match.circom --r1cs --sym --wasm --prime vesta");
    let output  = command.execute_output().unwrap();

    println!("{}", String::from_utf8(output.stdout).unwrap());

    let circuit_filepath = "match.r1cs";
    let witness_gen_filepath = "match_js/match.wasm";

    let root = current_dir().unwrap();

    let circuit_file = root.join(circuit_filepath);
    let witness_generator_file = root.join(witness_gen_filepath);
    let witness_generator_output = root.join("circom_witness.wtns");

    let r1cs = load_r1cs::<G1, G2>(&FileLocation::PathBuf(circuit_file));

    let mut private_inputs: Vec<HashMap<String, serde_json::Value>> = Vec::new();
    let mut private_input = HashMap::new();
    private_input.insert("doc".to_string(), json!(doc_vec));
    private_input.insert("prover_states".to_string(), json!(prover_states));
    private_input.insert("blind".to_string(),json!(commitment.blind));
    private_inputs.push(private_input);

    println!("commitment:{:#?}",commitment);
    println!(
        "Number of constraints: {}",
       r1cs.constraints.len()
    );

    println!(
        "Number of variables: {}",
       r1cs.num_variables
    );

    let circuit = CircomCircuit {
        r1cs: r1cs.clone(),
        witness: None,
    };

    let (pk, vk) = naive_spartan_snark_setup(circuit);

    //witness generation
    let iteration_count = private_inputs.len();
    let public_input: [Fq;0] = [];
    let start_public_input_hex = public_input.iter().map(|&x| format!("{:?}", x).strip_prefix("0x").unwrap().to_string()).collect::<Vec<String>>();
    let mut current_public_input = start_public_input_hex.clone();


    let witnesses = compute_witness::<G1, G2>(
        current_public_input,
        private_inputs[0].clone(),
        FileLocation::PathBuf(witness_generator_file),
        &witness_generator_output,
    );


    let prove_circuit = CircomCircuit {
        r1cs: r1cs.clone(),
        witness: Some(witnesses),
    };

    let z = vec![commitment.commit];

    let result = SpartanSNARK::prove(&pk,prove_circuit.clone(),&z);

    assert!(result.is_ok());

    let output = prove_circuit.output(&z);

    println!("output: {:?}", output);

    let snark = result.unwrap();

    // // verify the SNARK

    let io = z.into_iter()
      .chain(output.clone().into_iter())
      .collect::<Vec<_>>();
    println!("{:?}", io);
    let verifier_result = snark.verify(&vk, &io);

    println!("{:?}", verifier_result);

    assert!(verifier_result.is_ok()); 

    // let file = OpenOptions::new().write(true).append(true).create(true).open(out_write.clone()).unwrap();
    // let mut wtr = Writer::from_writer(file);
    // let _ = wtr.write_record(&[
    // format!("{}_{}",&doc[..10],doc.len()),
    // r,
    // dfa_ndelta.to_string(), //nedges().to_string(),
    // dfa_nstate.to_string(), //nstates().to_string(),
    // ]);
    // let spacer = "---------";
    // let _ = wtr.write_record(&[spacer, spacer, spacer, spacer]);
    // wtr.flush();

    // #[cfg(feature = "metrics")]
    // log::write_csv(&out_write.as_path().display().to_string()).unwrap();
    return   
}


#[test]
fn test_1() {
    let r  = "abc".to_string();
    let abvec: Vec<char> = (0..128).filter_map(std::char::from_u32).collect();
    let ab: String = "abc".to_string();
    //abvec.iter().collect();
    let doc = "abc".to_owned();
    naive_bench(r,ab, doc, PathBuf::from("out_test"));
}

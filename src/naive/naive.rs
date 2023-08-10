#![allow(missing_docs, non_snake_case)]

type G1 = pasta_curves::pallas::Point;
type G2 = pasta_curves::vesta::Point;
type EE = nova_snark::provider::ipa_pc::EvaluationEngine<G1>;

// use crate::backend::{r1cs_helper::init};
use crate::naive::naive_nova::*;
use crate::naive::naive_circom_writer::*;
use std::env::current_dir;
use std::path::PathBuf;
use std::fs::File;
use std::io::prelude::*;
use crate::naive::dfa::*; 
use crate::regex::re;
use crate::naive::naive_parser as naive_re;
use neptune::{
    poseidon::PoseidonConstants,
    sponge::api::{IOPattern, SpongeAPI, SpongeOp},
    sponge::circuit::SpongeCircuit,
    sponge::vanilla::{SpongeTrait,Sponge},
    Strength,
};
use generic_array::typenum;
use nova_scotia::circom::circuit::R1CS;
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

    #[cfg(feature = "metrics")]
    log::tic(Component::Compiler, "DFA", "DFA");

    let regex = re::simpl(re::new(&(r.clone())));

    let dfa = DFA::new(&alpha[..],naive_re::re::translate(&regex, &alpha[..]));
    let dfa_ndelta = dfa.deltas().len();
    let dfa_nstate = dfa.nstates();

    println!("N States: {:#?}",dfa_nstate);
    println!("N Delta: {:#?}",dfa_ndelta);

    #[cfg(feature = "metrics")]
    log::stop(Component::Compiler, "DFA", "DFA");

    #[cfg(feature = "metrics")]
    log::tic(Component::Solver, "DFA Solving", "Clear Match");

    let is_match = dfa.is_match(&doc);
    let solution = dfa.solve(&doc);
   
    let is_match_g = <G1 as Group>::Scalar::from(is_match as u64);

    #[cfg(feature = "metrics")]
    log::stop(Component::Solver, "DFA Solving", "Clear Match");

    #[cfg(feature = "metrics")]
    log::tic(Component::Compiler, "Circuit Gen", "Zok");

    println!("Make Circom");

    let _ = make_circom(&dfa, doc_len, alpha.len());

    let mut command = shell("circom match.circom --r1cs --sym --wasm --prime vesta");
    let output  = command.execute_output().unwrap();

    println!("{}", String::from_utf8(output.stdout).unwrap());
    
    #[cfg(feature = "metrics")]
    log::stop(Component::Compiler, "Circuit Gen", "Zok");

    #[cfg(feature = "metrics")]
    log::tic(Component::Compiler, "Circuit Gen", "r1cs");

    // println!("gen r1cs");

    // let circuit_filepath = "match.r1cs";
    // let witness_gen_filepath = "match_js/match.wasm";

    // let root = current_dir().unwrap();

    // let circuit_file = root.join(circuit_filepath);
    // let witness_generator_file = root.join(witness_gen_filepath);

    // let r1cs = load_r1cs::<G1, G2>(&FileLocation::PathBuf(circuit_file));

    // let mut private_inputs: Vec<HashMap<String, serde_json::Value>> = Vec::new();
    // let mut private_input = HashMap::new();
    // private_input.insert("doc".to_string(), json!(doc_vec));
    // private_input.insert("prover_states".to_string(), json!(solution));
    // private_inputs.push(private_input);

    // // #[cfg(feature = "metrics")]
    // // log::stop(Component::Compiler, "Circuit Gen", "r1cs");

    // // #[cfg(feature = "metrics")]
    // // log::r1cs(Component::Compiler, "Circuit Gen", "r1cs",P.r1cs.constraints.len());
    
    // // println!("N constraints: {:#?}",P.r1cs.constraints.len());

    // println!(
    //     "Number of constraints: {}",
    //    r1cs.constraints.len()
    // );

    // println!(
    //     "Number of variables: {}",
    //    r1cs.num_variables
    // );

    //let pc: PoseidonConstants<<G1 as Group>::Scalar, typenum::U4> = Sponge::<<G1 as Group>::Scalar, typenum::U4>::api_constants(Strength::Standard);

    // #[cfg(feature = "metrics")]
    // log::tic(Component::Compiler, "R1CS", "Commitment Generations");

    // println!("Gen commitment");

    // mem_log("Memory Usage Pre-Commitment");
    //let commitment = gen_commitment(doc_vec.clone(), &pc);
    // mem_log("Memory Usage Post-Commitment");

    // #[cfg(feature = "metrics")]
    // log::stop(Component::Compiler, "R1CS", "Commitment Generations");

    // #[cfg(feature = "metrics")]
    // log::tic(Component::Compiler, "R1CS", "To Circuit");

    // println!("To circuit");

    // mem_log("pre circuit new");
    //let circuit = NaiveCircuit::new(r1cs.clone(),  doc_len, pc.clone(), commitment.blind,commitment.commit,is_match_g);
    // mem_log("post circuit new");
    // #[cfg(feature = "metrics")]
    // log::stop(Component::Compiler, "R1CS", "To Circuit");

    // #[cfg(feature = "metrics")]
    // log::tic(Component::Compiler, "R1CS", "Proof Setup");

    // mem_log("pre spartan setup");
    // let (pk, vk) = naive_spartan_snark_setup(circuit);
    // mem_log("post spartan setup");

    // #[cfg(feature = "metrics")]
    // log::stop(Component::Compiler, "R1CS", "Proof Setup");

    // #[cfg(feature = "metrics")]
    // log::tic(Component::Solver, "Witnesses", "Generation");
    // println!("Wit gen");
    
    // mem_log("pre wit gen");
    // let witnesses = gen_wits(doc_vec, is_match, doc_len, solution, &dfa, alpha.len(), &P);
    // mem_log("post wit gen");

    // #[cfg(feature = "metrics")]
    // log::stop(Component::Solver, "Witnesses", "Generation");
    
    // #[cfg(feature = "metrics")]
    // log::tic(Component::Prover, "Proof", "Adding witnesses");
    
    // mem_log("pre_prove circuit");
    // let prove_circuit = NaiveCircuit::new(P.r1cs,witnesses, doc_len, pc, commitment.blind, commitment.commit, is_match_g);
    // mem_log("post prove circuit");

    // #[cfg(feature = "metrics")]
    // log::stop(Component::Prover, "Proof", "Adding witnesses");

    // let z = vec![commitment.commit];

    // #[cfg(feature = "metrics")]
    // log::tic(Component::Prover, "Proof", "Prove");

    // let result = SpartanSNARK::prove(&pk,prove_circuit.clone(),&z);

    // #[cfg(feature = "metrics")]
    // log::stop(Component::Prover, "Proof", "Prove");

    // assert!(result.is_ok());

    // let output = prove_circuit.output(&z);

    // let snark = result.unwrap();

    // #[cfg(feature = "metrics")]
    // log::space(
    //     Component::Prover,
    //     "Proof Size",
    //     "Spartan SNARK size",
    //     serde_json::to_string(&snark).unwrap().len(),
    // );

    // // verify the SNARK
    // #[cfg(feature = "metrics")]
    // log::tic(Component::Verifier, "Verify", "Verify");

    // let io = z.into_iter()
    //   .chain(output.clone().into_iter())
    //   .collect::<Vec<_>>();
    // let verifier_result = snark.verify(&vk, &io);

    // #[cfg(feature = "metrics")]
    // log::stop(Component::Verifier, "Verify", "Verify");
    // assert!(verifier_result.is_ok()); 

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

#![allow(missing_docs, non_snake_case)]

type G1 = pasta_curves::pallas::Point;
type G2 = pasta_curves::vesta::Point;
type EE = nova_snark::provider::ipa_pc::EvaluationEngine<G1>;

use crate::backend::{r1cs_helper::init};
use crate::naive::naive_nova::*;
use std::path::PathBuf;
use std::fs::File;
use std::io::prelude::*;
use crate::naive::dfa::*; 
use crate::naive::naive_parser::*;
use circ::front::zsharp::{self, ZSharpFE};
use circ::front::{FrontEnd, Mode};
use circ::ir::{opt::{opt, Opt}};
use circ::target::r1cs::{opt::reduce_linearities, trans::to_r1cs, ProverData, VerifierData};
use circ::cfg::*;
use neptune::circuit;
use neptune::{
    circuit2::Elt,
    poseidon::PoseidonConstants,
    sponge::api::{IOPattern, SpongeAPI, SpongeOp},
    sponge::circuit::SpongeCircuit,
    sponge::vanilla::{SpongeTrait,Sponge},
    Strength,
};
use ::bellperson::{
    gadgets::num::AllocatedNum, ConstraintSystem, LinearCombination, Namespace, SynthesisError,
    Variable,
};
use ff::{Field, PrimeField};
use generic_array::typenum;
use nova_snark::{
    traits::{circuit::StepCircuit, Group},
    CompressedSNARK, PublicParams, RecursiveSNARK, StepCounterType, FINAL_EXTERNAL_COUNTER,
    spartan::direct::*,
};
use rug::integer::{IsPrime, Order};
use rug::Integer;
use serde::__private::doc;
use std::{collections::HashMap, default};
use crate::backend::nova;
use core::marker::PhantomData;


#[derive(PartialEq, Eq, Debug)]
pub enum DeterminedLanguage {
    Zsharp,
    Datalog,
    C,
}

pub fn make_delta(state:u64, c: u32, next: u64) -> String{
    format!("\tout = if (state=={state} && cur_char=={c}) then {next} else out-0 fi\n")
}

pub fn make_match(state:u64) -> String{
    format!("\tmatch = if state=={state} then 1 else match-0 fi\n")
}
pub fn make_zok(dfa: DFA<'_>) -> std::io::Result<()> {
    let mut delta_base_string = "def delta(private field state, private field cur_char) -> field:
    \tfield out = -1\n".to_owned();

    let mut main_base_string = "\n\ndef main(private field[2] document) -> field: 
    \tfield size = 2
    \tfield state = 0
    \tfor field i in 0..size do
    \t\tstate = delta(state, document[i])
    \tendfor 
    \tfield match = 0\n".to_owned();

    for match_state in dfa.get_final_states() {
        main_base_string.push_str(&(make_match(match_state).to_owned()));
    }
    main_base_string.push_str("\treturn match");


    for delta in dfa.deltas() {
        let line = make_delta(delta.0, (delta.1 as u32), delta.2).to_owned();
        delta_base_string.push_str(&line);
    }
    delta_base_string.push_str("\treturn out");

    let mut final_string = delta_base_string; 
    final_string.push_str(&main_base_string);

    let mut file = File::create("match.zok")?;
    file.write_all(final_string.as_bytes())?;
    Ok(())
}


pub fn gen_r1cs() -> (ProverData, VerifierData){
    let mut path_buf = PathBuf::from("match.zok");
    let inputs = zsharp::Inputs {
        file: path_buf,
        mode: Mode::Proof,
    };
    let cs = ZSharpFE::gen(inputs);

    let mut opts = Vec::new();

    opts.push(Opt::ScalarizeVars);
    opts.push(Opt::Flatten);
    opts.push(Opt::Sha);
    opts.push(Opt::ConstantFold(Box::new([])));
    opts.push(Opt::ParseCondStores);
    opts.push(Opt::Tuple);
    opts.push(Opt::ConstantFold(Box::new([])));
    opts.push(Opt::Tuple);
    opts.push(Opt::Obliv);
    opts.push(Opt::Tuple);
    opts.push(Opt::LinearScan);
    opts.push(Opt::Tuple);
    opts.push(Opt::Flatten);
    opts.push(Opt::ConstantFold(Box::new([])));

    let cs = opt(cs, opts);

    let cs = cs.get("main");

    let mut r1cs = to_r1cs(cs, cfg());
    r1cs = reduce_linearities(r1cs, cfg());
    println!{"{:#?}",r1cs.constraints().len()};
    r1cs.finalize(&cs)
}

fn naive(r: &str, alpha: String, doc: String) {
    init();

    let doc_vec: Vec<u32> = doc.chars().map(|x| x as u32).collect();
    let regex = regex_parser(&String::from(r), &alpha);

    let mut dfa = DFA::new(&alpha[..], regex);
    // println!("{:#?}",dfa.get_init_state());
    println!("{:#?}",dfa.get_final_states());
    make_zok(dfa);

    let (P,V) = gen_r1cs();

    let pc: PoseidonConstants<<G1 as Group>::Scalar, typenum::U4> = Sponge::<<G1 as Group>::Scalar, typenum::U4>::api_constants(Strength::Standard);

    let circuit = gen_circuit(P.r1cs, None, pc.clone());

    let (pk, vk) = naive_spartan_snark_setup(circuit);

    let commitment = gen_commitment(doc_vec, &pc);


}


#[test]
fn test_1() {
    let r  = "ab";
    //let abvec: Vec<char> = (0..256).filter_map(std::char::from_u32).collect();
    //let ab: String = abvec.iter().collect();
    let ab = "abc".to_owned();
    let doc = "ab".to_owned();
    naive(r,ab, doc);
}
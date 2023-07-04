#![allow(missing_docs, non_snake_case)]
use clap::Parser;
use csv::Writer;
use crate::backend::{framework::*, r1cs_helper::init};
use std::fs::OpenOptions;
use std::path::Path;
use std::path::PathBuf;
use std::fs::File;
use std::io::prelude::*;
use crate::naive::dfa::*; 
use crate::naive::naive_parser::*;
use circ::front::zsharp::{self, ZSharpFE};
use circ::front::{FrontEnd, Mode};
use circ::ir::{opt::{opt, Opt}};
use circ::target::r1cs::{opt::reduce_linearities, trans::to_r1cs, ProverData, VerifierData};
use circ::cfg;
use circ::cfg::*;

#[derive(PartialEq, Eq, Debug)]
pub enum DeterminedLanguage {
    Zsharp,
    Datalog,
    C,
}

pub fn make_delta(state:u64, c: u32, next: u64) -> String{
    format!("\t out = if (state=={state} && cur_char=={c}) then {next} else out-0 fi\n")
}

pub fn make_match(state:u64) -> String{
    format!("\t match = if state=={state} then 1 else match-0 fi\n")
}
pub fn make_zok(dfa: DFA<'_>) -> std::io::Result<()> {
    let mut delta_base_string = "def delta(private field state, private field cur_char) -> field:
    \t field out = -1\n".to_owned();

    let mut main_base_string = "\n\ndef main(field commit, private field blind) -> field: 
    \t field size = 3
    \t field[size] document = [0,0,0]
    \t field state = 0
    \t for field i in 0..size do
    \t\t state = delta(state, i)
    \t endfor 
    \t field match = 0\n".to_owned();

    for match_state in dfa.get_final_states() {
        main_base_string.push_str(&(make_match(match_state).to_owned()));
    }
    main_base_string.push_str("\t return match");


    for delta in dfa.deltas() {
        let line = make_delta(delta.0, (delta.1 as u32), delta.2).to_owned();
        delta_base_string.push_str(&line);
    }
    delta_base_string.push_str("\t return out");

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
    r1cs.finalize(&cs)
}

fn naive(r: &str, alpha: String) {
    init();

    let regex = regex_parser(&String::from(r), &alpha);

    let mut dfa = DFA::new(&alpha[..], regex);
    // println!("{:#?}",dfa.get_init_state());
    println!("{:#?}",dfa.get_final_states());
    make_zok(dfa);

    let (P,V) = gen_r1cs();
    //Shoudl at least generate the r1cs have to figure out witnesses as well as
    //other issues re commitment 
}


#[test]
fn test_1() {
    let s  = "ab";
    //let abvec: Vec<char> = (0..256).filter_map(std::char::from_u32).collect();
    //let ab: String = abvec.iter().collect();
    let ab = "abc".to_owned();
    naive(s,ab);
}
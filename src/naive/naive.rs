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

#[derive(PartialEq, Eq, Debug)]
pub enum DeterminedLanguage {
    Zsharp,
    Datalog,
    C,
}

pub fn make_delta(state:u64, c: u32, next: u64) -> String{
    format!("\t out = if (state=={state} && cur_char=={c}) then {next} else out fi\n")
}

pub fn make_match(state:u64) -> String{
    format!("\t match = if state=={state} then 1 else match fi\n")
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

fn naive(r: &str, alpha: String) {
    init();

    let regex = regex_parser(&String::from(r), &alpha);

    let mut dfa = DFA::new(&alpha[..], regex);
    // println!("{:#?}",dfa.get_init_state());
    println!("{:#?}",dfa.get_final_states());
    make_zok(dfa);

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
            // The obliv elim pass produces more tuples, that must be eliminated
    opts.push(Opt::Tuple);
    opts.push(Opt::LinearScan);
    opts.push(Opt::Tuple);
    opts.push(Opt::Flatten);
    opts.push(Opt::ConstantFold(Box::new([])));

    let cs = opt(cs, opts);

    //     }
    // };
    // println!("Done with IR optimization");

    // match options.backend {
    //     #[cfg(feature = "r1cs")]
    //     Backend::R1cs {
    //         action,
    //         prover_key,
    //         verifier_key,
    //         proof_impl,
    //         ..
    //     } => {
    //         println!("Converting to r1cs");
    //         let cs = cs.get("main");
    //         trace!("IR: {}", circ::ir::term::text::serialize_computation(cs));
    //         let mut r1cs = to_r1cs(cs, cfg());

    //         println!("Pre-opt R1cs size: {}", r1cs.constraints().len());
    //         r1cs = reduce_linearities(r1cs, cfg());

    //         println!("Final R1cs size: {}", r1cs.constraints().len());
    //         let (prover_data, verifier_data) = r1cs.finalize(cs);
    //         match action {
    //             ProofAction::Count => (),
    //             #[cfg(feature = "bellman")]
    //             ProofAction::Setup => {
    //                 println!("Generating Parameters");
    //                 match proof_impl {
    //                     ProofImpl::Groth16 => Bellman::<Bls12>::setup_fs(
    //                         prover_data,
    //                         verifier_data,
    //                         prover_key,
    //                         verifier_key,
    //                     )
    //                     .unwrap(),
    //                     ProofImpl::Mirage => Mirage::<Bls12>::setup_fs(
    //                         prover_data,
    //                         verifier_data,
    //                         prover_key,
    //                         verifier_key,
    //                     )
    //                     .unwrap(),
    //                 };
    //             }
    //             #[cfg(not(feature = "bellman"))]
    //             ProofAction::Setup => panic!("Missing feature: bellman"),
    //             #[cfg(feature = "bellman")]
    //             ProofAction::CpSetup => {
    //                 println!("Generating Parameters");
    //                 match proof_impl {
    //                     ProofImpl::Groth16 => panic!("Groth16 is not CP"),
    //                     ProofImpl::Mirage => Mirage::<Bls12>::cp_setup_fs(
    //                         prover_data,
    //                         verifier_data,
    //                         prover_key,
    //                         verifier_key,
    //                     )
    //                     .unwrap(),
    //                 };
    //             }
    //             #[cfg(not(feature = "bellman"))]
    //             ProofAction::CpSetup => panic!("Missing feature: bellman"),
    //             #[cfg(feature = "spartan")]
    //             ProofAction::SpartanSetup => {
    //                 write_data::<_, _>(prover_key, verifier_key, &prover_data, &verifier_data)
    //                     .unwrap();
    //             }
    //             #[cfg(not(feature = "spartan"))]
    //             ProofAction::SpartanSetup => panic!("Missing feature: spartan"),
    //         }
    //     }
}


#[test]
fn test_1() {
    let s  = "ab";
    //let abvec: Vec<char> = (0..256).filter_map(std::char::from_u32).collect();
    //let ab: String = abvec.iter().collect();
    let ab = "abc".to_owned();
    naive(s,ab);
}
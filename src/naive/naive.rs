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
use crate::regex::re;
use crate::naive::naive_parser as naive_re;
use circ::front::zsharp::{self, ZSharpFE};
use circ::front::{FrontEnd, Mode};
use circ::ir::{opt::{opt, Opt}};
use circ::target::r1cs::{opt::reduce_linearities, trans::to_r1cs, ProverData, VerifierData};
use circ::cfg::*;
use neptune::{
    poseidon::PoseidonConstants,
    sponge::api::{IOPattern, SpongeAPI, SpongeOp},
    sponge::circuit::SpongeCircuit,
    sponge::vanilla::{SpongeTrait,Sponge},
    Strength,
};
use generic_array::typenum;
use nova_snark::{
    traits::{circuit::StepCircuit, Group},
    spartan::direct::*,
};
use std::fs::OpenOptions;
use csv::Writer;

#[cfg(feature = "metrics")]
use crate::metrics::{log, log::Component};


#[derive(PartialEq, Eq, Debug)]
pub enum DeterminedLanguage {
    Zsharp,
    Datalog,
    C,
}

pub fn make_delta(state:u64, c: u32, next: u64) -> String{
    format!("\tout = if (cur_state=={state} && cur_char=={c}) then {next} else out-0 fi\n")
}

pub fn make_match(state:u64) -> String{
    format!("\tmatch = if state=={state} then 1 else match-0 fi\n")
}
pub fn make_zok(dfa: DFA<'_>, doc_len: usize) -> std::io::Result<()> {
    let mut delta_base_string = "def delta(private field cur_state, private field cur_char) -> field:
    \tfield out = -1\n".to_owned();

    let mut main_base_string = format!("\n\ndef main(private field[{doc_len}] document) -> field: 
    \tfield size = {doc_len}
    \tfield state = 0
    \tfor field i in 0..size do
    \t\tstate = delta(state, document[i])
    \tendfor 
    \tfield match = 0\n").to_owned();

    for match_state in dfa.get_final_states() {
        main_base_string.push_str(&(make_match(match_state).to_owned()));
    }
    main_base_string.push_str("\tassert(match==1)\n\treturn match");


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
    let final_r1cs = r1cs.finalize(&cs);

    return final_r1cs;
}

pub fn naive_bench(r: String, alpha: String, doc: String, out_write:PathBuf) {
    init();

    let doc_vec: Vec<u32> = doc.chars().map(|x| x as u32).collect();
    let doc_len = doc_vec.len();

    #[cfg(feature = "metrics")]
    log::tic(Component::Compiler, "DFA", "DFA");

    let regex = re::simpl(re::new(&(r.clone())));

    let dfa = DFA::new(&alpha[..],naive_re::re::translate(&regex, &alpha[..]));
    let dfa_ndelta = dfa.deltas().len();
    let dfa_nstate = dfa.nstates();

    #[cfg(feature = "metrics")]
    log::stop(Component::Compiler, "DFA", "DFA");

    #[cfg(feature = "metrics")]
    log::tic(Component::Solver, "DFA Solving", "Clear Match");

    let is_match = dfa.is_match(&doc);
    let is_match_g = <G1 as Group>::Scalar::from(is_match as u64);

    #[cfg(feature = "metrics")]
    log::stop(Component::Solver, "DFA Solving", "Clear Match");

    #[cfg(feature = "metrics")]
    log::tic(Component::Compiler, "Circuit Gen", "Zok");

    let _ = make_zok(dfa, doc_len);
    
    #[cfg(feature = "metrics")]
    log::stop(Component::Compiler, "Circuit Gen", "Zok");

    #[cfg(feature = "metrics")]
    log::tic(Component::Compiler, "Circuit Gen", "r1cs");

    let (P,V) = gen_r1cs();
    
    #[cfg(feature = "metrics")]
    log::stop(Component::Compiler, "Circuit Gen", "r1cs");

    #[cfg(feature = "metrics")]
    log::r1cs(Component::Compiler, "Circuit Gen", "r1cs",P.r1cs.constraints.len());

    let pc: PoseidonConstants<<G1 as Group>::Scalar, typenum::U4> = Sponge::<<G1 as Group>::Scalar, typenum::U4>::api_constants(Strength::Standard);

    #[cfg(feature = "metrics")]
    log::tic(Component::Compiler, "R1CS", "Commitment Generations");
    let commitment = gen_commitment(doc_vec.clone(), &pc);

    #[cfg(feature = "metrics")]
    log::stop(Component::Compiler, "R1CS", "Commitment Generations");

    #[cfg(feature = "metrics")]
    log::tic(Component::Compiler, "R1CS", "To Circuit");
    let circuit = NaiveCircuit::new(P.r1cs.clone(), None, doc_len, pc.clone(), commitment.blind,commitment.commit,is_match_g);

    #[cfg(feature = "metrics")]
    log::stop(Component::Compiler, "R1CS", "To Circuit");

    #[cfg(feature = "metrics")]
    log::tic(Component::Compiler, "R1CS", "Proof Setup");
    let (pk, vk) = naive_spartan_snark_setup(circuit);

    #[cfg(feature = "metrics")]
    log::stop(Component::Compiler, "R1CS", "Proof Setup");

    #[cfg(feature = "metrics")]
    log::tic(Component::Solver, "Witnesses", "Generation");
    let witnesses = gen_wits(doc_vec.clone(), is_match, doc_len, &P);
    #[cfg(feature = "metrics")]
    log::stop(Component::Solver, "Witnesses", "Generation");

    #[cfg(feature = "metrics")]
    log::tic(Component::Prover, "Proof", "Adding witnesses");

    let prove_circuit = NaiveCircuit::new(P.r1cs.clone(),witnesses, doc_len, pc.clone(), commitment.blind, commitment.commit, is_match_g);

    #[cfg(feature = "metrics")]
    log::stop(Component::Prover, "Proof", "Adding witnesses");

    let z = vec![commitment.commit];

    #[cfg(feature = "metrics")]
    log::tic(Component::Prover, "Proof", "Prove");

    let result = SpartanSNARK::prove(&pk,prove_circuit.clone(),&z);

    #[cfg(feature = "metrics")]
    log::stop(Component::Prover, "Proof", "Prove");

    assert!(result.is_ok());

    let output = prove_circuit.output(&z);

    let snark = result.unwrap();

    #[cfg(feature = "metrics")]
    log::space(
        Component::Prover,
        "Proof Size",
        "Spartan SNARK size",
        serde_json::to_string(&snark).unwrap().len(),
    );

    // verify the SNARK
    #[cfg(feature = "metrics")]
    log::tic(Component::Verifier, "Verify", "Verify");

    let io = z.into_iter()
      .chain(output.clone().into_iter())
      .collect::<Vec<_>>();
    let verifier_result = snark.verify(&vk, &io);

    #[cfg(feature = "metrics")]
    log::stop(Component::Verifier, "Verify", "Verify");
    assert!(verifier_result.is_ok()); 

    let file = OpenOptions::new().write(true).append(true).create(true).open(out_write.clone()).unwrap();
    let mut wtr = Writer::from_writer(file);
    let _ = wtr.write_record(&[
    doc,
    r,
    dfa_ndelta.to_string(), //nedges().to_string(),
    dfa_nstate.to_string(), //nstates().to_string(),
    ]);
    let spacer = "---------";
    let _ = wtr.write_record(&[spacer, spacer, spacer, spacer]);
    wtr.flush();

    #[cfg(feature = "metrics")]
    log::write_csv(&out_write).unwrap();
   
}


#[test]
fn test_1() {
    let r  = "[a-c]{1,3}".to_string();
    let ab = "abcABC0123".to_owned();
    let doc = "bb".to_owned();
    naive_bench(r,ab, doc, PathBuf::from("out_test"));
}
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
pub fn make_vanishing(size: usize,name:&str,idx_string: String)-> String {
    format!("def vanishing_{name}(private field cur_index) -> field:
	field out = 1
    field[{size}] idxs = {idx_string}
	for field i in 0..{size} do
		out = out * (idxs[i]-cur_index)
	endfor
	return out\n")
}

pub fn make_idx_string(dfa: &DFA<'_>, n_char: u64) -> String {
    let mut out:String = "[".to_string();
    let n_state = dfa.nstates() as u64;
    for (in_state, c, out_state) in dfa.deltas() {
        let value = in_state*n_state*n_char + (c as u64)*n_state + out_state;
        let single = format!("{},",value);
        out.push_str(&single);
    }
    out.pop();
    out.push(']');
    out
}


pub fn make_match_string(dfa: &DFA<'_>) -> String {
    let mut out:String = "[".to_string();
    for s in dfa.get_final_states() {
        let single = format!("{},",s);
        out.push_str(&single);
    }
    out.pop();
    out.push(']');
    out
}

pub fn make_main(doc_len: usize,prover_states: usize,deltas:usize,n_accepting:usize, n_char: usize, n_states: usize, name1:&str,name2:&str)->String{
    format!("def main(private field[{doc_len}] document, private field[{prover_states}] prover_states) -> field: 
    assert(prover_states[0]==0)
	field valid_state = -1
	field combined_idx = 0
    for field i in 1..{prover_states} do
		combined_idx = prover_states[i-1]*{n_states}*{n_char} + document[i-1]*{n_states} + prover_states[i]
    	valid_state = vanishing_{name1}(combined_idx)
		assert(valid_state==0)
    endfor 
    field match = 0
	match = vanishing_{name2}(prover_states[{doc_len}])
	assert(match==0)
	return match")
}

pub fn make_zok(dfa: &DFA<'_>, doc_len: usize, n_char: usize) -> std::io::Result<()> {
    let mut final_string = make_vanishing(dfa.deltas().len(),"trans",make_idx_string(&dfa, n_char as u64)); 
    final_string.push_str(&make_vanishing(dfa.get_final_states().len(),"match",make_match_string(&dfa)));

    final_string.push_str(&make_main(doc_len, doc_len+1, dfa.deltas().len(), dfa.get_final_states().len(), n_char,dfa.nstates(),"trans","match"));
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

    println!("To DFA");

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

    println!("Make Zok");

    let _ = make_zok(&dfa, doc_len,alpha.len());
    
    #[cfg(feature = "metrics")]
    log::stop(Component::Compiler, "Circuit Gen", "Zok");

    #[cfg(feature = "metrics")]
    log::tic(Component::Compiler, "Circuit Gen", "r1cs");

    println!("gen r1cs");

    let (P,V) = gen_r1cs();
    
    #[cfg(feature = "metrics")]
    log::stop(Component::Compiler, "Circuit Gen", "r1cs");

    #[cfg(feature = "metrics")]
    log::r1cs(Component::Compiler, "Circuit Gen", "r1cs",P.r1cs.constraints.len());

    let pc: PoseidonConstants<<G1 as Group>::Scalar, typenum::U4> = Sponge::<<G1 as Group>::Scalar, typenum::U4>::api_constants(Strength::Standard);

    #[cfg(feature = "metrics")]
    log::tic(Component::Compiler, "R1CS", "Commitment Generations");

    println!("Gen commitment");

    let commitment = gen_commitment(doc_vec.clone(), &pc);

    #[cfg(feature = "metrics")]
    log::stop(Component::Compiler, "R1CS", "Commitment Generations");

    #[cfg(feature = "metrics")]
    log::tic(Component::Compiler, "R1CS", "To Circuit");

    println!("To circuit");

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
    println!("Wit gen");

    let witnesses = gen_wits(doc_vec.clone(), is_match, doc_len, solution, &dfa, alpha.len(), &P);
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
    log::write_csv(&out_write.as_path().display().to_string()).unwrap();
   
}


#[test]
fn test_1() {
    let r  = "[a-z]{1,5}[A-Z]{10}[0-9]+abc".to_string();
    let abvec: Vec<char> = (0..128).filter_map(std::char::from_u32).collect();
    let ab: String = "abcdefghijklmnopqrstuvwxyz1234567890QWERTYUIOPASDFGHJKLZXCVBNM".to_string();
    //abvec.iter().collect();
    let doc = "nPPZEKVUVLQ10abc".to_owned();
    naive_bench(r,ab, doc, PathBuf::from("out_test"));
}
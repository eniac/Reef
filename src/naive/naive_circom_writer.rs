#![allow(missing_docs, non_snake_case)]

use std::fs::File;
use std::io::prelude::*;
use crate::naive::dfa::*; 

pub fn make_vanishing(size: usize,name:&str,idx_string: String)-> String {
    format!("function roots{name}(i) {{
	var roots[{size}] = {idx_string};
	return roots[i];
    }}\n")
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

pub fn make_utils(dfa: &DFA<'_>, doc_len: usize, n_char: usize) -> std::io::Result<()> {
    let mut final_string:String = "pragma circom 2.0.3;
    template Multiplier2 () {  

        // Declaration of signals.  
        signal input in1;  
        signal input in2;  
        signal output out;  
     
        // Constraints.  
        out <== in1 * in2;  
     }
     
     template MultiplierN (N){
        //Declaration of signals and components.
        signal input in[N];
        signal output out;
        component comp[N-1];
     
        //Statements.
        for(var i = 0; i < N-1; i++){
            comp[i] = Multiplier2();
        }
     
         comp[0].in1 <== in[0];
         comp[0].in2 <== in[1];
         for(var i = 0; i < N-2; i++){
            comp[i+1].in1 <== comp[i].out;
            comp[i+1].in2 <== in[i+2]; 
         }
         out <== comp[N-2].out; 
     }\n".to_string();
    
    final_string.push_str(&make_vanishing(dfa.deltas().len(),"Trans",make_idx_string(&dfa, n_char as u64))); 

    final_string.push_str(&make_vanishing(dfa.get_final_states().len(),"Match",make_match_string(&dfa)));

    let mut file = File::create("utils.circom")?;
    file.write_all(final_string.as_bytes())?;
    Ok(())
}


pub fn make_main(doc_len: usize,prover_states: usize,deltas:usize,n_accepting:usize, n_char: usize, n_states: usize)->String{
    format!("pragma circom 2.0.3;

    include \"utils.circom\";
    
    template IsValidTrans() {{
        signal input curIndex;
        signal output out;
    
        component runningProduct = MultiplierN({deltas});

        for (var i = 0; i < {deltas}; i++) {{
            runningProduct.in[i] <== rootsTrans(i) - curIndex;
        }}
        out <== runningProduct.out;
    }}
    
    template IsValidMatch() {{
        signal input in;
        signal output out;
    
        component runningProduct = MultiplierN({n_accepting});
    
        for (var i = 0; i < {n_accepting}; i++) {{
            runningProduct.in[i] <== rootsMatch(i) - in;
        }}
        out <== runningProduct.out;
    }}
    
    template Main () {{
        signal input doc[{doc_len}];
        signal input prover_states[{prover_states}];
    
        signal output match;
    
        component valid_state[{doc_len}];
        component valid_match;
    
        prover_states[0]===0;
    
        for (var j=1;j<{prover_states};j++) {{
            valid_state[j-1] = IsValidTrans();
            valid_state[j-1].curIndex <== prover_states[j-1]*{n_states}*{n_char} + doc[j-1]*{n_states} +
            prover_states[j];
        }}
        valid_match = IsValidMatch();
        valid_match.in <== prover_states[{doc_len}];
    
        valid_match.out === 0;
    
        match <== valid_match.out;
    }}
    
    component main = Main();")
}

pub fn make_circom(dfa: &DFA<'_>, doc_len: usize, n_char: usize) -> std::io::Result<()> {
    make_utils(dfa, doc_len, n_char);
    let mut final_string = make_main(doc_len, doc_len+1, dfa.deltas().len(), dfa.get_final_states().len(), n_char,dfa.nstates());
    let mut file = File::create("match.circom")?;
    file.write_all(final_string.as_bytes())?;
    Ok(())
}
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
    let mut final_string:String = "
pragma circom 2.0.3;
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
}

template Poseidon4() {
    signal input in1;
    signal input in2;
    signal input in3; 
    signal input in4; 

    signal output out; 

    component p = Poseidon(4);
    p.inputs[0] <== in1;
    p.inputs[1] <== in2;
    p.inputs[2] <== in3;
    p.inputs[3] <== in4;

    out <== p.out;
}

template PoseidonMulti(N) {
    signal input in[N];
    signal input blind;
    signal output out;

    var nHashes = N\\3;

    component hashes[nHashes];

    for (var i = 0; i < nHashes;i++) { 
        hashes[i] = Poseidon4();
    }

    var cursor = 0;
    hashes[0].in1 <== blind; 
    hashes[0].in2 <== in[0];
    hashes[0].in3 <== in[1];
    hashes[0].in4 <== in[2];
    
    cursor+=2;

    for (var i = 0; i < nHashes-1; i++) {
        hashes[i+1].in1 <== hashes[i].out;
        hashes[i+1].in2 <== in[cursor+1];
        hashes[i+1].in3 <== in[cursor+2];
        hashes[i+1].in4 <== in[cursor+3];
        cursor+=3;
    }

    var rem = N%3;
    if (rem==0) {
        out <== hashes[nHashes-1].out;
    } else {
        component final = Poseidon(rem+1);
        final.inputs[0] <== hashes[nHashes-1].out;
        for (var i=1; i<=rem; i++) { 
            final.inputs[i] <== in[cursor+i];
        }
        out <== final.out;
        
    }

}

template IsZero() {
    signal input in;
    signal output out;
    signal inv;
    inv <-- in!=0 ? 1/in : 0;
    out <== -in*inv +1;
    in*out === 0;
}\n".to_string();
    
    final_string.push_str(&make_vanishing(dfa.deltas().len(),"Trans",make_idx_string(&dfa, n_char as u64))); 

    final_string.push_str(&make_vanishing(dfa.get_final_states().len(),"Match",make_match_string(&dfa)));

    let mut file = File::create("utils.circom")?;
    file.write_all(final_string.as_bytes())?;
    Ok(())
}


pub fn make_main(doc_len: usize,deltas:usize,n_accepting:usize, n_char: usize, n_states: usize)->String{
    let valid_match_body: String;
    if (n_accepting == 1) {
        valid_match_body = "isZero.in <== rootsMatch(0) - in;".to_string();
    } else {
        valid_match_body = format!("component runningProduct = MultiplierN({n_accepting});
    
        for (var i = 0; i < {n_accepting}; i++) {{
            runningProduct.in[i] <== rootsMatch(i) - in;
        }}
        isZero.in <== runningProduct.out;");
    }

    format!("pragma circom 2.0.3;

    include \"utils.circom\";
    include \"./Nova-Scotia/circomlibs/poseidon.circom\";
    
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
        
        component isZero = IsZero();

        {valid_match_body}
        out <== isZero.out;
    }}
    
    template Main () {{
        signal input cur_state;
        signal input next_state; 
        signal input char;

        signal input step_in[3];
        signal output step_out[3];

        signal running_hash <== step_in[1];
        signal index <== step_in[0];

        component indexIsZero = IsZero();
        indexIsZero.in <== index;
    
        component valid_state;
        
        valid_state = IsValidTrans();
        valid_state.curIndex <== cur_state*{n_states}*{n_char} + char*{n_states} + next_state;
        valid_state.out === 0;

        cur_state*indexIsZero.out === 0;

        component valid_match;
        valid_match = IsValidMatch();
        valid_match.in <== next_state;

        component hash = Poseidon(2);
        hash.inputs[0] <==running_hash;

        hash.inputs[1] <== char;

        step_out[0] <== index + 1;
        step_out[1] <== hash.out;
        step_out[2] <== valid_match.out;
    }}
    
    component main {{ public [step_in] }}= Main();")
}

pub fn make_circom(dfa: &DFA<'_>, doc_len: usize, n_char: usize) -> std::io::Result<()> {
    make_utils(dfa, doc_len, n_char);
    let mut final_string = make_main(doc_len, dfa.deltas().len(), dfa.get_final_states().len(), n_char,dfa.nstates());
    let mut file = File::create("match.circom")?;
    file.write_all(final_string.as_bytes())?;
    Ok(())
}
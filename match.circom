pragma circom 2.0.3;

    include "utils.circom";
    include "./third_party/Nova-Scotia/circomlibs/poseidon.circom";
    
    template IsValidTrans() {
        signal input curIndex;
        signal output out;
    
        component runningProduct = MultiplierN(24);

        for (var i = 0; i < 24; i++) {
            runningProduct.in[i] <== rootsTrans(i) - curIndex;
        }
        out <== runningProduct.out;
    }
    
    template IsValidMatch() {
        signal input in;
        signal output out;
    
        component runningProduct = MultiplierN(5);
        component isZero = IsZero();
    
    
        for (var i = 0; i < 5; i++) {
            runningProduct.in[i] <== rootsMatch(i) - in;
        }
        isZero.in <== runningProduct.out;
        out <== isZero.out;
    }
    
    template Main () {
        signal input doc_len;
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
        valid_state.curIndex <== cur_state*8*3 + char*8 + next_state;
        valid_state.out === 0;

        cur_state*indexIsZero.out === 0;

        component valid_match;
        valid_match = IsValidMatch();
        valid_match.in <== cur_state;

        component hash = Poseidon(2);
        hash.inputs[0] <==running_hash;

        hash.inputs[1] <== char;

        step_out[0] <== index + 1;
        step_out[1] <== hash.out;
        step_out[2] <== valid_match.out;
    }
    
    component main = Main();
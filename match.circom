pragma circom 2.0.3;

    include "utils.circom";
    include "./third_party/Nova-Scotia/circomlibs/poseidon.circom";
    
    template IsValidTrans() {
        signal input curIndex;
        signal output out;
    
        component runningProduct = MultiplierN(48640);

        for (var i = 0; i < 48640; i++) {
            runningProduct.in[i] <== rootsTrans(i) - curIndex;
        }
        out <== runningProduct.out;
    }
    
    template IsValidMatch() {
        signal input in;
        signal output out;
        
        component isZero = IsZero();

        component runningProduct = MultiplierN(238);
    
        for (var i = 0; i < 238; i++) {
            runningProduct.in[i] <== rootsMatch(i) - in;
        }
        isZero.in <== runningProduct.out;
        out <== isZero.out;
    }
    
    template Main () {
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
        valid_state.curIndex <== cur_state*380*128 + char*380 + next_state;
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
    }
    
    component main { public [step_in] }= Main();
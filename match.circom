pragma circom 2.0.3;

    include "utils.circom";
    include "./Nova-Scotia/circomlibs/poseidon.circom";
    
    template IsValidTrans() {
        signal input curIndex;
        signal output out;
    
        component runningProduct = MultiplierN(12);

        for (var i = 0; i < 12; i++) {
            runningProduct.in[i] <== rootsTrans(i) - curIndex;
        }
        out <== runningProduct.out;
    }
    
    template IsValidMatch() {
        signal input in;
        signal output out;
        
        component isZero = IsZero();

        component runningProduct = MultiplierN(3);
    
        for (var i = 0; i < 3; i++) {
            runningProduct.in[i] <== rootsMatch(i) - in;
        }
        isZero.in <== runningProduct.out;
        out <== isZero.out;
    }
    
    template Main () {
        signal input cur_state;
        signal input next_state; 
        signal input char;

        signal input step_in[4];
        signal output step_out[4];

        signal running_hash <== step_in[1];
        signal index <== step_in[0];
        signal cur_state_hash_in <== step_in[3];

        component indexIsZero = IsZero();
        indexIsZero.in <== index;

        component cur_state_hash = Poseidon(1);
        cur_state_hash.inputs[0] <== cur_state;

        component switcher  = Switcher();
        switcher.sel <== indexIsZero.out; 
        switcher.L <== cur_state_hash.out; 
        switcher.R <== cur_state_hash_in;

        cur_state_hash_in === switcher.outL;

        var temp_hash;
        temp_hash = cur_state_hash.out;

        component valid_state;
        
        valid_state = IsValidTrans();
        valid_state.curIndex <== cur_state*4*3 + char*4 + next_state;
        valid_state.out === 0;

        cur_state*indexIsZero.out === 0;

        component valid_match;
        valid_match = IsValidMatch();
        valid_match.in <== next_state;

        component hash = Poseidon(2);
        hash.inputs[0] <==running_hash;

        hash.inputs[1] <== char;

        component next_state_hash = Poseidon(1);
        next_state_hash.inputs[0] <== next_state;

        step_out[0] <== index + 1;
        step_out[1] <== hash.out;
        step_out[2] <== valid_match.out;
        step_out[3] <== next_state_hash.out;

    }
    
    component main { public [step_in] }= Main();
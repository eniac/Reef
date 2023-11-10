pragma circom 2.0.3;

    include "utils.circom";
    include "./Nova-Scotia/circomlibs/poseidon.circom";
    
    template IsValidTrans() {
        signal input curIndex;
        signal output out;
    
        component runningProduct = MultiplierN(12032);

        for (var i = 0; i < 12032; i++) {
            runningProduct.in[i] <== rootsTrans(i) - curIndex;
        }
        out <== runningProduct.out;
    }
    
    template IsValidMatch() {
        signal input in;
        signal output out;

        component runningProduct = MultiplierN(52);
    
        for (var i = 0; i < 52; i++) {
            runningProduct.in[i] <== rootsMatch(i) - in;
        }
        out <== runningProduct.out;
       
    }
    
    template Main () {
        signal input doc[128];
        signal input prover_states[129];
        signal input blind;

        signal input step_in[1];
    
        signal output hashed;
    
        component valid_state[128];
        component valid_match;
    
        prover_states[0]===0;
    
        for (var j=1;j<129;j++) {
            valid_state[j-1] = IsValidTrans();
            valid_state[j-1].curIndex <== prover_states[j-1]*94*128 + doc[j-1]*94 +
            prover_states[j];
            valid_state[j-1].out === 0;
        }
        valid_match = IsValidMatch();
        valid_match.in <== prover_states[128];
    
        valid_match.out === 0;

        component hash = PoseidonMulti(128);
        hash.in <== doc;
        hash.blind <== blind;
    
        hashed<==hash.out;
    }
    
    component main {public [step_in]} = Main();
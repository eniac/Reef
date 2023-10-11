pragma circom 2.0.3;

    include "utils.circom";
    include "./Nova-Scotia/circomlibs/poseidon.circom";
    
    template IsValidTrans() {
        signal input curIndex;
        signal output out;
    
        component runningProduct = MultiplierN(55424);

        for (var i = 0; i < 55424; i++) {
            runningProduct.in[i] <== rootsTrans(i) - curIndex;
        }
        out <== runningProduct.out;
    }
    
    template IsValidMatch() {
        signal input in;
        signal output out;

        out <== rootsMatch(0) - in;
       
    }
    
    template Main () {
        signal input doc[415];
        signal input prover_states[416];
        signal input blind;

        signal input step_in[1];
    
        signal output hashed;
    
        component valid_state[415];
        component valid_match;
    
        prover_states[0]===0;
    
        for (var j=1;j<416;j++) {
            valid_state[j-1] = IsValidTrans();
            valid_state[j-1].curIndex <== prover_states[j-1]*433*128 + doc[j-1]*433 +
            prover_states[j];
            valid_state[j-1].out === 0;
        }
        valid_match = IsValidMatch();
        valid_match.in <== prover_states[415];
    
        valid_match.out === 0;

        component hash = PoseidonMulti(415);
        hash.in <== doc;
        hash.blind <== blind;
    
        hashed<==hash.out;
    }
    
    component main {public [step_in]} = Main();
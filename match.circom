pragma circom 2.0.3;

    include "utils.circom";
    include "./third_party/Nova-Scotia/circomlibs/poseidon.circom";
    
    template IsValidTrans() {
        signal input curIndex;
        signal output out;
    
        component runningProduct = MultiplierN(8448);

        for (var i = 0; i < 8448; i++) {
            runningProduct.in[i] <== rootsTrans(i) - curIndex;
        }
        out <== runningProduct.out;
    }
    
    template IsValidMatch() {
        signal input in;
        signal output out;

        component runningProduct = MultiplierN(59);
    
        for (var i = 0; i < 59; i++) {
            runningProduct.in[i] <== rootsMatch(i) - in;
        }
        out <== runningProduct.out;
       
    }
    
    template Main () {
        signal input doc[2000];
        signal input prover_states[2001];
        signal input blind;
    
        signal output hashed;
    
        component valid_state[2000];
        component valid_match;
    
        prover_states[0]===0;
    
        for (var j=1;j<2001;j++) {
            valid_state[j-1] = IsValidTrans();
            valid_state[j-1].curIndex <== prover_states[j-1]*66*128 + doc[j-1]*66 +
            prover_states[j];
            valid_state[j-1].out === 0;
        }
        valid_match = IsValidMatch();
        valid_match.in <== prover_states[2000];
    
        valid_match.out === 0;

        component hash = PoseidonMulti(2000);
        hash.in <== doc;
        hash.blind <== blind;
    
        hashed<==hash.out;
    }
    
    component main = Main();
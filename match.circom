pragma circom 2.0.3;

    include "utils.circom";
    include "./third_party/Nova-Scotia/circomlibs/poseidon.circom";
    
    //Checks if a transition is a valid using a combined index
    template IsValidTrans() {
        signal input curIndex;
        signal output out;

        //Set up multiplier for total number of states
        component runningProduct = MultiplierN(18);

        for (var i = 0; i < 18; i++) {
            runningProduct.in[i] <== rootsTrans(i) - curIndex;
        }
        out <== runningProduct.out;
    }
    
    //Check if end state is accepting
    template IsValidMatch() {
        signal input in;
        signal output out;

        //Multiplier with a slot for each of the accepting states
        component runningProduct = MultiplierN(3);

        for (var i = 0; i < 3; i++) {
            runningProduct.in[i] <== rootsMatch(i) - in;
        }
        out <== runningProduct.out;
    }
    
    template Main () {
        signal input doc[3];
        signal input prover_states[4];
        signal input blind;
    
        signal output hashed;

        //Since singals are immutable create components for the tempaltes 
        component valid_state[3];
        component valid_match;

        //Have to create a blinded version of the document in the circuit 
        signal blinded_doc[4];
        blinded_doc[0] <== blind; 
        
        for (var j=0;j<3;j++) {
            blinded_doc[j+1] <== doc[j];
        }

        //Assert the first prover state is 0
        prover_states[0]===0;

        //For each transition make the combined index and assert is valid 
        for (var j=1;j<4;j++) {
            valid_state[j-1] = IsValidTrans();
            valid_state[j-1].curIndex <== prover_states[j-1]*6*3 + doc[j-1]*6 +
            prover_states[j];
            valid_state[j-1].out === 0;
        }

        //Check whether the final state is accepting 
        valid_match = IsValidMatch();
        valid_match.in <== prover_states[3];
    
        valid_match.out === 0;

        //Hash the blinded document and return the hash 
        component hash = Poseidon(4);
        hash.inputs <== blinded_doc;
    
        hashed<==hash.out;
    }
    
    component main = Main();
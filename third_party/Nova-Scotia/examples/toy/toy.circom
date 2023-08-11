pragma circom 2.0.3;

// include
//"https://github.com/0xPARC/circom-secp256k1/blob/master/circuits/bigint.circom";
include "utils.circom";

template IsValidTrans() {
    signal input curIndex;
    signal output out;

    component runningProduct = MultiplierN(3);

    for (var i = 0; i < 3; i++) {
        runningProduct.in[i] <== rootsTrans(i) - curIndex;
    }
    out <== runningProduct.out;
}

template IsValidMatch() {
    signal input in;
    signal output out;

    component runningProduct = MultiplierN(2);

    for (var i = 0; i < 2; i++) {
        runningProduct.in[i] <== rootsMatch(i) - in;
    }
    out <== runningProduct.out;
}

template Example () {
    signal input doc[4];
    signal input prover_states[5];

    signal output match;

    component valid_state[4];
    component valid_match;

    prover_states[0]===0;

    for (var j=1;j<5;j++) {
        valid_state[j-1] = IsValidTrans();
        valid_state[j-1].curIndex <== prover_states[j-1]*34*28 + doc[j-1]*34 +
        prover_states[j];
    }
    valid_match = IsValidMatch();
    valid_match.in <== prover_states[4];

    valid_match.out === 0;

    match <== valid_match.out;
}

component main = Example();

/* INPUT = {
    "step_in": [1, 1],
    "step_out": [1, 2],
    "adder": 0
} */
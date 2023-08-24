
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

    var nHashes = N\3;

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
}
function rootsTrans(i) {
	var roots[24] = [946,959,785,851,908,868,877,836,916,942,793,823,776,899,827,886,860,815,967,925,844,894,934,802];
	return roots[i];
    }
function rootsMatch(i) {
	var roots[5] = [4,5,2,6,3];
	return roots[i];
    }

pragma circom 2.0.3;

function rootsTrans(i) {
    var roots[3] = [
        10,
        20,
        30
    ];
    return roots[i];
}

function rootsMatch(i) {
    var roots[2] = [
        40,
        50
    ];
    return roots[i];
}


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
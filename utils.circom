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
function rootsTrans(i) {
	var roots[18] = [612,624,619,658,665,608,681,645,687,601,594,633,583,640,676,669,588,651];
	return roots[i];
    }
function rootsMatch(i) {
	var roots[3] = [4,3,5];
	return roots[i];
    }

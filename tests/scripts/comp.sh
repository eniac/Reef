cargo clean 
# cargo build --release --features 'metrics,reef'
#  echo "reef"
# ./tests/scripts/reef.sh &> out_reef
#  echo "end reef"

#  echo "reef h"
# ./tests/scripts/reef_h.sh &> out_rh 
#  echo "reef h"

cargo build --release --features 'metrics,nwr'
 echo "nwr"
./tests/scripts/nwr.sh &> out_nwr 
 echo "nwr"

cargo build --release --features 'metrics,naive'
 echo "naive"
./tests/scripts/naive.sh &> out_naive 
 echo "naive" 

cargo build --release --features 'metrics,reef'
 echo "dna"
./tests/scripts/dna.sh &> out_dna 
 echo "naive" 
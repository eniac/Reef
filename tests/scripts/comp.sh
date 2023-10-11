cargo clean 
cargo build --release --features 'metrics,reef'
 echo "reef"
RUST_BACKTRACE=1 ./target/release/reef --input 'adimage101.adserver99.telemetry.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-1234323' --output ./tests/results/pihole_2.txt --re '^(.+[_.-])?adse?rv(er?|ice)?s?[0-9]*[_.-]' ascii
# ./tests/scripts/reef.sh &> out_reef
 echo "end reef"

echo "reef h"
RUST_BACKTRACE=1 ./target/release/reef --input 'adimage101.adserver99.telemetry.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-1234323' --output ./tests/results/pihole_hybrid_2.txt --re '^(.+[_.-])?adse?rv(er?|ice)?s?[0-9]*[_.-]' -y ascii
# ./tests/scripts/reef_h.sh &> out_rh 
echo "reef h"

cargo build --release --features 'metrics,nwr'
echo "nwr"
RUST_BACKTRACE=1 ./target/release/reef --input "adimage101.adserver99.telemetry.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-1234323" --output ./tests/results/pihole_nwr_2.txt --re "^(.+[_.-])?adse?rv(er?|ice)?s?[0-9]*[_.-]" ascii
#./tests/scripts/nwr.sh &> out_nwr 
echo "nwr"

cargo build --release --features 'metrics,naive'
echo "naive"
#./tests/scripts/naive.sh &> out_naive 
RUST_BACKTRACE=1 ./target/release/reef --input 'adimage101.adserver99.telemetry.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-1234323' --output ./tests/results/pihole_naive_2.txt --re "^(.+[_.-])?adse?rv(er?|ice)?s?[0-9]*[_.-]" ascii
echo "naive" 

# cargo build --release --features 'metrics,reef'
# echo "dna"
#./tests/scripts/dna.sh &> out_dna 
 #echo "dna" 

 # cargo build --release --features 'metrics,reef'
 echo "email"
./tests/scripts/email_dkim.sh &> out_email
 echo "email" 


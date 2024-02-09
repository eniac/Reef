cargo clean 
cargo build --release --features 'metrics'
echo "reef"
./tests/scripts/reef.sh &> out_reef

echo "safa+nlookup"
./tests/scripts/safa_nlookup.sh &> out_safa_nlookup
echo "end safa+nlookup"

cargo clean 
cargo build --release --features 'metrics,nwr'
echo "nwr"
./tests/scripts/nwr.sh &> out_nwr
echo "end nwr"

cargo clean 
cargo build --release --features 'metrics,naive'
echo "naive"
./tests/scripts/naive.sh &> out_naive
echo "end naive" 
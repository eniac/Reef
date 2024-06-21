echo "reef"
./tests/scripts/reef.sh &> out_reef

echo "safa+nlookup"
./tests/scripts/safa_nlookup.sh &> out_safa_nlookup
echo "end safa+nlookup"

echo "nwr"
./tests/scripts/nwr.sh &> out_nwr
echo "end nwr"

echo "naive"
./tests/scripts/naive.sh &> out_naive
echo "end naive" 

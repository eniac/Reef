echo "reef"
./tests/scripts/reef-mini.sh &> out_reef_mini

echo "safa+nlookup"
./tests/scripts/safa_nlookup-mini.sh &> out_safa_nlookup_mini
echo "end safa+nlookup"

echo "nwr"
./tests/scripts/nwr-mini.sh &> out_nwr_mini
echo "end nwr"

echo "naive"
./tests/scripts/naive-mini.sh &> out_naive_mini
echo "end naive" 
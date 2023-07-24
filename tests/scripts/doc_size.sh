#./target/release/reef --input "nPPZEKVUVLQ10abc" --output ./tests/results/doc_size_naive.txt --re "[a-z]{1,5}[A-Z]{10}[0-9]+abc" ascii

#./target/release/reef --input "ctcCOGVETVRQB13290901abc|CpApLaC" --output ./tests/results/doc_size_naive.txt --re "[a-z]{1,5}[A-Z]{10}[0-9]+abc" ascii

#./target/release/reef --input "jnohMTVBOGTEGK3335990278887703997272653abco!\|{y)|+R-sv_#7)KB@|S" --output ./tests/results/doc_size_naive.txt --re "[a-z]{1,5}[A-Z]{10}[0-9]+abc" ascii

#./target/release/reef --input ./tests/docs/doclen_2pow8_90state --output ./tests/results/doc_size_naive.txt --re "[a-z]{1,5}[A-Z]{10}[0-9]+abc" ascii
./target/release/reef --input ./tests/docs/doclen_2pow10_90state --output ./tests/results/doc_size_naive.txt --re "[a-z]{1,5}[A-Z]{10}[0-9]+abc" ascii
./target/release/reef --input ./tests/docs/doclen_2pow12_90state --output ./tests/results/doc_size_naive.txt --re "[a-z]{1,5}[A-Z]{10}[0-9]+abc" ascii
./target/release/reef --input ./tests/docs/doclen_2pow14_90state --output ./tests/results/doc_size_naive.txt --re "[a-z]{1,5}[A-Z]{10}[0-9]+abc" ascii

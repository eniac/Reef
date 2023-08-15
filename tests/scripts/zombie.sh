./target/release/reef --input ./tests/docs/date_100B --output ./tests/results/zombie_naive.txt --re "([0-9][0-9]?)/([0-9][0-9]?)/([0-9][0-9]([0-9][0-9])?)" ascii
#./target/release/reef --input ./tests/docs/date_2000B --output ./tests/results/zombie_naive.txt --re "([0-9][0-9]?)/([0-9][0-9]?)/([0-9][0-9]([0-9][0-9])?)" ascii
#./target/release/reef --input ./tests/docs/DLP_100B --output ./tests/results/zombie_naive.txt --re "(([0-9a-zA-Z][0-9]{8})|([0-9]{3}[-\s]?[0-9]{2}?[-\s]?[0-9]{4})|(([0-9]{3}\s){2}[0-9]{3})|([0-9]{6,17})|(9[0-9]{2}[-\s]?(5[0-9]|6[0-5]|7[0-9]|8[0-8]|9([0-2]|[4-9]))[-\s]?[0-9]{4}))" ascii
#./target/release/reef --input ./tests/docs/DLP_2000B --output ./tests/results/zombie_naive.txt --re "(([0-9a-zA-Z][0-9]{8})|([0-9]{3}[-\s]?[0-9]{2}?[-\s]?[0-9]{4})|(([0-9]{3}\s){2}[0-9]{3})|([0-9]{6,17})|(9[0-9]{2}[-\s]?(5[0-9]|6[0-5]|7[0-9]|8[0-8]|9([0-2]|[4-9]))[-\s]?[0-9]{4}))" ascii
#./target/release/reef --input ./tests/docs/email_100B --output ./tests/results/zombie_naive.txt --re "([^ @]+)@([^ @]+)" ascii
#./target/release/reef --input ./tests/docs/email_2000B --output ./tests/results/zombie_naive.txt --re "([^ @]+)@([^ @]+)" ascii
#./target/release/reef --input ./tests/docs/uri_100B --output ./tests/results/zombie_naive.txt --re "([a-zA-Z][a-zA-Z0-9]*)://([^ /]+)(/[^ ]*)?" ascii
#./target/release/reef --input ./tests/docs/uri_2000B --output ./tests/results/zombie_naive.txt --re " ([a-zA-Z][a-zA-Z0-9]*)://([^ /]+)(/[^ ]*)?" ascii
#./target/release/reef --input ./tests/docs/uri_email_100B --output ./tests/results/zombie_naive.txt --re "([a-zA-Z][a-zA-Z0-9]*)://([^ /]+)(/[^ ]*)?|([^ @]+)@([^ @]+)" ascii
#./target/release/reef --input ./tests/docs/uri_email_2000B --output ./tests/results/zombie_naive.txt --re "([a-zA-Z][a-zA-Z0-9]*)://([^ /]+)(/[^ ]*)?|([^ @]+)@([^ @]+)" ascii

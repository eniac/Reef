./target/release/reef --input ./tests/docs/http_mb1 --output ./tests/results/http_match -r "HTTP\ /1.1\ 200\ OK.*MZ.*This\ program\ cannont\ be\ run\ in\ DOS\ mode\." ascii
./target/release/reef --input ./tests/docs/http_mb1 --output ./tests/results/http_nonmatch -r "GET\ (/.*/){2,}4{5,6}\.png" ascii
./target/release/reef --input ./tests/docs/http_mb2 --output ./tests/results/http_nonmatch -r "HTTP\ /1.1\ 200\ OK.*MZ.*This\ program\ cannont\ be\ run\ in\ DOS\ mode\." ascii
./target/release/reef --input ./tests/docs/http_mb2 --output ./tests/results/http_match -r "GET\ (/.*/){2,}4{5,6}\.png" ascii

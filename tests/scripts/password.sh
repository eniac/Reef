#reef
cargo clean 
cargo build --release --features 'metrics,reef'
./target/release/reef --input "B6u$r@s#R5mE" --output ./tests/results/good_pass.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
./target/release/reef --input "!73!v3JAhZP%" --output ./tests/results/good_pass.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
./target/release/reef --input "ZH&74d5#AqJ7" --output ./tests/results/good_pass.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
./target/release/reef --input "z8Ffa3%*#3Cc" --output ./tests/results/good_pass.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
./target/release/reef --input "^v56yWMW9U@$" --output ./tests/results/good_pass.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
./target/release/reef --input "MaJ@*n%!vx24" --output ./tests/results/good_pass.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
./target/release/reef --input "#5trXrNR$66x" --output ./tests/results/good_pass.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
./target/release/reef --input "YF75ZFh*^ts%" --output ./tests/results/good_pass.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
./target/release/reef --input "JWvm@q56j!9c" --output ./tests/results/good_pass.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
./target/release/reef --input "fpVz4W#$VB7%" --output ./tests/results/good_pass.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
./target/release/reef --input "q1w2e3r4" --output ./tests/results/bad_pass.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
./target/release/reef --input "12341234" --output ./tests/results/bad_pass.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
./target/release/reef --input "qwerty" --output ./tests/results/bad_pass.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
./target/release/reef --input "1234561" --output ./tests/results/bad_pass.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
./target/release/reef --input "vip" --output ./tests/results/bad_pass.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
./target/release/reef --input "jordan23" --output ./tests/results/bad_pass.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
./target/release/reef --input "family" --output ./tests/results/bad_pass.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
./target/release/reef --input "11111111" --output ./tests/results/bad_pass.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
./target/release/reef --input "123qwe" --output ./tests/results/bad_pass.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
./target/release/reef --input "freedom" --output ./tests/results/bad_pass.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
./target/release/reef --input "password1" --output ./tests/results/bad_pass.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii

#nwr
cargo clean 
cargo build --release --features 'metrics,nwr'
./target/release/reef --input "B6u$r@s#R5mE" --output ./tests/results/good_pass_nwr.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
./target/release/reef --input "!73!v3JAhZP%" --output ./tests/results/good_pass_nwr.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
./target/release/reef --input "ZH&74d5#AqJ7" --output ./tests/results/good_pass_nwr.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
./target/release/reef --input "z8Ffa3%*#3Cc" --output ./tests/results/good_pass_nwr.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
./target/release/reef --input "^v56yWMW9U@$" --output ./tests/results/good_pass_nwr.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
./target/release/reef --input "MaJ@*n%!vx24" --output ./tests/results/good_pass_nwr.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
./target/release/reef --input "#5trXrNR$66x" --output ./tests/results/good_pass_nwr.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
./target/release/reef --input "YF75ZFh*^ts%" --output ./tests/results/good_pass_nwr.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
./target/release/reef --input "JWvm@q56j!9c" --output ./tests/results/good_pass_nwr.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
./target/release/reef --input "fpVz4W#$VB7%" --output ./tests/results/good_pass_nwr.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
./target/release/reef --input "q1w2e3r4" --output ./tests/results/bad_pass_nwr.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
./target/release/reef --input "12341234" --output ./tests/results/bad_pass_nwr.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
./target/release/reef --input "qwerty" --output ./tests/results/bad_pass_nwr.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
./target/release/reef --input "1234561" --output ./tests/results/bad_pass_nwr.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
./target/release/reef --input "vip" --output ./tests/results/bad_pass_nwr.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
./target/release/reef --input "jordan23" --output ./tests/results/bad_pass_nwr.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
./target/release/reef --input "family" --output ./tests/results/bad_pass_nwr.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
./target/release/reef --input "11111111" --output ./tests/results/bad_pass_nwr.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
./target/release/reef --input "123qwe" --output ./tests/results/bad_pass_nwr.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
./target/release/reef --input "freedom" --output ./tests/results/bad_pass_nwr.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
./target/release/reef --input "password1" --output ./tests/results/bad_pass_nwr.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii

#naive
cargo clean 
cargo build --release --features 'metrics,naive'
./target/release/reef --input "B6u$r@s#R5mE" --output ./tests/results/good_pass_naive.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
./target/release/reef --input "!73!v3JAhZP%" --output ./tests/results/good_pass_naive.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
./target/release/reef --input "ZH&74d5#AqJ7" --output ./tests/results/good_pass_naive.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
./target/release/reef --input "z8Ffa3%*#3Cc" --output ./tests/results/good_pass_naive.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
./target/release/reef --input "^v56yWMW9U@$" --output ./tests/results/good_pass_naive.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
./target/release/reef --input "MaJ@*n%!vx24" --output ./tests/results/good_pass_naive.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
./target/release/reef --input "#5trXrNR$66x" --output ./tests/results/good_pass_naive.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
./target/release/reef --input "YF75ZFh*^ts%" --output ./tests/results/good_pass_naive.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
./target/release/reef --input "JWvm@q56j!9c" --output ./tests/results/good_pass_naive.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
./target/release/reef --input "fpVz4W#$VB7%" --output ./tests/results/good_pass_naive.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
./target/release/reef --input "q1w2e3r4" --output ./tests/results/bad_pass_naive.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
./target/release/reef --input "12341234" --output ./tests/results/bad_pass_naive.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
./target/release/reef --input "qwerty" --output ./tests/results/bad_pass_naive.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
./target/release/reef --input "1234561" --output ./tests/results/bad_pass_naive.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
./target/release/reef --input "vip" --output ./tests/results/bad_pass_naive.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
./target/release/reef --input "jordan23" --output ./tests/results/bad_pass_naive.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
./target/release/reef --input "family" --output ./tests/results/bad_pass_naive.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
./target/release/reef --input "11111111" --output ./tests/results/bad_pass_naive.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
./target/release/reef --input "123qwe" --output ./tests/results/bad_pass_naive.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
./target/release/reef --input "freedom" --output ./tests/results/bad_pass_naive.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
./target/release/reef --input "password1" --output ./tests/results/bad_pass_naive.txt --re "^(?=.*[A-Z].*[A-Z])(?=.*[!%^@#$&*])(?=.*[0-9].*[0-9])(?=.*[a-z].*[a-z].*[a-z]).{12}$" ascii
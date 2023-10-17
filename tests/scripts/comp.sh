cargo clean 
cargo build --release --features 'metrics,reef'
#echo "reef"
#./tests/scripts/reef.sh &> out_reef
#echo "end reef"

#echo "reef h"
#./tests/scripts/reef_h.sh &> out_rh 
#echo "reef h"

# cargo build --release --features 'metrics,nwr'
# echo "nwr"
# # RUST_BACKTRACE=1 ./target/release/reef --input "adimage101.adserver99.telemetry.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-1234323" --output ./tests/results/pihole_nwr_2.txt --re "^(.+[_.-])?adse?rv(er?|ice)?s?[0-9]*[_.-]" ascii
# #./tests/scripts/nwr.sh &> out_nwr 
# echo "nwr"

# cargo build --release --features 'metrics,naive'
# echo "naive"
# #./tests/scripts/naive.sh &> out_naive 
# RUST_BACKTRACE=1 ./target/release/reef --input 'adimage101.adserver99.telemetry.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-1234323' --output ./tests/results/pihole_naive_2.txt --re "^(.+[_.-])?adse?rv(er?|ice)?s?[0-9]*[_.-]" ascii
# echo "naive" 

#  # cargo build --release --features 'metrics,reef'
 echo "email"
./tests/scripts/email_dkim.sh &> out_email
 echo "email" 

echo "dna"
./tests/scripts/dna.sh &> out_dna 
echo "dna" 

echo "pihole"
./tests/scripts/pihole.sh &> out_pihole 
echo "pihole" 

cargo build --release --features 'metrics,naive'
echo "email naive for constraints"
RUST_BACKTRACE=1 ./target/release/reef --input ./tests/docs/email_med --output ./tests/results/email_dkim_naive --re "^Message-ID: .*[[:space:]]Date: Tue, 11 Jul 2000 11:11:00 -0700 \(PDT\)[[:space:]]From: .*[[:space:]]To: .*[[:space:]]Subject: Reimbursement of Individually Billed Items[[:space:]]Mime-Version: 1\.0[[:space:]]Content-Type: text\/plain; charset=us-ascii[[:space:]]Content-Transfer-Encoding: 7bit[[:space:]]X-From: Enron Announcements[[:space:]]X-To: All Enron Employees North America[[:space:]]X-cc: [[:space:]]X-bcc: [[:space:]]X-Folder: \\\\Michelle_Lokay_Dec2000_June2001_1\\\\Notes Folders\\\\Corporate[[:space:]]X-Origin: LOKAY-M[[:space:]]X-FileName: mlokay\.nsf[[:space:]]*The memo distributed on June 27 on Reimbursement of Individually Billed Items [[:space:]]requires[[:space:]]clarification\.  The intent of the memo was to give employees an alternate [[:space:]]method[[:space:]]of paying for pagers, cell phones, etc\.  Employees can continue to submit [[:space:]]these[[:space:]]invoices to Accounts Payable for processing or  pay these items with their [[:space:]]corporate[[:space:]]American Express card and request reimbursement through an expense report\.  [[:space:]]Either[[:space:]]way is an acceptable way to process these small dollar high volume invoices\.$" ascii > out_email_naive






# cargo clean 
# cargo build --release --features 'metrics,naive'

echo 'pihole'
for i in {1..10}; do
RUST_BACKTRACE=1 /usr/bin/time -v -a -o ./tests/results/memory/pihole_naive ./target/release/reef --input "ad.stackoverflow.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-500037&clickId=1234567" --output ./tests/results/timings/pihole --re "^ad([sxv]?[0-9]*|system)[_.-]([^.[:space:]]+\.){1,}|[_.-]ad([sxv]?[0-9]*|system)[_.-]" ascii;
RUST_BACKTRACE=1 /usr/bin/time -v -a -o ./tests/results/memory/pihole_naive ./target/release/reef --input 'adimage101.adserver99.telemetry.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-1234323' --output ./tests/results/timings/pihole --re "^(.+[_.-])?adse?rv(er?|ice)?s?[0-9]*[_.-]" ascii;
RUST_BACKTRACE=1 /usr/bin/time -v -a -o ./tests/results/memory/pihole_naive ./target/release/reef --input "adimage101.testingads.telemetry.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-5000379" --output ./tests/results/timings/pihole --re "^(.+[_.-])?telemetry[_.-]" ascii;
RUST_BACKTRACE=1 /usr/bin/time -v -a -o ./tests/results/memory/pihole_naive ./target/release/reef --input "adimage101.testingads.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-500037&clickId=12" --output ./tests/results/timings/pihole --re "^adim(age|g)s?[0-9]*[_.-]" ascii;
RUST_BACKTRACE=1 /usr/bin/time -v -a -o ./tests/results/memory/pihole_naive ./target/release/reef --input "adtracker101.testingads.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-500037&clickId=" --output ./tests/results/timings/pihole --re "^adtrack(er|ing)?[0-9]*[_.-]" ascii;
RUST_BACKTRACE=1 /usr/bin/time -v -a -o ./tests/results/memory/pihole_naive ./target/release/reef --input "advertising101.testingads.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-500037&click1" --output ./tests/results/timings/pihole --re "^advert(s|is(ing|ements?))?[0-9]*[_.-]" ascii;
RUST_BACKTRACE=1 /usr/bin/time -v -a -o ./tests/results/memory/pihole_naive ./target/release/reef --input "affiliate.link.testingads.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-500037&clickI" --output ./tests/results/timings/pihole --re "^aff(iliat(es?|ion))?[_.-]" ascii;
RUST_BACKTRACE=1 /usr/bin/time -v -a -o ./tests/results/memory/pihole_naive ./target/release/reef --input "analytics.testingads.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-500037&clickId=123" --output ./tests/results/timings/pihole --re "^analytics?[_.-]" ascii;
RUST_BACKTRACE=1 /usr/bin/time -v -a -o ./tests/results/memory/pihole_naive ./target/release/reef --input "banners.testingads.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-500037&clickId=12345" --output ./tests/results/timings/pihole --re "^banners?[_.-]" ascii;
RUST_BACKTRACE=1 /usr/bin/time -v -a -o ./tests/results/memory/pihole_naive ./target/release/reef --input "beacons2212.testingads.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-500037&clickId=1" --output ./tests/results/timings/pihole --re "^beacons?[0-9]*[_.-]" ascii;
RUST_BACKTRACE=1 /usr/bin/time -v -a -o ./tests/results/memory/pihole_naive ./target/release/reef --input "counters223.testingads.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-500037&clickId=2" --output ./tests/results/timings/pihole --re "^count(ers?)?[0-9]*[_.-]" ascii;
RUST_BACKTRACE=1 /usr/bin/time -v -a -o ./tests/results/memory/pihole_naive ./target/release/reef --input "mads.testingads.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-500037&clickId=11233456" --output ./tests/results/timings/pihole --re "^mads\." ascii;
RUST_BACKTRACE=1 /usr/bin/time -v -a -o ./tests/results/memory/pihole_naive ./target/release/reef --input "pixel.testing.facebook.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-500037&click" --output ./tests/results/timings/pihole --re "^pixels?[-.]" ascii;
RUST_BACKTRACE=1 /usr/bin/time -v -a -o ./tests/results/memory/pihole_naive ./target/release/reef --input "statistics19902.testing.facebook.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-500037" --output ./tests/results/timings/pihole --re "^stat(s|istics)?[0-9]*[_.-]" ascii;
done

echo 'email'
for i in {1..10}; do
RUST_BACKTRACE=1 /usr/bin/time -v -a -o ./tests/results/memory/email_small_naive ./target/release/reef --input ./tests/docs/email_small --output ./tests/results/timings/email_dkim --re "^Message-ID: .*[[:space:]]Date: Tue, 8 May 2001 09:16:00 -0700 \(PDT\)[[:space:]]From: .*[[:space:]]To: .*[[:space:]]Subject: Re:[[:space:]]Mime-Version: 1\.0[[:space:]]Content-Type: text\/plain; charset=us-ascii[[:space:]]Content-Transfer-Encoding: 7bit[[:space:]]X-From: Mike Maggi[[:space:]]X-To: Amanda Huble[[:space:]]X-cc: [[:space:]]X-bcc: [[:space:]]X-Folder: \\\\Michael_Maggi_Jun2001\\\\Notes Folders\\\\Sent[[:space:]]X-Origin: Maggi-M[[:space:]]X-FileName: mmaggi\.nsf[[:space:]]*at 5:00$" ascii
done 
for i in {1..10}; do
RUST_BACKTRACE=1 timeout 10h /usr/bin/time -v -a -o ./tests/results/memory/email_med_naive ./target/release/reef --input ./tests/docs/email_med --output ./tests/results/timings/email_dkim --re "^Message-ID: .*[[:space:]]Date: Tue, 11 Jul 2000 11:11:00 -0700 \(PDT\)[[:space:]]From: .*[[:space:]]To: .*[[:space:]]Subject: Reimbursement of Individually Billed Items[[:space:]]Mime-Version: 1\.0[[:space:]]Content-Type: text\/plain; charset=us-ascii[[:space:]]Content-Transfer-Encoding: 7bit[[:space:]]X-From: Enron Announcements[[:space:]]X-To: All Enron Employees North America[[:space:]]X-cc: [[:space:]]X-bcc: [[:space:]]X-Folder: \\\\Michelle_Lokay_Dec2000_June2001_1\\\\Notes Folders\\\\Corporate[[:space:]]X-Origin: LOKAY-M[[:space:]]X-FileName: mlokay\.nsf[[:space:]]*The memo distributed on June 27 on Reimbursement of Individually Billed Items [[:space:]]requires[[:space:]]clarification\.  The intent of the memo was to give employees an alternate [[:space:]]method[[:space:]]of paying for pagers, cell phones, etc\.  Employees can continue to submit [[:space:]]these[[:space:]]invoices to Accounts Payable for processing or  pay these items with their [[:space:]]corporate[[:space:]]American Express card and request reimbursement through an expense report\.  [[:space:]]Either[[:space:]]way is an acceptable way to process these small dollar high volume invoices\.$" ascii
done 
cargo clean 
cargo build ---release --features 'metrics,nwr'

echo 'email'
./target/release/reef --input ./tests/docs/email_small --output ./tests/results/email_dkim_nwr.txt --re "^Message-ID: .*[[:space:]]Date: Tue, 8 May 2001 09:16:00 -0700 \(PDT\)[[:space:]]From: .*[[:space:]]To: .*[[:space:]]Subject: Re:[[:space:]]Mime-Version: 1\.0[[:space:]]Content-Type: text\/plain; charset=us-ascii[[:space:]]Content-Transfer-Encoding: 7bit[[:space:]]X-From: Mike Maggi[[:space:]]X-To: Amanda Huble[[:space:]]X-cc: [[:space:]]X-bcc: [[:space:]]X-Folder: \\\\Michael_Maggi_Jun2001\\\\Notes Folders\\\\Sent[[:space:]]X-Origin: Maggi-M[[:space:]]X-FileName: mmaggi\.nsf[[:space:]]*at 5:00$" ascii
./target/release/reef --input ./tests/docs/email_med --output ./tests/results/email_dkim_nwr.txt --re "^Message-ID: .*[[:space:]]Date: Tue, 11 Jul 2000 11:11:00 -0700 \(PDT\)[[:space:]]From: .*[[:space:]]To: .*[[:space:]]Subject: Reimbursement of Individually Billed Items[[:space:]]Mime-Version: 1\.0[[:space:]]Content-Type: text\/plain; charset=us-ascii[[:space:]]Content-Transfer-Encoding: 7bit[[:space:]]X-From: Enron Announcements[[:space:]]X-To: All Enron Employees North America[[:space:]]X-cc: [[:space:]]X-bcc: [[:space:]]X-Folder: \\\\Michelle_Lokay_Dec2000_June2001_1\\\\Notes Folders\\\\Corporate[[:space:]]X-Origin: LOKAY-M[[:space:]]X-FileName: mlokay\.nsf[[:space:]]*The memo distributed on June 27 on Reimbursement of Individually Billed Items [[:space:]]requires[[:space:]]clarification\.  The intent of the memo was to give employees an alternate [[:space:]]method[[:space:]]of paying for pagers, cell phones, etc\.  Employees can continue to submit [[:space:]]these[[:space:]]invoices to Accounts Payable for processing or  pay these items with their [[:space:]]corporate[[:space:]]American Express card and request reimbursement through an expense report\.  [[:space:]]Either[[:space:]]way is an acceptable way to process these small dollar high volume invoices\.$" ascii

echo 'pihole'
./target/release/reef --input "ad.stackoverflow.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-500037&clickId=1234567" --output ./tests/results/pihole_nwr.txt --re "^ad([sxv]?[0-9]*|system)[_.-]([^.[:space:]]+\.){1,}|[_.-]ad([sxv]?[0-9]*|system)[_.-]" ascii
./target/release/reef --input "adimage101.adserver99.telemetry.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-1234323" --output ./tests/results/pihole_nwr.txt --re "^(.+[_.-])?adse?rv(er?|ice)?s?[0-9]*[_.-]" ascii
./target/release/reef --input "adimage101.testingads.telemetry.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-5000379" --output ./tests/results/pihole_nwr.txt --re "^(.+[_.-])?telemetry[_.-]" ascii
./target/release/reef --input "adimage101.testingads.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-500037&clickId=12" --output ./tests/results/pihole_nwr.txt --re "^adim(age|g)s?[0-9]*[_.-]" ascii
./target/release/reef --input "adtracker101.testingads.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-500037&clickId=" --output ./tests/results/pihole_nwr.txt --re "^adtrack(er|ing)?[0-9]*[_.-]" ascii
./target/release/reef --input "advertising101.testingads.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-500037&click1" --output ./tests/results/pihole_nwr.txt --re "^advert(s|is(ing|ements?))?[0-9]*[_.-]" ascii
./target/release/reef --input "affiliate.link.testingads.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-500037&clickI" --output ./tests/results/pihole_nwr.txt --re "^aff(iliat(es?|ion))?[_.-]" ascii
./target/release/reef --input "analytics.testingads.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-500037&clickId=123" --output ./tests/results/pihole_nwr.txt --re "^analytics?[_.-]" ascii
./target/release/reef --input "banners.testingads.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-500037&clickId=12345" --output ./tests/results/pihole_nwr.txt --re "^banners?[_.-]" ascii
./target/release/reef --input "beacons2212.testingads.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-500037&clickId=1" --output ./tests/results/pihole_nwr.txt --re "^beacons?[0-9]*[_.-]" ascii
./target/release/reef --input "counters223.testingads.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-500037&clickId=2" --output ./tests/results/pihole_nwr.txt --re "^count(ers?)?[0-9]*[_.-]" ascii
./target/release/reef --input "mads.testingads.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-500037&clickId=11233456" --output ./tests/results/pihole_nwr.txt --re "^mads\." ascii
./target/release/reef --input "pixel.testing.facebook.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-500037&click" --output ./tests/results/pihole_nwr.txt --re "^pixels?[-.]" ascii
./target/release/reef --input "statistics19902.testing.facebook.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-500037" --output ./tests/results/pihole_nwr.txt --re "^stat(s|istics)?[0-9]*[_.-]" ascii

echo 'zombie'
./target/release/reef --input ./tests/docs/date_100B --output ./tests/results/zombie_nwr.txt --re "([0-9][0-9]?)/([0-9][0-9]?)/([0-9][0-9]([0-9][0-9])?)" ascii
./target/release/reef --input ./tests/docs/date_2000B --output ./tests/results/zombie_nwr.txt --re "([0-9][0-9]?)/([0-9][0-9]?)/([0-9][0-9]([0-9][0-9])?)" ascii
./target/release/reef --input ./tests/docs/DLP_100B --output ./tests/results/zombie_nwr.txt --re "(([0-9a-zA-Z][0-9]{8})|([0-9]{3}[-\s]?[0-9]{2}?[-\s]?[0-9]{4})|(([0-9]{3}\s){2}[0-9]{3})|([0-9]{6,17})|(9[0-9]{2}[-\s]?(5[0-9]|6[0-5]|7[0-9]|8[0-8]|9([0-2]|[4-9]))[-\s]?[0-9]{4}))" ascii
./target/release/reef --input ./tests/docs/DLP_2000B --output ./tests/results/zombie_nwr.txt --re "(([0-9a-zA-Z][0-9]{8})|([0-9]{3}[-\s]?[0-9]{2}?[-\s]?[0-9]{4})|(([0-9]{3}\s){2}[0-9]{3})|([0-9]{6,17})|(9[0-9]{2}[-\s]?(5[0-9]|6[0-5]|7[0-9]|8[0-8]|9([0-2]|[4-9]))[-\s]?[0-9]{4}))" ascii
./target/release/reef --input ./tests/docs/email_100B --output ./tests/results/zombie_nwr.txt --re "([^ @]+)@([^ @]+)" ascii
./target/release/reef --input ./tests/docs/email_2000B --output ./tests/results/zombie_nwr.txt --re "([^ @]+)@([^ @]+)" ascii
./target/release/reef --input ./tests/docs/uri_100B --output ./tests/results/zombie_nwr.txt --re "([a-zA-Z][a-zA-Z0-9]*)://([^ /]+)(/[^ ]*)?" ascii
./target/release/reef --input ./tests/docs/uri_2000B --output ./tests/results/zombie_nwr.txt --re " ([a-zA-Z][a-zA-Z0-9]*)://([^ /]+)(/[^ ]*)?" ascii
./target/release/reef --input ./tests/docs/uri_email_100B --output ./tests/results/zombie_nwr.txt --re "([a-zA-Z][a-zA-Z0-9]*)://([^ /]+)(/[^ ]*)?|([^ @]+)@([^ @]+)" ascii
./target/release/reef --input ./tests/docs/uri_email_2000B --output ./tests/results/zombie_nwr.txt --re "([a-zA-Z][a-zA-Z0-9]*)://([^ /]+)(/[^ ]*)?|([^ @]+)@([^ @]+)" ascii

echo 'dna'
./target/release/reef --input ../docs/BRCA1_base+primary --output ./tests/results/brca1_primary_nonmatch1_nwr --re "^.{43052505}ATGGGCTACAGAAACCGTGCCAAAAGACTTCTACAGAGTGAACCCGAAAATCCTTCCTTG" dna
./target/release/reef --input ../docs/BRCA1_base+primary --output ./tests/results/brca1_primary_nonmatch2_nwr --re "^.{43050136}ATGCTGAAACTTCTCAACCAGAAGAAAGGGCCTTCACAGTGTCCTTTATGTAAGAATGATATAACCAAAAG
.*AGCCTACAAGAAAGTACGAGATTTAGTCAACTTGTTGAAGAGCTATTGAAAATCATTTGTGCTTTTCAGCTTGACACAGGTTTGGAGT.*ATGCAAACAGCTATAATTTTGCAAAAAAGGAAAATAACTCTCCTGAACATCTAAAAGATGAAGTTTCTATCATCCAAAGTATGGGCTACAGAAACCGTGCCAAAAGACTTCTACAGAGTGAACCCGAAAATCCTTCCTTG" dna
./target/release/reef --input ../docs/BRCA1_base+var1 --output ./tests/results/brca1_var1_match_nwr --re "^.{43052505}ATGGGCTACAGAAACCGTGCCAAAAGACTTCTACAGAGTGAACCCGAAAATCCTTCCTTG" dna 
./target/release/reef --input ../docs/BRCA1_base+var1 --output ./tests/results/brca1_var1_nonmatch_nwr --re "^.{43050136}ATGCTGAAACTTCTCAACCAGAAGAAAGGGCCTTCACAGTGTCCTTTATGTAAGAATGATATAACCAAAAG
.*AGCCTACAAGAAAGTACGAGATTTAGTCAACTTGTTGAAGAGCTATTGAAAATCATTTGTGCTTTTCAGCTTGACACAGGTTTGGAGT.*ATGCAAACAGCTATAATTTTGCAAAAAAGGAAAATAACTCTCCTGAACATCTAAAAGATGAAGTTTCTATCATCCAAAGTATGGGCTACAGAAACCGTGCCAAAAGACTTCTACAGAGTGAACCCGAAAATCCTTCCTTG" dna
./target/release/reef --input ../docs/BRCA1_base+var2 --output ./tests/results/brca1_var2_nonmatch_nwr --re "^.{43052505}ATGGGCTACAGAAACCGTGCCAAAAGACTTCTACAGAGTGAACCCGAAAATCCTTCCTTG" dna
./target/release/reef --input ../docs/BRCA1_base+var2 --output ./tests/results/brca1_var2_match_nwr --re "^.{43050136}ATGCTGAAACTTCTCAACCAGAAGAAAGGGCCTTCACAGTGTCCTTTATGTAAGAATGATATAACCAAAAG
.*AGCCTACAAGAAAGTACGAGATTTAGTCAACTTGTTGAAGAGCTATTGAAAATCATTTGTGCTTTTCAGCTTGACACAGGTTTGGAGT.*ATGCAAACAGCTATAATTTTGCAAAAAAGGAAAATAACTCTCCTGAACATCTAAAAGATGAAGTTTCTATCATCCAAAGTATGGGCTACAGAAACCGTGCCAAAAGACTTCTACAGAGTGAACCCGAAAATCCTTCCTTG" dna 
./target/release/reef --input ../docs/BRCA2_base+primary --output ./tests/results/brca2_primary_nonmatch_nwr --re "^.{32317497}CACAACTAAGGAACGTCAAGAGATACAGAATCCAAATTTTACCGCACCTGGTCAAGAATTTCTGTCTAAATCTCATTTGTATGAACATCTGACTTTGGAAAAATCTTCAAGCAATTTAGCAGTTTCAGGACATCCATTTTATCAAGTTTCTGCTACAAGAAATGAAAAAATGAGACACTTGATTACTACAGGCAGACCAACCAAAGTCTTTGTTCCACCTTTTAAAACTAAATCACATTTTCACAGAGTTGAACAGTGTGTTAGGAATATTAACTTGGAGGAAAACAGACAAAAGCAAAACATTGATGGACATGGCTCTGATGATAGTAA
AAATAAGATTAATGACAATGAGATTCATCAGTTTAACAAAAACAACTCCAATCAAGCAGTAGCTGTAACTTTCACAAAGTGTGAAGAAGAACCTTTAG.*
ATTTAATTACAAGTCTTCAGAATGCCAGAGATATACAGGATATGCGAATTAAGAAGAAACAAAGGCAACGCGTCTTTCCACAGCCAGGCAGTCTGTATCTTGCAAAAACATCCACTCTGCCTCGAATCTCTCTGAAAGCAGCAGTAGGAGGCCAAGTTCCCTCTGCGTGTTCTCATAAACAG.*CTGTATACGTATGGCGTTTCTAAACATTGCATAAAAATTAACAGCAAAA
ATGCAGAGTCTTTTCAGTTTCACACTGAAGATTATTTTGGTAAGGAAAGTTTATGGACTGGAAAAGGAATACAGTTGGCTGATGGTGGATGGCTCATACC
CTCCAATGATGGAAAGGCTGGAAAAGAAGAATTTTATAG.*GGCTCTGTGTGACACTCCAGGTGTGGATCCAAAGCTTATTTCTAGAATTTGGGTTTATAATCACTATA
GATGGATCATATGGAAACTGGCAGCTATGGAATGTGCCTTTCCTAAGGAATTTGCTAATAGATGCCTAAGCCCAGAAAGGGTGCTTCTTCAACTAAAATA
CAG" dna
./target/release/reef --input ../docs/BRCA2_base+var1 --output ./tests/results/brca1_primary_match_nwr --re "^.{32317497}CACAACTAAGGAACGTCAAGAGATACAGAATCCAAATTTTACCGCACCTGGTCAAGAATTTCTGTCTAAATCTCATTTGTATGAACATCTGACTTTGGAAAAATCTTCAAGCAATTTAGCAGTTTCAGGACATCCATTTTATCAAGTTTCTGCTACAAGAAATGAAAAAATGAGACACTTGATTACTACAGGCAGACCAACCAAAGTCTTTGTTCCACCTTTTAAAACTAAATCACATTTTCACAGAGTTGAACAGTGTGTTAGGAATATTAACTTGGAGGAAAACAGACAAAAGCAAAACATTGATGGACATGGCTCTGATGATAGTAA
AAATAAGATTAATGACAATGAGATTCATCAGTTTAACAAAAACAACTCCAATCAAGCAGTAGCTGTAACTTTCACAAAGTGTGAAGAAGAACCTTTAG.*
ATTTAATTACAAGTCTTCAGAATGCCAGAGATATACAGGATATGCGAATTAAGAAGAAACAAAGGCAACGCGTCTTTCCACAGCCAGGCAGTCTGTATCTTGCAAAAACATCCACTCTGCCTCGAATCTCTCTGAAAGCAGCAGTAGGAGGCCAAGTTCCCTCTGCGTGTTCTCATAAACAG.*CTGTATACGTATGGCGTTTCTAAACATTGCATAAAAATTAACAGCAAAA
ATGCAGAGTCTTTTCAGTTTCACACTGAAGATTATTTTGGTAAGGAAAGTTTATGGACTGGAAAAGGAATACAGTTGGCTGATGGTGGATGGCTCATACC
CTCCAATGATGGAAAGGCTGGAAAAGAAGAATTTTATAG.*GGCTCTGTGTGACACTCCAGGTGTGGATCCAAAGCTTATTTCTAGAATTTGGGTTTATAATCACTATA
GATGGATCATATGGAAACTGGCAGCTATGGAATGTGCCTTTCCTAAGGAATTTGCTAATAGATGCCTAAGCCCAGAAAGGGTGCTTCTTCAACTAAAATA
CAG" dna
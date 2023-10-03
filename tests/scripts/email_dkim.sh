#REEF
# cargo clean 
cargo build --release --features 'metrics,reef'
echo 'reef'
./target/release/reef --input ./tests/docs/email_small --output ./tests/results/email_dkim.txt --re "^Message-ID: .*[[:space:]]Date: Tue, 8 May 2001 09:16:00 -0700 \(PDT\)[[:space:]]From: .*[[:space:]]To: .*[[:space:]]Subject: Re:[[:space:]]Mime-Version: 1\.0[[:space:]]Content-Type: text\/plain; charset=us-ascii[[:space:]]Content-Transfer-Encoding: 7bit[[:space:]]X-From: Mike Maggi[[:space:]]X-To: Amanda Huble[[:space:]]X-cc: [[:space:]]X-bcc: [[:space:]]X-Folder: \\\\Michael_Maggi_Jun2001\\\\Notes Folders\\\\Sent[[:space:]]X-Origin: Maggi-M[[:space:]]X-FileName: mmaggi\.nsf[[:space:]]*at 5:00$" ascii
# ./target/release/reef --input ./tests/docs/email_med --output ./tests/results/email_dkim.txt --re "^Message-ID: .*[[:space:]]Date: Tue, 11 Jul 2000 11:11:00 -0700 \(PDT\)[[:space:]]From: .*[[:space:]]To: .*[[:space:]]Subject: Reimbursement of Individually Billed Items[[:space:]]Mime-Version: 1\.0[[:space:]]Content-Type: text\/plain; charset=us-ascii[[:space:]]Content-Transfer-Encoding: 7bit[[:space:]]X-From: Enron Announcements[[:space:]]X-To: All Enron Employees North America[[:space:]]X-cc: [[:space:]]X-bcc: [[:space:]]X-Folder: \\\\Michelle_Lokay_Dec2000_June2001_1\\\\Notes Folders\\\\Corporate[[:space:]]X-Origin: LOKAY-M[[:space:]]X-FileName: mlokay\.nsf[[:space:]]*The memo distributed on June 27 on Reimbursement of Individually Billed Items [[:space:]]requires[[:space:]]clarification\.  The intent of the memo was to give employees an alternate [[:space:]]method[[:space:]]of paying for pagers, cell phones, etc\.  Employees can continue to submit [[:space:]]these[[:space:]]invoices to Accounts Payable for processing or  pay these items with their [[:space:]]corporate[[:space:]]American Express card and request reimbursement through an expense report\.  [[:space:]]Either[[:space:]]way is an acceptable way to process these small dollar high volume invoices\.$" ascii

# #NWR
# cargo clean 
# cargo build --release --features 'metrics,nwr'
# echo 'nwr'
# ./target/release/reef --input ./tests/docs/email_small --output ./tests/results/email_dkim_nwr.txt --re "^Message-ID: .*[[:space:]]Date: Tue, 8 May 2001 09:16:00 -0700 \(PDT\)[[:space:]]From: .*[[:space:]]To: .*[[:space:]]Subject: Re:[[:space:]]Mime-Version: 1\.0[[:space:]]Content-Type: text\/plain; charset=us-ascii[[:space:]]Content-Transfer-Encoding: 7bit[[:space:]]X-From: Mike Maggi[[:space:]]X-To: Amanda Huble[[:space:]]X-cc: [[:space:]]X-bcc: [[:space:]]X-Folder: \\\\Michael_Maggi_Jun2001\\\\Notes Folders\\\\Sent[[:space:]]X-Origin: Maggi-M[[:space:]]X-FileName: mmaggi\.nsf[[:space:]]*at 5:00$" ascii
# ./target/release/reef --input ./tests/docs/email_med --output ./tests/results/email_dkim_nwr.txt --re "^Message-ID: .*[[:space:]]Date: Tue, 11 Jul 2000 11:11:00 -0700 \(PDT\)[[:space:]]From: .*[[:space:]]To: .*[[:space:]]Subject: Reimbursement of Individually Billed Items[[:space:]]Mime-Version: 1\.0[[:space:]]Content-Type: text\/plain; charset=us-ascii[[:space:]]Content-Transfer-Encoding: 7bit[[:space:]]X-From: Enron Announcements[[:space:]]X-To: All Enron Employees North America[[:space:]]X-cc: [[:space:]]X-bcc: [[:space:]]X-Folder: \\\\Michelle_Lokay_Dec2000_June2001_1\\\\Notes Folders\\\\Corporate[[:space:]]X-Origin: LOKAY-M[[:space:]]X-FileName: mlokay\.nsf[[:space:]]*The memo distributed on June 27 on Reimbursement of Individually Billed Items [[:space:]]requires[[:space:]]clarification\.  The intent of the memo was to give employees an alternate [[:space:]]method[[:space:]]of paying for pagers, cell phones, etc\.  Employees can continue to submit [[:space:]]these[[:space:]]invoices to Accounts Payable for processing or  pay these items with their [[:space:]]corporate[[:space:]]American Express card and request reimbursement through an expense report\.  [[:space:]]Either[[:space:]]way is an acceptable way to process these small dollar high volume invoices\.$" ascii


# #Naive
# cargo clean 
# cargo build --release --features 'metrics,naive'
# echo 'naive'
# ./target/release/reef --input ./tests/docs/email_small --output ./tests/results/email_dkim_naive.txt --re "^Message-ID: .*[[:space:]]Date: Tue, 8 May 2001 09:16:00 -0700 \(PDT\)[[:space:]]From: .*[[:space:]]To: .*[[:space:]]Subject: Re:[[:space:]]Mime-Version: 1\.0[[:space:]]Content-Type: text\/plain; charset=us-ascii[[:space:]]Content-Transfer-Encoding: 7bit[[:space:]]X-From: Mike Maggi[[:space:]]X-To: Amanda Huble[[:space:]]X-cc: [[:space:]]X-bcc: [[:space:]]X-Folder: \\\\Michael_Maggi_Jun2001\\\\Notes Folders\\\\Sent[[:space:]]X-Origin: Maggi-M[[:space:]]X-FileName: mmaggi\.nsf[[:space:]]*at 5:00$" ascii
# ./target/release/reef --input ./tests/docs/email_med --output ./tests/results/email_dkim_naive.txt --re "^Message-ID: .*[[:space:]]Date: Tue, 11 Jul 2000 11:11:00 -0700 \(PDT\)[[:space:]]From: .*[[:space:]]To: .*[[:space:]]Subject: Reimbursement of Individually Billed Items[[:space:]]Mime-Version: 1\.0[[:space:]]Content-Type: text\/plain; charset=us-ascii[[:space:]]Content-Transfer-Encoding: 7bit[[:space:]]X-From: Enron Announcements[[:space:]]X-To: All Enron Employees North America[[:space:]]X-cc: [[:space:]]X-bcc: [[:space:]]X-Folder: \\\\Michelle_Lokay_Dec2000_June2001_1\\\\Notes Folders\\\\Corporate[[:space:]]X-Origin: LOKAY-M[[:space:]]X-FileName: mlokay\.nsf[[:space:]]*The memo distributed on June 27 on Reimbursement of Individually Billed Items [[:space:]]requires[[:space:]]clarification\.  The intent of the memo was to give employees an alternate [[:space:]]method[[:space:]]of paying for pagers, cell phones, etc\.  Employees can continue to submit [[:space:]]these[[:space:]]invoices to Accounts Payable for processing or  pay these items with their [[:space:]]corporate[[:space:]]American Express card and request reimbursement through an expense report\.  [[:space:]]Either[[:space:]]way is an acceptable way to process these small dollar high volume invoices\.$" ascii

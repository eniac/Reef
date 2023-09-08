./target/release/reef --input ./tests/docs/email_small --output ./tests/results/email_dkim_naive.txt --re "Message-ID: .*\nDate: Tue, 8 May 2001 09:16:00 -0700 \(PDT\)\nFrom: .*\nTo: .*\nSubject: Re:\nMime-Version: 1\.0\nContent-Type: text\/plain; charset=us-ascii\nContent-Transfer-Encoding: 7bit\nX-From: Mike Maggi\nX-To: Amanda Huble\nX-cc: \nX-bcc: \nX-Folder: \\Michael_Maggi_Jun2001\\Notes Folders\\Sent\nX-Origin: Maggi-M\nX-FileName: mmaggi\.nsf\n\nat 5:00" ascii
./target/release/reef --input ./tests/docs/email_med --output ./tests/results/email_dkim_naive.txt --re "Message-ID: .*\nDate: Tue, 11 Jul 2000 11:11:00 -0700 \(PDT\)\nFrom: .*\nTo: .*\nSubject: Reimbursement of Individually Billed Items\nMime-Version: 1\.0\nContent-Type: text\/plain; charset=us-ascii\nContent-Transfer-Encoding: 7bit\nX-From: Enron Announcements\nX-To: All Enron Employees North America\nX-cc: \nX-bcc: \nX-Folder: \\Michelle_Lokay_Dec2000_June2001_1\\Notes Folders\\Corporate\nX-Origin: LOKAY-M\nX-FileName: mlokay\.nsf\n\nThe memo distributed on June 27 on Reimbursement of Individually Billed Items \nrequires\nclarification\.  The intent of the memo was to give employees an alternate \nmethod\nof paying for pagers, cell phones, etc\.  Employees can continue to submit \nthese\ninvoices to Accounts Payable for processing or  pay these items with their \ncorporate\nAmerican Express card and request reimbursement through an expense report\.  \nEither\nway is an acceptable way to process these small dollar high volume invoices\." ascii
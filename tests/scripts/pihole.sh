#reef
cargo clean 
cargo build --release --features 'metrics,reef'
echo 'reef'
./target/release/reef --input "ad.stackoverflow.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-500037&clickId=1234567" --output ./tests/results/pihole.txt --re "^ad([sxv]?[0-9]*|system)[_.-]([^.[:space:]]+\.){1,}|[_.-]ad([sxv]?[0-9]*|system)[_.-]" ascii
./target/release/reef --input "adimage101.adserver99.telemetry.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-1234323" --output ./tests/results/pihole.txt --re "^(.+[_.-])?adse?rv(er?|ice)?s?[0-9]*[_.-]" ascii
./target/release/reef --input "adimage101.testingads.telemetry.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-5000379" --output ./tests/results/pihole.txt --re "^(.+[_.-])?telemetry[_.-]" ascii
./target/release/reef --input "adimage101.testingads.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-500037&clickId=12" --output ./tests/results/pihole.txt --re "^adim(age|g)s?[0-9]*[_.-]" ascii
./target/release/reef --input "adtracker101.testingads.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-500037&clickId=" --output ./tests/results/pihole.txt --re "^adtrack(er|ing)?[0-9]*[_.-]" ascii
./target/release/reef --input "advertising101.testingads.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-500037&click1" --output ./tests/results/pihole.txt --re "^advert(s|is(ing|ements?))?[0-9]*[_.-]" ascii
./target/release/reef --input "affiliate.link.testingads.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-500037&clickI" --output ./tests/results/pihole.txt --re "^aff(iliat(es?|ion))?[_.-]" ascii
./target/release/reef --input "analytics.testingads.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-500037&clickId=123" --output ./tests/results/pihole.txt --re "^analytics?[_.-]" ascii
./target/release/reef --input "banners.testingads.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-500037&clickId=12345" --output ./tests/results/pihole.txt --re "^banners?[_.-]" ascii
./target/release/reef --input "beacons2212.testingads.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-500037&clickId=1" --output ./tests/results/pihole.txt --re "^beacons?[0-9]*[_.-]" ascii
./target/release/reef --input "counters223.testingads.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-500037&clickId=2" --output ./tests/results/pihole.txt --re "^count(ers?)?[0-9]*[_.-]" ascii
./target/release/reef --input "mads.testingads.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-500037&clickId=11233456" --output ./tests/results/pihole.txt --re "^mads\." ascii
./target/release/reef --input "pixel.testing.facebook.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-500037&click" --output ./tests/results/pihole.txt --re "^pixels?[-.]" ascii
./target/release/reef --input "statistics19902.testing.facebook.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-500037" --output ./tests/results/pihole.txt --re "^stat(s|istics)?[0-9]*[_.-]" ascii

reef hybrid
cargo clean 
cargo build --release --features 'metrics,reef'
echo 'reef hybrid'
./target/release/reef --input "ad.stackoverflow.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-500037&clickId=1234567" --output ./tests/results/pihole_hybrid.txt --re "^ad([sxv]?[0-9]*|system)[_.-]([^.[:space:]]+\.){1,}|[_.-]ad([sxv]?[0-9]*|system)[_.-]" -y ascii
./target/release/reef --input "adimage101.adserver99.telemetry.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-1234323" --output ./tests/results/pihole_hybrid.txt --re "^(.+[_.-])?adse?rv(er?|ice)?s?[0-9]*[_.-]" -y ascii
./target/release/reef --input "adimage101.testingads.telemetry.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-5000379" --output ./tests/results/pihole_hybrid.txt --re "^(.+[_.-])?telemetry[_.-]" -y ascii
./target/release/reef --input "adimage101.testingads.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-500037&clickId=12" --output ./tests/results/pihole_hybrid.txt --re "^adim(age|g)s?[0-9]*[_.-]" -y ascii
./target/release/reef --input "adtracker101.testingads.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-500037&clickId=" --output ./tests/results/pihole_hybrid.txt --re "^adtrack(er|ing)?[0-9]*[_.-]" -y ascii
./target/release/reef --input "advertising101.testingads.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-500037&click1" --output ./tests/results/pihole_hybrid.txt --re "^advert(s|is(ing|ements?))?[0-9]*[_.-]" -y ascii
./target/release/reef --input "affiliate.link.testingads.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-500037&clickI" --output ./tests/results/pihole_hybrid.txt --re "^aff(iliat(es?|ion))?[_.-]" -y ascii
./target/release/reef --input "analytics.testingads.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-500037&clickId=123" --output ./tests/results/pihole_hybrid.txt --re "^analytics?[_.-]" -y ascii
./target/release/reef --input "banners.testingads.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-500037&clickId=12345" --output ./tests/results/pihole_hybrid.txt --re "^banners?[_.-]" -y ascii
./target/release/reef --input "beacons2212.testingads.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-500037&clickId=1" --output ./tests/results/pihole_hybrid.txt --re "^beacons?[0-9]*[_.-]" -y ascii
./target/release/reef --input "counters223.testingads.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-500037&clickId=2" --output ./tests/results/pihole_hybrid.txt --re "^count(ers?)?[0-9]*[_.-]" -y ascii
./target/release/reef --input "mads.testingads.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-500037&clickId=11233456" --output ./tests/results/pihole_hybrid.txt --re "^mads\." -y ascii
./target/release/reef --input "pixel.testing.facebook.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-500037&click" --output ./tests/results/pihole_hybrid.txt --re "^pixels?[-.]" -y ascii
./target/release/reef --input "statistics19902.testing.facebook.com/uid?=abd?utm_source=partnerize&utm_medium=affiliate&utm_campaign=88849&utm_content=2-500037" --output ./tests/results/pihole_hybrid.txt --re "^stat(s|istics)?[0-9]*[_.-]" -y ascii



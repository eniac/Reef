 echo "start email"
 ./tests/scripts/email_dkim.sh > email_out
 echo "end email"

 echo "pihole"
 ./tests/scripts/pihole.sh > pihole_out
 echo "end pihole"

 echo "zombie"
 ./tests/scripts/zombie.sh > zombie_out 
 echo "end zombie"

 echo "password"
 ./tests/scripts/password.sh > password_out
 echo "end password" 
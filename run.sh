#/bin/bash -e

# hard coded path, please forgive me
TEMP=./temp.gv
FILES=/home/guigui/build/tptp/Problems/ARI/*.p

# Generate 'interesting' problem list :
# grep -L "real" /home/guigui/build/tptp/Problems/ARI/*.p | xargs grep -l "0 type" | xargs grep -l "0   ?" | xargs grep -l "Theorem" > arith_pbs

rm /home/guigui/build/tptp/Problems/ARI/*.ps
for f in $FILES
do
    ./zenon -x arith -itptp $f > /dev/null 2> /dev/null
    RET=$?
    if [ $RET -eq 0 ];
    then
        echo -e "\e[32m[PROOF FOUND] $f \e[0m"
        ./zenon -q -odot -x arith -itptp $f > $TEMP
        dot -Tps $TEMP -o $f.ps
    elif [ $RET -eq 12 ] || [ $RET -eq 1 ];
    then
        echo -e "\e[31m[NOT FOUND] $f \e[0m"
    else
        echo -e "\e[35m[ERROR $RET] $f \e[0m"
        ./zenon -x arith -itptp $f
    fi
done
echo `ls -l /home/guigui/build/tptp/Problems/ARI/*.ps | wc -l` / `ls -l /home/guigui/build/tptp/Problems/ARI/*.p | wc -l`
rm $TEMP

#/bin/bash -e

# hard coded path, please forgive me
TEMP=./temp42.gv
FILES=/home/guigui/build/tptp/Problems/ARI/*.p

# Generate 'interesting' problem list :
# grep -L "real" /home/guigui/build/tptp/Problems/ARI/*.p | xargs grep -l "0 type" | xargs grep -l "0   ?" | xargs grep -l "Theorem" > arith_pbs

TOTAL=0
SOLVED=0

for f in $FILES
#for f in `grep -L "real" /home/guigui/build/tptp/Problems/ARI/*.p | xargs grep -l "0 type" | xargs grep -l "0   ?" | xargs grep -l "Theorem"`
do
    TOTAL=$(($TOTAL + 1))
    ./zenon -x arith -itptp $f > /dev/null 2> /dev/null
    RET=$?
    if [ $RET -eq 0 ];
    then
        echo -e "\e[32m[PROOF FOUND] $f \e[0m"
        SOLVED=$(($SOLVED + 1))
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
echo "$SOLVED / $TOTAL"

rm $TEMP

#/bin/bash -e

# hard coded path, please forgive me
#FILES=/home/guigui/build/tptp/Problems/ARI/*
FILES1=test/arith-*.t
FILES2=test/arith-*.f

for f in $FILES1
do
    ./zenon -x arith -itptp $f > /dev/null 2> /dev/null
    RET=$?
    if [ $RET -eq 0 ];
    then
        echo -e "\e[32m[PROOF FOUND] $f \e[0m"
    elif [ $RET -eq 12 ] || [ $RET -eq 1 ];
    then
        echo -e "\e[31m[NOT FOUND] $f \e[0m"
    else
        echo -e "\e[35m[ERROR $RET] $f \e[0m"
    fi
done
for f in $FILES2
do
    ./zenon -x arith -itptp $f > /dev/null 2> /dev/null
    RET=$?
    if [ $RET -eq 0 ];
    then
        echo -e "\e[31m[PROOF FOUND] $f \e[0m"
    elif [ $RET -eq 12 ] || [ $RET -eq 1 ];
    then
        echo -e "\e[32m[NOT FOUND] $f \e[0m"
    else
        echo -e "\e[35m[ERROR $?] $f \e[0m"
    fi
done

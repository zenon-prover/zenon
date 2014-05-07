#/bin/bash -e

FILES=/home/guigui/build/tptp/Problems/ARI/*

for f in $FILES
do
    ./zenon -itptp $f > /dev/null 2> /dev/null
    if [ $? -eq 0 ];
    then
        echo -e "\e[32m[PROOF FOUND] $f \e[0m"
    fi
    if [ $? -eq 12 ];
    then
        echo -e "\e[35m[SYNTAX OK] $f \e[0m"
    fi
    if ! [ $? -eq 0 ] && ! [ $? -eq 12 ];
    then
        echo -e "\e[31m[ERROR $?] $f \e[0m"
    fi
done

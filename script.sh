#!/bin/bash
for x in ../TPTP-v5.4.0/FOF/SY*.p
do
    echo -n "proving"; echo $x;
    cp $x test.p;
    if ./limit.py ./zenon -q -odedukti -itptp test.p > test.dk;
    then ./limit.py camelide -v 1 test.dk || echo "dedukti fail";
    else echo "zenon fail";
    fi
done

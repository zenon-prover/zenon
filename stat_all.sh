#! /bin/bash

foftotal=$(ls tptp/FOF/ | wc -l)

for timeout in $( ls statistics_* | cut -d '_' -f 2 )
do
    # if [ -f statistics_0.$timeout ]
    # then
        total=$(cat statistics_$timeout | wc -l)
        zto=$(grep 'zenon_exit_status 124' statistics_$timeout | wc -l)
        ch=$(grep 'dkcheck_exit_status 0' statistics_$timeout | wc -l)
        other=$(($total - $zto - ch))

        echo "Total of $total problems ($((100 * $total / $foftotal))%)"
        echo "Using a timeout of $timeout s"
        echo -e "Zenon timeout:\t$zto ($((100 * $zto / $total))%)"
        echo -e "Checked\t\t$ch ($((100 * $ch / $total))%)"
        echo -e "Other:\t\t$other ($((100 * $other / $total))%)"
        echo
    # fi
done

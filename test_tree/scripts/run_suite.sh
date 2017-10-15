#!/bin/sh

TO=600
DIV=1000

for file in `ls ../code/*.c | sort --version-sort -f`; do

    echo -n $(basename $file)
    
    STARTTIME=$(date +"%s%3N")
    R1=`timeout $TO ../../duet.native -proofspace -config-rep predicate-tree $file > /dev/null`
    MIDTIME1=$(date +"%s%3N")
    T1=$(( $MIDTIME1 - $STARTTIME ))
    T1=`awk "BEGIN {print $T1/$DIV}"`
    printf "\t%.3f" $T1
    
    MIDTIME2=$(date +"%s%3N")
    R1=`timeout $TO ../../duet.native -proofspace -config-rep list $file > /dev/null`
    ENDTIME=$(date +"%s%3N")
    T2=$(( $ENDTIME - $MIDTIME2 ))
    T2=`awk "BEGIN {print $T2/$DIV}"`
    printf "\t%.3f\n" $T2

done

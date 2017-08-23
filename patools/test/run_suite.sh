#!/bin/sh

FAIL1=0
FAIL2=0
FAIL3=0
TO=10

for file in `ls embed_bench/embed*.struct`; do
    echo -n $file
    STARTTIME=$(date +"%s%3N")

    R1=`timeout $TO ../../patools.native uembeds $file`
    if [ "$R1" = "" ]; then
	FAIL1=$(($FAIL1 + 1))
	R1="--"
    fi
    echo -n "\t$R1"

    MIDTIME1=$(date +"%s%3N")
#    R2=`timeout $TO ../../patools.native embeds $file`
    R2=`timeout $TO python struct2mzn.py $file`
    if [ "$R2" = "" ]; then
	FAIL2=$(($FAIL2 + 1))
	R2="--"
    fi
    echo -n "\t$R2"


    MIDTIME2=$(date +"%s%3N")
    R3=`timeout $TO ../../patools.native cembeds $file`
    #R3=`timeout $TO python struct2mzn.py $file`
    ENDTIME=$(date +"%s%3N")
    if [ "$R3" = "" ]; then
	FAIL3=$(($FAIL3 + 1))
	R3="--"
    fi
    echo -n "\t$R3"

    echo -n "\t" $(( $MIDTIME1 - $STARTTIME ))
    echo -n "\t" $(( $MIDTIME2 - $MIDTIME1 ))
    echo "\t" $(( $ENDTIME - $MIDTIME2 ))
done
echo "Fail1: $FAIL1"
echo "Fail2: $FAIL2"
echo "Fail3: $FAIL3"

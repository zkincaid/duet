#!/bin/sh

FAIL1=0
FAIL2=0
FAIL3=0
FAIL4=0
FAIL5=0
TO=600

START=0
if ! [ -z "$1" ]; then
    START="$1"
fi

for file in `ls embed_bench/embed*.struct`; do

    NUM=`echo $file | sed -e s/[^0-9]//g`
    if [ "$NUM" -lt "$START" ]; then
	continue
    fi

    echo -n $file
    
    STARTTIME=$(date +"%s%3N")

    R1=`timeout $TO ../../patools.native uembeds $file`
    if [ "$R1" = "" ]; then
	FAIL1=$(($FAIL1 + 1))
	R1="--"
    fi
    echo -n "\t$R1"

    MIDTIME1=$(date +"%s%3N")
    R2=`timeout $TO ../../patools.native embeds $file`
    if [ "$R2" = "" ]; then
	FAIL2=$(($FAIL2 + 1))
	R2="--"
    fi
    echo -n "\t$R2"

    MIDTIME2=$(date +"%s%3N")
    R3=`timeout $TO ../../patools.native cembeds $file`
    if [ "$R3" = "" ]; then
	FAIL3=$(($FAIL3 + 1))
	R3="--"
    fi
    echo -n "\t$R3"
    MIDTIME3=$(date +"%s%3N")

    RS=`../../patools.native str2mzn $file`

    MIDTIMES=$(date +"%s%3N")

    if [ "$RS" = "True" ]; then
	MIDTIME4=$(date +"%s%3N")
	R4=`timeout $TO ./run_or_tools.sh tmp.mzn`
	if [ "$R4" = "" ]; then
	    FAIL4=$(($FAIL4 + 1))
	    R4="--"
	fi
	echo -n "\t$R4"

	MIDTIME5=$(date +"%s%3N")
	R5=`timeout $TO ./run_hcsp.sh tmp.mzn`
	if [ "$R5" = "" ]; then
	    FAIL5=$(($FAIL5 + 1))
	    R5="--"
	fi
	echo -n "\t$R5"

	ENDTIME=$(date +"%s%3N")

	echo -n "\t" $(( $MIDTIME1 - $STARTTIME ))
	echo -n "\t" $(( $MIDTIME2 - $MIDTIME1 ))
	echo -n "\t" $(( $MIDTIME3 - $MIDTIME2 ))
	echo -n "\t" $(( $MIDTIME5 - $MIDTIME4 ))
	echo "\t" $(( $ENDTIME - $MIDTIME5 ))
    else
	echo -n "\tFalse\tFalse"

	echo -n "\t" $(( $MIDTIME1 - $STARTTIME ))
	echo -n "\t" $(( $MIDTIME2 - $MIDTIME1 ))
	echo -n "\t" $(( $MIDTIME3 - $MIDTIME2 ))
	echo -n "\t" $(( $MIDTIMES - $MIDTIME3 ))
	echo "\t" $(( $MIDTIMES - $MIDTIME3 ))	
    fi

done
echo "Fail1: $FAIL1"
echo "Fail2: $FAIL2"
echo "Fail3: $FAIL3"
echo "Fail4: $FAIL4"
echo "Fail5: $FAIL5"

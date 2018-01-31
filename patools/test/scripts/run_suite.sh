#!/bin/sh

FAIL1=0
FAIL2=0
FAIL3=0
FAIL4=0
FAIL5=0
FAIL6=0
FAIL7=0
TO=100

START=0
DIR="../embed_bench"

if ! [ -z "$1" ]; then
    DIR="$1"
fi
if ! [ -z "$2" ]; then
    START="$2"
fi

for file in `ls $DIR/embed*.struct`; do

    NUM=`echo $file | sed -e s/[^0-9]//g`
    if [ "$NUM" -lt "$START" ]; then
	continue
    fi

    echo -n $file
    
    STARTTIME=$(date +"%s%3N")

    R1=`timeout $TO ../../../patools.native match-embeds $file`
    if [ "$R1" = "" ]; then
	FAIL1=$(($FAIL1 + 1))
	R1="--"
    fi
    echo -n "\t$R1"

    MIDTIME1=$(date +"%s%3N")

    R2=`timeout $TO ../../../patools.native crypto-mini-sat $file`
    if [ "$R2" = "" ]; then
	FAIL2=$(($FAIL2 + 1))
	R2="--"
    fi
    echo -n "\t$R2"

    MIDTIME2=$(date +"%s%3N")

    R3=`timeout $TO ../../../patools.native lingeling $file`
    if [ "$R3" = "" ]; then
	FAIL3=$(($FAIL3 + 1))
	R3="--"
    fi
    echo -n "\t$R3"

    MIDTIME3=$(date +"%s%3N")

    R4=`timeout $TO ../../../patools.native haifacsp $file`
    if [ "$R4" = "" ]; then
	FAIL4=$(($FAIL4 + 1))
	R4="--"
    fi
    echo -n "\t$R4"

    MIDTIME4=$(date +"%s%3N")

    R5=`timeout $TO ../../../patools.native gecode $file`
    if [ "$R5" = "" ]; then
	FAIL5=$(($FAIL5 + 1))
	R5="--"
    fi
    echo -n "\t$R5"

    MIDTIME5=$(date +"%s%3N")

    R6=`timeout $TO ../../../patools.native vf2 $file`
    if [ "$R6" = "" ]; then
	FAIL6=$(($FAIL6 + 1))
	R6="--"
    fi
    echo -n "\t$R6"

    MIDTIME6=$(date +"%s%3N")

    R7=`timeout $TO ../../../patools.native ortools $file`
    if [ "$R7" = "" ]; then
	FAIL7=$(($FAIL7 + 1))
	R7="--"
    fi
    echo -n "\t$R7"

    ENDTIME=$(date +"%s%3N")

    echo -n "\t" $(( $MIDTIME1 - $STARTTIME ))
    echo -n "\t" $(( $MIDTIME2 - $MIDTIME1 ))
    echo -n "\t" $(( $MIDTIME3 - $MIDTIME2 ))
    echo -n "\t" $(( $MIDTIME4 - $MIDTIME3 ))
    echo -n "\t" $(( $MIDTIME5 - $MIDTIME4 ))
    echo -n "\t" $(( $MIDTIME6 - $MIDTIME5 ))
    echo "\t" $(( $ENDTIME - $MIDTIME6 ))
done
echo "Fail1: $FAIL1"
echo "Fail2: $FAIL2"
echo "Fail3: $FAIL3"
echo "Fail4: $FAIL4"
echo "Fail5: $FAIL5"
echo "Fail6: $FAIL6"
echo "Fail7: $FAIL7"

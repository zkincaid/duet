#!/bin/sh

TO=600
DIV=1000
LAST1=""
LAST2=""

for file in `ls $1/*.c | sort --version-sort -f`; do
    echo -n $(basename $file)

    if [ "$LAST1" = "" ]; then
	STARTTIME=$(date +"%s%3N")
	R1=`timeout $TO ../../duet.native -proofspace -config-rep predicate-tree -embed-algo $2 $file | grep Embedding | sed -e s/[^0-9]//g`
	if [ "$R1" = "" ]; then
	    R1="0"
	fi
	MIDTIME1=$(date +"%s%3N")
	T1=$(( $MIDTIME1 - $STARTTIME ))
	T1=`awk "BEGIN {print $T1/$DIV}"`
	cond=`echo $T1 '>' $TO | bc -l`
	if [ "$cond" = "1" ]; then
	    LAST1="True"
	fi
      	printf "\t%.3f (%d)" $T1 $R1
    else
	printf "\t%.3f (%d)" $TO 0
    fi

    if [ "$LAST2" = "" ]; then
	MIDTIME2=$(date +"%s%3N")
	R2=`timeout $TO ../../duet.native -proofspace -config-rep list -embed-algo $2 $file | grep Embedding | sed -e s/[^0-9]//g`
	if [ "$R2" = "" ]; then
	    R2="0"
	fi
	ENDTIME=$(date +"%s%3N")
	T2=$(( $ENDTIME - $MIDTIME2 ))
	T2=`awk "BEGIN {print $T2/$DIV}"`
	cond=`echo $T2 '>' $TO | bc -l`
	if [ "$cond" = "1" ]; then
	    LAST2="True"
	fi
	printf "\t%.3f (%d)\n" $T2 $R2
    else
	printf "\t%.3f (%d)\n" $TO 0
    fi

done

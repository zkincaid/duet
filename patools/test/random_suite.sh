#!/bin/bash
NB=0
TO=1
while [[ $NB -lt 20 ]]; do
    predicates=$((2 + RANDOM % 9)) # ~[2,10]
    size1=$((10 + RANDOM % 41))    # ~[10,50]
    size2=$(($size1 + RANDOM % ($size1 + 1))) # ~[size1,2*size1]
    ppred1=`printf "%02d\n" $((1 + RANDOM % 25))` # ~(0,0.1)
    ppred2=`printf "%02d\n" $((10#$ppred1 + RANDOM % (2*10#$ppred1)))` # ~[ppred1,2*ppred1)
    pedge1=`printf "%02d\n" $((RANDOM % 11))` # ~(0,0.1)
    #pedge1="05"
    pedge2=`printf "%02d\n" $((10#$pedge1 + RANDOM % (4*10#$ppred1)))` # ~[pedge1,4*pedge1)
    python random_struct.py $size1 $predicates 0.$ppred1 0.$pedge1 > embed.struct
    python random_struct.py $size2 $predicates 0.$ppred2 0.$pedge2 >> embed.struct
    #    R1=`timeout $TO ../../patools.native embeds embed.struct`
    R1=`timeout $TO python struct2mzn.py embed.struct`
    R2=`timeout $TO ../../patools.native cembeds embed.struct`
    R3=`timeout $TO ../../patools.native uembeds embed.struct`
    if [[ "$R1" = "" || "$R2" = "" || "$R3" = "" ]]; then
	bench=`printf "embed_bench/embed%02d.struct" $NB`
	cp embed.struct $bench
	if [ "$R1" = "" ]; then
	    echo "struct2mzn timeout ($R2,$R3)"
	elif [ "$R2" = "" ]; then
	    echo "gecode timeout ($R1,$R3)"
	else
	    echo "embeds timeout ($R1,$R2)"
	fi
	NB=$(($NB + 1))
    else
	echo "Success: $R1"
    fi
done

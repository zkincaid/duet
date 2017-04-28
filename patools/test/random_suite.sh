#!/bin/sh

predicates=5
for i in `seq 1 100`; do
    python random_struct.py 20 $predicates 1.0 1.0 > embed_bench/embed$i.struct
    python random_struct.py 25 $predicates 3.0 5.0 >> embed_bench/embed$i.struct
    echo -n "embed$i"
    STARTTIME=$(date +"%s%3N")
    R1=`timeout 15 ../../patools.native embeds embed_bench/embed$i.struct`
    MIDTIME=$(date +"%s%3N")
    R2=`timeout 15 python struct2mzn.py embed_bench/embed$i.struct`
    ENDTIME=$(date +"%s%3N")
    echo -n "\t$R1\t$R2\t" $(( $MIDTIME - $STARTTIME ))
    echo "\t" $(( $ENDTIME - $MIDTIME ))
done

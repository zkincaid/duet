#!/bin/sh

R=`lingeling tmp.cnf | grep SATISFIABLE`
if [ "$R" = "s SATISFIABLE" ]; then
    exit 0
elif [ "$R" = "s UNSATISFIABLE" ]; then
    exit 1
else
    echo "ERROR"
    exit -1
fi

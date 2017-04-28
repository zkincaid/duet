#!/bin/bash
export PATH=$PATH:~/app/minizinc
if mzn-gecode $1 | grep --quiet "UNSAT"; then
    echo "False"
else
    echo "True"
fi

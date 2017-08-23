#!/bin/bash
export PATH=$PATH:~/app/minizinc
mzn2fzn $1 -o tmp.fzn 2>/dev/null
#hcsp.big -F fzn tmp.fzn
if hcsp.big -F fzn tmp.fzn | grep --quiet "UNSAT"; then
    echo "False"
else
    echo "True"
fi

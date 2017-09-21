#!/bin/bash
if minizinc -f ~/git_repos/or-tools/bin/fz $1 | grep --quiet "UNSAT"; then
    echo "False"
else
    echo "True"
fi

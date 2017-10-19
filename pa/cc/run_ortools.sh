#!/bin/bash
if minizinc -f ~/git_repos/or-tools/bin/fz "tmp.mzn" | grep --quiet "UNSAT"; then
    exit 1
else
    exit 0
fi

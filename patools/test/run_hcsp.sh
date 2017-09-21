#!/bin/bash
if minizinc -G hcsp -f "~/git_repos/haifa-csp/hcsp.big -F fzn" $1 | grep --quiet "UNSAT"; then
    echo "False"
else
    echo "True"
fi

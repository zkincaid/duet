#!/bin/bash
if minizinc -G hcsp -f "~/git_repos/haifa-csp/hcsp.big -F fzn" "tmp.mzn" | grep --quiet "UNSAT"; then
    exit 1
else
    exit 0
fi

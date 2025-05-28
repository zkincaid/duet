#!/bin/bash

inpath="~/src/research/projects/duet/bench/tasks/convhull/cra-monotone"
dir="loop-acceleration"
# outdir="/home/diagram/src/research/others/zak-convex-hull/bench/tasks/convhull/svcomp-$dir"
outdir="~/src/research/projects/duet/bench/tasks/convhull/cra-monotone-integralized"

for file in $(eval "ls $inpath/$dir/*.smt2")
do
    echo "./_build/default/srk/src/bigtop.exe -integralize-smt-file $file"
    mkdir -p $outdir/$dir
    echo "cp $file $outdir/$dir"
    # cp $(file) $(outdir)/$(dir)
    # ./_build/default/srk/src/bigtop.exe -integralize-smt-file $file
done

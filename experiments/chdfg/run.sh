P=../../duet.native
for f in `find . -name "*.c"`
do
  $P -stats -check-array-bounds -inline -coarsen $f > results/$f.coarsen;
#  $P -stats -check-array-bounds -no-must-alias -no-conc-edges -chdfg $f > results/$f.triv.hdfg;
#  $P -stats -check-array-bounds -no-conc-edges -chdfg $f > results/$f.hdfg;
#  $P -stats -check-array-bounds -no-must-alias -chdfg $f > results/$f.triv.chdfg;
  $P -stats -check-array-bounds -chdfg $f > results/$f.chdfg;
#  $P -stats -check-array-bounds -sequentialish -no-must-alias -no-conc-edges -chdfg $f > results/$f.seq.triv.hdfg;
#  $P -stats -check-array-bounds -sequentialish -no-conc-edges -chdfg $f > results/$f.seq.hdfg;
#  $P -stats -check-array-bounds -inline -chdfg $f > results/$f.inline.chdfg;
done

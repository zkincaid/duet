mkdir cra-monotone-c4b-hulls
mkdir cra-monotone-hola-hulls
mkdir cra-monotone-svcomp-reach-safety-hulls
mkdir cra-monotone-polybench-4.2.1-hulls
mkdir termination-monotone-no-phase-c4b-hulls
mkdir termination-monotone-no-phase-hola-hulls
mkdir termination-monotone-no-phase-svcomp-reach-safety-hulls
mkdir termination-monotone-no-phase-polybench-4.2.1-hulls

; CRA

PATH=.:$PATH python ./benchmarks/dump_hulls.py --cmd cra --indir ~/src/research/projects/duet/bench-nk-local-projection/tasks/C4B --outdir ./cra-monotone-c4b-hulls --mappings cra-monotone-c4b-hull-mappings.txt

PATH=.:$PATH python ./benchmarks/dump_hulls.py --cmd cra --indir ~/src/research/projects/duet/bench-nk-local-projection/tasks/HOLA --outdir ./cra-monotone-hola-hulls --mappings cra-monotone-hola-hull-mappings.txt

; Termination

PATH=.:$PATH python ./benchmarks/dump_hulls.py --cmd termination --indir ~/src/research/projects/duet/bench-nk-local-projection/tasks/C4B --outdir ./termination-monotone-no-phase-c4b-hulls --mappings termination-monotone-no-phase-c4b-hull-mappings.txt

PATH=.:$PATH python ./benchmarks/dump_hulls.py --cmd termination --indir ~/src/research/projects/duet/bench-nk-local-projection/tasks/HOLA --outdir ./termination-monotone-no-phase-hola-hulls --mappings termination-monotone-no-phase-hola-hull-mappings.txt

; Polybench requires special flags, and termination hulls take much longer

PATH=.:$PATH python ./benchmarks/dump_hulls.py --cmd cra --polybench --indir ~/src/research/projects/duet/bench-nk-local-projection/tasks/PolyBenchC-4.2.1 --outdir ./cra-monotone-polybench-4.2.1-hulls --mappings cra-monotone-polybench-hull-mappings.txt

PATH=.:$PATH python ./benchmarks/dump_hulls.py --cmd termination --polybench --indir ~/src/research/projects/duet/bench-nk-local-projection/tasks/PolyBenchC-4.2.1 --outdir ./termination-monotone-no-phase-polybench-4.2.1-hulls --mappings termination-monotone-no-phase-polybench-4.2.1-hull-mappings.txt


; SVCOMP takes longer

PATH=.:$PATH python ./benchmarks/dump_hulls.py --cmd cra --svcomp --indir ~/src/research/others/sv-benchmarks/sv-benchmarks-reach-safety-2025 --outdir ./cra-monotone-svcomp-reach-safety-hulls --mappings cra-monotone-svcomp-reach-safety-hull-mappings.txt

PATH=.:$PATH python ./benchmarks/dump_hulls.py --cmd termination --svcomp --indir ~/src/research/others/sv-benchmarks/sv-benchmarks-reach-safety-2025 --outdir ./termination-monotone-no-phase-svcomp-reach-safety-hulls --mappings termination-monotone-no-phase-svcomp-reach-safety-hull-mappings.txt









Redo: geo1-ll_valuebound20dab1bc.i
/tmp/geo1-ll2_unwindbound20573cab.i
/tmp/dijkstra-u_unwindbound100732fa0.i
geo3-ll_unwindbound2ba3f65.i
/tmp/ps5-ll_unwindbound1001e7244.i


./loop-invariants/
./loop-acceleration/
./loop-new/
./loop-simple/
./loop-crafted/


./nla-digbench-scaling/ incomplete

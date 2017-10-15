cp ../embeds/struct.ml ../../pa/struct.ml
cd ../../
make
cd test_tree/scripts/
./run_suite.sh > ../results/embeds_threader.txt
./run_count.sh > ../results/embeds_count.txt

cp ../gecode/struct.ml ../../pa/struct.ml
cd ../../
make
cd test_tree/scripts/
./run_suite.sh > ../results/gecode_threader.txt
./run_count.sh > ../results/gecode_count.txt

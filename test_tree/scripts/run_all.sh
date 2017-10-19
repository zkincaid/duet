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

cp ../haifa/struct.ml ../../pa/struct.ml
cd ../../
make
cd test_tree/scripts/
./run_suite.sh > ../results/haifa_threader.txt
./run_count.sh > ../results/haifa_count.txt

cp ../ortools/struct.ml ../../pa/struct.ml
cd ../../
make
cd test_tree/scripts/
./run_suite.sh > ../results/ortools_threader.txt
./run_count.sh > ../results/ortools_count.txt

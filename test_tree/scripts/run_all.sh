#Secret Bench Top
echo "Secret - MatchEmbeds"
./run_one.sh ../code/secret match-embeds > secret_match.txt
echo "Secret - CryptoMiniSat"
./run_one.sh ../code/secret crypto-mini-sat > secret_crypto.txt
echo "Secret - HaifaCSP"
./run_one.sh ../code/secret haifacsp > secret_haifa.txt
echo "Secret - VF2"
./run_one.sh ../code/secret vf2 > secret_vf2.txt

#Count Threads TOP
echo "Count - MatchEmbeds"
./run_one.sh ../code/count_threads match-embeds > count_match.txt
echo "Count - CryptoMiniSat"
./run_one.sh ../code/count_threads crypto-mini-sat > count_crypto.txt
echo "Count - HaifaCSP"
./run_one.sh ../code/count_threads haifacsp > count_haifa.txt
echo "Count - VF2"
./run_one.sh ../code/count_threads vf2 > count_vf2.txt

#Secret Bench Bottom
echo "Secret - Lingeling"
./run_one.sh ../code/secret lingeling > secret_ling.txt
echo "Secret - Gecode"
./run_one.sh ../code/secret gecode > secret_gecode.txt
echo "Secret - OrTools"
./run_one.sh ../code/secret or-tools > secret_ortools.txt

#Count Threads Bottom
echo "Count - Lingeling"
./run_one.sh ../code/count_threads lingeling > count_ling.txt
echo "Count - Gecode"
./run_one.sh ../code/count_threads gecode > count_gecode.txt
echo "Count - OrTools"
./run_one.sh ../code/count_threads or-tools > count_ortools.txt


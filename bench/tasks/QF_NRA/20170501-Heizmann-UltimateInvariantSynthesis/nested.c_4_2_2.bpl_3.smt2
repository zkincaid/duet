(set-info :smt-lib-version 2.6)
(set-logic QF_NRA)
(set-info :source |
Generated by a component of the Ultimate program analysis framework [1] 
that implements a constraint-based synthesis of invariants [2].

This SMT script belongs to a set of SMT scripts that was generated by 
applying Ultimate to benchmarks [3] from the SV-COMP 2017 [4,5].

This script might _not_ contain all SMT commands that are used by 
Ultimate . In order to satisfy the restrictions of
the SMT-COMP we have to drop e.g., the commands for getting
values (resp. models), unsatisfiable cores and interpolants.

2017-05-01, Matthias Heizmann (heizmann@informatik.uni-freiburg.de)


[1] https://ultimate.informatik.uni-freiburg.de/
[2] Michael Colon, Sriram Sankaranarayanan, Henny Sipma: Linear Invariant 
Generation Using Non-linear Constraint Solving. CAV 2003: 420-432
[3] https://github.com/sosy-lab/sv-benchmarks
[4] Dirk Beyer: Software Verification with Validation of Results - 
(Report on SV-COMP 2017). TACAS (2) 2017: 331-349
[5] https://sv-comp.sosy-lab.org/2017/
|)
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "industrial")
(set-info :status sat)
(declare-fun lp_0_0c () Real)
(declare-fun lp_0_0_ULTIMATE.start_main_~c~5 () Real)
(declare-fun lp_0_0_ULTIMATE.start_main_~b~5 () Real)
(declare-fun lp_0_0_ULTIMATE.start_main_~a~5 () Real)
(declare-fun lp_0_0_~last () Real)
(declare-fun lp_0_1c () Real)
(declare-fun lp_0_1_ULTIMATE.start_main_~c~5 () Real)
(declare-fun lp_0_1_ULTIMATE.start_main_~b~5 () Real)
(declare-fun lp_0_1_ULTIMATE.start_main_~a~5 () Real)
(declare-fun lp_0_1_~last () Real)
(declare-fun motzkin_896_0 () Real)
(declare-fun motzkin_896_1 () Real)
(declare-fun motzkin_896_2 () Real)
(declare-fun motzkin_896_3 () Real)
(declare-fun motzkin_896_4 () Real)
(declare-fun motzkin_896_5 () Real)
(declare-fun motzkin_896_6 () Real)
(declare-fun motzkin_896_7 () Real)
(declare-fun motzkin_896_8 () Real)
(declare-fun motzkin_896_9 () Real)
(declare-fun motzkin_896_10 () Real)
(declare-fun motzkin_896_11 () Real)
(declare-fun motzkin_896_12 () Real)
(declare-fun motzkin_896_13 () Real)
(declare-fun motzkin_896_14 () Real)
(declare-fun motzkin_897_0 () Real)
(declare-fun motzkin_897_1 () Real)
(declare-fun motzkin_897_2 () Real)
(declare-fun motzkin_897_3 () Real)
(declare-fun motzkin_897_4 () Real)
(declare-fun motzkin_897_5 () Real)
(declare-fun motzkin_897_6 () Real)
(declare-fun motzkin_897_7 () Real)
(declare-fun motzkin_897_8 () Real)
(declare-fun motzkin_897_9 () Real)
(declare-fun motzkin_897_10 () Real)
(declare-fun motzkin_897_11 () Real)
(declare-fun motzkin_897_12 () Real)
(declare-fun motzkin_897_13 () Real)
(declare-fun motzkin_897_14 () Real)
(assert (and (>= motzkin_896_0 0.0) (>= motzkin_896_1 0.0) (>= motzkin_896_2 0.0) (>= motzkin_896_3 0.0) (>= motzkin_896_4 0.0) (>= motzkin_896_5 0.0) (>= motzkin_896_6 0.0) (>= motzkin_896_7 0.0) (>= motzkin_896_8 0.0) (>= motzkin_896_9 0.0) (>= motzkin_896_10 0.0) (>= motzkin_896_11 0.0) (>= motzkin_896_12 0.0) (>= motzkin_896_13 0.0) (>= motzkin_896_14 0.0) (= (+ motzkin_896_0 (* motzkin_896_4 (- 1.0))) 0.0) (= (+ motzkin_896_1 (* motzkin_896_6 (- 1.0)) (* motzkin_896_14 (+ (* (- 1.0) lp_0_0_ULTIMATE.start_main_~c~5) 0.0))) 0.0) (= (+ (* motzkin_896_2 (- 1.0)) motzkin_896_10 (* motzkin_896_14 (+ (* (- 1.0) lp_0_0_ULTIMATE.start_main_~b~5) 0.0))) 0.0) (= (+ motzkin_896_3 motzkin_896_5 motzkin_896_7 (* motzkin_896_8 (- 1.0)) (* motzkin_896_11 (- 1.0)) (* motzkin_896_12 (- 1.0))) 0.0) (= (+ (* motzkin_896_3 (- 1.0)) motzkin_896_11) 0.0) (= (+ (* motzkin_896_5 (- 1.0)) motzkin_896_12 (* motzkin_896_14 (+ (* (- 1.0) lp_0_0_~last) 0.0))) 0.0) (= (+ (* motzkin_896_9 (- 1.0)) motzkin_896_13 (* motzkin_896_14 (+ (* (- 1.0) lp_0_0_ULTIMATE.start_main_~a~5) 0.0))) 0.0) (<= (+ (* motzkin_896_0 (- 1.0)) motzkin_896_4 (* motzkin_896_7 2147483648.0) (* motzkin_896_8 2147483647.0) (* motzkin_896_14 (+ (* (- 1.0) lp_0_0c) 0.0))) 0.0) (or (< (+ (* motzkin_896_0 (- 1.0)) motzkin_896_4 (* motzkin_896_7 2147483648.0) (* motzkin_896_8 2147483647.0)) 0.0) (> motzkin_896_14 0.0)) (>= motzkin_897_0 0.0) (>= motzkin_897_1 0.0) (>= motzkin_897_2 0.0) (>= motzkin_897_3 0.0) (>= motzkin_897_4 0.0) (>= motzkin_897_5 0.0) (>= motzkin_897_6 0.0) (>= motzkin_897_7 0.0) (>= motzkin_897_8 0.0) (>= motzkin_897_9 0.0) (>= motzkin_897_10 0.0) (>= motzkin_897_11 0.0) (>= motzkin_897_12 0.0) (>= motzkin_897_13 0.0) (>= motzkin_897_14 0.0) (= (+ motzkin_897_0 (* motzkin_897_4 (- 1.0))) 0.0) (= (+ motzkin_897_1 (* motzkin_897_6 (- 1.0)) (* motzkin_897_14 (+ (* (- 1.0) lp_0_1_ULTIMATE.start_main_~c~5) 0.0))) 0.0) (= (+ (* motzkin_897_2 (- 1.0)) motzkin_897_10 (* motzkin_897_14 (+ (* (- 1.0) lp_0_1_ULTIMATE.start_main_~b~5) 0.0))) 0.0) (= (+ motzkin_897_3 motzkin_897_5 motzkin_897_7 (* motzkin_897_8 (- 1.0)) (* motzkin_897_11 (- 1.0)) (* motzkin_897_12 (- 1.0))) 0.0) (= (+ (* motzkin_897_3 (- 1.0)) motzkin_897_11) 0.0) (= (+ (* motzkin_897_5 (- 1.0)) motzkin_897_12 (* motzkin_897_14 (+ (* (- 1.0) lp_0_1_~last) 0.0))) 0.0) (= (+ (* motzkin_897_9 (- 1.0)) motzkin_897_13 (* motzkin_897_14 (+ (* (- 1.0) lp_0_1_ULTIMATE.start_main_~a~5) 0.0))) 0.0) (<= (+ (* motzkin_897_0 (- 1.0)) motzkin_897_4 (* motzkin_897_7 2147483648.0) (* motzkin_897_8 2147483647.0) (* motzkin_897_14 (+ (* (- 1.0) lp_0_1c) 0.0))) 0.0) (or (< (+ (* motzkin_897_0 (- 1.0)) motzkin_897_4 (* motzkin_897_7 2147483648.0) (* motzkin_897_8 2147483647.0)) 0.0) (> motzkin_897_14 0.0))))
(declare-fun motzkin_898_0 () Real)
(declare-fun motzkin_898_1 () Real)
(declare-fun motzkin_898_2 () Real)
(declare-fun motzkin_898_3 () Real)
(declare-fun motzkin_898_4 () Real)
(declare-fun motzkin_898_5 () Real)
(declare-fun motzkin_898_6 () Real)
(declare-fun motzkin_899_0 () Real)
(declare-fun motzkin_899_1 () Real)
(declare-fun motzkin_899_2 () Real)
(declare-fun motzkin_899_3 () Real)
(declare-fun motzkin_899_4 () Real)
(declare-fun motzkin_899_5 () Real)
(declare-fun motzkin_899_6 () Real)
(declare-fun motzkin_900_0 () Real)
(declare-fun motzkin_900_1 () Real)
(declare-fun motzkin_900_2 () Real)
(declare-fun motzkin_900_3 () Real)
(declare-fun motzkin_900_4 () Real)
(declare-fun motzkin_900_5 () Real)
(declare-fun motzkin_900_6 () Real)
(declare-fun motzkin_901_0 () Real)
(declare-fun motzkin_901_1 () Real)
(declare-fun motzkin_901_2 () Real)
(declare-fun motzkin_901_3 () Real)
(declare-fun motzkin_901_4 () Real)
(declare-fun motzkin_901_5 () Real)
(declare-fun motzkin_901_6 () Real)
(assert (and (>= motzkin_898_0 0.0) (>= motzkin_898_1 0.0) (>= motzkin_898_2 0.0) (>= motzkin_898_3 0.0) (>= motzkin_898_4 0.0) (>= motzkin_898_5 0.0) (>= motzkin_898_6 0.0) (= (+ motzkin_898_0 (* motzkin_898_1 (- 1.0)) (* motzkin_898_2 (- 1.0)) motzkin_898_3 (* motzkin_898_5 (+ (* 1.0 lp_0_0_ULTIMATE.start_main_~c~5) 0.0)) (* motzkin_898_6 (+ (* 1.0 lp_0_1_ULTIMATE.start_main_~c~5) 0.0))) 0.0) (= (+ (* motzkin_898_0 (- 1.0)) (* motzkin_898_4 (+ (* (- 1.0) lp_0_0_~last) 0.0)) (* motzkin_898_5 (+ (* 1.0 lp_0_0_~last) 0.0)) (* motzkin_898_6 (+ (* 1.0 lp_0_1_~last) 0.0))) 0.0) (= (+ motzkin_898_1 (* motzkin_898_3 (- 1.0)) (* motzkin_898_4 (+ (* (- 1.0) lp_0_0_ULTIMATE.start_main_~c~5) 0.0))) 0.0) (= (+ (* motzkin_898_4 (+ (* (- 1.0) lp_0_0_ULTIMATE.start_main_~b~5) 0.0)) (* motzkin_898_5 (+ (* 1.0 lp_0_0_ULTIMATE.start_main_~b~5) 0.0)) (* motzkin_898_6 (+ (* 1.0 lp_0_1_ULTIMATE.start_main_~b~5) 0.0))) 0.0) (= (+ (* motzkin_898_4 (+ (* (- 1.0) lp_0_0_ULTIMATE.start_main_~a~5) 0.0)) (* motzkin_898_5 (+ (* 1.0 lp_0_0_ULTIMATE.start_main_~a~5) 0.0)) (* motzkin_898_6 (+ (* 1.0 lp_0_1_ULTIMATE.start_main_~a~5) 0.0))) 0.0) (<= (+ (* motzkin_898_0 (- 1.0)) (* motzkin_898_1 (- 1.0)) (* motzkin_898_2 199999.0) motzkin_898_3 (* motzkin_898_4 (+ (* (- 1.0) lp_0_0c) 0.0)) (* motzkin_898_5 (+ (* 1.0 lp_0_0c) 0.0)) (* motzkin_898_6 (+ (* 1.0 lp_0_1c) 0.0))) 0.0) (or (< (+ (* motzkin_898_0 (- 1.0)) (* motzkin_898_1 (- 1.0)) (* motzkin_898_2 199999.0) motzkin_898_3 (* motzkin_898_5 (+ (* 1.0 lp_0_0c) 0.0)) (* motzkin_898_6 (+ (* 1.0 lp_0_1c) 0.0))) 0.0) (> motzkin_898_4 0.0)) (>= motzkin_899_0 0.0) (>= motzkin_899_1 0.0) (>= motzkin_899_2 0.0) (>= motzkin_899_3 0.0) (>= motzkin_899_4 0.0) (>= motzkin_899_5 0.0) (>= motzkin_899_6 0.0) (= (+ motzkin_899_0 (* motzkin_899_1 (- 1.0)) (* motzkin_899_2 (- 1.0)) motzkin_899_3 (* motzkin_899_5 (+ (* 1.0 lp_0_0_ULTIMATE.start_main_~c~5) 0.0)) (* motzkin_899_6 (+ (* 1.0 lp_0_1_ULTIMATE.start_main_~c~5) 0.0))) 0.0) (= (+ (* motzkin_899_0 (- 1.0)) (* motzkin_899_4 (+ (* (- 1.0) lp_0_1_~last) 0.0)) (* motzkin_899_5 (+ (* 1.0 lp_0_0_~last) 0.0)) (* motzkin_899_6 (+ (* 1.0 lp_0_1_~last) 0.0))) 0.0) (= (+ motzkin_899_1 (* motzkin_899_3 (- 1.0)) (* motzkin_899_4 (+ (* (- 1.0) lp_0_1_ULTIMATE.start_main_~c~5) 0.0))) 0.0) (= (+ (* motzkin_899_4 (+ (* (- 1.0) lp_0_1_ULTIMATE.start_main_~b~5) 0.0)) (* motzkin_899_5 (+ (* 1.0 lp_0_0_ULTIMATE.start_main_~b~5) 0.0)) (* motzkin_899_6 (+ (* 1.0 lp_0_1_ULTIMATE.start_main_~b~5) 0.0))) 0.0) (= (+ (* motzkin_899_4 (+ (* (- 1.0) lp_0_1_ULTIMATE.start_main_~a~5) 0.0)) (* motzkin_899_5 (+ (* 1.0 lp_0_0_ULTIMATE.start_main_~a~5) 0.0)) (* motzkin_899_6 (+ (* 1.0 lp_0_1_ULTIMATE.start_main_~a~5) 0.0))) 0.0) (<= (+ (* motzkin_899_0 (- 1.0)) (* motzkin_899_1 (- 1.0)) (* motzkin_899_2 199999.0) motzkin_899_3 (* motzkin_899_4 (+ (* (- 1.0) lp_0_1c) 0.0)) (* motzkin_899_5 (+ (* 1.0 lp_0_0c) 0.0)) (* motzkin_899_6 (+ (* 1.0 lp_0_1c) 0.0))) 0.0) (or (< (+ (* motzkin_899_0 (- 1.0)) (* motzkin_899_1 (- 1.0)) (* motzkin_899_2 199999.0) motzkin_899_3 (* motzkin_899_5 (+ (* 1.0 lp_0_0c) 0.0)) (* motzkin_899_6 (+ (* 1.0 lp_0_1c) 0.0))) 0.0) (> motzkin_899_4 0.0)) (>= motzkin_900_0 0.0) (>= motzkin_900_1 0.0) (>= motzkin_900_2 0.0) (>= motzkin_900_3 0.0) (>= motzkin_900_4 0.0) (>= motzkin_900_5 0.0) (>= motzkin_900_6 0.0) (= (+ (* motzkin_900_0 (- 1.0)) (* motzkin_900_1 (- 1.0)) (* motzkin_900_2 (- 1.0)) motzkin_900_3 (* motzkin_900_5 (+ (* 1.0 lp_0_0_ULTIMATE.start_main_~c~5) 0.0)) (* motzkin_900_6 (+ (* 1.0 lp_0_1_ULTIMATE.start_main_~c~5) 0.0))) 0.0) (= (+ motzkin_900_0 (* motzkin_900_4 (+ (* (- 1.0) lp_0_0_~last) 0.0)) (* motzkin_900_5 (+ (* 1.0 lp_0_0_~last) 0.0)) (* motzkin_900_6 (+ (* 1.0 lp_0_1_~last) 0.0))) 0.0) (= (+ motzkin_900_1 (* motzkin_900_3 (- 1.0)) (* motzkin_900_4 (+ (* (- 1.0) lp_0_0_ULTIMATE.start_main_~c~5) 0.0))) 0.0) (= (+ (* motzkin_900_4 (+ (* (- 1.0) lp_0_0_ULTIMATE.start_main_~b~5) 0.0)) (* motzkin_900_5 (+ (* 1.0 lp_0_0_ULTIMATE.start_main_~b~5) 0.0)) (* motzkin_900_6 (+ (* 1.0 lp_0_1_ULTIMATE.start_main_~b~5) 0.0))) 0.0) (= (+ (* motzkin_900_4 (+ (* (- 1.0) lp_0_0_ULTIMATE.start_main_~a~5) 0.0)) (* motzkin_900_5 (+ (* 1.0 lp_0_0_ULTIMATE.start_main_~a~5) 0.0)) (* motzkin_900_6 (+ (* 1.0 lp_0_1_ULTIMATE.start_main_~a~5) 0.0))) 0.0) (<= (+ (* motzkin_900_0 (- 1.0)) (* motzkin_900_1 (- 1.0)) (* motzkin_900_2 199999.0) motzkin_900_3 (* motzkin_900_4 (+ (* (- 1.0) lp_0_0c) 0.0)) (* motzkin_900_5 (+ (* 1.0 lp_0_0c) 0.0)) (* motzkin_900_6 (+ (* 1.0 lp_0_1c) 0.0))) 0.0) (or (< (+ (* motzkin_900_0 (- 1.0)) (* motzkin_900_1 (- 1.0)) (* motzkin_900_2 199999.0) motzkin_900_3 (* motzkin_900_5 (+ (* 1.0 lp_0_0c) 0.0)) (* motzkin_900_6 (+ (* 1.0 lp_0_1c) 0.0))) 0.0) (> motzkin_900_4 0.0)) (>= motzkin_901_0 0.0) (>= motzkin_901_1 0.0) (>= motzkin_901_2 0.0) (>= motzkin_901_3 0.0) (>= motzkin_901_4 0.0) (>= motzkin_901_5 0.0) (>= motzkin_901_6 0.0) (= (+ (* motzkin_901_0 (- 1.0)) (* motzkin_901_1 (- 1.0)) (* motzkin_901_2 (- 1.0)) motzkin_901_3 (* motzkin_901_5 (+ (* 1.0 lp_0_0_ULTIMATE.start_main_~c~5) 0.0)) (* motzkin_901_6 (+ (* 1.0 lp_0_1_ULTIMATE.start_main_~c~5) 0.0))) 0.0) (= (+ motzkin_901_0 (* motzkin_901_4 (+ (* (- 1.0) lp_0_1_~last) 0.0)) (* motzkin_901_5 (+ (* 1.0 lp_0_0_~last) 0.0)) (* motzkin_901_6 (+ (* 1.0 lp_0_1_~last) 0.0))) 0.0) (= (+ motzkin_901_1 (* motzkin_901_3 (- 1.0)) (* motzkin_901_4 (+ (* (- 1.0) lp_0_1_ULTIMATE.start_main_~c~5) 0.0))) 0.0) (= (+ (* motzkin_901_4 (+ (* (- 1.0) lp_0_1_ULTIMATE.start_main_~b~5) 0.0)) (* motzkin_901_5 (+ (* 1.0 lp_0_0_ULTIMATE.start_main_~b~5) 0.0)) (* motzkin_901_6 (+ (* 1.0 lp_0_1_ULTIMATE.start_main_~b~5) 0.0))) 0.0) (= (+ (* motzkin_901_4 (+ (* (- 1.0) lp_0_1_ULTIMATE.start_main_~a~5) 0.0)) (* motzkin_901_5 (+ (* 1.0 lp_0_0_ULTIMATE.start_main_~a~5) 0.0)) (* motzkin_901_6 (+ (* 1.0 lp_0_1_ULTIMATE.start_main_~a~5) 0.0))) 0.0) (<= (+ (* motzkin_901_0 (- 1.0)) (* motzkin_901_1 (- 1.0)) (* motzkin_901_2 199999.0) motzkin_901_3 (* motzkin_901_4 (+ (* (- 1.0) lp_0_1c) 0.0)) (* motzkin_901_5 (+ (* 1.0 lp_0_0c) 0.0)) (* motzkin_901_6 (+ (* 1.0 lp_0_1c) 0.0))) 0.0) (or (< (+ (* motzkin_901_0 (- 1.0)) (* motzkin_901_1 (- 1.0)) (* motzkin_901_2 199999.0) motzkin_901_3 (* motzkin_901_5 (+ (* 1.0 lp_0_0c) 0.0)) (* motzkin_901_6 (+ (* 1.0 lp_0_1c) 0.0))) 0.0) (> motzkin_901_4 0.0))))
(declare-fun motzkin_902_0 () Real)
(declare-fun motzkin_902_1 () Real)
(declare-fun motzkin_902_2 () Real)
(declare-fun motzkin_902_3 () Real)
(declare-fun motzkin_902_4 () Real)
(declare-fun motzkin_902_5 () Real)
(declare-fun motzkin_902_6 () Real)
(declare-fun motzkin_902_7 () Real)
(declare-fun motzkin_902_8 () Real)
(declare-fun motzkin_902_9 () Real)
(declare-fun motzkin_902_10 () Real)
(declare-fun motzkin_902_11 () Real)
(declare-fun motzkin_902_12 () Real)
(declare-fun motzkin_903_0 () Real)
(declare-fun motzkin_903_1 () Real)
(declare-fun motzkin_903_2 () Real)
(declare-fun motzkin_903_3 () Real)
(declare-fun motzkin_903_4 () Real)
(declare-fun motzkin_903_5 () Real)
(declare-fun motzkin_903_6 () Real)
(declare-fun motzkin_903_7 () Real)
(declare-fun motzkin_903_8 () Real)
(declare-fun motzkin_903_9 () Real)
(declare-fun motzkin_903_10 () Real)
(declare-fun motzkin_903_11 () Real)
(declare-fun motzkin_903_12 () Real)
(declare-fun motzkin_904_0 () Real)
(declare-fun motzkin_904_1 () Real)
(declare-fun motzkin_904_2 () Real)
(declare-fun motzkin_904_3 () Real)
(declare-fun motzkin_904_4 () Real)
(declare-fun motzkin_904_5 () Real)
(declare-fun motzkin_904_6 () Real)
(declare-fun motzkin_904_7 () Real)
(declare-fun motzkin_904_8 () Real)
(declare-fun motzkin_904_9 () Real)
(declare-fun motzkin_904_10 () Real)
(declare-fun motzkin_904_11 () Real)
(declare-fun motzkin_904_12 () Real)
(declare-fun motzkin_905_0 () Real)
(declare-fun motzkin_905_1 () Real)
(declare-fun motzkin_905_2 () Real)
(declare-fun motzkin_905_3 () Real)
(declare-fun motzkin_905_4 () Real)
(declare-fun motzkin_905_5 () Real)
(declare-fun motzkin_905_6 () Real)
(declare-fun motzkin_905_7 () Real)
(declare-fun motzkin_905_8 () Real)
(declare-fun motzkin_905_9 () Real)
(declare-fun motzkin_905_10 () Real)
(declare-fun motzkin_905_11 () Real)
(declare-fun motzkin_905_12 () Real)
(assert (and (>= motzkin_902_0 0.0) (>= motzkin_902_1 0.0) (>= motzkin_902_2 0.0) (>= motzkin_902_3 0.0) (>= motzkin_902_4 0.0) (>= motzkin_902_5 0.0) (>= motzkin_902_6 0.0) (>= motzkin_902_7 0.0) (>= motzkin_902_8 0.0) (>= motzkin_902_9 0.0) (>= motzkin_902_10 0.0) (>= motzkin_902_11 0.0) (>= motzkin_902_12 0.0) (= (+ motzkin_902_0 (* motzkin_902_7 (- 1.0)) (* motzkin_902_11 (+ (* 1.0 lp_0_0_ULTIMATE.start_main_~c~5) 0.0)) (* motzkin_902_12 (+ (* 1.0 lp_0_1_ULTIMATE.start_main_~c~5) 0.0))) 0.0) (= (+ (* motzkin_902_1 (- 1.0)) motzkin_902_9 motzkin_902_10) 0.0) (= (+ motzkin_902_1 (* motzkin_902_10 (- 1.0)) (* motzkin_902_11 (+ (* 1.0 lp_0_0_ULTIMATE.start_main_~b~5) 0.0)) (* motzkin_902_12 (+ (* 1.0 lp_0_1_ULTIMATE.start_main_~b~5) 0.0))) 0.0) (= (+ (* motzkin_902_2 (- 1.0)) motzkin_902_3 (* motzkin_902_4 (- 1.0)) motzkin_902_8) 0.0) (= (+ motzkin_902_2 (* motzkin_902_8 (- 1.0))) 0.0) (= (+ (* motzkin_902_5 (- 1.0)) motzkin_902_6 (* motzkin_902_9 (- 1.0))) 0.0) (= (+ motzkin_902_5 (* motzkin_902_6 (- 1.0)) (* motzkin_902_11 (+ (* 1.0 lp_0_0_ULTIMATE.start_main_~a~5) 0.0)) (* motzkin_902_12 (+ (* 1.0 lp_0_1_ULTIMATE.start_main_~a~5) 0.0))) 0.0) (= (+ motzkin_902_7 (* motzkin_902_11 (+ (* 1.0 lp_0_0_~last) 0.0)) (* motzkin_902_12 (+ (* 1.0 lp_0_1_~last) 0.0))) 0.0) (<= (+ (* motzkin_902_0 (- 200000.0)) (* motzkin_902_1 2.0) (* motzkin_902_5 2.0) (* motzkin_902_6 (- 2.0)) (* motzkin_902_7 (- 1.0)) (* motzkin_902_9 (- 1.0)) (* motzkin_902_10 (- 2.0)) (* motzkin_902_11 (+ (* 1.0 lp_0_0c) 0.0)) (* motzkin_902_12 (+ (* 1.0 lp_0_1c) 0.0))) 0.0) (or (< (+ (* motzkin_902_0 (- 200000.0)) (* motzkin_902_1 2.0) (* motzkin_902_5 2.0) (* motzkin_902_6 (- 2.0)) (* motzkin_902_7 (- 1.0)) (* motzkin_902_9 (- 1.0)) (* motzkin_902_10 (- 2.0)) (* motzkin_902_11 (+ (* 1.0 lp_0_0c) 0.0)) (* motzkin_902_12 (+ (* 1.0 lp_0_1c) 0.0))) 0.0) (> 0.0 0.0)) (>= motzkin_903_0 0.0) (>= motzkin_903_1 0.0) (>= motzkin_903_2 0.0) (>= motzkin_903_3 0.0) (>= motzkin_903_4 0.0) (>= motzkin_903_5 0.0) (>= motzkin_903_6 0.0) (>= motzkin_903_7 0.0) (>= motzkin_903_8 0.0) (>= motzkin_903_9 0.0) (>= motzkin_903_10 0.0) (>= motzkin_903_11 0.0) (>= motzkin_903_12 0.0) (= (+ motzkin_903_0 motzkin_903_10 (* motzkin_903_11 (+ (* 1.0 lp_0_0_ULTIMATE.start_main_~c~5) 0.0)) (* motzkin_903_12 (+ (* 1.0 lp_0_1_ULTIMATE.start_main_~c~5) 0.0))) 0.0) (= (+ (* motzkin_903_1 (- 1.0)) motzkin_903_8 motzkin_903_9) 0.0) (= (+ motzkin_903_1 (* motzkin_903_9 (- 1.0)) (* motzkin_903_11 (+ (* 1.0 lp_0_0_ULTIMATE.start_main_~b~5) 0.0)) (* motzkin_903_12 (+ (* 1.0 lp_0_1_ULTIMATE.start_main_~b~5) 0.0))) 0.0) (= (+ (* motzkin_903_2 (- 1.0)) motzkin_903_3 (* motzkin_903_4 (- 1.0)) motzkin_903_7) 0.0) (= (+ motzkin_903_2 (* motzkin_903_7 (- 1.0))) 0.0) (= (+ (* motzkin_903_5 (- 1.0)) motzkin_903_6 (* motzkin_903_8 (- 1.0))) 0.0) (= (+ motzkin_903_5 (* motzkin_903_6 (- 1.0)) (* motzkin_903_11 (+ (* 1.0 lp_0_0_ULTIMATE.start_main_~a~5) 0.0)) (* motzkin_903_12 (+ (* 1.0 lp_0_1_ULTIMATE.start_main_~a~5) 0.0))) 0.0) (= (+ (* motzkin_903_10 (- 1.0)) (* motzkin_903_11 (+ (* 1.0 lp_0_0_~last) 0.0)) (* motzkin_903_12 (+ (* 1.0 lp_0_1_~last) 0.0))) 0.0) (<= (+ (* motzkin_903_0 (- 200000.0)) (* motzkin_903_1 2.0) (* motzkin_903_5 2.0) (* motzkin_903_6 (- 2.0)) (* motzkin_903_8 (- 1.0)) (* motzkin_903_9 (- 2.0)) (* motzkin_903_10 (- 2.0)) (* motzkin_903_11 (+ (* 1.0 lp_0_0c) 0.0)) (* motzkin_903_12 (+ (* 1.0 lp_0_1c) 0.0))) 0.0) (or (< (+ (* motzkin_903_0 (- 200000.0)) (* motzkin_903_1 2.0) (* motzkin_903_5 2.0) (* motzkin_903_6 (- 2.0)) (* motzkin_903_8 (- 1.0)) (* motzkin_903_9 (- 2.0)) (* motzkin_903_10 (- 2.0)) (* motzkin_903_11 (+ (* 1.0 lp_0_0c) 0.0)) (* motzkin_903_12 (+ (* 1.0 lp_0_1c) 0.0))) 0.0) (> 0.0 0.0)) (>= motzkin_904_0 0.0) (>= motzkin_904_1 0.0) (>= motzkin_904_2 0.0) (>= motzkin_904_3 0.0) (>= motzkin_904_4 0.0) (>= motzkin_904_5 0.0) (>= motzkin_904_6 0.0) (>= motzkin_904_7 0.0) (>= motzkin_904_8 0.0) (>= motzkin_904_9 0.0) (>= motzkin_904_10 0.0) (>= motzkin_904_11 0.0) (>= motzkin_904_12 0.0) (= (+ motzkin_904_0 (* motzkin_904_7 (- 1.0)) (* motzkin_904_11 (+ (* 1.0 lp_0_0_ULTIMATE.start_main_~c~5) 0.0)) (* motzkin_904_12 (+ (* 1.0 lp_0_1_ULTIMATE.start_main_~c~5) 0.0))) 0.0) (= (+ (* motzkin_904_1 (- 1.0)) (* motzkin_904_9 (- 1.0)) motzkin_904_10) 0.0) (= (+ motzkin_904_1 (* motzkin_904_10 (- 1.0)) (* motzkin_904_11 (+ (* 1.0 lp_0_0_ULTIMATE.start_main_~b~5) 0.0)) (* motzkin_904_12 (+ (* 1.0 lp_0_1_ULTIMATE.start_main_~b~5) 0.0))) 0.0) (= (+ (* motzkin_904_2 (- 1.0)) motzkin_904_3 (* motzkin_904_4 (- 1.0)) motzkin_904_8) 0.0) (= (+ motzkin_904_2 (* motzkin_904_8 (- 1.0))) 0.0) (= (+ (* motzkin_904_5 (- 1.0)) motzkin_904_6 motzkin_904_9) 0.0) (= (+ motzkin_904_5 (* motzkin_904_6 (- 1.0)) (* motzkin_904_11 (+ (* 1.0 lp_0_0_ULTIMATE.start_main_~a~5) 0.0)) (* motzkin_904_12 (+ (* 1.0 lp_0_1_ULTIMATE.start_main_~a~5) 0.0))) 0.0) (= (+ motzkin_904_7 (* motzkin_904_11 (+ (* 1.0 lp_0_0_~last) 0.0)) (* motzkin_904_12 (+ (* 1.0 lp_0_1_~last) 0.0))) 0.0) (<= (+ (* motzkin_904_0 (- 200000.0)) (* motzkin_904_1 2.0) (* motzkin_904_5 2.0) (* motzkin_904_6 (- 2.0)) (* motzkin_904_7 (- 1.0)) (* motzkin_904_9 (- 1.0)) (* motzkin_904_10 (- 2.0)) (* motzkin_904_11 (+ (* 1.0 lp_0_0c) 0.0)) (* motzkin_904_12 (+ (* 1.0 lp_0_1c) 0.0))) 0.0) (or (< (+ (* motzkin_904_0 (- 200000.0)) (* motzkin_904_1 2.0) (* motzkin_904_5 2.0) (* motzkin_904_6 (- 2.0)) (* motzkin_904_7 (- 1.0)) (* motzkin_904_9 (- 1.0)) (* motzkin_904_10 (- 2.0)) (* motzkin_904_11 (+ (* 1.0 lp_0_0c) 0.0)) (* motzkin_904_12 (+ (* 1.0 lp_0_1c) 0.0))) 0.0) (> 0.0 0.0)) (>= motzkin_905_0 0.0) (>= motzkin_905_1 0.0) (>= motzkin_905_2 0.0) (>= motzkin_905_3 0.0) (>= motzkin_905_4 0.0) (>= motzkin_905_5 0.0) (>= motzkin_905_6 0.0) (>= motzkin_905_7 0.0) (>= motzkin_905_8 0.0) (>= motzkin_905_9 0.0) (>= motzkin_905_10 0.0) (>= motzkin_905_11 0.0) (>= motzkin_905_12 0.0) (= (+ motzkin_905_0 motzkin_905_10 (* motzkin_905_11 (+ (* 1.0 lp_0_0_ULTIMATE.start_main_~c~5) 0.0)) (* motzkin_905_12 (+ (* 1.0 lp_0_1_ULTIMATE.start_main_~c~5) 0.0))) 0.0) (= (+ (* motzkin_905_1 (- 1.0)) (* motzkin_905_8 (- 1.0)) motzkin_905_9) 0.0) (= (+ motzkin_905_1 (* motzkin_905_9 (- 1.0)) (* motzkin_905_11 (+ (* 1.0 lp_0_0_ULTIMATE.start_main_~b~5) 0.0)) (* motzkin_905_12 (+ (* 1.0 lp_0_1_ULTIMATE.start_main_~b~5) 0.0))) 0.0) (= (+ (* motzkin_905_2 (- 1.0)) motzkin_905_3 (* motzkin_905_4 (- 1.0)) motzkin_905_7) 0.0) (= (+ motzkin_905_2 (* motzkin_905_7 (- 1.0))) 0.0) (= (+ (* motzkin_905_5 (- 1.0)) motzkin_905_6 motzkin_905_8) 0.0) (= (+ motzkin_905_5 (* motzkin_905_6 (- 1.0)) (* motzkin_905_11 (+ (* 1.0 lp_0_0_ULTIMATE.start_main_~a~5) 0.0)) (* motzkin_905_12 (+ (* 1.0 lp_0_1_ULTIMATE.start_main_~a~5) 0.0))) 0.0) (= (+ (* motzkin_905_10 (- 1.0)) (* motzkin_905_11 (+ (* 1.0 lp_0_0_~last) 0.0)) (* motzkin_905_12 (+ (* 1.0 lp_0_1_~last) 0.0))) 0.0) (<= (+ (* motzkin_905_0 (- 200000.0)) (* motzkin_905_1 2.0) (* motzkin_905_5 2.0) (* motzkin_905_6 (- 2.0)) (* motzkin_905_8 (- 1.0)) (* motzkin_905_9 (- 2.0)) (* motzkin_905_10 (- 2.0)) (* motzkin_905_11 (+ (* 1.0 lp_0_0c) 0.0)) (* motzkin_905_12 (+ (* 1.0 lp_0_1c) 0.0))) 0.0) (or (< (+ (* motzkin_905_0 (- 200000.0)) (* motzkin_905_1 2.0) (* motzkin_905_5 2.0) (* motzkin_905_6 (- 2.0)) (* motzkin_905_8 (- 1.0)) (* motzkin_905_9 (- 2.0)) (* motzkin_905_10 (- 2.0)) (* motzkin_905_11 (+ (* 1.0 lp_0_0c) 0.0)) (* motzkin_905_12 (+ (* 1.0 lp_0_1c) 0.0))) 0.0) (> 0.0 0.0))))
(check-sat)
(exit)
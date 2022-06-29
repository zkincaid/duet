(set-info :smt-lib-version 2.6)
(set-info :source |The authors Robert Vajda and Zoltan Kovacs released this problem in the paper that can be found in "http://ceur-ws.org/Vol-2752/paper15.pdf". A short description of the problem can be found down below.

RegHexagon-Diagonal_Side:
 Comparison of Diagonal and Side (regular hexagon):Let A, B be arbitrary points. Let poly1 be the regular 6-gon with vertices A, B, C, D, E, F. Let f be the segment A, B. Let l be the segment E, A. Compare segment A, B and segment E, A.

This problem was added to SMT-LIB by Tereso del Rio and Matthew England.| )
(set-info :category "industrial")
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :status sat)
(set-logic QF_NRA)
(declare-fun m () Real)
(declare-fun v10 () Real)
(declare-fun v11 () Real)
(declare-fun v12 () Real)
(declare-fun v13 () Real)
(declare-fun v14 () Real)
(declare-fun v16 () Real)
(declare-fun v17 () Real)
(declare-fun v9 () Real)
(assert (and (< 0 m) (< 0 v17) (< 0 v16) (= (+ (* (* v10 v10) (- 1) )(* v9 (- 4) )7) 0) (= (+ (* (* v10 v10) (- 1) )(* v11 (- 4) )(* v9 6) (- 3) )0) (= (+ (* v10 v9) v10 (* v12 (- 2))) 0) (= (+ (* v10 v10) (* (* v10 v12) (- 1) )(* v11 3) (* v13 (- 2) )(* v9 (- 1))) 0) (= (+ (* v10 v11) (* (* v10 v9) (- 1) )(* v10 (- 1) )(* v12 3) (* v14 (- 2))) 0) (= (+ (* v10 v10) (- 3) )0) (= (+ (* v11 v11) (* v12 v12) (* (* v17 v17) (- 1))) 0) (= (+ (* (* m v17) (- 1) )1) 0) (= (+ (* v16 (- 1) )1) 0)))
(check-sat)
(exit)

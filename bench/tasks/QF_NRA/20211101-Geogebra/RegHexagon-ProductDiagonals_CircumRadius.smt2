(set-info :smt-lib-version 2.6)
(set-info :source |The authors Robert Vajda and Zoltan Kovacs released this problem in the paper that can be found in "http://ceur-ws.org/Vol-2752/paper15.pdf". A short description of the problem can be found down below.

RegHexagon-ProductDiagonals_CircumRadius:
 Comparison of circumradius and product of lengths of diagonals (regular hexagon):Let A, B be arbitrary points. Let poly1 be the regular 6-gon with vertices A, B, C, D, E, F. Let b be the segment A, B. Let f be the segment F, A. Let c be the segment A, C. Let d be the segment A, D. Let e be the segment A, E. Let G be the midpoint of d. Let r be the segment G, B. Compare b c d e f and r^5.

This problem was added to SMT-LIB by Tereso del Rio and Matthew England.| )
(set-info :category "industrial")
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :status sat)
(set-logic QF_NRA)
(declare-fun m () Real)
(declare-fun v11 () Real)
(declare-fun v12 () Real)
(declare-fun v13 () Real)
(declare-fun v14 () Real)
(declare-fun v15 () Real)
(declare-fun v16 () Real)
(declare-fun v17 () Real)
(declare-fun v18 () Real)
(declare-fun v19 () Real)
(declare-fun v20 () Real)
(declare-fun v21 () Real)
(declare-fun v22 () Real)
(assert (and (< 0 m) (< 0 v22) (< 0 v20) (< 0 v17) (< 0 v21) (< 0 v18) (< 0 v19) (= (+ (* (* v16 v16) (- 4) )(* v15 (- 8) )7) 0) (= (+ (* (* v16 v16) (- 4) )(* v11 (- 4) )(* v15 12) (- 3) )0) (= (+ (* (* v15 v16) 2) (* v12 (- 1) )v16) 0) (= (+ (* (* v12 v16) (- 2) )(* (* v16 v16) 4) (* v11 3) (* v13 (- 2) )(* v15 (- 2))) 0) (= (+ (* (* v11 v16) 2) (* (* v15 v16) (- 4) )(* v12 3) (* v14 (- 2) )(* v16 (- 2))) 0) (= (+ (* (* v16 v16) 4) (- 3) )0) (= (+ (* v15 v15) (* v16 v16) (* (* v22 v22) (- 1) )(* v15 (- 2) )1) 0) (= (+ (* (* v16 v16) 4) (* (* v21 v21) (- 4) )9) 0) (= (+ (* v11 v11) (* v12 v12) (* (* v20 v20) (- 1))) 0) (= (+ (* (* v15 v15) 4) (* (* v16 v16) 4) (* (* v17 v17) (- 1))) 0) (= (+ (* v13 v13) (* v14 v14) (* (* v18 v18) (- 1))) 0) (= (+ (* v19 (- 1) )1) 0) (= (+ (* (* m (* v22 v22 v22 v22 v22)) (- 1) )(* v17 v18 v20 v21)) 0)))
(check-sat)
(exit)

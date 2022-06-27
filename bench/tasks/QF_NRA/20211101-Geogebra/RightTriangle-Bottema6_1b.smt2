(set-info :smt-lib-version 2.6)
(set-info :source |The authors Robert Vajda and Zoltan Kovacs released this problem in the paper that can be found in "http://ceur-ws.org/Vol-2752/paper15.pdf". A short description of the problem can be found down below.

RightTriangle-Bottema6.1b:
 Comparison of Sum of Heights and Perimeter via realgeom, Bottema 6.1 (right triangle, ver. b):Let C, B be arbitrary points. Let a be the segment C, B. Let f be the line through C perpendicular to a. Let A be a point on f. Let c be the segment A, B. Let h be the line through C perpendicular to c. Let D be the intersection of c and h. Let h_c be the segment C, D. Let b be the segment C, A. Compare a + b + h_c and a + b + c.

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
(declare-fun v9 () Real)
(assert (and (< 0 m) (< 0 v14) (< 0 v13) (< 0 v16) (< 0 v15) (= (+ (* (* v16 v16) (- 1) )(* v9 v9) 1) 0) (= (+ (* v11 v9) v12 (* v9 (- 1))) 0) (= (+ (* (* v12 v9) (- 1) )v11) 0) (= (+ (* (* v14 v14) (- 1) )(* v9 v9)) 0) (= (+ (* v11 v11) (* v12 v12) (* (* v13 v13) (- 1))) 0) (= (+ (* v15 (- 1) )1) 0) (= (+ (* (* m v14) (- 1) )(* (* m v16) (- 1) )(* m (- 1) )v13 v14 1) 0)))
(check-sat)
(exit)

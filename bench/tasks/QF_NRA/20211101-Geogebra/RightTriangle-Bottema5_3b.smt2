(set-info :smt-lib-version 2.6)
(set-info :source |The authors Robert Vajda and Zoltan Kovacs released this problem in the paper that can be found in "http://ceur-ws.org/Vol-2752/paper15.pdf". A short description of the problem can be found down below.

RightTriangle-Bottema5.3b:
 Comparison of Circumradius and Perimeter via realgeom, Bottema 5.3 (right triangle, ver. b):Let C, B be arbitrary points. Let a be the segment C, B. Let f be the line through C perpendicular to a. Let A be a point on f. Let c be the segment A, B. Let b be the segment C, A. Let O be the midpoint of c. Let R be the segment C, O. Compare a + b + c and segment C, O.

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
(declare-fun v8 () Real)
(declare-fun w1 () Real)
(assert (and (< 0 m) (< 0 v11) (< 0 v13) (< 0 v14) (< 0 v12) (= (+ (* (* v14 v14) (- 1) )(* v8 v8) 1) 0) (= (+ (* (* v13 v13) (- 1) )(* v8 v8)) 0) (= (+ (* (* v11 v11) (- 4) )(* v8 v8) 1) 0) (= (+ v13 v14 (* w1 (- 1) )1) 0) (= (+ (* (* m v11) (- 1) )w1) 0) (= (+ (* v12 (- 1) )1) 0)))
(check-sat)
(exit)

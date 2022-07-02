(set-info :smt-lib-version 2.6)
(set-info :source |The authors Robert Vajda and Zoltan Kovacs released this problem in the paper that can be found in "http://ceur-ws.org/Vol-2752/paper15.pdf". A short description of the problem can be found down below.

IsoTriangle-Perimeter_CircumRadius_b:
 Comparison of Perimeter and CircumRadius via realgeom (isosceles triangle, ver. b):Let B_2, B_1 be arbitrary points. Let a be the segment B_2, B_1. Let c be the circle through B_1 with center B_2. Let d be the circle through B_2 with center B_1. Let D be the intersection point of d, c. Let g be the line through D perpendicular to a. Let A be a point on g. Let b be the segment B_2, A. Let i be the perpendicular bisector of B_2A. Let E be the intersection of g and i. Let R be the segment B_2, E. Compare segment B_2, E and a + 2b.

This problem was added to SMT-LIB by Tereso del Rio and Matthew England.| )
(set-info :category "industrial")
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :status sat)
(set-logic QF_NRA)
(declare-fun m () Real)
(declare-fun v14 () Real)
(declare-fun v15 () Real)
(declare-fun v16 () Real)
(declare-fun v17 () Real)
(declare-fun v18 () Real)
(declare-fun v19 () Real)
(declare-fun v8 () Real)
(declare-fun w2 () Real)
(assert (and (< 0 m) (< 0 v17) (< 0 v19) (< 0 v18) (= (+ (* (* v14 v14) 2) (* (* v14 v15) (- 2) )(* (* v14 v16) (- 2) )(* v15 v16)) 0) (= (+ (* (* v15 v15) (- 1) )(* (* v8 v8) (- 1) )(* v8 2)) 0) (= (+ (* (* v15 v15) (- 1) )(* (* v8 v8) (- 1) )(* v15 2) (* v8 2) (- 1) )0) (= (+ (* (* v14 v14) 4) (* (* v14 v15) (- 4) )(* (* v15 v15) 2) (* (* v19 v19) (- 1))) 0) (= (+ (* v15 v15) (* v16 v16) (* (* v17 v17) (- 1))) 0) (= (+ (* v19 2) (* w2 (- 1) )1) 0) (= (+ (* (* m w2) (- 1) )v17) 0) (= (+ (* v18 (- 1) )1) 0)))
(check-sat)
(exit)

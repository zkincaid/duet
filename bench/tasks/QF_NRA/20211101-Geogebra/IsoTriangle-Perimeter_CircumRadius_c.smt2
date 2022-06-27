(set-info :smt-lib-version 2.6)
(set-info :source |The authors Robert Vajda and Zoltan Kovacs released this problem in the paper that can be found in "http://ceur-ws.org/Vol-2752/paper15.pdf". A short description of the problem can be found down below.

IsoTriangle-Perimeter_CircumRadius_c:
 Comparison of Perimeter and CircumRadius via realgeom (isosceles triangle, ver. c):Let B_2, B_1 be arbitrary points. Let a be the segment B_2, B_1. Let c be the circle through B_1 with center B_2. Let d be the circle through B_2 with center B_1. Let E be the intersection point of c, d. Let g be the line through E perpendicular to a. Let A be a point on g. Let b be the segment B_2, A. Let e be the circle through A with center B_2. Let k be the circle through B_2 with center A. Let F be the intersection point of e, k. Let i be the line through F perpendicular to b. Let H be the intersection of g and i. Let R be the segment B_2, H. Compare a + 2b and segment B_2, H.

This problem was added to SMT-LIB by Tereso del Rio and Matthew England.| )
(set-info :category "industrial")
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :status unknown)
(set-logic QF_NRA)
(declare-fun m () Real)
(declare-fun v11 () Real)
(declare-fun v13 () Real)
(declare-fun v14 () Real)
(declare-fun v15 () Real)
(declare-fun v16 () Real)
(declare-fun v17 () Real)
(declare-fun v18 () Real)
(declare-fun v19 () Real)
(declare-fun v8 () Real)
(declare-fun w1 () Real)
(assert (and (< 0 m) (< 0 v17) (< 0 v19) (< 0 v18) (= (+ (* (* v11 v14) (- 1) )(* v11 v16) (* v14 v13) (* (* v13 v15) (- 1) )(* (* v13 v16) (- 1) )(* v15 v15)) 0) (= (+ (* (* v15 v15) (- 1) )(* (* v8 v8) (- 1) )(* v8 2)) 0) (= (+ (* (* v11 v13) (- 2) )(* v13 v13) (* (* v14 v14) (- 1) )(* (* v14 v15) 2)) 0) (= (+ (* (* v15 v15) (- 1) )(* (* v8 v8) (- 1) )(* v15 2) (* v8 2) (- 1) )0) (= (+ (* (* v11 v11) (- 1) )(* (* v11 v14) 2) (* (* v14 v13) (- 2) )(* (* v13 v15) 2) (* (* v14 v14) (- 1) )(* (* v14 v15) 2) (* (* v15 v15) (- 1))) 0) (= (+ (* v11 v11) (* (* v11 v13) (- 2) )(* v13 v13) (* v15 v15) (* (* v19 v19) (- 1))) 0) (= (+ (* v15 v15) (* v16 v16) (* (* v17 v17) (- 1))) 0) (= (+ (* v19 2) (* w1 (- 1) )1) 0) (= (+ (* (* m v17) (- 1) )w1) 0) (= (+ (* v18 (- 1) )1) 0)))
(check-sat)
(exit)

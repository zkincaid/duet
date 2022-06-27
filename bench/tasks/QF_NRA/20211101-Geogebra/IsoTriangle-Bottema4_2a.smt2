(set-info :smt-lib-version 2.6)
(set-info :source |The authors Robert Vajda and Zoltan Kovacs released this problem in the paper that can be found in "http://ceur-ws.org/Vol-2752/paper15.pdf". A short description of the problem can be found down below.

IsoTriangle-Bottema4.2a:
 Comparison of Area and Perimeter via RealGeom, Bottema 4.2 (isosceles triangle, ver. a):Let A, B be arbitrary points. Let c be the segment A, B. Let d be the circle through B with center A. Let C be a point on d. Let a be the segment B, C. Let f be the line through A perpendicular to a. Let D be the intersection of f and a. Let h_a be the segment A, D. Compare (a + 2c)^2 and a h_a / 2.

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
(declare-fun v7 () Real)
(declare-fun v8 () Real)
(declare-fun v9 () Real)
(assert (and (< 0 m) (< 0 v13) (< 0 v12) (< 0 v11) (= (+ (* v10 v8) (* v7 v9) (* v7 (- 1))) 0) (= (+ (* (* v12 v12) (- 1) )(* v7 v7) (* v8 v8)) 0) (= (+ (* (* v7 v7) (- 1) )(* (* v8 v8) (- 1) )(* v8 (- 2))) 0) (= (+ (* (* v10 v7) (- 1) )(* v8 v9)) 0) (= (+ (* v10 v10) (* (* v13 v13) (- 1) )(* v9 v9)) 0) (= (+ (* v11 (- 1) )1) 0) (= (+ (* (* m v12 v13) (- 1) )(* (* v12 v12) 2) (* v12 8) 8) 0)))
(check-sat)
(exit)

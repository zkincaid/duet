(set-info :smt-lib-version 2.6)
(set-logic QF_NRA)
(set-info :author |Thomas Sturm, CNRS France, http://science.thomas-sturm.de|)
(set-info :source |
Transmitted by: Thomas Sturm
Generated on: 20161105
Received on: 20161105
Generator: RedLog, http://www.redlog.eu/
Application: qualitative analysis of systems of ODE in physics, chemistry, and the life sciences
Publication: Algebraic Biology 2008, doi:10.1007/978-3-540-85101-1_15
Additional information:
All problems have the following form: a certain polynomial has a zero where all variables are positive.  Interval solutions for satisfiable problems is a valuable information.
|)
(set-info :series |MBO - Methylene Blue Oscillator System|)
(set-info :instance |E1|)
(set-info :category "industrial")
(set-info :status unsat)
(declare-const h6 Real)
(declare-const h5 Real)
(declare-const h4 Real)
(declare-const h3 Real)
(declare-const h2 Real)
(declare-const h1 Real)
(assert (and (> h1 0) (> h2 0) (> h3 0) (> h4 0) (> h5 0) (> h6 0) (= (+ (* 12 
(* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5) (* 12 (* h1 h1 h1 h1) (* h2 h2 h2) 
(* h3 h3) h6) (* 4 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5)) (* 10 (* h1 h1 h1 
h1) (* h2 h2 h2) h3 h5 h6) (* 4 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6)) (* 2 
(* h1 h1 h1 h1) (* h2 h2 h2) (* h5 h5) h6) (* 2 (* h1 h1 h1 h1) (* h2 h2 h2) h5 
(* h6 h6)) (* 48 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5) (* 48 (* h1 h1 h1 h1
) (* h2 h2) (* h3 h3 h3) h6) (* 26 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5) 
(* 20 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h6) (* 32 (* h1 h1 h1 h1) (* h2 h2)
 (* h3 h3) (* h5 h5)) (* 76 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h5 h6) (* 40 (* 
h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6)) (* 10 (* h1 h1 h1 h1) (* h2 h2) h3 
h4 (* h5 h5)) (* 16 (* h1 h1 h1 h1) (* h2 h2) h3 h4 h5 h6) (* 4 (* h1 h1 h1 h1) 
(* h2 h2) h3 h4 (* h6 h6)) (* 8 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5)) (* 28
 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5) h6) (* 32 (* h1 h1 h1 h1) (* h2 h2) h3 
h5 (* h6 h6)) (* 8 (* h1 h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6)) (* 4 (* h1 h1 h1 
h1) (* h2 h2) h4 (* h5 h5) h6) (* 2 (* h1 h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6)) 
(* 4 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5 h5) h6) (* 8 (* h1 h1 h1 h1) (* h2 h2) 
(* h5 h5) (* h6 h6)) (* 4 (* h1 h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6)) (* 56 (* h1
 h1 h1 h1) h2 (* h3 h3 h3) h4 h5) (* 32 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h6) 
(* 32 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5)) (* 80 (* h1 h1 h1 h1) h2 (* h3 
h3 h3) h5 h6) (* 64 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6)) (* 18 (* h1 h1 h1
 h1) h2 (* h3 h3) (* h4 h4) h5) (* 8 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h6) 
(* 48 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5)) (* 88 (* h1 h1 h1 h1) h2 (* h3 
h3) h4 h5 h6) (* 32 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6)) (* 16 (* h1 h1 h1
 h1) h2 (* h3 h3) (* h5 h5 h5)) (* 64 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5) h6)
 (* 104 (* h1 h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6)) (* 32 (* h1 h1 h1 h1) h2 (* 
h3 h3) (* h6 h6 h6)) (* 8 (* h1 h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5)) (* 6 (* h1 
h1 h1 h1) h2 h3 (* h4 h4) h5 h6) (* 12 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5 h5)) 
(* 40 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5) h6) (* 24 (* h1 h1 h1 h1) h2 h3 h4 h5 
(* h6 h6)) (* 16 (* h1 h1 h1 h1) h2 h3 (* h5 h5 h5) h6) (* 48 (* h1 h1 h1 h1) h2
 h3 (* h5 h5) (* h6 h6)) (* 24 (* h1 h1 h1 h1) h2 h3 h5 (* h6 h6 h6)) (* 2 (* h1
 h1 h1 h1) h2 (* h4 h4) (* h5 h5) h6) (* 4 (* h1 h1 h1 h1) h2 h4 (* h5 h5 h5) h6
) (* 8 (* h1 h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6)) (* 8 (* h1 h1 h1 h1) h2 (* h5 
h5 h5) (* h6 h6)) (* 8 (* h1 h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6)) (* 16 (* h1 h1
 h1 h1) (* h3 h3 h3) (* h4 h4) h5) (* 16 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h5 
h5)) (* 64 (* h1 h1 h1 h1) (* h3 h3 h3) h4 h5 h6) (* 32 (* h1 h1 h1 h1) (* h3 h3
 h3) (* h5 h5) h6) (* 64 (* h1 h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6)) (* 4 (* h1 
h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5) (* 16 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) 
(* h5 h5)) (* 24 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) h5 h6) (* 8 (* h1 h1 h1 h1)
 (* h3 h3) h4 (* h5 h5 h5)) (* 64 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5) h6) (* 
48 (* h1 h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6)) (* 16 (* h1 h1 h1 h1) (* h3 h3) 
(* h5 h5 h5) h6) (* 64 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6)) (* 32 (* 
h1 h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6)) (* 2 (* h1 h1 h1 h1) h3 (* h4 h4 h4) (* 
h5 h5)) (* 4 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5)) (* 12 (* h1 h1 h1 h1) h3
 (* h4 h4) (* h5 h5) h6) (* 16 (* h1 h1 h1 h1) h3 h4 (* h5 h5 h5) h6) (* 24 (* 
h1 h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6)) (* 16 (* h1 h1 h1 h1) h3 (* h5 h5 h5) 
(* h6 h6)) (* 16 (* h1 h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6)) (* 6 (* h1 h1 h1) 
(* h2 h2 h2 h2) (* h3 h3) h5) (* 6 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h6) 
(* 2 (* h1 h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5)) (* 5 (* h1 h1 h1) (* h2 h2 h2 h2
) h3 h5 h6) (* 2 (* h1 h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6)) (* (* h1 h1 h1) (* 
h2 h2 h2 h2) (* h5 h5) h6) (* (* h1 h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6)) (* 42 
(* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5) (* 42 (* h1 h1 h1) (* h2 h2 h2) (* h3
 h3 h3) h6) (* 45 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5) (* 36 (* h1 h1 h1) 
(* h2 h2 h2) (* h3 h3) h4 h6) (* 30 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5
)) (* 71 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 h6) (* 38 (* h1 h1 h1) (* h2 h2 
h2) (* h3 h3) (* h6 h6)) (* 17 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5)) (* 29 
(* h1 h1 h1) (* h2 h2 h2) h3 h4 h5 h6) (* 8 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* 
h6 h6)) (* 8 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5)) (* 27 (* h1 h1 h1) (* h2
 h2 h2) h3 (* h5 h5) h6) (* 31 (* h1 h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6)) (* 8 
(* h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6)) (* 7 (* h1 h1 h1) (* h2 h2 h2) h4 (* 
h5 h5) h6) (* 4 (* h1 h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6)) (* 4 (* h1 h1 h1) (* 
h2 h2 h2) (* h5 h5 h5) h6) (* 8 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6)) 
(* 4 (* h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6)) (* 48 (* h1 h1 h1) (* h2 h2) (* 
h3 h3 h3 h3) h5) (* 48 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h6) (* 153 (* h1 
h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5) (* 108 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) 
h4 h6) (* 76 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5)) (* 182 (* h1 h1 h1) 
(* h2 h2) (* h3 h3 h3) h5 h6) (* 120 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 
h6)) (* 58 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5) (* 30 (* h1 h1 h1) (* 
h2 h2) (* h3 h3) (* h4 h4) h6) (* 125 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 
h5)) (* 229 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6) (* 90 (* h1 h1 h1) (* h2 
h2) (* h3 h3) h4 (* h6 h6)) (* 36 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5))
 (* 128 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) h6) (* 182 (* h1 h1 h1) (* h2
 h2) (* h3 h3) h5 (* h6 h6)) (* 60 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6)
) (* 25 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5)) (* 23 (* h1 h1 h1) (* h2 
h2) h3 (* h4 h4) h5 h6) (* 2 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h6 h6)) (* 
32 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5)) (* 99 (* h1 h1 h1) (* h2 h2) h3 h4
 (* h5 h5) h6) (* 69 (* h1 h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6)) (* 6 (* h1 h1 h1
) (* h2 h2) h3 h4 (* h6 h6 h6)) (* 4 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5)) 
(* 34 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) h6) (* 80 (* h1 h1 h1) (* h2 h2) h3
 (* h5 h5) (* h6 h6)) (* 46 (* h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6)) (* 4 (* 
h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6 h6)) (* 7 (* h1 h1 h1) (* h2 h2) (* h4 h4) 
(* h5 h5) h6) (* (* h1 h1 h1) (* h2 h2) (* h4 h4) h5 (* h6 h6)) (* 12 (* h1 h1 
h1) (* h2 h2) h4 (* h5 h5 h5) h6) (* 21 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5) (* 
h6 h6)) (* 3 (* h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6 h6)) (* 2 (* h1 h1 h1) (* h2 
h2) (* h5 h5 h5 h5) h6) (* 14 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6)) (* 
14 (* h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6)) (* 2 (* h1 h1 h1) (* h2 h2) h5
 (* h6 h6 h6 h6)) (* 56 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h5) (* 32 (* h1 h1 h1
) h2 (* h3 h3 h3 h3) h4 h6) (* 32 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5)) (* 
80 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h5 h6) (* 64 (* h1 h1 h1) h2 (* h3 h3 h3 h3) 
(* h6 h6)) (* 102 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5) (* 32 (* h1 h1 h1) 
h2 (* h3 h3 h3) (* h4 h4) h6) (* 134 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5)) 
(* 296 (* h1 h1 h1) h2 (* h3 h3 h3) h4 h5 h6) (* 96 (* h1 h1 h1) h2 (* h3 h3 h3)
 h4 (* h6 h6)) (* 32 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5)) (* 140 (* h1 h1 
h1) h2 (* h3 h3 h3) (* h5 h5) h6) (* 232 (* h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6 
h6)) (* 64 (* h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6)) (* 23 (* h1 h1 h1) h2 (* 
h3 h3) (* h4 h4 h4) h5) (* 4 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h6) (* 95 
(* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5)) (* 131 (* h1 h1 h1) h2 (* h3 h3) 
(* h4 h4) h5 h6) (* 20 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h6 h6)) (* 66 (* 
h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5)) (* 262 (* h1 h1 h1) h2 (* h3 h3) h4 (* 
h5 h5) h6) (* 232 (* h1 h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6)) (* 32 (* h1 h1 h1) 
h2 (* h3 h3) h4 (* h6 h6 h6)) (* 8 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5)) 
(* 68 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) h6) (* 192 (* h1 h1 h1) h2 (* h3 h3
) (* h5 h5) (* h6 h6)) (* 124 (* h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6)) (* 16 
(* h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6 h6)) (* 11 (* h1 h1 h1) h2 h3 (* h4 h4 h4)
 (* h5 h5)) (* 3 (* h1 h1 h1) h2 h3 (* h4 h4 h4) h5 h6) (* 24 (* h1 h1 h1) h2 h3
 (* h4 h4) (* h5 h5 h5)) (* 63 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) h6) (* 15 
(* h1 h1 h1) h2 h3 (* h4 h4) h5 (* h6 h6)) (* 6 (* h1 h1 h1) h2 h3 h4 (* h5 h5 
h5 h5)) (* 70 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5) h6) (* 112 (* h1 h1 h1) h2 h3 
h4 (* h5 h5) (* h6 h6)) (* 24 (* h1 h1 h1) h2 h3 h4 h5 (* h6 h6 h6)) (* 8 (* h1 
h1 h1) h2 h3 (* h5 h5 h5 h5) h6) (* 56 (* h1 h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6)
) (* 60 (* h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6)) (* 12 (* h1 h1 h1) h2 h3 h5 
(* h6 h6 h6 h6)) (* (* h1 h1 h1) h2 (* h4 h4 h4) (* h5 h5) h6) (* 4 (* h1 h1 h1)
 h2 (* h4 h4) (* h5 h5 h5) h6) (* 5 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 h6
)) (* 2 (* h1 h1 h1) h2 h4 (* h5 h5 h5 h5) h6) (* 12 (* h1 h1 h1) h2 h4 (* h5 h5
 h5) (* h6 h6)) (* 8 (* h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6 h6)) (* 4 (* h1 h1 h1
) h2 (* h5 h5 h5 h5) (* h6 h6)) (* 8 (* h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6)) 
(* 4 (* h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6 h6)) (* 16 (* h1 h1 h1) (* h3 h3 h3 
h3) (* h4 h4) h5) (* 16 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5)) (* 64 (* h1 
h1 h1) (* h3 h3 h3 h3) h4 h5 h6) (* 32 (* h1 h1 h1) (* h3 h3 h3 h3) (* h5 h5) h6
) (* 64 (* h1 h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6)) (* 16 (* h1 h1 h1) (* h3 h3 
h3) (* h4 h4 h4) h5) (* 40 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5)) (* 80 
(* h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 h6) (* 16 (* h1 h1 h1) (* h3 h3 h3) h4 
(* h5 h5 h5)) (* 136 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) h6) (* 128 (* h1 h1 
h1) (* h3 h3 h3) h4 h5 (* h6 h6)) (* 32 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5 h5) 
h6) (* 112 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6)) (* 64 (* h1 h1 h1) (* 
h3 h3 h3) h5 (* h6 h6 h6)) (* 2 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4 h4) h5) (* 16
 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5)) (* 14 (* h1 h1 h1) (* h3 h3) (* 
h4 h4 h4) h5 h6) (* 20 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5)) (* 80 (* 
h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) h6) (* 36 (* h1 h1 h1) (* h3 h3) (* h4 
h4) h5 (* h6 h6)) (* 4 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5)) (* 68 (* h1 h1
 h1) (* h3 h3) h4 (* h5 h5 h5) h6) (* 128 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5) 
(* h6 h6)) (* 40 (* h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6)) (* 8 (* h1 h1 h1) 
(* h3 h3) (* h5 h5 h5 h5) h6) (* 56 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6
)) (* 64 (* h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6)) (* 16 (* h1 h1 h1) (* h3
 h3) h5 (* h6 h6 h6 h6)) (* (* h1 h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5)) (* 4 (* 
h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5)) (* 7 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 
h5) h6) (* 2 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5)) (* 20 (* h1 h1 h1) h3 
(* h4 h4) (* h5 h5 h5) h6) (* 18 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5) (* h6 h6)) 
(* 8 (* h1 h1 h1) h3 h4 (* h5 h5 h5 h5) h6) (* 32 (* h1 h1 h1) h3 h4 (* h5 h5 h5
) (* h6 h6)) (* 20 (* h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6)) (* 8 (* h1 h1 h1) 
h3 (* h5 h5 h5 h5) (* h6 h6)) (* 16 (* h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6)) 
(* 8 (* h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6 h6)) (* 12 (* h1 h1) (* h2 h2 h2 h2) 
(* h3 h3 h3) h5) (* 12 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h6) (* 13 (* h1 h1
) (* h2 h2 h2 h2) (* h3 h3) h4 h5) (* 10 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 
h6) (* 8 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h5 h5)) (* 19 (* h1 h1) (* h2 h2
 h2 h2) (* h3 h3) h5 h6) (* 10 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h6 h6)) 
(* 5 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h5 h5)) (* 8 (* h1 h1) (* h2 h2 h2 h2) 
h3 h4 h5 h6) (* 2 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h6 h6)) (* 2 (* h1 h1) (* 
h2 h2 h2 h2) h3 (* h5 h5 h5)) (* 7 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) h6) 
(* 8 (* h1 h1) (* h2 h2 h2 h2) h3 h5 (* h6 h6)) (* 2 (* h1 h1) (* h2 h2 h2 h2) 
h3 (* h6 h6 h6)) (* 2 (* h1 h1) (* h2 h2 h2 h2) h4 (* h5 h5) h6) (* (* h1 h1) 
(* h2 h2 h2 h2) h4 h5 (* h6 h6)) (* (* h1 h1) (* h2 h2 h2 h2) (* h5 h5 h5) h6) 
(* 2 (* h1 h1) (* h2 h2 h2 h2) (* h5 h5) (* h6 h6)) (* (* h1 h1) (* h2 h2 h2 h2)
 h5 (* h6 h6 h6)) (* 24 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h5) (* 24 (* h1 
h1) (* h2 h2 h2) (* h3 h3 h3 h3) h6) (* 87 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) 
h4 h5) (* 60 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h6) (* 38 (* h1 h1) (* h2 h2
 h2) (* h3 h3 h3) (* h5 h5)) (* 91 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 h6) 
(* 60 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h6 h6)) (* 49 (* h1 h1) (* h2 h2 h2
) (* h3 h3) (* h4 h4) h5) (* 26 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h4 h4) h6) 
(* 73 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h5 h5)) (* 138 (* h1 h1) (* h2 h2 
h2) (* h3 h3) h4 h5 h6) (* 56 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h6 h6)) (* 
18 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5 h5)) (* 64 (* h1 h1) (* h2 h2 h2) 
(* h3 h3) (* h5 h5) h6) (* 91 (* h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* h6 h6)) (* 
30 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6 h6)) (* 21 (* h1 h1) (* h2 h2 h2) 
h3 (* h4 h4) (* h5 h5)) (* 20 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) h5 h6) (* 2 
(* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h6 h6)) (* 19 (* h1 h1) (* h2 h2 h2) h3 
h4 (* h5 h5 h5)) (* 60 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) h6) (* 43 (* h1 h1
) (* h2 h2 h2) h3 h4 h5 (* h6 h6)) (* 4 (* h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6 h6
)) (* 2 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5 h5)) (* 17 (* h1 h1) (* h2 h2 h2) 
h3 (* h5 h5 h5) h6) (* 40 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* h6 h6)) (* 23 
(* h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6 h6)) (* 2 (* h1 h1) (* h2 h2 h2) h3 (* h6 
h6 h6 h6)) (* 6 (* h1 h1) (* h2 h2 h2) (* h4 h4) (* h5 h5) h6) (* (* h1 h1) (* 
h2 h2 h2) (* h4 h4) h5 (* h6 h6)) (* 7 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5 h5) h6
) (* 13 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5) (* h6 h6)) (* 2 (* h1 h1) (* h2 h2 
h2) h4 h5 (* h6 h6 h6)) (* (* h1 h1) (* h2 h2 h2) (* h5 h5 h5 h5) h6) (* 7 (* h1
 h1) (* h2 h2 h2) (* h5 h5 h5) (* h6 h6)) (* 7 (* h1 h1) (* h2 h2 h2) (* h5 h5) 
(* h6 h6 h6)) (* (* h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6 h6)) (* 108 (* h1 h1) (* 
h2 h2) (* h3 h3 h3 h3) h4 h5) (* 72 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h6) 
(* 28 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h5 h5)) (* 84 (* h1 h1) (* h2 h2) 
(* h3 h3 h3 h3) h5 h6) (* 72 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h6 h6)) (* 
144 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h5) (* 60 (* h1 h1) (* h2 h2) (* 
h3 h3 h3) (* h4 h4) h6) (* 167 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h5 h5)) 
(* 354 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 h6) (* 128 (* h1 h1) (* h2 h2) (* 
h3 h3 h3) h4 (* h6 h6)) (* 26 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5 h5)) (* 
124 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) h6) (* 214 (* h1 h1) (* h2 h2) 
(* h3 h3 h3) h5 (* h6 h6)) (* 68 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6 h6)) 
(* 36 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4 h4) h5) (* 8 (* h1 h1) (* h2 h2) 
(* h3 h3) (* h4 h4 h4) h6) (* 130 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h5 
h5)) (* 176 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 h6) (* 32 (* h1 h1) (* h2
 h2) (* h3 h3) (* h4 h4) (* h6 h6)) (* 81 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5
 h5 h5)) (* 292 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) h6) (* 252 (* h1 h1) 
(* h2 h2) (* h3 h3) h4 h5 (* h6 h6)) (* 40 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* 
h6 h6 h6)) (* 6 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5 h5)) (* 57 (* h1 h1) 
(* h2 h2) (* h3 h3) (* h5 h5 h5) h6) (* 165 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 
h5) (* h6 h6)) (* 112 (* h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6 h6)) (* 16 (* h1
 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6 h6)) (* 17 (* h1 h1) (* h2 h2) h3 (* h4 h4 
h4) (* h5 h5)) (* 6 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) h5 h6) (* 33 (* h1 h1) 
(* h2 h2) h3 (* h4 h4) (* h5 h5 h5)) (* 83 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* 
h5 h5) h6) (* 24 (* h1 h1) (* h2 h2) h3 (* h4 h4) h5 (* h6 h6)) (* 11 (* h1 h1) 
(* h2 h2) h3 h4 (* h5 h5 h5 h5)) (* 80 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) h6
) (* 119 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* h6 h6)) (* 30 (* h1 h1) (* h2 h2
) h3 h4 h5 (* h6 h6 h6)) (* 7 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) h6) (* 48 
(* h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* h6 h6)) (* 53 (* h1 h1) (* h2 h2) h3 (* 
h5 h5) (* h6 h6 h6)) (* 12 (* h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6 h6)) (* 2 (* h1
 h1) (* h2 h2) (* h4 h4 h4) (* h5 h5) h6) (* 7 (* h1 h1) (* h2 h2) (* h4 h4) (* 
h5 h5 h5) h6) (* 8 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6)) (* 4 (* h1
 h1) (* h2 h2) h4 (* h5 h5 h5 h5) h6) (* 15 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5) 
(* h6 h6)) (* 10 (* h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6 h6)) (* 4 (* h1 h1) 
(* h2 h2) (* h5 h5 h5 h5) (* h6 h6)) (* 8 (* h1 h1) (* h2 h2) (* h5 h5 h5) (* h6
 h6 h6)) (* 4 (* h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6 h6)) (* 68 (* h1 h1) h2 
(* h3 h3 h3 h3) (* h4 h4) h5) (* 16 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h6) 
(* 62 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h5 h5)) (* 172 (* h1 h1) h2 (* h3 h3 h3
 h3) h4 h5 h6) (* 48 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6)) (* 8 (* h1 h1) 
h2 (* h3 h3 h3 h3) (* h5 h5 h5)) (* 52 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) h6
) (* 104 (* h1 h1) h2 (* h3 h3 h3 h3) h5 (* h6 h6)) (* 32 (* h1 h1) h2 (* h3 h3 
h3 h3) (* h6 h6 h6)) (* 54 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h5) (* 8 (* h1
 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h6) (* 135 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4)
 (* h5 h5)) (* 212 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 h6) (* 32 (* h1 h1) h2
 (* h3 h3 h3) (* h4 h4) (* h6 h6)) (* 61 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5 
h5)) (* 295 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6) (* 282 (* h1 h1) h2 (* h3
 h3 h3) h4 h5 (* h6 h6)) (* 40 (* h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6 h6)) (* 4 
(* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5 h5)) (* 50 (* h1 h1) h2 (* h3 h3 h3) (* h5
 h5 h5) h6) (* 162 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* h6 h6)) (* 124 (* h1 
h1) h2 (* h3 h3 h3) h5 (* h6 h6 h6)) (* 16 (* h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6
 h6)) (* 6 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4 h4) h5) (* 52 (* h1 h1) h2 (* h3 
h3) (* h4 h4 h4) (* h5 h5)) (* 40 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 h6) (* 
67 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5 h5)) (* 197 (* h1 h1) h2 (* h3 h3) 
(* h4 h4) (* h5 h5) h6) (* 94 (* h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* h6 h6)) (* 
15 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5 h5)) (* 146 (* h1 h1) h2 (* h3 h3) h4 
(* h5 h5 h5) h6) (* 251 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* h6 h6)) (* 92 (* 
h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6)) (* 12 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5
 h5) h6) (* 80 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* h6 h6)) (* 106 (* h1 h1) 
h2 (* h3 h3) (* h5 h5) (* h6 h6 h6)) (* 32 (* h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6
 h6)) (* 3 (* h1 h1) h2 h3 (* h4 h4 h4 h4) (* h5 h5)) (* 13 (* h1 h1) h2 h3 (* 
h4 h4 h4) (* h5 h5 h5)) (* 20 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) h6) (* 8 
(* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5 h5)) (* 51 (* h1 h1) h2 h3 (* h4 h4) (* h5
 h5 h5) h6) (* 47 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* h6 h6)) (* 20 (* h1 h1)
 h2 h3 h4 (* h5 h5 h5 h5) h6) (* 68 (* h1 h1) h2 h3 h4 (* h5 h5 h5) (* h6 h6)) 
(* 46 (* h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6 h6)) (* 12 (* h1 h1) h2 h3 (* h5 h5 
h5 h5) (* h6 h6)) (* 30 (* h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6 h6)) (* 16 (* h1 
h1) h2 h3 (* h5 h5) (* h6 h6 h6 h6)) (* (* h1 h1) h2 (* h4 h4 h4) (* h5 h5 h5) 
h6) (* (* h1 h1) h2 (* h4 h4) (* h5 h5 h5 h5) h6) (* 4 (* h1 h1) h2 (* h4 h4) 
(* h5 h5 h5) (* h6 h6)) (* 3 (* h1 h1) h2 h4 (* h5 h5 h5 h5) (* h6 h6)) (* 5 (* 
h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6 h6)) (* 2 (* h1 h1) h2 (* h5 h5 h5 h5) (* h6 
h6 h6)) (* 2 (* h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6 h6)) (* 8 (* h1 h1) (* h3 h3 
h3 h3) (* h4 h4 h4) h5) (* 16 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5)) (* 
40 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 h6) (* 4 (* h1 h1) (* h3 h3 h3 h3) h4 
(* h5 h5 h5)) (* 48 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) h6) (* 64 (* h1 h1) 
(* h3 h3 h3 h3) h4 h5 (* h6 h6)) (* 8 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5 h5) h6)
 (* 32 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6)) (* 32 (* h1 h1) (* h3 h3 
h3 h3) h5 (* h6 h6 h6)) (* 4 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4 h4) h5) (* 20 
(* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5)) (* 24 (* h1 h1) (* h3 h3 h3) (* 
h4 h4 h4) h5 h6) (* 16 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5)) (* 88 (* 
h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6) (* 52 (* h1 h1) (* h3 h3 h3) (* h4 
h4) h5 (* h6 h6)) (* 2 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5 h5)) (* 48 (* h1 h1
) (* h3 h3 h3) h4 (* h5 h5 h5) h6) (* 124 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5) 
(* h6 h6)) (* 48 (* h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6 h6)) (* 4 (* h1 h1) (* h3
 h3 h3) (* h5 h5 h5 h5) h6) (* 32 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6))
 (* 56 (* h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6)) (* 16 (* h1 h1) (* h3 h3 
h3) h5 (* h6 h6 h6 h6)) (* 4 (* h1 h1) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5)) (* 
10 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5)) (* 24 (* h1 h1) (* h3 h3) (* 
h4 h4 h4) (* h5 h5) h6) (* 4 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5)) (* 
44 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6) (* 52 (* h1 h1) (* h3 h3) (* 
h4 h4) (* h5 h5) (* h6 h6)) (* 12 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) h6) (* 
62 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6)) (* 48 (* h1 h1) (* h3 h3) h4 
(* h5 h5) (* h6 h6 h6)) (* 8 (* h1 h1) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6)) (* 
28 (* h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6)) (* 16 (* h1 h1) (* h3 h3) (* 
h5 h5) (* h6 h6 h6 h6)) (* (* h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5 h5)) (* (* h1 
h1) h3 (* h4 h4 h4) (* h5 h5 h5 h5)) (* 6 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5)
 h6) (* 5 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) h6) (* 13 (* h1 h1) h3 (* h4 h4
) (* h5 h5 h5) (* h6 h6)) (* 8 (* h1 h1) h3 h4 (* h5 h5 h5 h5) (* h6 h6)) (* 12 
(* h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6 h6)) (* 4 (* h1 h1) h3 (* h5 h5 h5 h5) (* 
h6 h6 h6)) (* 4 (* h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6 h6)) (* 14 h1 (* h2 h2 h2 
h2) (* h3 h3 h3) h4 h5) (* 8 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h6) (* 4 h1 (* 
h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5)) (* 10 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h5 h6
) (* 8 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h6 h6)) (* 9 h1 (* h2 h2 h2 h2) (* h3 
h3) (* h4 h4) h5) (* 4 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h6) (* 12 h1 (* h2
 h2 h2 h2) (* h3 h3) h4 (* h5 h5)) (* 22 h1 (* h2 h2 h2 h2) (* h3 h3) h4 h5 h6) 
(* 8 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h6 h6)) (* 2 h1 (* h2 h2 h2 h2) (* h3 h3
) (* h5 h5 h5)) (* 8 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) h6) (* 13 h1 (* h2 
h2 h2 h2) (* h3 h3) h5 (* h6 h6)) (* 4 h1 (* h2 h2 h2 h2) (* h3 h3) (* h6 h6 h6)
) (* 4 h1 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5)) (* 3 h1 (* h2 h2 h2 h2) h3 (* 
h4 h4) h5 h6) (* 3 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5)) (* 10 h1 (* h2 h2 h2 
h2) h3 h4 (* h5 h5) h6) (* 6 h1 (* h2 h2 h2 h2) h3 h4 h5 (* h6 h6)) (* 2 h1 (* 
h2 h2 h2 h2) h3 (* h5 h5 h5) h6) (* 6 h1 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6))
 (* 3 h1 (* h2 h2 h2 h2) h3 h5 (* h6 h6 h6)) (* h1 (* h2 h2 h2 h2) (* h4 h4) (* 
h5 h5) h6) (* h1 (* h2 h2 h2 h2) h4 (* h5 h5 h5) h6) (* 2 h1 (* h2 h2 h2 h2) h4 
(* h5 h5) (* h6 h6)) (* h1 (* h2 h2 h2 h2) (* h5 h5 h5) (* h6 h6)) (* h1 (* h2 
h2 h2 h2) (* h5 h5) (* h6 h6 h6)) (* 28 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5) 
(* 16 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h6) (* 8 h1 (* h2 h2 h2) (* h3 h3 h3 h3
) (* h5 h5)) (* 20 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h5 h6) (* 16 h1 (* h2 h2 h2) 
(* h3 h3 h3 h3) (* h6 h6)) (* 50 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5) (* 
16 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h6) (* 49 h1 (* h2 h2 h2) (* h3 h3 h3)
 h4 (* h5 h5)) (* 108 h1 (* h2 h2 h2) (* h3 h3 h3) h4 h5 h6) (* 32 h1 (* h2 h2 
h2) (* h3 h3 h3) h4 (* h6 h6)) (* 8 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5)) 
(* 35 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6) (* 58 h1 (* h2 h2 h2) (* h3 h3 
h3) h5 (* h6 h6)) (* 16 h1 (* h2 h2 h2) (* h3 h3 h3) (* h6 h6 h6)) (* 19 h1 (* 
h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5) (* 4 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4)
 h6) (* 47 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5)) (* 69 h1 (* h2 h2 h2) 
(* h3 h3) (* h4 h4) h5 h6) (* 12 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h6 h6)) 
(* 24 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5)) (* 95 h1 (* h2 h2 h2) (* h3 h3)
 h4 (* h5 h5) h6) (* 81 h1 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6)) (* 12 h1 (* 
h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6)) (* 2 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 
h5)) (* 17 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6) (* 48 h1 (* h2 h2 h2) (* 
h3 h3) (* h5 h5) (* h6 h6)) (* 31 h1 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6)) (* 
4 h1 (* h2 h2 h2) (* h3 h3) (* h6 h6 h6 h6)) (* 9 h1 (* h2 h2 h2) h3 (* h4 h4 h4
) (* h5 h5)) (* 3 h1 (* h2 h2 h2) h3 (* h4 h4 h4) h5 h6) (* 12 h1 (* h2 h2 h2) 
h3 (* h4 h4) (* h5 h5 h5)) (* 33 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6) (* 9
 h1 (* h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6)) (* 3 h1 (* h2 h2 h2) h3 h4 (* h5 h5 
h5 h5)) (* 26 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5) h6) (* 39 h1 (* h2 h2 h2) h3 h4
 (* h5 h5) (* h6 h6)) (* 9 h1 (* h2 h2 h2) h3 h4 h5 (* h6 h6 h6)) (* 2 h1 (* h2 
h2 h2) h3 (* h5 h5 h5 h5) h6) (* 14 h1 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6)) 
(* 15 h1 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6)) (* 3 h1 (* h2 h2 h2) h3 h5 (* 
h6 h6 h6 h6)) (* h1 (* h2 h2 h2) (* h4 h4 h4) (* h5 h5) h6) (* 2 h1 (* h2 h2 h2)
 (* h4 h4) (* h5 h5 h5) h6) (* 3 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6)) 
(* h1 (* h2 h2 h2) h4 (* h5 h5 h5 h5) h6) (* 4 h1 (* h2 h2 h2) h4 (* h5 h5 h5) 
(* h6 h6)) (* 3 h1 (* h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6)) (* h1 (* h2 h2 h2) 
(* h5 h5 h5 h5) (* h6 h6)) (* 2 h1 (* h2 h2 h2) (* h5 h5 h5) (* h6 h6 h6)) (* h1
 (* h2 h2 h2) (* h5 h5) (* h6 h6 h6 h6)) (* 60 h1 (* h2 h2) (* h3 h3 h3 h3) (* 
h4 h4) h5) (* 16 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h6) (* 34 h1 (* h2 h2) 
(* h3 h3 h3 h3) h4 (* h5 h5)) (* 112 h1 (* h2 h2) (* h3 h3 h3 h3) h4 h5 h6) (* 
32 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6)) (* 4 h1 (* h2 h2) (* h3 h3 h3 h3) 
(* h5 h5 h5)) (* 26 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6) (* 52 h1 (* h2 h2
) (* h3 h3 h3 h3) h5 (* h6 h6)) (* 16 h1 (* h2 h2) (* h3 h3 h3 h3) (* h6 h6 h6))
 (* 46 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5) (* 8 h1 (* h2 h2) (* h3 h3 h3)
 (* h4 h4 h4) h6) (* 97 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5)) (* 154 h1
 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6) (* 24 h1 (* h2 h2) (* h3 h3 h3) (* h4 
h4) (* h6 h6)) (* 33 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5)) (* 178 h1 (* h2 
h2) (* h3 h3 h3) h4 (* h5 h5) h6) (* 170 h1 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 
h6)) (* 24 h1 (* h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6)) (* 2 h1 (* h2 h2) (* h3 h3
 h3) (* h5 h5 h5 h5)) (* 25 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6) (* 81 h1 
(* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6)) (* 62 h1 (* h2 h2) (* h3 h3 h3) h5 
(* h6 h6 h6)) (* 8 h1 (* h2 h2) (* h3 h3 h3) (* h6 h6 h6 h6)) (* 6 h1 (* h2 h2) 
(* h3 h3) (* h4 h4 h4 h4) h5) (* 44 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5
)) (* 34 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6) (* 48 h1 (* h2 h2) (* h3 h3)
 (* h4 h4) (* h5 h5 h5)) (* 141 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6) 
(* 66 h1 (* h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6)) (* 8 h1 (* h2 h2) (* h3 h3)
 h4 (* h5 h5 h5 h5)) (* 88 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6) (* 150 h1 
(* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6)) (* 54 h1 (* h2 h2) (* h3 h3) h4 h5 
(* h6 h6 h6)) (* 6 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6) (* 40 h1 (* h2 h2)
 (* h3 h3) (* h5 h5 h5) (* h6 h6)) (* 53 h1 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 
h6 h6)) (* 16 h1 (* h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6)) (* 3 h1 (* h2 h2) h3 
(* h4 h4 h4 h4) (* h5 h5)) (* 11 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5)) (* 
17 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6) (* 7 h1 (* h2 h2) h3 (* h4 h4) (* 
h5 h5 h5 h5)) (* 37 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6) (* 33 h1 (* h2 h2
) h3 (* h4 h4) (* h5 h5) (* h6 h6)) (* 13 h1 (* h2 h2) h3 h4 (* h5 h5 h5 h5) h6)
 (* 41 h1 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6)) (* 27 h1 (* h2 h2) h3 h4 (* h5
 h5) (* h6 h6 h6)) (* 6 h1 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6)) (* 15 h1 (* 
h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6)) (* 8 h1 (* h2 h2) h3 (* h5 h5) (* h6 h6 h6 
h6)) (* h1 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5) h6) (* h1 (* h2 h2) (* h4 h4) (* 
h5 h5 h5 h5) h6) (* 3 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6)) (* 2 h1 (* 
h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6)) (* 3 h1 (* h2 h2) h4 (* h5 h5 h5) (* h6 h6 
h6)) (* h1 (* h2 h2) (* h5 h5 h5 h5) (* h6 h6 h6)) (* h1 (* h2 h2) (* h5 h5 h5) 
(* h6 h6 h6 h6)) (* 16 h1 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h5) (* 32 h1 h2 (* h3 
h3 h3 h3) (* h4 h4) (* h5 h5)) (* 56 h1 h2 (* h3 h3 h3 h3) (* h4 h4) h5 h6) (* 
10 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5)) (* 60 h1 h2 (* h3 h3 h3 h3) h4 (* h5 
h5) h6) (* 64 h1 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6)) (* 8 h1 h2 (* h3 h3 h3 h3) 
(* h5 h5 h5) h6) (* 28 h1 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6)) (* 24 h1 h2 
(* h3 h3 h3 h3) h5 (* h6 h6 h6)) (* 8 h1 h2 (* h3 h3 h3) (* h4 h4 h4 h4) h5) (* 
38 h1 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5)) (* 36 h1 h2 (* h3 h3 h3) (* h4 h4 
h4) h5 h6) (* 32 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5)) (* 120 h1 h2 (* h3 
h3 h3) (* h4 h4) (* h5 h5) h6) (* 60 h1 h2 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6)) 
(* 5 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5)) (* 60 h1 h2 (* h3 h3 h3) h4 (* h5 h5
 h5) h6) (* 126 h1 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6)) (* 44 h1 h2 (* h3 h3 
h3) h4 h5 (* h6 h6 h6)) (* 4 h1 h2 (* h3 h3 h3) (* h5 h5 h5 h5) h6) (* 28 h1 h2 
(* h3 h3 h3) (* h5 h5 h5) (* h6 h6)) (* 44 h1 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6
 h6)) (* 12 h1 h2 (* h3 h3 h3) h5 (* h6 h6 h6 h6)) (* 8 h1 h2 (* h3 h3) (* h4 h4
 h4 h4) (* h5 h5)) (* 19 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5)) (* 36 h1 h2 
(* h3 h3) (* h4 h4 h4) (* h5 h5) h6) (* 8 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 
h5)) (* 60 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) h6) (* 60 h1 h2 (* h3 h3) (* 
h4 h4) (* h5 h5) (* h6 h6)) (* 15 h1 h2 (* h3 h3) h4 (* h5 h5 h5 h5) h6) (* 63 
h1 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6)) (* 44 h1 h2 (* h3 h3) h4 (* h5 h5) 
(* h6 h6 h6)) (* 7 h1 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6)) (* 22 h1 h2 (* h3 
h3) (* h5 h5 h5) (* h6 h6 h6)) (* 12 h1 h2 (* h3 h3) (* h5 h5) (* h6 h6 h6 h6)) 
(* 2 h1 h2 h3 (* h4 h4 h4 h4) (* h5 h5 h5)) (* 2 h1 h2 h3 (* h4 h4 h4) (* h5 h5 
h5 h5)) (* 9 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5) h6) (* 7 h1 h2 h3 (* h4 h4) (* 
h5 h5 h5 h5) h6) (* 15 h1 h2 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6)) (* 8 h1 h2 h3 
h4 (* h5 h5 h5 h5) (* h6 h6)) (* 11 h1 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6)) (* 3 
h1 h2 h3 (* h5 h5 h5 h5) (* h6 h6 h6)) (* 3 h1 h2 h3 (* h5 h5 h5) (* h6 h6 h6 h6
)) (* 4 h1 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5)) (* 2 h1 (* h3 h3 h3 h3) (* h4
 h4) (* h5 h5 h5)) (* 16 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6) (* 6 h1 (* 
h3 h3 h3 h3) h4 (* h5 h5 h5) h6) (* 20 h1 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6)
) (* 4 h1 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6)) (* 8 h1 (* h3 h3 h3 h3) (* h5 
h5) (* h6 h6 h6)) (* 2 h1 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5)) (* 4 h1 (* h3 
h3 h3) (* h4 h4 h4) (* h5 h5 h5)) (* 10 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) 
h6) (* h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5)) (* 16 h1 (* h3 h3 h3) (* h4 h4
) (* h5 h5 h5) h6) (* 18 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6)) (* 3 h1 
(* h3 h3 h3) h4 (* h5 h5 h5 h5) h6) (* 20 h1 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 
h6)) (* 14 h1 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6)) (* 2 h1 (* h3 h3 h3) (* h5
 h5 h5 h5) (* h6 h6)) (* 8 h1 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6)) (* 4 h1 
(* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6)) (* h1 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5
 h5)) (* h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5)) (* 5 h1 (* h3 h3) (* h4 h4 
h4) (* h5 h5 h5) h6) (* 4 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6) (* 9 h1 (* 
h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6)) (* 5 h1 (* h3 h3) h4 (* h5 h5 h5 h5) 
(* h6 h6)) (* 7 h1 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6)) (* 2 h1 (* h3 h3) (* 
h5 h5 h5 h5) (* h6 h6 h6)) (* 2 h1 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6)) (* 4 
(* h2 h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5) (* 2 (* h2 h2 h2 h2) (* h3 h3 h3) h4 
(* h5 h5)) (* 8 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 h6) (* 2 (* h2 h2 h2 h2) (* 
h3 h3 h3) (* h5 h5) h6) (* 4 (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6)) (* 2 (* 
h2 h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5) (* 4 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4)
 (* h5 h5)) (* 6 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6) (* (* h2 h2 h2 h2) 
(* h3 h3) h4 (* h5 h5 h5)) (* 8 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6) (* 6 
(* h2 h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6)) (* (* h2 h2 h2 h2) (* h3 h3) (* h5 h5
 h5) h6) (* 4 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6)) (* 2 (* h2 h2 h2 h2
) (* h3 h3) h5 (* h6 h6 h6)) (* (* h2 h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5)) (* 
(* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5)) (* 3 (* h2 h2 h2 h2) h3 (* h4 h4) (* 
h5 h5) h6) (* 2 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) h6) (* 3 (* h2 h2 h2 h2) h3 
h4 (* h5 h5) (* h6 h6)) (* (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6)) (* (* h2 
h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6)) (* 8 (* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4)
 h5) (* 4 (* h2 h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5)) (* 16 (* h2 h2 h2) (* h3 h3
 h3 h3) h4 h5 h6) (* 4 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6) (* 8 (* h2 h2 
h2) (* h3 h3 h3 h3) h5 (* h6 h6)) (* 8 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5
) (* 14 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5)) (* 24 (* h2 h2 h2) (* h3 
h3 h3) (* h4 h4) h5 h6) (* 4 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5)) (* 28 
(* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6) (* 24 (* h2 h2 h2) (* h3 h3 h3) h4 h5
 (* h6 h6)) (* 4 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6) (* 14 (* h2 h2 h2) 
(* h3 h3 h3) (* h5 h5) (* h6 h6)) (* 8 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6)
) (* 2 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5) (* 8 (* h2 h2 h2) (* h3 h3) 
(* h4 h4 h4) (* h5 h5)) (* 8 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6) (* 7 (* 
h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5)) (* 24 (* h2 h2 h2) (* h3 h3) (* h4 
h4) (* h5 h5) h6) (* 12 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6)) (* (* h2 
h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5)) (* 14 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5
) h6) (* 24 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6)) (* 8 (* h2 h2 h2) (* 
h3 h3) h4 h5 (* h6 h6 h6)) (* (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6) (* 7 
(* h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6)) (* 8 (* h2 h2 h2) (* h3 h3) (* h5
 h5) (* h6 h6 h6)) (* 2 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6)) (* (* h2 h2 
h2) h3 (* h4 h4 h4 h4) (* h5 h5)) (* 2 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5)
) (* 4 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6) (* (* h2 h2 h2) h3 (* h4 h4) 
(* h5 h5 h5 h5)) (* 6 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6) (* 6 (* h2 h2 
h2) h3 (* h4 h4) (* h5 h5) (* h6 h6)) (* 2 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) h6
) (* 6 (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6)) (* 4 (* h2 h2 h2) h3 h4 (* h5 
h5) (* h6 h6 h6)) (* (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6)) (* 2 (* h2 h2 h2
) h3 (* h5 h5 h5) (* h6 h6 h6)) (* (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6)) 
(* 8 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4 h4) h5) (* 8 (* h2 h2) (* h3 h3 h3 h3) 
(* h4 h4) (* h5 h5)) (* 24 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 h6) (* 2 (* h2
 h2) (* h3 h3 h3 h3) h4 (* h5 h5 h5)) (* 16 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 
h5) h6) (* 24 (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* h6 h6)) (* 2 (* h2 h2) (* h3 h3
 h3 h3) (* h5 h5 h5) h6) (* 8 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6)) (* 
8 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6 h6)) (* 4 (* h2 h2) (* h3 h3 h3) (* h4 
h4 h4 h4) h5) (* 14 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5)) (* 16 (* h2 
h2) (* h3 h3 h3) (* h4 h4 h4) h5 h6) (* 8 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5
 h5 h5)) (* 42 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6) (* 24 (* h2 h2) 
(* h3 h3 h3) (* h4 h4) h5 (* h6 h6)) (* (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5 h5
)) (* 16 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) h6) (* 42 (* h2 h2) (* h3 h3 h3)
 h4 (* h5 h5) (* h6 h6)) (* 16 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6 h6)) (* (* 
h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) h6) (* 8 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5)
 (* h6 h6)) (* 14 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6)) (* 4 (* h2 h2) 
(* h3 h3 h3) h5 (* h6 h6 h6 h6)) (* 4 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) (* h5 
h5)) (* 7 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5)) (* 16 (* h2 h2) (* h3 
h3) (* h4 h4 h4) (* h5 h5) h6) (* 2 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5
)) (* 21 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6) (* 24 (* h2 h2) (* h3 h3
) (* h4 h4) (* h5 h5) (* h6 h6)) (* 4 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) h6)
 (* 21 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6)) (* 16 (* h2 h2) (* h3 h3) 
h4 (* h5 h5) (* h6 h6 h6)) (* 2 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6)) 
(* 7 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6)) (* 4 (* h2 h2) (* h3 h3) (* 
h5 h5) (* h6 h6 h6 h6)) (* (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5 h5)) (* (* h2 
h2) h3 (* h4 h4 h4) (* h5 h5 h5 h5)) (* 4 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5)
 h6) (* 3 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) h6) (* 6 (* h2 h2) h3 (* h4 h4)
 (* h5 h5 h5) (* h6 h6)) (* 3 (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* h6 h6)) (* 4 
(* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6 h6)) (* (* h2 h2) h3 (* h5 h5 h5 h5) (* h6
 h6 h6)) (* (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6 h6)) (* 4 h2 (* h3 h3 h3 h3) 
(* h4 h4 h4) (* h5 h5)) (* 2 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5)) (* 12 h2
 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6) (* 4 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5)
 h6) (* 12 h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6)) (* 2 h2 (* h3 h3 h3 h3) 
(* h5 h5 h5) (* h6 h6)) (* 4 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6)) (* 2 h2 
(* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5)) (* 4 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 
h5 h5)) (* 8 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6) (* h2 (* h3 h3 h3) (* h4
 h4) (* h5 h5 h5 h5)) (* 12 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6) (* 12 h2 
(* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6)) (* 2 h2 (* h3 h3 h3) h4 (* h5 h5 h5 
h5) h6) (* 12 h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6)) (* 8 h2 (* h3 h3 h3) h4
 (* h5 h5) (* h6 h6 h6)) (* h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6)) (* 4 h2 
(* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6)) (* 2 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 
h6 h6)) (* h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5)) (* h2 (* h3 h3) (* h4 h4 
h4) (* h5 h5 h5 h5)) (* 4 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6) (* 3 h2 (* 
h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6) (* 6 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) 
(* h6 h6)) (* 3 h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6)) (* 4 h2 (* h3 h3) h4 
(* h5 h5 h5) (* h6 h6 h6)) (* h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6)) (* h2 
(* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6))) 0)))
(check-sat)
(exit)

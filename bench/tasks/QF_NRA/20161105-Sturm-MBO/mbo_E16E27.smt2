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
(set-info :instance |E16E27|)
(set-info :category "industrial")
(set-info :status unsat)
(declare-const j2 Real)
(declare-const h6 Real)
(declare-const h5 Real)
(declare-const h3 Real)
(declare-const h2 Real)
(declare-const h1 Real)
(assert (and (> h1 0) (> h2 0) (> h3 0) (> h5 0) (> h6 0) (> j2 0) (= (+ (* 16 
(* h1 h1 h1) (* h3 h3) h6 (* j2 j2)) (* 16 (* h1 h1 h1) (* h3 h3) h6 j2) (* 4 
(* h1 h1 h1) (* h3 h3) h6) (* 4 (* h1 h1 h1) h3 (* h6 h6) j2) (* 2 (* h1 h1 h1) 
h3 (* h6 h6)) (* 16 (* h1 h1) h2 (* h3 h3) h5 (* j2 j2)) (* 12 (* h1 h1) h2 (* 
h3 h3) h5 j2) (* 2 (* h1 h1) h2 (* h3 h3) h5) (* 48 (* h1 h1) h2 (* h3 h3) h6 
(* j2 j2)) (* 36 (* h1 h1) h2 (* h3 h3) h6 j2) (* 6 (* h1 h1) h2 (* h3 h3) h6) 
(* 8 (* h1 h1) h2 h3 h5 h6 j2) (* 5 (* h1 h1) h2 h3 h5 h6) (* 12 (* h1 h1) h2 h3
 (* h6 h6) j2) (* 4 (* h1 h1) h2 h3 (* h6 h6)) (* (* h1 h1) h2 h5 (* h6 h6)) (* 
64 (* h1 h1) (* h3 h3 h3) h6 (* j2 j2 j2)) (* 96 (* h1 h1) (* h3 h3 h3) h6 (* j2
 j2)) (* 48 (* h1 h1) (* h3 h3 h3) h6 j2) (* 8 (* h1 h1) (* h3 h3 h3) h6) (* 48 
(* h1 h1) (* h3 h3) h5 h6 (* j2 j2)) (* 44 (* h1 h1) (* h3 h3) h5 h6 j2) (* 10 
(* h1 h1) (* h3 h3) h5 h6) (* 32 (* h1 h1) (* h3 h3) (* h6 h6) (* j2 j2)) (* 28 
(* h1 h1) (* h3 h3) (* h6 h6) j2) (* 6 (* h1 h1) (* h3 h3) (* h6 h6)) (* 12 (* 
h1 h1) h3 h5 (* h6 h6) j2) (* 5 (* h1 h1) h3 h5 (* h6 h6)) (* 4 (* h1 h1) h3 (* 
h6 h6 h6) j2) (* 2 (* h1 h1) h3 (* h6 h6 h6)) (* 32 h1 (* h2 h2) (* h3 h3) h5 
(* j2 j2)) (* 20 h1 (* h2 h2) (* h3 h3) h5 j2) (* 3 h1 (* h2 h2) (* h3 h3) h5) 
(* 48 h1 (* h2 h2) (* h3 h3) h6 (* j2 j2)) (* 24 h1 (* h2 h2) (* h3 h3) h6 j2) 
(* 2 h1 (* h2 h2) (* h3 h3) h6) (* 4 h1 (* h2 h2) h3 (* h5 h5) j2) (* h1 (* h2 
h2) h3 (* h5 h5)) (* 16 h1 (* h2 h2) h3 h5 h6 j2) (* 7 h1 (* h2 h2) h3 h5 h6) 
(* 12 h1 (* h2 h2) h3 (* h6 h6) j2) (* 2 h1 (* h2 h2) h3 (* h6 h6)) (* h1 (* h2 
h2) (* h5 h5) h6) (* 2 h1 (* h2 h2) h5 (* h6 h6)) (* 64 h1 h2 (* h3 h3 h3) h5 
(* j2 j2 j2)) (* 80 h1 h2 (* h3 h3 h3) h5 (* j2 j2)) (* 32 h1 h2 (* h3 h3 h3) h5
 j2) (* 4 h1 h2 (* h3 h3 h3) h5) (* 128 h1 h2 (* h3 h3 h3) h6 (* j2 j2 j2)) (* 
144 h1 h2 (* h3 h3 h3) h6 (* j2 j2)) (* 48 h1 h2 (* h3 h3 h3) h6 j2) (* 4 h1 h2 
(* h3 h3 h3) h6) (* 32 h1 h2 (* h3 h3) (* h5 h5) (* j2 j2)) (* 24 h1 h2 (* h3 h3
) (* h5 h5) j2) (* 4 h1 h2 (* h3 h3) (* h5 h5)) (* 112 h1 h2 (* h3 h3) h5 h6 (* 
j2 j2)) (* 88 h1 h2 (* h3 h3) h5 h6 j2) (* 18 h1 h2 (* h3 h3) h5 h6) (* 64 h1 h2
 (* h3 h3) (* h6 h6) (* j2 j2)) (* 44 h1 h2 (* h3 h3) (* h6 h6) j2) (* 8 h1 h2 
(* h3 h3) (* h6 h6)) (* 16 h1 h2 h3 (* h5 h5) h6 j2) (* 9 h1 h2 h3 (* h5 h5) h6)
 (* 28 h1 h2 h3 h5 (* h6 h6) j2) (* 10 h1 h2 h3 h5 (* h6 h6)) (* 8 h1 h2 h3 (* 
h6 h6 h6) j2) (* 2 h1 h2 h3 (* h6 h6 h6)) (* 2 h1 h2 (* h5 h5) (* h6 h6)) (* h1 
h2 h5 (* h6 h6 h6)) (* 128 h1 (* h3 h3 h3) h5 h6 (* j2 j2 j2)) (* 176 h1 (* h3 
h3 h3) h5 h6 (* j2 j2)) (* 80 h1 (* h3 h3 h3) h5 h6 j2) (* 12 h1 (* h3 h3 h3) h5
 h6) (* 64 h1 (* h3 h3 h3) (* h6 h6) (* j2 j2 j2)) (* 80 h1 (* h3 h3 h3) (* h6 
h6) (* j2 j2)) (* 32 h1 (* h3 h3 h3) (* h6 h6) j2) (* 4 h1 (* h3 h3 h3) (* h6 h6
)) (* 48 h1 (* h3 h3) (* h5 h5) h6 (* j2 j2)) (* 40 h1 (* h3 h3) (* h5 h5) h6 j2
) (* 8 h1 (* h3 h3) (* h5 h5) h6) (* 64 h1 (* h3 h3) h5 (* h6 h6) (* j2 j2)) (* 
52 h1 (* h3 h3) h5 (* h6 h6) j2) (* 11 h1 (* h3 h3) h5 (* h6 h6)) (* 16 h1 (* h3
 h3) (* h6 h6 h6) (* j2 j2)) (* 12 h1 (* h3 h3) (* h6 h6 h6) j2) (* 2 h1 (* h3 
h3) (* h6 h6 h6)) (* 12 h1 h3 (* h5 h5) (* h6 h6) j2) (* 4 h1 h3 (* h5 h5) (* h6
 h6)) (* 8 h1 h3 h5 (* h6 h6 h6) j2) (* 3 h1 h3 h5 (* h6 h6 h6)) (* 16 (* h2 h2 
h2) (* h3 h3) h5 (* j2 j2)) (* 8 (* h2 h2 h2) (* h3 h3) h5 j2) (* (* h2 h2 h2) 
(* h3 h3) h5) (* 16 (* h2 h2 h2) (* h3 h3) h6 (* j2 j2)) (* 4 (* h2 h2 h2) (* h3
 h3) h6 j2) (* 4 (* h2 h2 h2) h3 (* h5 h5) j2) (* (* h2 h2 h2) h3 (* h5 h5)) (* 
8 (* h2 h2 h2) h3 h5 h6 j2) (* 2 (* h2 h2 h2) h3 h5 h6) (* 4 (* h2 h2 h2) h3 (* 
h6 h6) j2) (* (* h2 h2 h2) (* h5 h5) h6) (* (* h2 h2 h2) h5 (* h6 h6)) (* 64 (* 
h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2)) (* 64 (* h2 h2) (* h3 h3 h3) h5 (* j2 j2)) 
(* 20 (* h2 h2) (* h3 h3 h3) h5 j2) (* 2 (* h2 h2) (* h3 h3 h3) h5) (* 64 (* h2 
h2) (* h3 h3 h3) h6 (* j2 j2 j2)) (* 48 (* h2 h2) (* h3 h3 h3) h6 (* j2 j2)) (* 
8 (* h2 h2) (* h3 h3 h3) h6 j2) (* 32 (* h2 h2) (* h3 h3) (* h5 h5) (* j2 j2)) 
(* 24 (* h2 h2) (* h3 h3) (* h5 h5) j2) (* 4 (* h2 h2) (* h3 h3) (* h5 h5)) (* 
64 (* h2 h2) (* h3 h3) h5 h6 (* j2 j2)) (* 44 (* h2 h2) (* h3 h3) h5 h6 j2) (* 7
 (* h2 h2) (* h3 h3) h5 h6) (* 32 (* h2 h2) (* h3 h3) (* h6 h6) (* j2 j2)) (* 16
 (* h2 h2) (* h3 h3) (* h6 h6) j2) (* 4 (* h2 h2) h3 (* h5 h5 h5) j2) (* (* h2 
h2) h3 (* h5 h5 h5)) (* 16 (* h2 h2) h3 (* h5 h5) h6 j2) (* 7 (* h2 h2) h3 (* h5
 h5) h6) (* 16 (* h2 h2) h3 h5 (* h6 h6) j2) (* 6 (* h2 h2) h3 h5 (* h6 h6)) (* 
4 (* h2 h2) h3 (* h6 h6 h6) j2) (* (* h2 h2) (* h5 h5 h5) h6) (* 2 (* h2 h2) (* 
h5 h5) (* h6 h6)) (* (* h2 h2) h5 (* h6 h6 h6)) (* 64 h2 (* h3 h3 h3) (* h5 h5) 
(* j2 j2 j2)) (* 80 h2 (* h3 h3 h3) (* h5 h5) (* j2 j2)) (* 32 h2 (* h3 h3 h3) 
(* h5 h5) j2) (* 4 h2 (* h3 h3 h3) (* h5 h5)) (* 128 h2 (* h3 h3 h3) h5 h6 (* j2
 j2 j2)) (* 128 h2 (* h3 h3 h3) h5 h6 (* j2 j2)) (* 40 h2 (* h3 h3 h3) h5 h6 j2)
 (* 4 h2 (* h3 h3 h3) h5 h6) (* 64 h2 (* h3 h3 h3) (* h6 h6) (* j2 j2 j2)) (* 48
 h2 (* h3 h3 h3) (* h6 h6) (* j2 j2)) (* 8 h2 (* h3 h3 h3) (* h6 h6) j2) (* 16 
h2 (* h3 h3) (* h5 h5 h5) (* j2 j2)) (* 12 h2 (* h3 h3) (* h5 h5 h5) j2) (* 2 h2
 (* h3 h3) (* h5 h5 h5)) (* 64 h2 (* h3 h3) (* h5 h5) h6 (* j2 j2)) (* 56 h2 (* 
h3 h3) (* h5 h5) h6 j2) (* 12 h2 (* h3 h3) (* h5 h5) h6) (* 64 h2 (* h3 h3) h5 
(* h6 h6) (* j2 j2)) (* 44 h2 (* h3 h3) h5 (* h6 h6) j2) (* 7 h2 (* h3 h3) h5 
(* h6 h6)) (* 16 h2 (* h3 h3) (* h6 h6 h6) (* j2 j2)) (* 4 h2 (* h3 h3) (* h6 h6
 h6) j2) (* 8 h2 h3 (* h5 h5 h5) h6 j2) (* 4 h2 h3 (* h5 h5 h5) h6) (* 16 h2 h3 
(* h5 h5) (* h6 h6) j2) (* 7 h2 h3 (* h5 h5) (* h6 h6)) (* 8 h2 h3 h5 (* h6 h6 
h6) j2) (* 2 h2 h3 h5 (* h6 h6 h6)) (* h2 (* h5 h5 h5) (* h6 h6)) (* h2 (* h5 h5
) (* h6 h6 h6)) (* 64 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 80 (* h3 h3 h3)
 (* h5 h5) h6 (* j2 j2)) (* 32 (* h3 h3 h3) (* h5 h5) h6 j2) (* 4 (* h3 h3 h3) 
(* h5 h5) h6) (* 64 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 64 (* h3 h3 h3) 
h5 (* h6 h6) (* j2 j2)) (* 20 (* h3 h3 h3) h5 (* h6 h6) j2) (* 2 (* h3 h3 h3) h5
 (* h6 h6)) (* 16 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2)) (* 12 (* h3 h3) (* h5 h5 
h5) h6 j2) (* 2 (* h3 h3) (* h5 h5 h5) h6) (* 32 (* h3 h3) (* h5 h5) (* h6 h6) 
(* j2 j2)) (* 24 (* h3 h3) (* h5 h5) (* h6 h6) j2) (* 4 (* h3 h3) (* h5 h5) (* 
h6 h6)) (* 16 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 8 (* h3 h3) h5 (* h6 h6 h6
) j2) (* (* h3 h3) h5 (* h6 h6 h6)) (* 4 h3 (* h5 h5 h5) (* h6 h6) j2) (* h3 (* 
h5 h5 h5) (* h6 h6)) (* 4 h3 (* h5 h5) (* h6 h6 h6) j2) (* h3 (* h5 h5) (* h6 h6
 h6))) 0)))
(check-sat)
(exit)

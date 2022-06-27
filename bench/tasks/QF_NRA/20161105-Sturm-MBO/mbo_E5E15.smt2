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
(set-info :instance |E5E15|)
(set-info :category "industrial")
(set-info :status unsat)
(declare-const j2 Real)
(declare-const h6 Real)
(declare-const h5 Real)
(declare-const h4 Real)
(declare-const h3 Real)
(declare-const h2 Real)
(declare-const h1 Real)
(assert (and (> h1 0) (> h2 0) (> h3 0) (> h4 0) (> h5 0) (> h6 0) (> j2 0) (= 
(+ (* 3840 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 9408 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 7168 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2 j2 j2)) (* 2288
 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2 j2)) (* 320 (* h1 h1 
h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2)) (* 16 (* h1 h1 h1 h1) (* h2 h2
 h2) (* h3 h3) h5 (* j2 j2 j2)) (* 2560 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 8192 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 7456 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h6 
(* j2 j2 j2 j2 j2 j2)) (* 2864 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h6 (* j2 
j2 j2 j2 j2)) (* 496 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h6 (* j2 j2 j2 j2)) 
(* 32 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h6 (* j2 j2 j2)) (* 960 (* h1 h1 h1
 h1) (* h2 h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3552 (* h1 h1 
h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4912 (* h1 h1 
h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 3208 (* h1 h1 h1 
h1) (* h2 h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1032 (* h1 h1 h1 h1) (* 
h2 h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 152 (* h1 h1 h1 h1) (* h2 h2 h2) 
h3 (* h5 h5) (* j2 j2 j2 j2)) (* 8 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* 
j2 j2 j2)) (* 1760 (* h1 h1 h1 h1) (* h2 h2 h2) h3 h5 h6 (* j2 j2 j2 j2 j2 j2 j2
 j2 j2)) (* 6832 (* h1 h1 h1 h1) (* h2 h2 h2) h3 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 10056 (* h1 h1 h1 h1) (* h2 h2 h2) h3 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 7172 (* h1 h1 h1 h1) (* h2 h2 h2) h3 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 2624 (* 
h1 h1 h1 h1) (* h2 h2 h2) h3 h5 h6 (* j2 j2 j2 j2 j2)) (* 468 (* h1 h1 h1 h1) 
(* h2 h2 h2) h3 h5 h6 (* j2 j2 j2 j2)) (* 32 (* h1 h1 h1 h1) (* h2 h2 h2) h3 h5 
h6 (* j2 j2 j2)) (* 320 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6) (* j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 1744 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 3376 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 2868 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 1172 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 224 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6) (* j2 j2 j2 j2)) (* 16 (* h1 h1
 h1 h1) (* h2 h2 h2) h3 (* h6 h6) (* j2 j2 j2)) (* 320 (* h1 h1 h1 h1) (* h2 h2 
h2) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1504 (* h1 h1 h1 h1) (* 
h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2928 (* h1 h1 h1 h1) 
(* h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3048 (* h1 h1 h1 h1) 
(* h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1824 (* h1 h1 h1 h1) (* 
h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 624 (* h1 h1 h1 h1) (* h2 h2 h2
) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 112 (* h1 h1 h1 h1) (* h2 h2 h2) (* h5 h5)
 h6 (* j2 j2 j2 j2)) (* 8 (* h1 h1 h1 h1) (* h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2)
) (* 160 (* h1 h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2
 j2)) (* 912 (* h1 h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 2056 (* h1 h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 2396 (* h1 h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 1564 (* h1 h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 572 (* h1 h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 108 (* 
h1 h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 8 (* h1 h1 h1 h1) (* 
h2 h2 h2) h5 (* h6 h6) (* j2 j2 j2)) (* 9600 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 
h3) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 28320 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 
h3) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 29200 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3)
 h5 (* j2 j2 j2 j2 j2 j2)) (* 13744 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 
(* j2 j2 j2 j2 j2)) (* 3232 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* j2 j2 
j2 j2)) (* 368 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2)) (* 16 (* 
h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* j2 j2)) (* 6400 (* h1 h1 h1 h1) (* h2 
h2) (* h3 h3 h3) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 23680 (* h1 h1 h1 h1) (* h2 
h2) (* h3 h3 h3) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 28560 (* h1 h1 h1 h1) (* h2 h2)
 (* h3 h3 h3) h6 (* j2 j2 j2 j2 j2 j2)) (* 15616 (* h1 h1 h1 h1) (* h2 h2) (* h3
 h3 h3) h6 (* j2 j2 j2 j2 j2)) (* 4320 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h6
 (* j2 j2 j2 j2)) (* 592 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2))
 (* 32 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h6 (* j2 j2)) (* 2720 (* h1 h1 h1 
h1) (* h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 11264 (* h1 h1 
h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 16184 (* h1 h1 
h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 10048 (* h1 h1 h1 
h1) (* h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 3048 (* h1 h1 h1 h1) (* 
h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 440 (* h1 h1 h1 h1) (* h2 h2) (* 
h3 h3) h4 h5 (* j2 j2 j2 j2)) (* 24 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 
(* j2 j2 j2)) (* 960 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2 j2
 j2 j2 j2 j2)) (* 6992 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 14200 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2 
j2 j2 j2)) (* 11128 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2 j2 
j2)) (* 4112 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 
720 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 48 (* h1 h1 h1
 h1) (* h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2)) (* 4320 (* h1 h1 h1 h1) (* h2 h2) 
(* h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 18384 (* h1 h1 h1 h1) (* 
h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 30024 (* h1 h1 h1 h1)
 (* h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 24604 (* h1 h1 h1 h1
) (* h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 11280 (* h1 h1 h1 h1) 
(* h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 2804 (* h1 h1 h1 h1) (* h2 
h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 344 (* h1 h1 h1 h1) (* h2 h2) (* h3 
h3) (* h5 h5) (* j2 j2 j2)) (* 16 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) 
(* j2 j2)) (* 8560 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 38832 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 65444 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2 
j2 j2 j2)) (* 53044 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2 
j2)) (* 23888 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 
6160 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 848 (* h1 h1 
h1 h1) (* h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2)) (* 48 (* h1 h1 h1 h1) (* h2 h2) 
(* h3 h3) h5 h6 (* j2 j2)) (* 2080 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 12696 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 27636 (* h1 h1 h1 h1) (* h2 h2) (* h3 
h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 27236 (* h1 h1 h1 h1) (* h2 h2) (* h3
 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 14040 (* h1 h1 h1 h1) (* h2 h2) (* h3 
h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 3920 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) 
(* h6 h6) (* j2 j2 j2 j2)) (* 560 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6) 
(* j2 j2 j2)) (* 32 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6) (* j2 j2)) (* 
320 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (* 2544 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2
)) (* 6816 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 8284 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 4944 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1488
 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 216 (* h1 h1 
h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2)) (* 12 (* h1 h1 h1 h1) (* h2 h2
) h3 h4 (* h5 h5) (* j2 j2 j2)) (* 640 (* h1 h1 h1 h1) (* h2 h2) h3 h4 h5 h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4328 (* h1 h1 h1 h1) (* h2 h2) h3 h4 h5 h6 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 12280 (* h1 h1 h1 h1) (* h2 h2) h3 h4 h5 h6 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 17158 (* h1 h1 h1 h1) (* h2 h2) h3 h4 h5 h6 (* 
j2 j2 j2 j2 j2 j2 j2)) (* 11994 (* h1 h1 h1 h1) (* h2 h2) h3 h4 h5 h6 (* j2 j2 
j2 j2 j2 j2)) (* 4304 (* h1 h1 h1 h1) (* h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2 j2)) 
(* 760 (* h1 h1 h1 h1) (* h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2)) (* 52 (* h1 h1 h1 
h1) (* h2 h2) h3 h4 h5 h6 (* j2 j2 j2)) (* 400 (* h1 h1 h1 h1) (* h2 h2) h3 h4 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2500 (* h1 h1 h1 h1) (* h2 h2) h3 
h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 5214 (* h1 h1 h1 h1) (* h2 h2) h3 
h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4436 (* h1 h1 h1 h1) (* h2 h2) h3 h4 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1778 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h6 
h6) (* j2 j2 j2 j2 j2)) (* 336 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6) (* j2 
j2 j2 j2)) (* 24 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2)) (* 960 
(* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
4512 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
8224 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 7352
 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 3396 (* h1 
h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 804 (* h1 h1 h1 h1) 
(* h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 92 (* h1 h1 h1 h1) (* h2 h2) h3 
(* h5 h5 h5) (* j2 j2 j2)) (* 4 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* j2 
j2)) (* 2080 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 11456 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 26808 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 34240 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2)) (* 25684 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2 
j2)) (* 11494 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
2996 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 418 (* h1 h1 
h1 h1) (* h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2)) (* 24 (* h1 h1 h1 h1) (* h2 h2) 
h3 (* h5 h5) h6 (* j2 j2)) (* 1360 (* h1 h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8592 (* h1 h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 22164 (* h1 h1 h1 h1) (* h2 h2) h3 h5 (* h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 30800 (* h1 h1 h1 h1) (* h2 h2) h3 h5 (* h6
 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 25000 (* h1 h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6
) (* j2 j2 j2 j2 j2 j2)) (* 11992 (* h1 h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6) (* 
j2 j2 j2 j2 j2)) (* 3302 (* h1 h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 
j2)) (* 478 (* h1 h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2)) (* 28 (* h1 
h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6) (* j2 j2)) (* 320 (* h1 h1 h1 h1) (* h2 h2) 
h3 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2064 (* h1 h1 h1 h1) (* h2 h2
) h3 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 5040 (* h1 h1 h1 h1) (* h2 h2)
 h3 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 5848 (* h1 h1 h1 h1) (* h2 h2) h3 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3394 (* h1 h1 h1 h1) (* h2 h2) h3 (* h6 
h6 h6) (* j2 j2 j2 j2 j2)) (* 1002 (* h1 h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6) (* 
j2 j2 j2 j2)) (* 144 (* h1 h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2)) (* 
8 (* h1 h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6) (* j2 j2)) (* 400 (* h1 h1 h1 h1) 
(* h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2080 (* h1 h1 h1
 h1) (* h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4420 (* h1 h1 
h1 h1) (* h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4884 (* h1 h1 
h1 h1) (* h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2996 (* h1 h1 h1 
h1) (* h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 1016 (* h1 h1 h1 h1) (* 
h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 176 (* h1 h1 h1 h1) (* h2 h2) h4 
(* h5 h5) h6 (* j2 j2 j2 j2)) (* 12 (* h1 h1 h1 h1) (* h2 h2) h4 (* h5 h5) h6 
(* j2 j2 j2)) (* 120 (* h1 h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 984 (* h1 h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 2702 (* h1 h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 3552 (* h1 h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 2460 (* h1 h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 910 (* h1 h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 168 (* h1 h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 12 (* h1 h1
 h1 h1) (* h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 320 (* h1 h1 h1 h1) (* h2 h2)
 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1824 (* h1 h1 h1 h1) (* 
h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4352 (* h1 h1 h1 h1) 
(* h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 5640 (* h1 h1 h1 h1) 
(* h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 4308 (* h1 h1 h1 h1) (* 
h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 1968 (* h1 h1 h1 h1) (* h2 h2) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 520 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5 h5
) h6 (* j2 j2 j2 j2)) (* 72 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5 h5) h6 (* j2 j2 
j2)) (* 4 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5 h5) h6 (* j2 j2)) (* 400 (* h1 h1 
h1 h1) (* h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2560 
(* h1 h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 6716 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 9404 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2
)) (* 7642 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 3662 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
1002 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 142 (* h1
 h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 8 (* h1 h1 h1 h1) (* 
h2 h2) (* h5 h5) (* h6 h6) (* j2 j2)) (* 160 (* h1 h1 h1 h1) (* h2 h2) h5 (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1072 (* h1 h1 h1 h1) (* h2 h2) h5 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2928 (* h1 h1 h1 h1) (* h2 h2) 
h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4244 (* h1 h1 h1 h1) (* h2 h2) 
h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3550 (* h1 h1 h1 h1) (* h2 h2) h5 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1742 (* h1 h1 h1 h1) (* h2 h2) h5 (* h6 
h6 h6) (* j2 j2 j2 j2 j2)) (* 486 (* h1 h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6) (* 
j2 j2 j2 j2)) (* 70 (* h1 h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 4
 (* h1 h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6) (* j2 j2)) (* 6800 (* h1 h1 h1 h1) h2
 (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 24360 (* h1 h1 h1 h1) h2 
(* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 34160 (* h1 h1 h1 h1) h2 (* 
h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 25152 (* h1 h1 h1 h1) h2 (* h3 h3 
h3) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 10648 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h5 
(* j2 j2 j2 j2 j2)) (* 2560 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2
)) (* 320 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h5 (* j2 j2 j2)) (* 16 (* h1 h1 h1 
h1) h2 (* h3 h3 h3) h4 h5 (* j2 j2)) (* 2400 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 13880 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 27160 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 25896 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h6 (* j2 
j2 j2 j2 j2 j2)) (* 13400 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 
j2)) (* 3800 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 552 (* h1
 h1 h1 h1) h2 (* h3 h3 h3) h4 h6 (* j2 j2 j2)) (* 32 (* h1 h1 h1 h1) h2 (* h3 h3
 h3) h4 h6 (* j2 j2)) (* 4800 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* j2 j2
 j2 j2 j2 j2 j2 j2 j2)) (* 22560 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 40880 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* j2
 j2 j2 j2 j2 j2 j2)) (* 37072 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* j2 j2
 j2 j2 j2 j2)) (* 18812 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2
 j2)) (* 5692 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 1024
 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2)) (* 100 (* h1 h1 h1 h1) 
h2 (* h3 h3 h3) (* h5 h5) (* j2 j2)) (* 4 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h5 
h5) j2) (* 10400 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 50080 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 91680 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 81536 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 39204 
(* h1 h1 h1 h1) h2 (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 10976 (* h1 h1 h1 
h1) h2 (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 1848 (* h1 h1 h1 h1) h2 (* h3 h3 
h3) h5 h6 (* j2 j2 j2)) (* 180 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h5 h6 (* j2 j2)) 
(* 8 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h5 h6 j2) (* 3200 (* h1 h1 h1 h1) h2 (* h3 
h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 19040 (* h1 h1 h1 h1) h2 (* 
h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 43920 (* h1 h1 h1 h1) h2 (* 
h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 51088 (* h1 h1 h1 h1) h2 (* h3 
h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 33288 (* h1 h1 h1 h1) h2 (* h3 h3 h3)
 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 12656 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6
) (* j2 j2 j2 j2)) (* 2784 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6) (* j2 j2 j2
)) (* 328 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6) (* j2 j2)) (* 16 (* h1 h1 h1
 h1) h2 (* h3 h3 h3) (* h6 h6) j2) (* 480 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4)
 h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3816 (* h1 h1 h1 h1) h2 (* h3 h3) (* 
h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8604 (* h1 h1 h1 h1) h2 (* h3 h3) 
(* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 8512 (* h1 h1 h1 h1) h2 (* h3 h3) 
(* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 4528 (* h1 h1 h1 h1) h2 (* h3 h3) (* 
h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 1328 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) 
h5 (* j2 j2 j2 j2 j2)) (* 200 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* j2 j2
 j2 j2)) (* 12 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 1200 
(* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
5220 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
7716 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 5424
 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 1956 (* h1 
h1 h1 h1) h2 (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 348 (* h1 h1 h1 h1) 
h2 (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2)) (* 24 (* h1 h1 h1 h1) h2 (* h3 h3) 
(* h4 h4) h6 (* j2 j2 j2)) (* 1440 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 9728 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5
) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 26008 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h5
 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 35184 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h5
 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 26012 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5
) (* j2 j2 j2 j2 j2 j2)) (* 10858 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* 
j2 j2 j2 j2 j2)) (* 2554 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 
j2)) (* 316 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 16 (* h1 
h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* j2 j2)) (* 3200 (* h1 h1 h1 h1) h2 (* h3 
h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 22000 (* h1 h1 h1 h1) h2 (* 
h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 60312 (* h1 h1 h1 h1) h2 (* 
h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 83448 (* h1 h1 h1 h1) h2 (* h3 
h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 62978 (* h1 h1 h1 h1) h2 (* h3 h3) h4 
h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 27606 (* h1 h1 h1 h1) h2 (* h3 h3) h4 h5 h6 (* 
j2 j2 j2 j2 j2)) (* 7060 (* h1 h1 h1 h1) h2 (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) 
(* 976 (* h1 h1 h1 h1) h2 (* h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 56 (* h1 h1 h1 h1)
 h2 (* h3 h3) h4 h5 h6 (* j2 j2)) (* 2960 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 15792 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 30640 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 28260 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 14028 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* 3856 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6) (* j2 j2 
j2 j2)) (* 552 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6) (* j2 j2 j2)) (* 32 (* 
h1 h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6) (* j2 j2)) (* 1920 (* h1 h1 h1 h1) h2 (* 
h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 9984 (* h1 h1 h1 h1) h2 
(* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 20000 (* h1 h1 h1 h1) h2 
(* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 19616 (* h1 h1 h1 h1) h2 (* 
h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 10240 (* h1 h1 h1 h1) h2 (* h3 h3)
 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 3108 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5 
h5) (* j2 j2 j2 j2)) (* 550 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* j2 j2 
j2)) (* 52 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* j2 j2)) (* 2 (* h1 h1 h1
 h1) h2 (* h3 h3) (* h5 h5 h5) j2) (* 4480 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5
) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 27616 (* h1 h1 h1 h1) h2 (* h3 h3) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 71344 (* h1 h1 h1 h1) h2 (* h3 
h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 99840 (* h1 h1 h1 h1) h2 (* h3 
h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 82488 (* h1 h1 h1 h1) h2 (* h3 h3)
 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 41552 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5
 h5) h6 (* j2 j2 j2 j2 j2)) (* 12684 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5) h6 
(* j2 j2 j2 j2)) (* 2296 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2))
 (* 230 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5) h6 (* j2 j2)) (* 10 (* h1 h1 h1 
h1) h2 (* h3 h3) (* h5 h5) h6 j2) (* 3680 (* h1 h1 h1 h1) h2 (* h3 h3) h5 (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 25456 (* h1 h1 h1 h1) h2 (* h3 h3) h5 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 72704 (* h1 h1 h1 h1) h2 (* h3 h3) 
h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 111592 (* h1 h1 h1 h1) h2 (* h3 h3)
 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 101368 (* h1 h1 h1 h1) h2 (* h3 h3) 
h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 57292 (* h1 h1 h1 h1) h2 (* h3 h3) h5 (* 
h6 h6) (* j2 j2 j2 j2 j2)) (* 20168 (* h1 h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6) 
(* j2 j2 j2 j2)) (* 4266 (* h1 h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6) (* j2 j2 j2))
 (* 494 (* h1 h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6) (* j2 j2)) (* 24 (* h1 h1 h1 
h1) h2 (* h3 h3) h5 (* h6 h6) j2) (* 1280 (* h1 h1 h1 h1) h2 (* h3 h3) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8256 (* h1 h1 h1 h1) h2 (* h3 h3) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 20800 (* h1 h1 h1 h1) h2 (* h3 h3) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 26240 (* h1 h1 h1 h1) h2 (* h3 h3) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 17960 (* h1 h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2)) (* 6936 (* h1 h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6) (* j2 j2 
j2 j2)) (* 1508 (* h1 h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2)) (* 172 
(* h1 h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6) (* j2 j2)) (* 8 (* h1 h1 h1 h1) h2 (* 
h3 h3) (* h6 h6 h6) j2) (* 400 (* h1 h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2080 (* h1 h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4340 (* h1 h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5
) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4508 (* h1 h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5)
 (* j2 j2 j2 j2 j2 j2 j2)) (* 2424 (* h1 h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* 
j2 j2 j2 j2 j2 j2)) (* 696 (* h1 h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* j2 j2 j2
 j2 j2)) (* 102 (* h1 h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 6 
(* h1 h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 480 (* h1 h1 h1 h1) 
h2 h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2816 (* h1 h1 h1 h1)
 h2 h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 7484 (* h1 h1 h1 h1) 
h2 h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 10088 (* h1 h1 h1 h1) h2 
h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 6795 (* h1 h1 h1 h1) h2 h3 (* h4
 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 2376 (* h1 h1 h1 h1) h2 h3 (* h4 h4) h5 h6 
(* j2 j2 j2 j2 j2)) (* 413 (* h1 h1 h1 h1) h2 h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2)
) (* 28 (* h1 h1 h1 h1) h2 h3 (* h4 h4) h5 h6 (* j2 j2 j2)) (* 120 (* h1 h1 h1 
h1) h2 h3 (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1144 (* h1 h1 
h1 h1) h2 h3 (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2624 (* h1 h1 
h1 h1) h2 h3 (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2240 (* h1 h1 h1 
h1) h2 h3 (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 892 (* h1 h1 h1 h1) h2 
h3 (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 168 (* h1 h1 h1 h1) h2 h3 (* h4 h4
) (* h6 h6) (* j2 j2 j2 j2)) (* 12 (* h1 h1 h1 h1) h2 h3 (* h4 h4) (* h6 h6) (* 
j2 j2 j2)) (* 320 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 2144 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2
 j2 j2)) (* 6016 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 8840 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
7084 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 3048 (* h1 
h1 h1 h1) h2 h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 708 (* h1 h1 h1 h1) h2 h3
 h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 84 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5 h5) 
(* j2 j2 j2)) (* 4 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5 h5) (* j2 j2)) (* 2160 (* 
h1 h1 h1 h1) h2 h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 13432 
(* h1 h1 h1 h1) h2 h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 33960 
(* h1 h1 h1 h1) h2 h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 44652 (* 
h1 h1 h1 h1) h2 h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 33136 (* h1 h1 
h1 h1) h2 h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 14462 (* h1 h1 h1 h1) h2 
h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 3679 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5
) h6 (* j2 j2 j2 j2)) (* 501 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5) h6 (* j2 j2 j2))
 (* 28 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5) h6 (* j2 j2)) (* 1360 (* h1 h1 h1 h1) 
h2 h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 9032 (* h1 h1 h1 h1)
 h2 h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 25432 (* h1 h1 h1 h1) 
h2 h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 37876 (* h1 h1 h1 h1) h2 
h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 31378 (* h1 h1 h1 h1) h2 h3 h4 
h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 14880 (* h1 h1 h1 h1) h2 h3 h4 h5 (* h6 
h6) (* j2 j2 j2 j2 j2)) (* 4001 (* h1 h1 h1 h1) h2 h3 h4 h5 (* h6 h6) (* j2 j2 
j2 j2)) (* 563 (* h1 h1 h1 h1) h2 h3 h4 h5 (* h6 h6) (* j2 j2 j2)) (* 32 (* h1 
h1 h1 h1) h2 h3 h4 h5 (* h6 h6) (* j2 j2)) (* 160 (* h1 h1 h1 h1) h2 h3 h4 (* h6
 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1392 (* h1 h1 h1 h1) h2 h3 h4 (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4072 (* h1 h1 h1 h1) h2 h3 h4 (* h6 h6 h6
) (* j2 j2 j2 j2 j2 j2 j2)) (* 5200 (* h1 h1 h1 h1) h2 h3 h4 (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 3128 (* h1 h1 h1 h1) h2 h3 h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2
)) (* 948 (* h1 h1 h1 h1) h2 h3 h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 140 (* h1 h1
 h1 h1) h2 h3 h4 (* h6 h6 h6) (* j2 j2 j2)) (* 8 (* h1 h1 h1 h1) h2 h3 h4 (* h6 
h6 h6) (* j2 j2)) (* 1280 (* h1 h1 h1 h1) h2 h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 8256 (* h1 h1 h1 h1) h2 h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 21760 (* h1 h1 h1 h1) h2 h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 30112 (* h1 h1 h1 h1) h2 h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 23576 (* h1 h1 h1 h1) h2 h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 10712 (* h1 h1 h1 h1) h2 h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 2908 (* h1
 h1 h1 h1) h2 h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 480 (* h1 h1 h1 h1) h2 h3 
(* h5 h5 h5) h6 (* j2 j2 j2)) (* 46 (* h1 h1 h1 h1) h2 h3 (* h5 h5 h5) h6 (* j2 
j2)) (* 2 (* h1 h1 h1 h1) h2 h3 (* h5 h5 h5) h6 j2) (* 2080 (* h1 h1 h1 h1) h2 
h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 14336 (* h1 h1 h1 
h1) h2 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 41024 (* h1 h1 
h1 h1) h2 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 63068 (* h1 h1 
h1 h1) h2 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 56724 (* h1 h1 h1 
h1) h2 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 31008 (* h1 h1 h1 h1) h2
 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 10556 (* h1 h1 h1 h1) h2 h3 (* h5
 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 2186 (* h1 h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6
) (* j2 j2 j2)) (* 250 (* h1 h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6) (* j2 j2)) (* 
12 (* h1 h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6) j2) (* 960 (* h1 h1 h1 h1) h2 h3 h5
 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 6592 (* h1 h1 h1 h1) h2 h3 
h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 18880 (* h1 h1 h1 h1) h2 h3 
h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 29160 (* h1 h1 h1 h1) h2 h3 h5 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 26448 (* h1 h1 h1 h1) h2 h3 h5 (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 14644 (* h1 h1 h1 h1) h2 h3 h5 (* h6 h6 h6) (* 
j2 j2 j2 j2 j2)) (* 5076 (* h1 h1 h1 h1) h2 h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) 
(* 1070 (* h1 h1 h1 h1) h2 h3 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 124 (* h1 h1 h1 
h1) h2 h3 h5 (* h6 h6 h6) (* j2 j2)) (* 6 (* h1 h1 h1 h1) h2 h3 h5 (* h6 h6 h6) 
j2) (* 120 (* h1 h1 h1 h1) h2 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 804 (* h1 h1 h1 h1) h2 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2
 j2 j2)) (* 2056 (* h1 h1 h1 h1) h2 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 2550 (* h1 h1 h1 h1) h2 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2)) (* 1634 (* h1 h1 h1 h1) h2 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 550 (* h1 h1 h1 h1) h2 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 92 (* h1
 h1 h1 h1) h2 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 6 (* h1 h1 h1 h1) h2 
(* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 240 (* h1 h1 h1 h1) h2 (* h4 h4) h5 (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1028 (* h1 h1 h1 h1) h2 (* h4 h4) h5 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1696 (* h1 h1 h1 h1) h2 (* h4 h4) h5 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1285 (* h1 h1 h1 h1) h2 (* h4 h4) h5 (* 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 482 (* h1 h1 h1 h1) h2 (* h4 h4) h5 (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* 87 (* h1 h1 h1 h1) h2 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 
j2)) (* 6 (* h1 h1 h1 h1) h2 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 160 (* h1 
h1 h1 h1) h2 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1152 (* h1
 h1 h1 h1) h2 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3344 (* h1 
h1 h1 h1) h2 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 5044 (* h1 h1 h1
 h1) h2 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 4264 (* h1 h1 h1 h1) h2 
h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 2046 (* h1 h1 h1 h1) h2 h4 (* h5 h5
 h5) h6 (* j2 j2 j2 j2 j2)) (* 544 (* h1 h1 h1 h1) h2 h4 (* h5 h5 h5) h6 (* j2 
j2 j2 j2)) (* 74 (* h1 h1 h1 h1) h2 h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 4 (* h1 
h1 h1 h1) h2 h4 (* h5 h5 h5) h6 (* j2 j2)) (* 400 (* h1 h1 h1 h1) h2 h4 (* h5 h5
) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2560 (* h1 h1 h1 h1) h2 h4 (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 6856 (* h1 h1 h1 h1) h2 h4 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 9922 (* h1 h1 h1 h1) h2 h4 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 8290 (* h1 h1 h1 h1) h2 h4 (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3992 (* h1 h1 h1 h1) h2 h4 (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 1071 (* h1 h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2)) (* 147 (* h1 h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) 
(* 8 (* h1 h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 320 (* h1 h1 h1 h1)
 h2 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1584 (* h1 h1 h1 h1) 
h2 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3144 (* h1 h1 h1 h1) h2 h4
 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3168 (* h1 h1 h1 h1) h2 h4 h5 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1710 (* h1 h1 h1 h1) h2 h4 h5 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2)) (* 493 (* h1 h1 h1 h1) h2 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)
) (* 71 (* h1 h1 h1 h1) h2 h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 4 (* h1 h1 h1 h1)
 h2 h4 h5 (* h6 h6 h6) (* j2 j2)) (* 320 (* h1 h1 h1 h1) h2 (* h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2144 (* h1 h1 h1 h1) h2 (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 6096 (* h1 h1 h1 h1) h2 (* h5 h5 h5
) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 9576 (* h1 h1 h1 h1) h2 (* h5 h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 9068 (* h1 h1 h1 h1) h2 (* h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 5306 (* h1 h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* 1896 (* h1 h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2)) (* 396 (* h1 h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 44 (* 
h1 h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 2 (* h1 h1 h1 h1) h2 (* h5 
h5 h5) (* h6 h6) j2) (* 320 (* h1 h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 2144 (* h1 h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 6096 (* h1 h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 9576 (* h1 h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 9068 (* h1 h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 5306 (* h1 h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2)) (* 1896 (* h1 h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) 
(* 396 (* h1 h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 44 (* h1 h1 h1
 h1) h2 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 2 (* h1 h1 h1 h1) h2 (* h5 h5) (* 
h6 h6 h6) j2) (* 1200 (* h1 h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 5040 (* h1 h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 8800 (* h1 h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 8588 (* h1 h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* j2 
j2 j2 j2 j2 j2 j2)) (* 5204 (* h1 h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 
j2 j2 j2 j2)) (* 2020 (* h1 h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 
j2)) (* 492 (* h1 h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 68 (* 
h1 h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 4 (* h1 h1 h1 h1) (* h3 
h3 h3) (* h4 h4) h5 (* j2 j2)) (* 1200 (* h1 h1 h1 h1) (* h3 h3 h3) (* h4 h4) h6
 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4440 (* h1 h1 h1 h1) (* h3 h3 h3) (* h4 h4) 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6880 (* h1 h1 h1 h1) (* h3 h3 h3) (* h4 h4) 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 5808 (* h1 h1 h1 h1) (* h3 h3 h3) (* h4 h4) h6 
(* j2 j2 j2 j2 j2 j2)) (* 2880 (* h1 h1 h1 h1) (* h3 h3 h3) (* h4 h4) h6 (* j2 
j2 j2 j2 j2)) (* 832 (* h1 h1 h1 h1) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2)) 
(* 128 (* h1 h1 h1 h1) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2)) (* 8 (* h1 h1 h1 
h1) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2)) (* 1600 (* h1 h1 h1 h1) (* h3 h3 h3) h4
 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8320 (* h1 h1 h1 h1) (* h3 h3 
h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 17520 (* h1 h1 h1 h1) (* h3 
h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 19864 (* h1 h1 h1 h1) (* h3 
h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 13776 (* h1 h1 h1 h1) (* h3 h3 
h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 6228 (* h1 h1 h1 h1) (* h3 h3 h3) h4 
(* h5 h5) (* j2 j2 j2 j2 j2)) (* 1858 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) 
(* j2 j2 j2 j2)) (* 356 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2)) 
(* 40 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2)) (* 2 (* h1 h1 h1 h1) 
(* h3 h3 h3) h4 (* h5 h5) j2) (* 4000 (* h1 h1 h1 h1) (* h3 h3 h3) h4 h5 h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 23200 (* h1 h1 h1 h1) (* h3 h3 h3) h4 h5 h6 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 55280 (* h1 h1 h1 h1) (* h3 h3 h3) h4 h5 h6 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 70840 (* h1 h1 h1 h1) (* h3 h3 h3) h4 h5 h6 (* 
j2 j2 j2 j2 j2 j2 j2)) (* 54256 (* h1 h1 h1 h1) (* h3 h3 h3) h4 h5 h6 (* j2 j2 
j2 j2 j2 j2)) (* 26004 (* h1 h1 h1 h1) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2))
 (* 7896 (* h1 h1 h1 h1) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 1496 (* h1 h1
 h1 h1) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 164 (* h1 h1 h1 h1) (* h3 h3 h3) 
h4 h5 h6 (* j2 j2)) (* 8 (* h1 h1 h1 h1) (* h3 h3 h3) h4 h5 h6 j2) (* 1600 (* h1
 h1 h1 h1) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8320 (* 
h1 h1 h1 h1) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 17520 (* 
h1 h1 h1 h1) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 19664 (* h1 
h1 h1 h1) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 12936 (* h1 h1 h1 
h1) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 5128 (* h1 h1 h1 h1) (* h3 
h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 1200 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* 
h6 h6) (* j2 j2 j2)) (* 152 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2))
 (* 8 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h6 h6) j2) (* 3200 (* h1 h1 h1 h1) (* 
h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 19840 (* h1 h1 h1 
h1) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 50080 (* h1 h1 
h1 h1) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 66448 (* h1 h1 
h1 h1) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 50560 (* h1 h1 h1 
h1) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 23104 (* h1 h1 h1 h1) 
(* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 6516 (* h1 h1 h1 h1) (* h3 h3 
h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 1112 (* h1 h1 h1 h1) (* h3 h3 h3) (* h5 h5)
 h6 (* j2 j2 j2)) (* 104 (* h1 h1 h1 h1) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2)) 
(* 4 (* h1 h1 h1 h1) (* h3 h3 h3) (* h5 h5) h6 j2) (* 3200 (* h1 h1 h1 h1) (* h3
 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 21440 (* h1 h1 h1 h1)
 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 59200 (* h1 h1 h1 
h1) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 87328 (* h1 h1 h1 
h1) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 75024 (* h1 h1 h1 h1)
 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 38752 (* h1 h1 h1 h1) (* h3
 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 12040 (* h1 h1 h1 h1) (* h3 h3 h3) 
h5 (* h6 h6) (* j2 j2 j2 j2)) (* 2176 (* h1 h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6) 
(* j2 j2 j2)) (* 208 (* h1 h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2)) (* 8 
(* h1 h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6) j2) (* 360 (* h1 h1 h1 h1) (* h3 h3) 
(* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1272 (* h1 h1 h1 h1) (* h3
 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1800 (* h1 h1 h1 h1) (* 
h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1402 (* h1 h1 h1 h1) (* 
h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 658 (* h1 h1 h1 h1) (* h3 h3
) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 188 (* h1 h1 h1 h1) (* h3 h3) (* h4 
h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 30 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 
(* j2 j2 j2 j2)) (* 2 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2)) 
(* 360 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (* 1092 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 1344 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
868 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 308 (* 
h1 h1 h1 h1) (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 56 (* h1 h1 h1 h1)
 (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2)) (* 4 (* h1 h1 h1 h1) (* h3 h3) (* h4
 h4 h4) h6 (* j2 j2 j2)) (* 960 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4752 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) 
(* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 9352 (* h1 h1 h1 h1) (* h3 h3) (* 
h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 9688 (* h1 h1 h1 h1) (* h3 h3) 
(* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 5980 (* h1 h1 h1 h1) (* h3 h3) 
(* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2306 (* h1 h1 h1 h1) (* h3 h3) (* 
h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 546 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) 
(* h5 h5) (* j2 j2 j2 j2)) (* 72 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) 
(* j2 j2 j2)) (* 4 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 
1680 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 9696 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 22232 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 26632 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)
) (* 18742 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 
8006 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 2032 (* h1
 h1 h1 h1) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 280 (* h1 h1 h1 h1) (* 
h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 16 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) 
h5 h6 (* j2 j2)) (* 960 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 4392 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 7700 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 6832 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 3372 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h6 h6) (* 
j2 j2 j2 j2 j2)) (* 936 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 
j2 j2)) (* 136 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 8 
(* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2)) (* 640 (* h1 h1 h1 h1) 
(* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3648 (* h1 h1 h1
 h1) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8384 (* h1 h1 
h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 10176 (* h1 h1 
h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 7328 (* h1 h1 h1 
h1) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 3380 (* h1 h1 h1 h1) (* 
h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 1012 (* h1 h1 h1 h1) (* h3 h3) h4 
(* h5 h5 h5) (* j2 j2 j2 j2)) (* 192 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) 
(* j2 j2 j2)) (* 21 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2)) (* (* 
h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) j2) (* 3200 (* h1 h1 h1 h1) (* h3 h3) h4 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 20720 (* h1 h1 h1 h1) (* h3 
h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 54776 (* h1 h1 h1 h1) (* 
h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 76472 (* h1 h1 h1 h1) (* 
h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 61704 (* h1 h1 h1 h1) (* h3 
h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 30238 (* h1 h1 h1 h1) (* h3 h3) h4
 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 9270 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5)
 h6 (* j2 j2 j2 j2)) (* 1762 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 
j2)) (* 191 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 9 (* h1 h1 
h1 h1) (* h3 h3) h4 (* h5 h5) h6 j2) (* 2560 (* h1 h1 h1 h1) (* h3 h3) h4 h5 (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 17712 (* h1 h1 h1 h1) (* h3 h3) h4 
h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 49920 (* h1 h1 h1 h1) (* h3 h3) 
h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 74936 (* h1 h1 h1 h1) (* h3 h3) 
h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 66528 (* h1 h1 h1 h1) (* h3 h3) h4 
h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 37000 (* h1 h1 h1 h1) (* h3 h3) h4 h5 (* 
h6 h6) (* j2 j2 j2 j2 j2)) (* 13004 (* h1 h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6) 
(* j2 j2 j2 j2)) (* 2778 (* h1 h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2))
 (* 326 (* h1 h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 16 (* h1 h1 h1 
h1) (* h3 h3) h4 h5 (* h6 h6) j2) (* 640 (* h1 h1 h1 h1) (* h3 h3) h4 (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3648 (* h1 h1 h1 h1) (* h3 h3) h4 (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 8384 (* h1 h1 h1 h1) (* h3 h3) h4 (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 10096 (* h1 h1 h1 h1) (* h3 h3) h4 (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 6952 (* h1 h1 h1 h1) (* h3 h3) h4 (* h6 h6 h6) (* 
j2 j2 j2 j2 j2)) (* 2808 (* h1 h1 h1 h1) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 
j2)) (* 652 (* h1 h1 h1 h1) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2)) (* 80 (* h1 
h1 h1 h1) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2)) (* 4 (* h1 h1 h1 h1) (* h3 h3) h4
 (* h6 h6 h6) j2) (* 1280 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 8576 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 23424 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 33472 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2)) (* 26944 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2)) (* 12584 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2)) (* 3552 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 
596 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 54 (* h1 h1 h1 h1
) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2)) (* 2 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5 
h5) h6 j2) (* 2560 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 18272 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2 j2)) (* 54512 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 88032 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 83328 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 46892 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 15328 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5) (* h6
 h6) (* j2 j2 j2 j2)) (* 2812 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6) (* 
j2 j2 j2)) (* 266 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 10
 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6) j2) (* 1280 (* h1 h1 h1 h1) (* h3
 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 9216 (* h1 h1 h1 h1) 
(* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 27392 (* h1 h1 h1 
h1) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 43360 (* h1 h1 h1 
h1) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 39488 (* h1 h1 h1 h1)
 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 21088 (* h1 h1 h1 h1) (* h3
 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 6584 (* h1 h1 h1 h1) (* h3 h3) h5 
(* h6 h6 h6) (* j2 j2 j2 j2)) (* 1168 (* h1 h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6) 
(* j2 j2 j2)) (* 108 (* h1 h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 4 
(* h1 h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6) j2) (* 120 (* h1 h1 h1 h1) h3 (* h4 h4
 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 544 (* h1 h1 h1 h1) h3 (* 
h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 924 (* h1 h1 h1 h1) h3 
(* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 774 (* h1 h1 h1 h1) h3 
(* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 372 (* h1 h1 h1 h1) h3 (* h4
 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 105 (* h1 h1 h1 h1) h3 (* h4 h4 h4) 
(* h5 h5) (* j2 j2 j2 j2 j2)) (* 16 (* h1 h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) 
(* j2 j2 j2 j2)) (* (* h1 h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 
480 (* h1 h1 h1 h1) h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
1636 (* h1 h1 h1 h1) h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2058 
(* h1 h1 h1 h1) h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1305 (* h1 h1
 h1 h1) h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 441 (* h1 h1 h1 h1) h3 
(* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 75 (* h1 h1 h1 h1) h3 (* h4 h4 h4) h5 
h6 (* j2 j2 j2 j2)) (* 5 (* h1 h1 h1 h1) h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 
180 (* h1 h1 h1 h1) h3 (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
426 (* h1 h1 h1 h1) h3 (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 368 
(* h1 h1 h1 h1) h3 (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 148 (* h1 h1
 h1 h1) h3 (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 28 (* h1 h1 h1 h1) h3 
(* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 2 (* h1 h1 h1 h1) h3 (* h4 h4 h4) (* 
h6 h6) (* j2 j2 j2)) (* 160 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 912 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* j2
 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2056 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 2376 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 1560 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* j2 
j2 j2 j2 j2 j2)) (* 622 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2
 j2)) (* 148 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 19 
(* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* (* h1 h1 h1 h1) h3 
(* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 640 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4128 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5
 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 10620 (* h1 h1 h1 h1) h3 (* h4 h4) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 14024 (* h1 h1 h1 h1) h3 (* h4 h4) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 10352 (* h1 h1 h1 h1) h3 (* h4 h4) (* 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 4473 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5) 
h6 (* j2 j2 j2 j2 j2)) (* 1117 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5) h6 (* j2 
j2 j2 j2)) (* 148 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 8 
(* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 1480 (* h1 h1 h1 h1) h3 
(* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 6756 (* h1 h1 h1 h1) 
h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 11712 (* h1 h1 h1 h1) 
h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 9934 (* h1 h1 h1 h1) h3 
(* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4630 (* h1 h1 h1 h1) h3 (* h4 
h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1207 (* h1 h1 h1 h1) h3 (* h4 h4) h5 (* 
h6 h6) (* j2 j2 j2 j2)) (* 164 (* h1 h1 h1 h1) h3 (* h4 h4) h5 (* h6 h6) (* j2 
j2 j2)) (* 9 (* h1 h1 h1 h1) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 240 (* h1 
h1 h1 h1) h3 (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 848 (* h1 h1
 h1 h1) h3 (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1120 (* h1 h1 h1 
h1) h3 (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 702 (* h1 h1 h1 h1) h3 
(* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 222 (* h1 h1 h1 h1) h3 (* h4 h4) 
(* h6 h6 h6) (* j2 j2 j2 j2)) (* 34 (* h1 h1 h1 h1) h3 (* h4 h4) (* h6 h6 h6) 
(* j2 j2 j2)) (* 2 (* h1 h1 h1 h1) h3 (* h4 h4) (* h6 h6 h6) (* j2 j2)) (* 640 
(* h1 h1 h1 h1) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4448
 (* h1 h1 h1 h1) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 12704 
(* h1 h1 h1 h1) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 19088 (* 
h1 h1 h1 h1) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 16204 (* h1 h1 
h1 h1) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 7992 (* h1 h1 h1 h1) h3 
h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 2394 (* h1 h1 h1 h1) h3 h4 (* h5 h5 h5
) h6 (* j2 j2 j2 j2)) (* 437 (* h1 h1 h1 h1) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2))
 (* 45 (* h1 h1 h1 h1) h3 h4 (* h5 h5 h5) h6 (* j2 j2)) (* 2 (* h1 h1 h1 h1) h3 
h4 (* h5 h5 h5) h6 j2) (* 1120 (* h1 h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8064 (* h1 h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 23968 (* h1 h1 h1 h1) h3 h4 (* h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 38220 (* h1 h1 h1 h1) h3 h4 (* h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 35828 (* h1 h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6)
 (* j2 j2 j2 j2 j2 j2)) (* 20536 (* h1 h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6) (* j2
 j2 j2 j2 j2)) (* 7234 (* h1 h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)
) (* 1513 (* h1 h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 171 (* h1 
h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 8 (* h1 h1 h1 h1) h3 h4 (* h5 
h5) (* h6 h6) j2) (* 1120 (* h1 h1 h1 h1) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 6224 (* h1 h1 h1 h1) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 13800 (* h1 h1 h1 h1) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 15640 (* h1 h1 h1 h1) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
9844 (* h1 h1 h1 h1) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 3604 (* h1 h1 
h1 h1) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 762 (* h1 h1 h1 h1) h3 h4 h5 
(* h6 h6 h6) (* j2 j2 j2)) (* 86 (* h1 h1 h1 h1) h3 h4 h5 (* h6 h6 h6) (* j2 j2)
) (* 4 (* h1 h1 h1 h1) h3 h4 h5 (* h6 h6 h6) j2) (* 640 (* h1 h1 h1 h1) h3 (* h5
 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4608 (* h1 h1 h1 h1) h3 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 13856 (* h1 h1 h1 h1) 
h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 22432 (* h1 h1 h1 h1) 
h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 21048 (* h1 h1 h1 h1) h3 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 11536 (* h1 h1 h1 h1) h3 (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 3604 (* h1 h1 h1 h1) h3 (* h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2)) (* 626 (* h1 h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6) (* j2 
j2 j2)) (* 56 (* h1 h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 2 (* h1 h1
 h1 h1) h3 (* h5 h5 h5) (* h6 h6) j2) (* 640 (* h1 h1 h1 h1) h3 (* h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4608 (* h1 h1 h1 h1) h3 (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 13856 (* h1 h1 h1 h1) h3 (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 22432 (* h1 h1 h1 h1) h3 (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 21048 (* h1 h1 h1 h1) h3 (* h5 h5)
 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 11536 (* h1 h1 h1 h1) h3 (* h5 h5) (* h6
 h6 h6) (* j2 j2 j2 j2 j2)) (* 3604 (* h1 h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2)) (* 626 (* h1 h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) 
(* 56 (* h1 h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 2 (* h1 h1 h1 h1) 
h3 (* h5 h5) (* h6 h6 h6) j2) (* 60 (* h1 h1 h1 h1) (* h4 h4 h4) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 272 (* h1 h1 h1 h1) (* h4 h4 h4) (* h5 h5) h6
 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 432 (* h1 h1 h1 h1) (* h4 h4 h4) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 296 (* h1 h1 h1 h1) (* h4 h4 h4) (* h5 h5) h6 (* j2
 j2 j2 j2 j2 j2)) (* 99 (* h1 h1 h1 h1) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2
 j2)) (* 16 (* h1 h1 h1 h1) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* (* h1 
h1 h1 h1) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 90 (* h1 h1 h1 h1) (* h4 h4
 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 258 (* h1 h1 h1 h1) (* h4 h4 
h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 223 (* h1 h1 h1 h1) (* h4 h4 h4) 
h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 85 (* h1 h1 h1 h1) (* h4 h4 h4) h5 (* h6 
h6) (* j2 j2 j2 j2 j2)) (* 15 (* h1 h1 h1 h1) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2
 j2 j2)) (* (* h1 h1 h1 h1) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 80 (* h1 
h1 h1 h1) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 456 (* h1
 h1 h1 h1) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 988 (* h1 
h1 h1 h1) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1020 (* h1 h1 
h1 h1) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 528 (* h1 h1 h1 h1) 
(* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 142 (* h1 h1 h1 h1) (* h4 h4) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 19 (* h1 h1 h1 h1) (* h4 h4) (* h5 h5 h5) h6
 (* j2 j2 j2)) (* (* h1 h1 h1 h1) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 200 
(* h1 h1 h1 h1) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 1080 (* h1 h1 h1 h1) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 2198 (* h1 h1 h1 h1) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2
)) (* 2138 (* h1 h1 h1 h1) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 1073 (* h1 h1 h1 h1) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 285
 (* h1 h1 h1 h1) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 38 (* h1 h1 
h1 h1) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 2 (* h1 h1 h1 h1) (* h4 h4
) (* h5 h5) (* h6 h6) (* j2 j2)) (* 120 (* h1 h1 h1 h1) (* h4 h4) h5 (* h6 h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 484 (* h1 h1 h1 h1) (* h4 h4) h5 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 682 (* h1 h1 h1 h1) (* h4 h4) h5 (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2)) (* 418 (* h1 h1 h1 h1) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 
j2 j2)) (* 125 (* h1 h1 h1 h1) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 18 
(* h1 h1 h1 h1) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2)) (* (* h1 h1 h1 h1) (* h4
 h4) h5 (* h6 h6 h6) (* j2 j2)) (* 160 (* h1 h1 h1 h1) h4 (* h5 h5 h5) (* h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 992 (* h1 h1 h1 h1) h4 (* h5 h5 h5) (* h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2472 (* h1 h1 h1 h1) h4 (* h5 h5 h5) (* h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2)) (* 3176 (* h1 h1 h1 h1) h4 (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 2254 (* h1 h1 h1 h1) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2)) (* 892 (* h1 h1 h1 h1) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 
195 (* h1 h1 h1 h1) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 22 (* h1 h1 h1 h1
) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* (* h1 h1 h1 h1) h4 (* h5 h5 h5) (* h6 
h6) j2) (* 160 (* h1 h1 h1 h1) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2
 j2 j2)) (* 992 (* h1 h1 h1 h1) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 2472 (* h1 h1 h1 h1) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 3176 (* h1 h1 h1 h1) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 2254 (* h1 h1 h1 h1) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 892 (* 
h1 h1 h1 h1) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 195 (* h1 h1 h1 h1) 
h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 22 (* h1 h1 h1 h1) h4 (* h5 h5) (* h6
 h6 h6) (* j2 j2)) (* (* h1 h1 h1 h1) h4 (* h5 h5) (* h6 h6 h6) j2) (* 1536 (* 
h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4224 (* 
h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 3904 (* h1 
h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2 j2 j2)) (* 1568 (* h1 h1 h1) 
(* h2 h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2 j2)) (* 272 (* h1 h1 h1) (* h2 h2 h2
 h2) (* h3 h3) h5 (* j2 j2 j2 j2)) (* 16 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) 
h5 (* j2 j2 j2)) (* 1024 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h6 (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 3584 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h6 (* j2 j2 j2 
j2 j2 j2 j2)) (* 3904 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h6 (* j2 j2 j2 j2 
j2 j2)) (* 1856 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h6 (* j2 j2 j2 j2 j2)) 
(* 400 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h6 (* j2 j2 j2 j2)) (* 32 (* h1 h1
 h1) (* h2 h2 h2 h2) (* h3 h3) h6 (* j2 j2 j2)) (* 384 (* h1 h1 h1) (* h2 h2 h2 
h2) h3 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1536 (* h1 h1 h1) (* h2 h2 
h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2368 (* h1 h1 h1) (* h2 h2 
h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1792 (* h1 h1 h1) (* h2 h2 h2 
h2) h3 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 696 (* h1 h1 h1) (* h2 h2 h2 h2) h3 
(* h5 h5) (* j2 j2 j2 j2 j2)) (* 128 (* h1 h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) 
(* j2 j2 j2 j2)) (* 8 (* h1 h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) (* j2 j2 j2)) 
(* 704 (* h1 h1 h1) (* h2 h2 h2 h2) h3 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
2944 (* h1 h1 h1) (* h2 h2 h2 h2) h3 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4800 
(* h1 h1 h1) (* h2 h2 h2 h2) h3 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 3920 (* h1 h1
 h1) (* h2 h2 h2 h2) h3 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 1700 (* h1 h1 h1) (* h2 
h2 h2 h2) h3 h5 h6 (* j2 j2 j2 j2 j2)) (* 372 (* h1 h1 h1) (* h2 h2 h2 h2) h3 h5
 h6 (* j2 j2 j2 j2)) (* 32 (* h1 h1 h1) (* h2 h2 h2 h2) h3 h5 h6 (* j2 j2 j2)) 
(* 128 (* h1 h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (* 736 (* h1 h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 1552 (* h1 h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
1512 (* h1 h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 740 (* 
h1 h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 176 (* h1 h1 h1) 
(* h2 h2 h2 h2) h3 (* h6 h6) (* j2 j2 j2 j2)) (* 16 (* h1 h1 h1) (* h2 h2 h2 h2)
 h3 (* h6 h6) (* j2 j2 j2)) (* 128 (* h1 h1 h1) (* h2 h2 h2 h2) (* h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 640 (* h1 h1 h1) (* h2 h2 h2 h2) (* h5 h5) h6
 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1344 (* h1 h1 h1) (* h2 h2 h2 h2) (* h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1536 (* h1 h1 h1) (* h2 h2 h2 h2) (* h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1032 (* h1 h1 h1) (* h2 h2 h2 h2) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 408 (* h1 h1 h1) (* h2 h2 h2 h2) (* h5 h5) h6 (* j2 j2
 j2 j2 j2)) (* 88 (* h1 h1 h1) (* h2 h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 
8 (* h1 h1 h1) (* h2 h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2)) (* 64 (* h1 h1 h1) (* 
h2 h2 h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 384 (* h1 h1 h1)
 (* h2 h2 h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 928 (* h1 h1 h1
) (* h2 h2 h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1184 (* h1 h1 h1)
 (* h2 h2 h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 868 (* h1 h1 h1) (* 
h2 h2 h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 368 (* h1 h1 h1) (* h2 h2 h2
 h2) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 84 (* h1 h1 h1) (* h2 h2 h2 h2) h5 (* 
h6 h6) (* j2 j2 j2 j2)) (* 8 (* h1 h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6) (* j2 j2 
j2)) (* 5376 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 22080 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2 j2 j2 j2)
) (* 31232 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2 j2 j2)) (* 
18608 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2 j2)) (* 5200 (* 
h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2)) (* 672 (* h1 h1 h1) (* 
h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2)) (* 32 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3
 h3) h5 (* j2 j2)) (* 3584 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 17408 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2
 j2 j2 j2 j2)) (* 29024 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2 j2
 j2 j2)) (* 20176 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2 j2 j2)) 
(* 6688 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2 j2)) (* 1056 (* h1
 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2)) (* 64 (* h1 h1 h1) (* h2 h2 
h2) (* h3 h3 h3) h6 (* j2 j2)) (* 1088 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5
 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 11360 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4
 h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 23600 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4
 h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 17544 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5
 (* j2 j2 j2 j2 j2 j2)) (* 5760 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 (* j2 
j2 j2 j2 j2)) (* 864 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2)) 
(* 48 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2)) (* 384 (* h1 h1 h1
) (* h2 h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 5984 (* h1 h1 
h1) (* h2 h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 18784 (* h1 h1 
h1) (* h2 h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 17704 (* h1 h1 h1)
 (* h2 h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2)) (* 7184 (* h1 h1 h1) (* h2 
h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 1344 (* h1 h1 h1) (* h2 h2 h2) (* 
h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 96 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h6 
(* j2 j2 j2)) (* 2112 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 12672 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 27904 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 29424 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5)
 (* j2 j2 j2 j2 j2 j2)) (* 16124 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) 
(* j2 j2 j2 j2 j2)) (* 4604 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) (* j2 
j2 j2 j2)) (* 632 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2)) 
(* 32 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) (* j2 j2)) (* 4128 (* h1 h1 
h1) (* h2 h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 27152 (* h1 
h1 h1) (* h2 h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 60824 (* h1 
h1 h1) (* h2 h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 63068 (* h1 h1 
h1) (* h2 h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 34424 (* h1 h1 h1) 
(* h2 h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 10216 (* h1 h1 h1) (* h2 h2 
h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 1560 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3)
 h5 h6 (* j2 j2 j2)) (* 96 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 h6 (* j2 j2)) 
(* 960 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 8688 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 24656 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2)) (* 30148 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 18608 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2
)) (* 6064 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 992
 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2)) (* 64 (* h1 h1 h1) 
(* h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2)) (* 128 (* h1 h1 h1) (* h2 h2 h2) h3 
h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2688 (* h1 h1 h1) (* h2 h2 h2
) h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 9024 (* h1 h1 h1) (* h2 h2 
h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 12288 (* h1 h1 h1) (* h2 h2 
h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 8104 (* h1 h1 h1) (* h2 h2 h2) 
h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2680 (* h1 h1 h1) (* h2 h2 h2) h3 h4 
(* h5 h5) (* j2 j2 j2 j2 j2)) (* 416 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) 
(* j2 j2 j2 j2)) (* 24 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2)) 
(* 256 (* h1 h1 h1) (* h2 h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 3920 (* h1 h1 h1) (* h2 h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 14984 (* h1 h1 h1) (* h2 h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
23612 (* h1 h1 h1) (* h2 h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 18094 
(* h1 h1 h1) (* h2 h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 7116 (* h1 h1 h1
) (* h2 h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 1376 (* h1 h1 h1) (* h2 h2 h2)
 h3 h4 h5 h6 (* j2 j2 j2 j2)) (* 104 (* h1 h1 h1) (* h2 h2 h2) h3 h4 h5 h6 (* j2
 j2 j2)) (* 384 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 2896 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 6880 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 6564 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2))
 (* 2924 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 608 
(* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2 j2)) (* 48 (* h1 h1 h1) 
(* h2 h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2)) (* 864 (* h1 h1 h1) (* h2 h2 h2) h3 
(* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4176 (* h1 h1 h1) (* h2 h2 h2) 
h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 8040 (* h1 h1 h1) (* h2 h2 h2) 
h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 7884 (* h1 h1 h1) (* h2 h2 h2) h3 
(* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 4184 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 
h5 h5) (* j2 j2 j2 j2 j2)) (* 1180 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) (* 
j2 j2 j2 j2)) (* 160 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2)) (* 
8 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) (* j2 j2)) (* 960 (* h1 h1 h1) (* h2
 h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 7536 (* h1 h1 h1) 
(* h2 h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 22760 (* h1 h1 
h1) (* h2 h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 35340 (* h1 h1 
h1) (* h2 h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 31194 (* h1 h1 h1)
 (* h2 h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 16134 (* h1 h1 h1) (* h2
 h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 4796 (* h1 h1 h1) (* h2 h2 h2) h3
 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 752 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) h6 
(* j2 j2 j2)) (* 48 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) h6 (* j2 j2)) (* 608 
(* h1 h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
5664 (* h1 h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 18744 (* h1 h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 31248 (* h1 h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
29424 (* h1 h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 16168 
(* h1 h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 5086 (* h1 h1 
h1) (* h2 h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 840 (* h1 h1 h1) (* h2 h2 
h2) h3 h5 (* h6 h6) (* j2 j2 j2)) (* 56 (* h1 h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6
) (* j2 j2)) (* 320 (* h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 2064 (* h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 5120 (* h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 6244 (* h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 4040 (* h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
1396 (* h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 240 (* h1 h1 
h1) (* h2 h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2)) (* 16 (* h1 h1 h1) (* h2 h2 h2) 
h3 (* h6 h6 h6) (* j2 j2)) (* 544 (* h1 h1 h1) (* h2 h2 h2) h4 (* h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2832 (* h1 h1 h1) (* h2 h2 h2) h4 (* h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 6056 (* h1 h1 h1) (* h2 h2 h2) h4 (* h5 h5
) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6860 (* h1 h1 h1) (* h2 h2 h2) h4 (* h5 h5)
 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 4428 (* h1 h1 h1) (* h2 h2 h2) h4 (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 1624 (* h1 h1 h1) (* h2 h2 h2) h4 (* h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* 312 (* h1 h1 h1) (* h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) 
(* 24 (* h1 h1 h1) (* h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 160 (* h1 h1 h1
) (* h2 h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1280 (* h1 
h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3568 (* 
h1 h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4848 (* 
h1 h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3562 (* h1 
h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1436 (* h1 h1 h1) 
(* h2 h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 296 (* h1 h1 h1) (* h2 h2 h2
) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 24 (* h1 h1 h1) (* h2 h2 h2) h4 h5 (* h6 
h6) (* j2 j2 j2)) (* 288 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 1680 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 4168 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 5724 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2)) (* 4740 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2)) (* 2412 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2)) (* 732 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 120
 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 8 (* h1 h1 h1) (* h2
 h2 h2) (* h5 h5 h5) h6 (* j2 j2)) (* 432 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2664 (* h1 h1 h1) (* h2 h2 h2) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 6948 (* h1 h1 h1) (* h2 
h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 9974 (* h1 h1 h1) (* 
h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 8584 (* h1 h1 h1) (* 
h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4514 (* h1 h1 h1) (* h2 
h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1408 (* h1 h1 h1) (* h2 h2 h2)
 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 236 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5)
 (* h6 h6) (* j2 j2 j2)) (* 16 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6) (* 
j2 j2)) (* 160 (* h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2
 j2 j2 j2)) (* 1072 (* h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 2968 (* h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 4452 (* h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 3960 (* h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 2136 (* h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
680 (* h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 116 (* h1 h1 
h1) (* h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 8 (* h1 h1 h1) (* h2 h2 h2) h5
 (* h6 h6 h6) (* j2 j2)) (* 3840 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 14400 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 (* j2
 j2 j2 j2 j2 j2 j2)) (* 20128 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2
 j2 j2 j2 j2)) (* 13152 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2 j2 j2
 j2)) (* 4160 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2 j2 j2)) (* 608 
(* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2 j2)) (* 32 (* h1 h1 h1) (* h2
 h2) (* h3 h3 h3 h3) h5 (* j2 j2)) (* 2560 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3
) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 11520 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3
) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 18592 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) 
h6 (* j2 j2 j2 j2 j2 j2)) (* 13952 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h6 (* 
j2 j2 j2 j2 j2)) (* 5184 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2 j2 
j2)) (* 928 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2 j2)) (* 64 (* h1 
h1 h1) (* h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2)) (* 3808 (* h1 h1 h1) (* h2 h2) 
(* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 31488 (* h1 h1 h1) (* h2 
h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 72104 (* h1 h1 h1) (* h2 
h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 69104 (* h1 h1 h1) (* h2 h2)
 (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 32224 (* h1 h1 h1) (* h2 h2) (* h3
 h3 h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 7888 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4
 h5 (* j2 j2 j2 j2)) (* 976 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 
j2)) (* 48 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2)) (* 1344 (* h1 h1
 h1) (* h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 15088 (* h1
 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 51048 (* h1
 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 63712 (* h1 h1
 h1) (* h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2)) (* 36776 (* h1 h1 h1) 
(* h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 10912 (* h1 h1 h1) (* h2 h2)
 (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 1624 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3)
 h4 h6 (* j2 j2 j2)) (* 96 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2)) 
(* 3648 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2
 j2)) (* 25104 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 64064 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2
 j2 j2 j2)) (* 78836 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 
j2 j2 j2)) (* 50968 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2
 j2)) (* 18120 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2)) 
(* 3464 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2)) (* 328 (* h1
 h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2)) (* 12 (* h1 h1 h1) (* h2 h2)
 (* h3 h3 h3) (* h5 h5) j2) (* 7584 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 h6 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 55264 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 141328 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5
 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 170060 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 
h6 (* j2 j2 j2 j2 j2 j2)) (* 106340 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 h6 
(* j2 j2 j2 j2 j2)) (* 36692 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 
j2 j2)) (* 6972 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2)) (* 668 
(* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2)) (* 24 (* h1 h1 h1) (* h2 h2
) (* h3 h3 h3) h5 h6 j2) (* 2112 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 19376 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 61000 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 89432 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3
) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 69464 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 30224 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h6
 h6) (* j2 j2 j2 j2)) (* 7368 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6) (* 
j2 j2 j2)) (* 936 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2)) (* 48
 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6) j2) (* 192 (* h1 h1 h1) (* h2 h2)
 (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4848 (* h1 h1 h1) 
(* h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 17296 (* h1 
h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 23340 
(* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 14140
 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 4276 
(* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 628 (* h1 
h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 36 (* h1 h1 h1) (* 
h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 1152 (* h1 h1 h1) (* h2 h2) (* h3
 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8688 (* h1 h1 h1) (* h2 h2)
 (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 18712 (* h1 h1 h1) (* h2
 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 15140 (* h1 h1 h1) (* 
h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 5744 (* h1 h1 h1) (* h2 
h2) (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 1036 (* h1 h1 h1) (* h2 h2) 
(* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2)) (* 72 (* h1 h1 h1) (* h2 h2) (* h3 h3) 
(* h4 h4) h6 (* j2 j2 j2)) (* 704 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 12304 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 
(* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 47016 (* h1 h1 h1) (* h2 h2) (* h3 
h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 77388 (* h1 h1 h1) (* h2 h2) 
(* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 65370 (* h1 h1 h1) (* h2 h2)
 (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 30276 (* h1 h1 h1) (* h2 h2) 
(* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 7552 (* h1 h1 h1) (* h2 h2) (* h3 
h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 952 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* 
h5 h5) (* j2 j2 j2)) (* 48 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 
j2)) (* 1536 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 23304 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 95760 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 167622 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2
 j2 j2 j2)) (* 147008 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 
j2 j2)) (* 71560 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) 
(* 19640 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 2840 (* 
h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 168 (* h1 h1 h1) (* h2 
h2) (* h3 h3) h4 h5 h6 (* j2 j2)) (* 3040 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 23344 (* h1 h1 h1) (* h2 h2) (* h3 
h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 59072 (* h1 h1 h1) (* h2 h2) 
(* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 64532 (* h1 h1 h1) (* h2 h2)
 (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 35812 (* h1 h1 h1) (* h2 h2) 
(* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 10584 (* h1 h1 h1) (* h2 h2) (* h3
 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 1592 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 
(* h6 h6) (* j2 j2 j2)) (* 96 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6) (* 
j2 j2)) (* 2688 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 15072 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 34192 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 
j2 j2 j2 j2 j2 j2)) (* 40264 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) (* j2
 j2 j2 j2 j2 j2)) (* 26228 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 
j2 j2 j2 j2)) (* 9368 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 
j2)) (* 1776 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2)) (* 166 
(* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2)) (* 6 (* h1 h1 h1) (* h2
 h2) (* h3 h3) (* h5 h5 h5) j2) (* 2624 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 25232 (* h1 h1 h1) (* h2 h2) (* h3 
h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 89760 (* h1 h1 h1) (* h2 h2)
 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 161516 (* h1 h1 h1) (* 
h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 165016 (* h1 h1 h1) 
(* h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 100226 (* h1 h1 h1) 
(* h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 36014 (* h1 h1 h1) (* h2
 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 7322 (* h1 h1 h1) (* h2 h2) (* 
h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 758 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 
h5) h6 (* j2 j2)) (* 30 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) h6 j2) (* 
2016 (* h1 h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2
 j2)) (* 22552 (* h1 h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 87904 (* h1 h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 169482 (* h1 h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 184046 (* h1 h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 119950 (* h1 h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6) (* 
j2 j2 j2 j2 j2)) (* 47592 (* h1 h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2
 j2 j2)) (* 11138 (* h1 h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2)) 
(* 1398 (* h1 h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2)) (* 72 (* h1 h1 
h1) (* h2 h2) (* h3 h3) h5 (* h6 h6) j2) (* 1600 (* h1 h1 h1) (* h2 h2) (* h3 h3
) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 11600 (* h1 h1 h1) (* h2 h2) 
(* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 32608 (* h1 h1 h1) (* h2 
h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 45980 (* h1 h1 h1) (* h2
 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 35632 (* h1 h1 h1) (* h2 
h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 15588 (* h1 h1 h1) (* h2 h2) 
(* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 3792 (* h1 h1 h1) (* h2 h2) (* h3 h3)
 (* h6 h6 h6) (* j2 j2 j2)) (* 476 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6)
 (* j2 j2)) (* 24 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6) j2) (* 544 (* h1
 h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
3920 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2
)) (* 10056 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 11964 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2
 j2 j2)) (* 7068 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2
 j2)) (* 2124 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) 
(* 312 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 18 (* 
h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 640 (* h1 h1 h1) (* 
h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4748 (* h1 h1 h1
) (* h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 15460 (* h1 h1
 h1) (* h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 23601 (* h1 h1
 h1) (* h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 17375 (* h1 h1 h1
) (* h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 6473 (* h1 h1 h1) (* h2
 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 1183 (* h1 h1 h1) (* h2 h2) h3 
(* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 84 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) h5 h6
 (* j2 j2 j2)) (* 208 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 2212 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 6058 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 5758 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 2452 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 
j2 j2 j2 j2)) (* 484 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 j2 j2 
j2)) (* 36 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 288 
(* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
3408 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 12232 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 20284 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
17532 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 8108 
(* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 1984 (* h1 h1 
h1) (* h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 244 (* h1 h1 h1) (* h2 h2) 
h3 h4 (* h5 h5 h5) (* j2 j2 j2)) (* 12 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5)
 (* j2 j2)) (* 3376 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 22760 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 62764 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 90730 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2)) (* 74464 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 
j2 j2 j2)) (* 35622 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)
) (* 9774 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 1419 (* 
h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2)) (* 84 (* h1 h1 h1) (* h2 h2
) h3 h4 (* h5 h5) h6 (* j2 j2)) (* 1760 (* h1 h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 13988 (* h1 h1 h1) (* h2 h2) h3 h4 h5 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 44852 (* h1 h1 h1) (* h2 h2) h3 h4 
h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 74271 (* h1 h1 h1) (* h2 h2) h3 h4 
h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 68165 (* h1 h1 h1) (* h2 h2) h3 h4 h5 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 35564 (* h1 h1 h1) (* h2 h2) h3 h4 h5 (* h6 
h6) (* j2 j2 j2 j2 j2)) (* 10401 (* h1 h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6) (* j2
 j2 j2 j2)) (* 1577 (* h1 h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2)) (* 
96 (* h1 h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2)) (* 272 (* h1 h1 h1) (* 
h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2756 (* h1 h1 h1) 
(* h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 8702 (* h1 h1 h1) 
(* h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 11784 (* h1 h1 h1) (* 
h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 7588 (* h1 h1 h1) (* h2 h2) 
h3 h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2452 (* h1 h1 h1) (* h2 h2) h3 h4 (* 
h6 h6 h6) (* j2 j2 j2 j2)) (* 388 (* h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6 h6) (* 
j2 j2 j2)) (* 24 (* h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2)) (* 192 (* 
h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1056 
(* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2336 
(* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 2648 (* 
h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1620 (* h1 h1 
h1) (* h2 h2) h3 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 516 (* h1 h1 h1) (* h2 
h2) h3 (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 76 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5
 h5 h5) (* j2 j2 j2)) (* 4 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) (* j2 j2)) 
(* 1472 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 10544 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 31488 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 50764 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2)) (* 48000 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 27220 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 9142 
(* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 1732 (* h1 h1 h1) 
(* h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 166 (* h1 h1 h1) (* h2 h2) h3 (* 
h5 h5 h5) h6 (* j2 j2)) (* 6 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) h6 j2) (* 
2608 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2
 j2)) (* 18808 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 57612 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 97322 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 98864 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6) (* j2
 j2 j2 j2 j2 j2)) (* 62161 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2)) (* 24122 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2
 j2)) (* 5571 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 696
 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2)) (* 36 (* h1 h1 h1) (* 
h2 h2) h3 (* h5 h5) (* h6 h6) j2) (* 1120 (* h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8464 (* h1 h1 h1) (* h2 h2) h3 h5 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 26812 (* h1 h1 h1) (* h2 h2) h3 h5 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 46530 (* h1 h1 h1) (* h2 h2) h3 h5 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 48364 (* h1 h1 h1) (* h2 h2) h3 h5 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 30995 (* h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6 
h6) (* j2 j2 j2 j2 j2)) (* 12188 (* h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6) (* j2
 j2 j2 j2)) (* 2829 (* h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 
352 (* h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2)) (* 18 (* h1 h1 h1) (* 
h2 h2) h3 h5 (* h6 h6 h6) j2) (* 64 (* h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 464 (* h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1328 (* h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 1912 (* h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 1466 (* h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6 h6) (* j2 j2 
j2 j2 j2)) (* 586 (* h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 
112 (* h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 8 (* h1 h1 h1) 
(* h2 h2) h3 (* h6 h6 h6 h6) (* j2 j2)) (* 328 (* h1 h1 h1) (* h2 h2) (* h4 h4) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2056 (* h1 h1 h1) (* h2 h2) 
(* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 5026 (* h1 h1 h1) (* 
h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6144 (* h1 h1 h1) 
(* h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 4044 (* h1 h1 h1) 
(* h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 1440 (* h1 h1 h1) (* 
h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 258 (* h1 h1 h1) (* h2 h2) 
(* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 18 (* h1 h1 h1) (* h2 h2) (* h4 h4) 
(* h5 h5) h6 (* j2 j2 j2)) (* 24 (* h1 h1 h1) (* h2 h2) (* h4 h4) h5 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 628 (* h1 h1 h1) (* h2 h2) (* h4 h4) h5 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2470 (* h1 h1 h1) (* h2 h2) (* h4 
h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3983 (* h1 h1 h1) (* h2 h2) (* 
h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3121 (* h1 h1 h1) (* h2 h2) (* 
h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1249 (* h1 h1 h1) (* h2 h2) (* h4 
h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 243 (* h1 h1 h1) (* h2 h2) (* h4 h4) h5 
(* h6 h6) (* j2 j2 j2 j2)) (* 18 (* h1 h1 h1) (* h2 h2) (* h4 h4) h5 (* h6 h6) 
(* j2 j2 j2)) (* 464 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 2960 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 7892 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 11360 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2)) (* 9552 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2)) (* 4756 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2))
 (* 1358 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 202 (* h1
 h1 h1) (* h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 12 (* h1 h1 h1) (* h2 h2) 
h4 (* h5 h5 h5) h6 (* j2 j2)) (* 792 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 5208 (* h1 h1 h1) (* h2 h2) h4 (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 14262 (* h1 h1 h1) (* h2 h2) h4
 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 21056 (* h1 h1 h1) (* h2 h2
) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 18124 (* h1 h1 h1) (* h2 
h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 9204 (* h1 h1 h1) (* h2 h2)
 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2668 (* h1 h1 h1) (* h2 h2) h4 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 401 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5) 
(* h6 h6) (* j2 j2 j2)) (* 24 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6) (* 
j2 j2)) (* 56 (* h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 936 (* h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2 j2)) (* 3806 (* h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 7072 (* h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 7052 (* h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2))
 (* 3949 (* h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1224 
(* h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 193 (* h1 h1 h1) 
(* h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 12 (* h1 h1 h1) (* h2 h2) h4 h5 
(* h6 h6 h6) (* j2 j2)) (* 64 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5 h5) h6 (* j2 j2
 j2 j2 j2 j2 j2 j2 j2 j2)) (* 416 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1152 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1768 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 1636 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2)) (* 928 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5 h5) h6 (* j2 j2 j2
 j2 j2)) (* 312 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 56
 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 4 (* h1 h1 h1) (* h2
 h2) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 464 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3200 (* h1 h1 h1) (* h2 h2) (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 9452 (* h1 h1 h1) (* h2 
h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 15612 (* h1 h1 h1) 
(* h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 15786 (* h1 h1 h1)
 (* h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 10050 (* h1 h1 h1) 
(* h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 3988 (* h1 h1 h1) (* h2 
h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 940 (* h1 h1 h1) (* h2 h2) (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2)) (* 118 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 
h6) (* j2 j2)) (* 6 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6) j2) (* 456 (* 
h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 3168 (* h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
 j2)) (* 9402 (* h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 15574 (* h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 15772 (* h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2
 j2 j2)) (* 10048 (* h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2)) (* 3988 (* h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 
940 (* h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 118 (* h1 h1 
h1) (* h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 6 (* h1 h1 h1) (* h2 h2) (* 
h5 h5) (* h6 h6 h6) j2) (* 32 (* h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2
 j2 j2 j2 j2 j2 j2 j2 j2)) (* 240 (* h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 752 (* h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1284 (* h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 1302 (* h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 798 (* h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2 j2
 j2 j2)) (* 286 (* h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 54
 (* h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 4 (* h1 h1 h1) (* h2
 h2) h5 (* h6 h6 h6 h6) (* j2 j2)) (* 2720 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h5
 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 11920 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h5 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 21024 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h5 (* 
j2 j2 j2 j2 j2 j2 j2)) (* 19520 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h5 (* j2 j2 
j2 j2 j2 j2)) (* 10416 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2))
 (* 3200 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2)) (* 512 (* h1 h1 
h1) h2 (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2)) (* 32 (* h1 h1 h1) h2 (* h3 h3 h3 h3)
 h4 h5 (* j2 j2)) (* 960 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2
 j2 j2 j2 j2)) (* 6320 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 15152 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 
j2)) (* 18192 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2)) (* 
12080 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 4464 (* h1 h1
 h1) h2 (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 848 (* h1 h1 h1) h2 (* h3 h3 
h3 h3) h4 h6 (* j2 j2 j2)) (* 64 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h6 (* j2 j2)
) (* 1920 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 10560 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 23264 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)
) (* 26528 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 
17048 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 6392 (* 
h1 h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 1408 (* h1 h1 h1) h2 
(* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2)) (* 168 (* h1 h1 h1) h2 (* h3 h3 h3 h3) 
(* h5 h5) (* j2 j2)) (* 8 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) j2) (* 4160 
(* h1 h1 h1) h2 (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 23360 
(* h1 h1 h1) h2 (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 52032 (* 
h1 h1 h1) h2 (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 58880 (* h1 h1 
h1) h2 (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 36520 (* h1 h1 h1) h2 (* 
h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 12768 (* h1 h1 h1) h2 (* h3 h3 h3 h3) 
h5 h6 (* j2 j2 j2 j2)) (* 2576 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2
)) (* 296 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h5 h6 (* j2 j2)) (* 16 (* h1 h1 h1) h2
 (* h3 h3 h3 h3) h5 h6 j2) (* 1280 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8640 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 23456 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 33312 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 27088 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 
j2 j2 j2)) (* 12960 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2)) 
(* 3584 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2)) (* 528 (* h1 h1 
h1) h2 (* h3 h3 h3 h3) (* h6 h6) (* j2 j2)) (* 32 (* h1 h1 h1) h2 (* h3 h3 h3 h3
) (* h6 h6) j2) (* 672 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 9720 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 29684 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 39168 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 (* j2 
j2 j2 j2 j2 j2 j2)) (* 27508 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 
j2 j2 j2 j2)) (* 11136 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 
j2)) (* 2556 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 312 
(* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 16 (* h1 h1 h1) h2 
(* h3 h3 h3) (* h4 h4) h5 (* j2 j2)) (* 1632 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 
h4) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 12816 (* h1 h1 h1) h2 (* h3 h3 h3) (* 
h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 27568 (* h1 h1 h1) h2 (* h3 h3 h3) (* 
h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 27184 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 
h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 14112 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h6
 (* j2 j2 j2 j2 j2)) (* 3936 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 
j2 j2)) (* 560 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2)) (* 32 (* 
h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h6 (* j2 j2)) (* 1216 (* h1 h1 h1) h2 (* h3 
h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 15456 (* h1 h1 h1) h2 
(* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 56624 (* h1 h1 h1) 
h2 (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 94752 (* h1 h1 h1) 
h2 (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 84188 (* h1 h1 h1) h2 
(* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 42844 (* h1 h1 h1) h2 (* h3 
h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 12948 (* h1 h1 h1) h2 (* h3 h3 h3) h4
 (* h5 h5) (* j2 j2 j2 j2)) (* 2274 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) 
(* j2 j2 j2)) (* 212 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) (* j2 j2)) (* 8 
(* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) j2) (* 2880 (* h1 h1 h1) h2 (* h3 h3 
h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 34984 (* h1 h1 h1) h2 (* h3 
h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 132988 (* h1 h1 h1) h2 (* h3 
h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 235512 (* h1 h1 h1) h2 (* h3 h3 
h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 221752 (* h1 h1 h1) h2 (* h3 h3 h3) h4
 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 119748 (* h1 h1 h1) h2 (* h3 h3 h3) h4 h5 h6 
(* j2 j2 j2 j2 j2)) (* 39000 (* h1 h1 h1) h2 (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 
j2)) (* 7540 (* h1 h1 h1) h2 (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 780 (* h1 h1
 h1) h2 (* h3 h3 h3) h4 h5 h6 (* j2 j2)) (* 32 (* h1 h1 h1) h2 (* h3 h3 h3) h4 
h5 h6 j2) (* 3296 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2 j2)) (* 25488 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 68416 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2)) (* 87848 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2
)) (* 61064 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
24224 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 5480 (* h1 
h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2)) (* 656 (* h1 h1 h1) h2 (* h3 
h3 h3) h4 (* h6 h6) (* j2 j2)) (* 32 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6) 
j2) (* 1920 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2
 j2)) (* 11136 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2
 j2)) (* 25760 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2
)) (* 30464 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 
19840 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 7332 (* 
h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 1570 (* h1 h1 h1) h2 
(* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2)) (* 178 (* h1 h1 h1) h2 (* h3 h3 h3) (* 
h5 h5 h5) (* j2 j2)) (* 8 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) j2) (* 3072 
(* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
29264 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 106072 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2))
 (* 195304 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 202040 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
122394 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 44194 
(* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 9346 (* h1 h1 h1) 
h2 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 1082 (* h1 h1 h1) h2 (* h3 h3 h3) 
(* h5 h5) h6 (* j2 j2)) (* 54 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) h6 j2) (* 
2752 (* h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 29440 (* h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 114888 (* h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2
 j2)) (* 226368 (* h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 253008 (* h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 168804 (* h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 68272
 (* h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 16364 (* h1 h1 h1
) h2 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 2132 (* h1 h1 h1) h2 (* h3 h3 h3
) h5 (* h6 h6) (* j2 j2)) (* 116 (* h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6) j2) 
(* 1280 (* h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 8768 (* h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2))
 (* 24320 (* h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 35504 (* h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
29664 (* h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 14376 (* 
h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 3936 (* h1 h1 h1) h2 
(* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2)) (* 560 (* h1 h1 h1) h2 (* h3 h3 h3) (* 
h6 h6 h6) (* j2 j2)) (* 32 (* h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6) j2) (* 480 
(* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
3204 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 6738 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 6392 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 
3286 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 932 (* 
h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 136 (* h1 h1 h1) 
h2 (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 8 (* h1 h1 h1) h2 (* h3 h3) (* 
h4 h4 h4) h5 (* j2 j2 j2)) (* 624 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3444 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 5388 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 3840 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h6 (* 
j2 j2 j2 j2 j2 j2)) (* 1376 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 
j2 j2 j2)) (* 240 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2)) (* 
16 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2)) (* 1856 (* h1 h1 h1) 
h2 (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 12520 (* 
h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
32500 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2))
 (* 42160 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)
) (* 29744 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) 
(* 11810 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 
2662 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 320 (* h1
 h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 16 (* h1 h1 h1) h2 (* 
h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 2720 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4
) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 22188 (* h1 h1 h1) h2 (* h3 h3) 
(* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 66302 (* h1 h1 h1) h2 (* h3 
h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 96678 (* h1 h1 h1) h2 (* h3 
h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 75812 (* h1 h1 h1) h2 (* h3 h3)
 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 33940 (* h1 h1 h1) h2 (* h3 h3) (* h4
 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 8678 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 h6
 (* j2 j2 j2 j2)) (* 1170 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)
) (* 64 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 1808 (* h1 h1 h1
) h2 (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 12644 (* 
h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 28624
 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
28808 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
14892 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 4116 
(* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 576 (* h1 h1 
h1) h2 (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 32 (* h1 h1 h1) h2 (* h3 
h3) (* h4 h4) (* h6 h6) (* j2 j2)) (* 896 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5 
h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8160 (* h1 h1 h1) h2 (* h3 h3) h4 (* 
h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 27952 (* h1 h1 h1) h2 (* h3 h3) h4 
(* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 47528 (* h1 h1 h1) h2 (* h3 h3) h4 
(* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 43844 (* h1 h1 h1) h2 (* h3 h3) h4 (* 
h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 22720 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5 
h5) (* j2 j2 j2 j2 j2)) (* 6844 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) (* j2 
j2 j2 j2)) (* 1183 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2)) (* 
108 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) (* j2 j2)) (* 4 (* h1 h1 h1) h2 
(* h3 h3) h4 (* h5 h5 h5) j2) (* 6816 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 50424 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 152116 (* h1 h1 h1) h2 (* h3 h3) h4 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 242548 (* h1 h1 h1) h2 (* h3 h3) h4
 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 223224 (* h1 h1 h1) h2 (* h3 h3) h4 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 122781 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5
 h5) h6 (* j2 j2 j2 j2 j2)) (* 40672 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) h6 
(* j2 j2 j2 j2)) (* 7951 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2))
 (* 837 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 36 (* h1 h1 h1) 
h2 (* h3 h3) h4 (* h5 h5) h6 j2) (* 4480 (* h1 h1 h1) h2 (* h3 h3) h4 h5 (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 38568 (* h1 h1 h1) h2 (* h3 h3) h4 h5 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 130516 (* h1 h1 h1) h2 (* h3 h3) h4
 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 228304 (* h1 h1 h1) h2 (* h3 h3) 
h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 228646 (* h1 h1 h1) h2 (* h3 h3) h4
 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 138446 (* h1 h1 h1) h2 (* h3 h3) h4 h5 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 51142 (* h1 h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6)
 (* j2 j2 j2 j2)) (* 11184 (* h1 h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2
)) (* 1318 (* h1 h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 64 (* h1 h1 
h1) h2 (* h3 h3) h4 h5 (* h6 h6) j2) (* 1440 (* h1 h1 h1) h2 (* h3 h3) h4 (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 10960 (* h1 h1 h1) h2 (* h3 h3) h4 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 30928 (* h1 h1 h1) h2 (* h3 h3) h4 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 42524 (* h1 h1 h1) h2 (* h3 h3) h4 (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 31176 (* h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6 h6)
 (* j2 j2 j2 j2 j2)) (* 12660 (* h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6 h6) (* j2 j2
 j2 j2)) (* 2860 (* h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2)) (* 336 
(* h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6 h6) (* j2 j2)) (* 16 (* h1 h1 h1) h2 (* h3
 h3) h4 (* h6 h6 h6) j2) (* 384 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 2304 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 5536 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 6816 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) (* j2 
j2 j2 j2 j2 j2)) (* 4608 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 
j2 j2)) (* 1748 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 
382 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 44 (* h1 h1 h1) 
h2 (* h3 h3) (* h5 h5 h5 h5) (* j2 j2)) (* 2 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 
h5 h5) j2) (* 2432 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 18752 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 60400 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 104856 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2
 j2 j2 j2 j2 j2)) (* 106244 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2)) (* 64146 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2)) (* 22954 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 4799
 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 550 (* h1 h1 h1) h2 
(* h3 h3) (* h5 h5 h5) h6 (* j2 j2)) (* 27 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5
) h6 j2) (* 4848 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 37944 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 125880 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 230072 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 252342 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 170026 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 69566 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5) (* h6
 h6) (* j2 j2 j2 j2)) (* 16693 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6) (* 
j2 j2 j2)) (* 2144 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 
113 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6) j2) (* 2240 (* h1 h1 h1) h2 
(* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 18560 (* h1 h1 
h1) h2 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 64112 (* h1 
h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 120144 (* h1
 h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 133332 (* h1 
h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 90288 (* h1 h1 h1)
 h2 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 37296 (* h1 h1 h1) h2 (* h3
 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 9140 (* h1 h1 h1) h2 (* h3 h3) h5 (* h6
 h6 h6) (* j2 j2 j2)) (* 1210 (* h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2
)) (* 66 (* h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6) j2) (* 256 (* h1 h1 h1) h2 
(* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1856 (* h1 h1 h1) 
h2 (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 5440 (* h1 h1 h1) 
h2 (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 8320 (* h1 h1 h1) h2 
(* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 7176 (* h1 h1 h1) h2 (* h3 
h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 3544 (* h1 h1 h1) h2 (* h3 h3) (* h6 
h6 h6 h6) (* j2 j2 j2 j2)) (* 980 (* h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6 h6) (* 
j2 j2 j2)) (* 140 (* h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6 h6) (* j2 j2)) (* 8 (* 
h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6 h6) j2) (* 328 (* h1 h1 h1) h2 h3 (* h4 h4 h4
) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1672 (* h1 h1 h1) h2 h3 (* h4 
h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3390 (* h1 h1 h1) h2 h3 (* 
h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3406 (* h1 h1 h1) h2 h3 (* 
h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1770 (* h1 h1 h1) h2 h3 (* h4 
h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 492 (* h1 h1 h1) h2 h3 (* h4 h4 h4) 
(* h5 h5) (* j2 j2 j2 j2 j2)) (* 70 (* h1 h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) 
(* j2 j2 j2 j2)) (* 4 (* h1 h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) 
(* 96 (* h1 h1 h1) h2 h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 1476 (* h1 h1 h1) h2 h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 5148 (* h1 h1 h1) h2 h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
7503 (* h1 h1 h1) h2 h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 5143 (* 
h1 h1 h1) h2 h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 1792 (* h1 h1 h1) 
h2 h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 306 (* h1 h1 h1) h2 h3 (* h4 h4 
h4) h5 h6 (* j2 j2 j2 j2)) (* 20 (* h1 h1 h1) h2 h3 (* h4 h4 h4) h5 h6 (* j2 j2 
j2)) (* 24 (* h1 h1 h1) h2 h3 (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 536 (* h1 h1 h1) h2 h3 (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 1640 (* h1 h1 h1) h2 h3 (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 1520 (* h1 h1 h1) h2 h3 (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 620 
(* h1 h1 h1) h2 h3 (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 116 (* h1 h1 h1
) h2 h3 (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 8 (* h1 h1 h1) h2 h3 (* h4 h4
 h4) (* h6 h6) (* j2 j2 j2)) (* 464 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2904 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5
 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 7536 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 10220 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 7608 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5 
h5) (* j2 j2 j2 j2 j2 j2)) (* 3094 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) (* 
j2 j2 j2 j2 j2)) (* 695 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2
)) (* 82 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 4 (* h1 h1 
h1) h2 h3 (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 1904 (* h1 h1 h1) h2 h3 (* h4 h4)
 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 13116 (* h1 h1 h1) h2 h3 (* 
h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 36166 (* h1 h1 h1) h2 h3 
(* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 50958 (* h1 h1 h1) h2 h3 
(* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 39749 (* h1 h1 h1) h2 h3 (* 
h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 17807 (* h1 h1 h1) h2 h3 (* h4 h4)
 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 4529 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5)
 h6 (* j2 j2 j2 j2)) (* 601 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 
j2)) (* 32 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 368 (* h1 h1 
h1) h2 h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 5252 (* 
h1 h1 h1) h2 h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 21618 
(* h1 h1 h1) h2 h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 39422 
(* h1 h1 h1) h2 h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 36115 (* 
h1 h1 h1) h2 h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 17878 (* h1 h1 
h1) h2 h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 4829 (* h1 h1 h1) h2 h3 
(* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 663 (* h1 h1 h1) h2 h3 (* h4 h4) h5 
(* h6 h6) (* j2 j2 j2)) (* 36 (* h1 h1 h1) h2 h3 (* h4 h4) h5 (* h6 h6) (* j2 j2
)) (* 56 (* h1 h1 h1) h2 h3 (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2
)) (* 888 (* h1 h1 h1) h2 h3 (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2))
 (* 3336 (* h1 h1 h1) h2 h3 (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
4832 (* h1 h1 h1) h2 h3 (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3056 
(* h1 h1 h1) h2 h3 (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 944 (* h1 h1 h1
) h2 h3 (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 140 (* h1 h1 h1) h2 h3 (* h4 
h4) (* h6 h6 h6) (* j2 j2 j2)) (* 8 (* h1 h1 h1) h2 h3 (* h4 h4) (* h6 h6 h6) 
(* j2 j2)) (* 64 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 480 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 1536 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 2664 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
2652 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1496 (* h1 
h1 h1) h2 h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 452 (* h1 h1 h1) h2 h3 h4
 (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 68 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5 h5) 
(* j2 j2 j2)) (* 4 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5 h5) (* j2 j2)) (* 1968 (* 
h1 h1 h1) h2 h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 14208 
(* h1 h1 h1) h2 h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 42204 
(* h1 h1 h1) h2 h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 66600 (* 
h1 h1 h1) h2 h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 60686 (* h1 h1 
h1) h2 h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 32920 (* h1 h1 h1) h2 h3 
h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 10713 (* h1 h1 h1) h2 h3 h4 (* h5 h5 
h5) h6 (* j2 j2 j2 j2)) (* 2033 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5) h6 (* j2 j2 
j2)) (* 203 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5) h6 (* j2 j2)) (* 8 (* h1 h1 h1) 
h2 h3 h4 (* h5 h5 h5) h6 j2) (* 3080 (* h1 h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 23164 (* h1 h1 h1) h2 h3 h4 (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 72496 (* h1 h1 h1) h2 h3 h4 (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 122072 (* h1 h1 h1) h2 h3 h4 (* h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 120662 (* h1 h1 h1) h2 h3 h4 (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 72599 (* h1 h1 h1) h2 h3 h4 (* h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2)) (* 26764 (* h1 h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6) (* j2
 j2 j2 j2)) (* 5817 (* h1 h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 
675 (* h1 h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 32 (* h1 h1 h1) h2 
h3 h4 (* h5 h5) (* h6 h6) j2) (* 464 (* h1 h1 h1) h2 h3 h4 h5 (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 5376 (* h1 h1 h1) h2 h3 h4 h5 (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 22464 (* h1 h1 h1) h2 h3 h4 h5 (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 46444 (* h1 h1 h1) h2 h3 h4 h5 (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 52970 (* h1 h1 h1) h2 h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 34936 (* h1 h1 h1) h2 h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 13575 (* h1 h1 h1) h2 h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 3010 (* h1 h1
 h1) h2 h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 347 (* h1 h1 h1) h2 h3 h4 h5 (* 
h6 h6 h6) (* j2 j2)) (* 16 (* h1 h1 h1) h2 h3 h4 h5 (* h6 h6 h6) j2) (* 32 (* h1
 h1 h1) h2 h3 h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 304 (* h1 h1
 h1) h2 h3 h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1032 (* h1 h1 h1) 
h2 h3 h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1648 (* h1 h1 h1) h2 h3 h4
 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1336 (* h1 h1 h1) h2 h3 h4 (* h6 h6 
h6 h6) (* j2 j2 j2 j2 j2)) (* 548 (* h1 h1 h1) h2 h3 h4 (* h6 h6 h6 h6) (* j2 j2
 j2 j2)) (* 108 (* h1 h1 h1) h2 h3 h4 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 8 (* h1 
h1 h1) h2 h3 h4 (* h6 h6 h6 h6) (* j2 j2)) (* 256 (* h1 h1 h1) h2 h3 (* h5 h5 h5
 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1856 (* h1 h1 h1) h2 h3 (* h5 h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 5632 (* h1 h1 h1) h2 h3 (* h5 h5 h5
 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 9248 (* h1 h1 h1) h2 h3 (* h5 h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 8888 (* h1 h1 h1) h2 h3 (* h5 h5 h5 h5) h6 (* j2
 j2 j2 j2 j2 j2)) (* 5080 (* h1 h1 h1) h2 h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 
j2)) (* 1708 (* h1 h1 h1) h2 h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 336 (* h1
 h1 h1) h2 h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 38 (* h1 h1 h1) h2 h3 (* h5 h5
 h5 h5) h6 (* j2 j2)) (* 2 (* h1 h1 h1) h2 h3 (* h5 h5 h5 h5) h6 j2) (* 1504 (* 
h1 h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
11600 (* h1 h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 37720 (* h1 h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 67284 (* h1 h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
71804 (* h1 h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 47036 
(* h1 h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 18775 (* h1 h1 
h1) h2 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 4411 (* h1 h1 h1) h2 h3 (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 557 (* h1 h1 h1) h2 h3 (* h5 h5 h5) (* h6 
h6) (* j2 j2)) (* 29 (* h1 h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6) j2) (* 1488 (* h1
 h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 11464
 (* h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
37384 (* h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
67120 (* h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
72384 (* h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 48156 
(* h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 19645 (* h1 h1 
h1) h2 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 4745 (* h1 h1 h1) h2 h3 (* 
h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 617 (* h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6 
h6) (* j2 j2)) (* 33 (* h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6) j2) (* 192 (* h1 
h1 h1) h2 h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1472 (* h1
 h1 h1) h2 h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4800 (* h1 
h1 h1) h2 h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 8648 (* h1 h1 h1
) h2 h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 9392 (* h1 h1 h1) h2 h3 
h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6340 (* h1 h1 h1) h2 h3 h5 (* h6 h6
 h6 h6) (* j2 j2 j2 j2 j2)) (* 2676 (* h1 h1 h1) h2 h3 h5 (* h6 h6 h6 h6) (* j2 
j2 j2 j2)) (* 694 (* h1 h1 h1) h2 h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 100 (* 
h1 h1 h1) h2 h3 h5 (* h6 h6 h6 h6) (* j2 j2)) (* 6 (* h1 h1 h1) h2 h3 h5 (* h6 
h6 h6 h6) j2) (* 24 (* h1 h1 h1) h2 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 340 (* h1 h1 h1) h2 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 1168 (* h1 h1 h1) h2 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 1666 (* h1 h1 h1) h2 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2)) (* 1134 (* h1 h1 h1) h2 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 
j2 j2)) (* 388 (* h1 h1 h1) h2 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
64 (* h1 h1 h1) h2 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 4 (* h1 h1 h1) 
h2 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 48 (* h1 h1 h1) h2 (* h4 h4 h4) h5
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 442 (* h1 h1 h1) h2 (* h4 h4 h4) 
h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 991 (* h1 h1 h1) h2 (* h4 h4 h4) h5
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 847 (* h1 h1 h1) h2 (* h4 h4 h4) h5 (* 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 332 (* h1 h1 h1) h2 (* h4 h4 h4) h5 (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* 60 (* h1 h1 h1) h2 (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 
j2)) (* 4 (* h1 h1 h1) h2 (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 80 (* h1 h1
 h1) h2 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 768 (* 
h1 h1 h1) h2 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2676 
(* h1 h1 h1) h2 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4556 
(* h1 h1 h1) h2 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 4164 (* 
h1 h1 h1) h2 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 2086 (* h1 h1 
h1) h2 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 563 (* h1 h1 h1) h2 (* 
h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 76 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5
 h5) h6 (* j2 j2 j2)) (* 4 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) 
(* 104 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 1300 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 4956 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 8786 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 8186 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 4142 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2)) (* 1124 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) 
(* 152 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 8 (* h1 h1
 h1) h2 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 112 (* h1 h1 h1) h2 (* h4 h4
) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 876 (* h1 h1 h1) h2 (* h4 
h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2320 (* h1 h1 h1) h2 (* h4 
h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2789 (* h1 h1 h1) h2 (* h4 h4) 
h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1655 (* h1 h1 h1) h2 (* h4 h4) h5 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 497 (* h1 h1 h1) h2 (* h4 h4) h5 (* h6 h6 h6) 
(* j2 j2 j2 j2)) (* 72 (* h1 h1 h1) h2 (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2)) 
(* 4 (* h1 h1 h1) h2 (* h4 h4) h5 (* h6 h6 h6) (* j2 j2)) (* 32 (* h1 h1 h1) h2 
h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 256 (* h1 h1 h1) h2 
h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 848 (* h1 h1 h1) h2 h4 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1508 (* h1 h1 h1) h2 h4 (* h5
 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1560 (* h1 h1 h1) h2 h4 (* h5 h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 950 (* h1 h1 h1) h2 h4 (* h5 h5 h5 h5) h6 (* j2
 j2 j2 j2 j2)) (* 328 (* h1 h1 h1) h2 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 
58 (* h1 h1 h1) h2 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 4 (* h1 h1 h1) h2 h4 
(* h5 h5 h5 h5) h6 (* j2 j2)) (* 232 (* h1 h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1924 (* h1 h1 h1) h2 h4 (* h5 h5 h5) (* h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 6612 (* h1 h1 h1) h2 h4 (* h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 12290 (* h1 h1 h1) h2 h4 (* h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 13466 (* h1 h1 h1) h2 h4 (* h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 8886 (* h1 h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2)) (* 3476 (* h1 h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2)) (* 770 (* h1 h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 88 (* h1 
h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 4 (* h1 h1 h1) h2 h4 (* h5 h5 
h5) (* h6 h6) j2) (* 144 (* h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 1472 (* h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 5668 (* h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 11266 (* h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 12853 (* h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 8687 (* h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2)) (* 3444 (* h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 
768 (* h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 88 (* h1 h1 h1) 
h2 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 4 (* h1 h1 h1) h2 h4 (* h5 h5) (* h6 
h6 h6) j2) (* 64 (* h1 h1 h1) h2 h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 368 (* h1 h1 h1) h2 h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 872 (* h1 h1 h1) h2 h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1088
 (* h1 h1 h1) h2 h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 758 (* h1 h1 h1
) h2 h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 289 (* h1 h1 h1) h2 h4 h5 (* 
h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 55 (* h1 h1 h1) h2 h4 h5 (* h6 h6 h6 h6) (* j2 
j2 j2)) (* 4 (* h1 h1 h1) h2 h4 h5 (* h6 h6 h6 h6) (* j2 j2)) (* 64 (* h1 h1 h1)
 h2 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 480 (* h1 h1
 h1) h2 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1552 (* h1 
h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2824 (* h1 
h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3164 (* h1 h1 
h1) h2 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2242 (* h1 h1 h1) h2 
(* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 992 (* h1 h1 h1) h2 (* h5 h5 h5
 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 260 (* h1 h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6)
 (* j2 j2 j2)) (* 36 (* h1 h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 2 
(* h1 h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6) j2) (* 144 (* h1 h1 h1) h2 (* h5 h5 h5
) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1056 (* h1 h1 h1) h2 (* h5 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3344 (* h1 h1 h1) h2 (* 
h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 5970 (* h1 h1 h1) h2 (* 
h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 6576 (* h1 h1 h1) h2 (* h5 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4592 (* h1 h1 h1) h2 (* h5 h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2008 (* h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2)) (* 522 (* h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 
j2)) (* 72 (* h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 4 (* h1 h1 h1
) h2 (* h5 h5 h5) (* h6 h6 h6) j2) (* 64 (* h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 480 (* h1 h1 h1) h2 (* h5 h5) (* h6 h6
 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1552 (* h1 h1 h1) h2 (* h5 h5) (* h6 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2824 (* h1 h1 h1) h2 (* h5 h5) (* h6 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3164 (* h1 h1 h1) h2 (* h5 h5) (* h6 h6 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2242 (* h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2)) (* 992 (* h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2
 j2)) (* 260 (* h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 36 (* h1
 h1 h1) h2 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 2 (* h1 h1 h1) h2 (* h5 h5) 
(* h6 h6 h6 h6) j2) (* 480 (* h1 h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2
 j2 j2 j2 j2 j2 j2 j2)) (* 2400 (* h1 h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 5056 (* h1 h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 5944 (* h1 h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 (* 
j2 j2 j2 j2 j2 j2 j2)) (* 4328 (* h1 h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 
j2 j2 j2 j2 j2)) (* 2024 (* h1 h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 
j2 j2)) (* 600 (* h1 h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 104
 (* h1 h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 8 (* h1 h1 h1) (* h3
 h3 h3 h3) (* h4 h4) h5 (* j2 j2)) (* 480 (* h1 h1 h1) (* h3 h3 h3 h3) (* h4 h4)
 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2160 (* h1 h1 h1) (* h3 h3 h3 h3) (* h4 
h4) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4096 (* h1 h1 h1) (* h3 h3 h3 h3) (* h4 
h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 4256 (* h1 h1 h1) (* h3 h3 h3 h3) (* h4 h4) 
h6 (* j2 j2 j2 j2 j2 j2)) (* 2624 (* h1 h1 h1) (* h3 h3 h3 h3) (* h4 h4) h6 (* 
j2 j2 j2 j2 j2)) (* 960 (* h1 h1 h1) (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2
)) (* 192 (* h1 h1 h1) (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2)) (* 16 (* h1 h1
 h1) (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2)) (* 640 (* h1 h1 h1) (* h3 h3 h3 h3)
 h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3840 (* h1 h1 h1) (* h3 h3 
h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 9568 (* h1 h1 h1) (* h3 
h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 13040 (* h1 h1 h1) (* h3 
h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 10848 (* h1 h1 h1) (* h3 h3 
h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 5832 (* h1 h1 h1) (* h3 h3 h3 h3) 
h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 2068 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h5 
h5) (* j2 j2 j2 j2)) (* 472 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 
j2)) (* 64 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2)) (* 4 (* h1 h1 h1
) (* h3 h3 h3 h3) h4 (* h5 h5) j2) (* 1600 (* h1 h1 h1) (* h3 h3 h3 h3) h4 h5 h6
 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 10560 (* h1 h1 h1) (* h3 h3 h3 h3) h4 h5 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 29280 (* h1 h1 h1) (* h3 h3 h3 h3) h4 h5 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 44592 (* h1 h1 h1) (* h3 h3 h3 h3) h4 h5 h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 41120 (* h1 h1 h1) (* h3 h3 h3 h3) h4 h5 h6 (* j2 
j2 j2 j2 j2 j2)) (* 23880 (* h1 h1 h1) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 
j2)) (* 8784 (* h1 h1 h1) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 2000 (* 
h1 h1 h1) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 264 (* h1 h1 h1) (* h3 h3 h3
 h3) h4 h5 h6 (* j2 j2)) (* 16 (* h1 h1 h1) (* h3 h3 h3 h3) h4 h5 h6 j2) (* 640 
(* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
3840 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
9568 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
12960 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 10448 
(* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 5136 (* h1 h1 
h1) (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 1504 (* h1 h1 h1) (* h3 h3 
h3 h3) h4 (* h6 h6) (* j2 j2 j2)) (* 240 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h6 
h6) (* j2 j2)) (* 16 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h6 h6) j2) (* 1280 (* h1
 h1 h1) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8960 
(* h1 h1 h1) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
26176 (* h1 h1 h1) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
41376 (* h1 h1 h1) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
38528 (* h1 h1 h1) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 21760 
(* h1 h1 h1) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 7496 (* h1 h1 
h1) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 1552 (* h1 h1 h1) (* h3 h3 
h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 176 (* h1 h1 h1) (* h3 h3 h3 h3) (* h5 h5) 
h6 (* j2 j2)) (* 8 (* h1 h1 h1) (* h3 h3 h3 h3) (* h5 h5) h6 j2) (* 1280 (* h1 
h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 9600 
(* h1 h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
30336 (* h1 h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
52544 (* h1 h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
54432 (* h1 h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 34624 
(* h1 h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 13392 (* h1 h1 
h1) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 3008 (* h1 h1 h1) (* h3 h3 
h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 352 (* h1 h1 h1) (* h3 h3 h3 h3) h5 (* h6 
h6) (* j2 j2)) (* 16 (* h1 h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6) j2) (* 480 (* h1 
h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2016 
(* h1 h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
3424 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
3128 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 1704
 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 560 (* h1 
h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 104 (* h1 h1 h1) (* 
h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 8 (* h1 h1 h1) (* h3 h3 h3) (* h4 
h4 h4) h5 (* j2 j2 j2)) (* 480 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 1776 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4 h4) h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 2656 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4 h4) h6 (* 
j2 j2 j2 j2 j2 j2 j2)) (* 2064 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 
j2 j2 j2 j2 j2)) (* 880 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2
 j2)) (* 192 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2)) (* 16 
(* h1 h1 h1) (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2)) (* 1360 (* h1 h1 h1) (* 
h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 7248 (* h1 
h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 15600
 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
17868 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 12212 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) 
(* 5248 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 
1402 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 214 (* h1
 h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 14 (* h1 h1 h1) (* h3 
h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 2080 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4
) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 13608 (* h1 h1 h1) (* h3 h3 h3) 
(* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 35284 (* h1 h1 h1) (* h3 h3 
h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 47620 (* h1 h1 h1) (* h3 h3 
h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 37200 (* h1 h1 h1) (* h3 h3 h3)
 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 17556 (* h1 h1 h1) (* h3 h3 h3) (* h4
 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 4960 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 h6
 (* j2 j2 j2 j2)) (* 780 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2))
 (* 52 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 1120 (* h1 h1 h1)
 (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 5856 (* h1 
h1 h1) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 12248 
(* h1 h1 h1) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 13248
 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 7984 
(* h1 h1 h1) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2680 (* h1 
h1 h1) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 464 (* h1 h1 h1) (* 
h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 32 (* h1 h1 h1) (* h3 h3 h3) (* 
h4 h4) (* h6 h6) (* j2 j2)) (* 640 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4032 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5
) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 10496 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5
 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 14784 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5
 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 12512 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5
) (* j2 j2 j2 j2 j2 j2)) (* 6740 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2
 j2 j2 j2 j2)) (* 2368 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)
) (* 528 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2)) (* 69 (* h1 h1 
h1) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2)) (* 4 (* h1 h1 h1) (* h3 h3 h3) h4 
(* h5 h5 h5) j2) (* 4080 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 27824 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 77888 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 116388 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 102044 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 55098 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* 18804 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)
) (* 4020 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 502 (* h1 
h1 h1) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 28 (* h1 h1 h1) (* h3 h3 h3) 
h4 (* h5 h5) h6 j2) (* 2880 (* h1 h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 21776 (* h1 h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 67656 (* h1 h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 112392 (* h1 h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2)) (* 109848 (* h1 h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 66260 (* h1 h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 
j2 j2 j2 j2)) (* 25316 (* h1 h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)
) (* 6052 (* h1 h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 824 (* h1 
h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 48 (* h1 h1 h1) (* h3 h3 h3) 
h4 h5 (* h6 h6) j2) (* 640 (* h1 h1 h1) (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2
 j2 j2 j2 j2 j2 j2)) (* 3904 (* h1 h1 h1) (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 9952 (* h1 h1 h1) (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 13840 (* h1 h1 h1) (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 11424 (* h1 h1 h1) (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2)
) (* 5688 (* h1 h1 h1) (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1656 (* 
h1 h1 h1) (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2)) (* 256 (* h1 h1 h1) (* h3 
h3 h3) h4 (* h6 h6 h6) (* j2 j2)) (* 16 (* h1 h1 h1) (* h3 h3 h3) h4 (* h6 h6 h6
) j2) (* 1280 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 9344 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 28416 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 46528 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2)) (* 44416 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2)) (* 25256 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
8568 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 1724 (* h1 h1
 h1) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 186 (* h1 h1 h1) (* h3 h3 h3)
 (* h5 h5 h5) h6 (* j2 j2)) (* 8 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5 h5) h6 j2) 
(* 2720 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
 j2 j2)) (* 20416 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 64656 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2
 j2 j2 j2 j2 j2 j2)) (* 112664 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 118072 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 76296 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* 29808 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2
 j2 j2 j2)) (* 6596 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) 
(* 740 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 32 (* h1 h1 
h1) (* h3 h3 h3) (* h5 h5) (* h6 h6) j2) (* 1280 (* h1 h1 h1) (* h3 h3 h3) h5 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 9728 (* h1 h1 h1) (* h3 h3 h3
) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 31296 (* h1 h1 h1) (* h3 h3
 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 55424 (* h1 h1 h1) (* h3 h3
 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 58816 (* h1 h1 h1) (* h3 h3 h3
) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 38160 (* h1 h1 h1) (* h3 h3 h3) h5 
(* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 14832 (* h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6 
h6) (* j2 j2 j2 j2)) (* 3272 (* h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 
j2)) (* 368 (* h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 16 (* h1 h1 
h1) (* h3 h3 h3) h5 (* h6 h6 h6) j2) (* 72 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4 h4
) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 240 (* h1 h1 h1) (* h3 h3) (* h4 h4 
h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 312 (* h1 h1 h1) (* h3 h3) (* h4 h4
 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 218 (* h1 h1 h1) (* h3 h3) (* h4 h4 
h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 88 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4 h4)
 h5 (* j2 j2 j2 j2 j2 j2)) (* 20 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2
 j2 j2 j2 j2)) (* 2 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2)) 
(* 72 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 204 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 228 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
128 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 36 (* h1
 h1 h1) (* h3 h3) (* h4 h4 h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 4 (* h1 h1 h1) (* h3
 h3) (* h4 h4 h4 h4) h6 (* j2 j2 j2 j2)) (* 456 (* h1 h1 h1) (* h3 h3) (* h4 h4 
h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2128 (* h1 h1 h1) (* h3 h3) 
(* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3908 (* h1 h1 h1) (* 
h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3686 (* h1 h1 h1) 
(* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1988 (* h1 h1 h1) 
(* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 635 (* h1 h1 h1) (* 
h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 111 (* h1 h1 h1) (* h3 h3) 
(* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 8 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4)
 (* h5 h5) (* j2 j2 j2)) (* 408 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2956 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 h6 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 7502 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 9156 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 6094 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 h6 
(* j2 j2 j2 j2 j2 j2)) (* 2254 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 
j2 j2 j2 j2)) (* 428 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) 
(* 32 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 264 (* h1 h1 h1
) (* h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1324 (* h1
 h1 h1) (* h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2420 
(* h1 h1 h1) (* h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2112 
(* h1 h1 h1) (* h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 936 (* 
h1 h1 h1) (* h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 200 (* h1 h1 
h1) (* h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 16 (* h1 h1 h1) (* h3 
h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2)) (* 576 (* h1 h1 h1) (* h3 h3) (* h4 h4)
 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3280 (* h1 h1 h1) (* h3 h3) 
(* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 7528 (* h1 h1 h1) (* 
h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 9096 (* h1 h1 h1) 
(* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 6428 (* h1 h1 h1) 
(* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2806 (* h1 h1 h1) (* 
h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 750 (* h1 h1 h1) (* h3 h3) 
(* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 112 (* h1 h1 h1) (* h3 h3) (* h4 h4) 
(* h5 h5 h5) (* j2 j2 j2)) (* 7 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) 
(* j2 j2)) (* 1952 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 13120 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2
 j2 j2 j2 j2 j2 j2 j2 j2)) (* 35420 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 49556 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 39076 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5
 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 18027 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 
h5) h6 (* j2 j2 j2 j2 j2)) (* 4914 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) h6
 (* j2 j2 j2 j2)) (* 731 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 
j2)) (* 45 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 848 (* h1
 h1 h1) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
7680 (* h1 h1 h1) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2
)) (* 25524 (* h1 h1 h1) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 41894 (* h1 h1 h1) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2)) (* 37868 (* h1 h1 h1) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 19778 (* h1 h1 h1) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2
)) (* 5924 (* h1 h1 h1) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 928
 (* h1 h1 h1) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 58 (* h1 h1 h1) 
(* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 320 (* h1 h1 h1) (* h3 h3) (* h4 
h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2000 (* h1 h1 h1) (* h3 h3) 
(* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4824 (* h1 h1 h1) (* h3 
h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 5864 (* h1 h1 h1) (* h3 
h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3868 (* h1 h1 h1) (* h3 h3)
 (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1372 (* h1 h1 h1) (* h3 h3) (* h4
 h4) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 240 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h6
 h6 h6) (* j2 j2 j2)) (* 16 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 
j2)) (* 128 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2
 j2 j2)) (* 832 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 2240 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 3264 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 
j2 j2)) (* 2848 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2))
 (* 1572 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 564 
(* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 128 (* h1 h1 h1) 
(* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2)) (* 17 (* h1 h1 h1) (* h3 h3) h4 (* h5
 h5 h5 h5) (* j2 j2)) (* (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) j2) (* 1728 
(* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
12464 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 37024 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 58572 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
53676 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 29544 
(* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 10051 (* h1 h1 
h1) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 2119 (* h1 h1 h1) (* h3 h3)
 h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 259 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) 
h6 (* j2 j2)) (* 14 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) h6 j2) (* 2656 (* h1 
h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
20408 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 64912 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 111108 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 111774 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 68214 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2
 j2)) (* 25424 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) 
(* 5795 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 746 (* h1
 h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 41 (* h1 h1 h1) (* h3 h3)
 h4 (* h5 h5) (* h6 h6) j2) (* 768 (* h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 7072 (* h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 25760 (* h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 49048 (* h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6
 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 53868 (* h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6
) (* j2 j2 j2 j2 j2 j2)) (* 35592 (* h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6) (* 
j2 j2 j2 j2 j2)) (* 14424 (* h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 
j2)) (* 3560 (* h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 488 (* 
h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2)) (* 28 (* h1 h1 h1) (* h3 h3) 
h4 h5 (* h6 h6 h6) j2) (* 128 (* h1 h1 h1) (* h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2
 j2 j2 j2 j2 j2 j2 j2)) (* 832 (* h1 h1 h1) (* h3 h3) h4 (* h6 h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 2240 (* h1 h1 h1) (* h3 h3) h4 (* h6 h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 3248 (* h1 h1 h1) (* h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 2760 (* h1 h1 h1) (* h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 
j2)) (* 1400 (* h1 h1 h1) (* h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 412 
(* h1 h1 h1) (* h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 64 (* h1 h1 h1) (* h3
 h3) h4 (* h6 h6 h6 h6) (* j2 j2)) (* 4 (* h1 h1 h1) (* h3 h3) h4 (* h6 h6 h6 h6
) j2) (* 256 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 1920 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 6016 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 10176 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2)) (* 10048 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2)) (* 5896 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
2048 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 420 (* h1 h1 
h1) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 46 (* h1 h1 h1) (* h3 h3) (* 
h5 h5 h5 h5) h6 (* j2 j2)) (* 2 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5 h5) h6 j2) 
(* 1152 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
 j2 j2)) (* 9120 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2 j2)) (* 30464 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 55784 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2
 j2 j2 j2 j2 j2 j2)) (* 60864 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 40284 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2
 j2 j2 j2 j2)) (* 15790 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2)) (* 3444 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 
378 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 16 (* h1 h1 h1) 
(* h3 h3) (* h5 h5 h5) (* h6 h6) j2) (* 1152 (* h1 h1 h1) (* h3 h3) (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 9152 (* h1 h1 h1) (* h3 h3) 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 30800 (* h1 h1 h1) (* 
h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 57072 (* h1 h1 h1)
 (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 63304 (* h1 h1 h1
) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 42764 (* h1 h1 h1) 
(* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 17128 (* h1 h1 h1) (* h3
 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 3800 (* h1 h1 h1) (* h3 h3) (* 
h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 422 (* h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 
h6 h6) (* j2 j2)) (* 18 (* h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6) j2) (* 256
 (* h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 2048 (* h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 6912 (* h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2))
 (* 12768 (* h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 14016 (* h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
9312 (* h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 3672 (* h1
 h1 h1) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 816 (* h1 h1 h1) (* h3 
h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 92 (* h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6
 h6) (* j2 j2)) (* 4 (* h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6 h6) j2) (* 24 (* h1 
h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 104 
(* h1 h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 164
 (* h1 h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 122 
(* h1 h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 50 (* h1 
h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 11 (* h1 h1 h1) h3
 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* (* h1 h1 h1) h3 (* h4 h4 h4 h4
) (* h5 h5) (* j2 j2 j2 j2)) (* 96 (* h1 h1 h1) h3 (* h4 h4 h4 h4) h5 h6 (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 308 (* h1 h1 h1) h3 (* h4 h4 h4 h4) h5 h6 (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 350 (* h1 h1 h1) h3 (* h4 h4 h4 h4) h5 h6 (* j2 j2 j2 j2 
j2 j2 j2)) (* 191 (* h1 h1 h1) h3 (* h4 h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) 
(* 50 (* h1 h1 h1) h3 (* h4 h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 5 (* h1 h1 h1
) h3 (* h4 h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 36 (* h1 h1 h1) h3 (* h4 h4 h4 h4
) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 78 (* h1 h1 h1) h3 (* h4 h4 h4 h4) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 58 (* h1 h1 h1) h3 (* h4 h4 h4 h4) (* h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 18 (* h1 h1 h1) h3 (* h4 h4 h4 h4) (* h6 h6) (* j2
 j2 j2 j2 j2)) (* 2 (* h1 h1 h1) h3 (* h4 h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2)) 
(* 80 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2
)) (* 416 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 840 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 852 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 480 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 158 
(* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 28 (* h1 h1 h1)
 h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 2 (* h1 h1 h1) h3 (* h4 h4 h4)
 (* h5 h5 h5) (* j2 j2 j2)) (* 152 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1276 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3646 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5
) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4852 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5)
 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 3324 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 1214 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* 223 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) 
(* 16 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 392 (* h1 h1 h1
) h3 (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2022 (* h1 h1 
h1) h3 (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3665 (* h1 h1 
h1) h3 (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2994 (* h1 h1 h1) 
h3 (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1222 (* h1 h1 h1) h3 (* 
h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 241 (* h1 h1 h1) h3 (* h4 h4 h4) 
h5 (* h6 h6) (* j2 j2 j2 j2)) (* 18 (* h1 h1 h1) h3 (* h4 h4 h4) h5 (* h6 h6) 
(* j2 j2 j2)) (* 84 (* h1 h1 h1) h3 (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 298 (* h1 h1 h1) h3 (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2
 j2)) (* 372 (* h1 h1 h1) h3 (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 202 (* h1 h1 h1) h3 (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 48 (* h1
 h1 h1) h3 (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 4 (* h1 h1 h1) h3 (* h4
 h4 h4) (* h6 h6 h6) (* j2 j2 j2)) (* 32 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5 
h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 208 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5
 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 552 (* h1 h1 h1) h3 (* h4 h4) (* h5 
h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 776 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5
 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 632 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5 
h5) (* j2 j2 j2 j2 j2 j2)) (* 310 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) (* 
j2 j2 j2 j2 j2)) (* 92 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)
) (* 15 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* (* h1 h1 h1) 
h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 392 (* h1 h1 h1) h3 (* h4 h4) (* h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2808 (* h1 h1 h1) h3 (* h4 h4) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8188 (* h1 h1 h1) h3 (* h4 h4
) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 12442 (* h1 h1 h1) h3 (* h4 h4
) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 10564 (* h1 h1 h1) h3 (* h4 h4) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 5111 (* h1 h1 h1) h3 (* h4 h4) (* h5 
h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 1426 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) h6 
(* j2 j2 j2 j2)) (* 213 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) 
(* 13 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 352 (* h1 h1 h1) 
h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3476 (* 
h1 h1 h1) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
12272 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2))
 (* 21208 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 19952 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 10635 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
3163 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 482 (* h1
 h1 h1) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 29 (* h1 h1 h1) h3 (* 
h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 520 (* h1 h1 h1) h3 (* h4 h4) h5 (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3220 (* h1 h1 h1) h3 (* h4 h4) h5 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 7602 (* h1 h1 h1) h3 (* h4 h4) h5 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 8746 (* h1 h1 h1) h3 (* h4 h4) h5 (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 5253 (* h1 h1 h1) h3 (* h4 h4) h5 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2)) (* 1685 (* h1 h1 h1) h3 (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 
j2 j2)) (* 271 (* h1 h1 h1) h3 (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 17 (* 
h1 h1 h1) h3 (* h4 h4) h5 (* h6 h6 h6) (* j2 j2)) (* 48 (* h1 h1 h1) h3 (* h4 h4
) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 208 (* h1 h1 h1) h3 (* h4 h4) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 352 (* h1 h1 h1) h3 (* h4 h4) (* h6
 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 294 (* h1 h1 h1) h3 (* h4 h4) (* h6 h6 h6 
h6) (* j2 j2 j2 j2 j2)) (* 126 (* h1 h1 h1) h3 (* h4 h4) (* h6 h6 h6 h6) (* j2 
j2 j2 j2)) (* 26 (* h1 h1 h1) h3 (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 2 
(* h1 h1 h1) h3 (* h4 h4) (* h6 h6 h6 h6) (* j2 j2)) (* 128 (* h1 h1 h1) h3 h4 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 992 (* h1 h1 h1) h3 h4 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3232 (* h1 h1 h1) h3 h4 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 5712 (* h1 h1 h1) h3 h4 (* h5
 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 5916 (* h1 h1 h1) h3 h4 (* h5 h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 3656 (* h1 h1 h1) h3 h4 (* h5 h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2)) (* 1346 (* h1 h1 h1) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) 
(* 297 (* h1 h1 h1) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 37 (* h1 h1 h1) h3
 h4 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 2 (* h1 h1 h1) h3 h4 (* h5 h5 h5 h5) h6 j2)
 (* 608 (* h1 h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 4792 (* h1 h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 15788 (* h1 h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 28176 (* h1 h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 29628 (* h1 h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 18877 (* h1 h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 7328 
(* h1 h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 1717 (* h1 h1 h1) 
h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 222 (* h1 h1 h1) h3 h4 (* h5 h5 h5
) (* h6 h6) (* j2 j2)) (* 12 (* h1 h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6) j2) (* 
352 (* h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (* 3352 (* h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2
)) (* 12592 (* h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 24760 (* h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 28080 (* h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
19036 (* h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 7789 (* 
h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1905 (* h1 h1 h1) h3 
h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 254 (* h1 h1 h1) h3 h4 (* h5 h5) (* 
h6 h6 h6) (* j2 j2)) (* 14 (* h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6) j2) (* 224 
(* h1 h1 h1) h3 h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1424 
(* h1 h1 h1) h3 h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3720 (* h1
 h1 h1) h3 h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 5144 (* h1 h1 h1) 
h3 h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4068 (* h1 h1 h1) h3 h4 h5 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1876 (* h1 h1 h1) h3 h4 h5 (* h6 h6 h6 h6
) (* j2 j2 j2 j2)) (* 498 (* h1 h1 h1) h3 h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2)) 
(* 70 (* h1 h1 h1) h3 h4 h5 (* h6 h6 h6 h6) (* j2 j2)) (* 4 (* h1 h1 h1) h3 h4 
h5 (* h6 h6 h6 h6) j2) (* 128 (* h1 h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2
 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1024 (* h1 h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3488 (* h1 h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6560 (* h1 h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 7384 (* h1 h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 5040 (* h1 h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2)) (* 2020 (* h1 h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) 
(* 442 (* h1 h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 48 (* h1 h1 h1
) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 2 (* h1 h1 h1) h3 (* h5 h5 h5 h5) 
(* h6 h6) j2) (* 288 (* h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 2256 (* h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 7528 (* h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 13880 (* h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 15336 (* h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 10298 (* h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)
) (* 4076 (* h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 886 (* 
h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 96 (* h1 h1 h1) h3 (* h5
 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 4 (* h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6) 
j2) (* 128 (* h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 1024 (* h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 3488 (* h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 6560 (* h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 7384 (* h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2))
 (* 5040 (* h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2020 
(* h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 442 (* h1 h1 h1) 
h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 48 (* h1 h1 h1) h3 (* h5 h5) (* h6
 h6 h6 h6) (* j2 j2)) (* 2 (* h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6 h6) j2) (* 12 
(* h1 h1 h1) (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 52 
(* h1 h1 h1) (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 76 (* 
h1 h1 h1) (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 44 (* h1 h1 
h1) (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 11 (* h1 h1 h1) (* h4
 h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* (* h1 h1 h1) (* h4 h4 h4 h4) (* 
h5 h5) h6 (* j2 j2 j2 j2)) (* 18 (* h1 h1 h1) (* h4 h4 h4 h4) h5 (* h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 48 (* h1 h1 h1) (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2
 j2 j2 j2 j2 j2)) (* 35 (* h1 h1 h1) (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2
 j2 j2)) (* 10 (* h1 h1 h1) (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
(* h1 h1 h1) (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 40 (* h1 h1 h1) 
(* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 208 (* h1 h1 h1)
 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 400 (* h1 h1 h1) 
(* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 352 (* h1 h1 h1) (* h4
 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 146 (* h1 h1 h1) (* h4 h4 h4) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 28 (* h1 h1 h1) (* h4 h4 h4) (* h5 h5 h5)
 h6 (* j2 j2 j2 j2)) (* 2 (* h1 h1 h1) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)
) (* 52 (* h1 h1 h1) (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
 j2)) (* 326 (* h1 h1 h1) (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 700 (* h1 h1 h1) (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 649 (* h1 h1 h1) (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 279 (* h1 h1 h1) (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 55 (* h1 h1 h1) (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 4 (* h1 
h1 h1) (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 42 (* h1 h1 h1) (* h4 
h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 170 (* h1 h1 h1) (* h4 h4
 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 229 (* h1 h1 h1) (* h4 h4 h4) 
h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 119 (* h1 h1 h1) (* h4 h4 h4) h5 (* h6
 h6 h6) (* j2 j2 j2 j2 j2)) (* 26 (* h1 h1 h1) (* h4 h4 h4) h5 (* h6 h6 h6) (* 
j2 j2 j2 j2)) (* 2 (* h1 h1 h1) (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 16
 (* h1 h1 h1) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
104 (* h1 h1 h1) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
268 (* h1 h1 h1) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 348 
(* h1 h1 h1) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 240 (* h1 h1
 h1) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 86 (* h1 h1 h1) (* h4 
h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 15 (* h1 h1 h1) (* h4 h4) (* h5 h5 h5
 h5) h6 (* j2 j2 j2)) (* (* h1 h1 h1) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2)) 
(* 116 (* h1 h1 h1) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 708 (* h1 h1 h1) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 1696 (* h1 h1 h1) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 2028 (* h1 h1 h1) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 1279 (* h1 h1 h1) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 417 (* h1 h1 h1) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 66 (* 
h1 h1 h1) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 4 (* h1 h1 h1) (* h4
 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 72 (* h1 h1 h1) (* h4 h4) (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 506 (* h1 h1 h1) (* h4 h4) (* h5
 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1354 (* h1 h1 h1) (* h4 h4) 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1763 (* h1 h1 h1) (* h4 h4) 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1183 (* h1 h1 h1) (* h4 h4) (* 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 401 (* h1 h1 h1) (* h4 h4) (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2)) (* 65 (* h1 h1 h1) (* h4 h4) (* h5 h5) (* h6 h6 h6
) (* j2 j2 j2)) (* 4 (* h1 h1 h1) (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2)) 
(* 24 (* h1 h1 h1) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
116 (* h1 h1 h1) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 210 
(* h1 h1 h1) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 178 (* h1 h1
 h1) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 73 (* h1 h1 h1) (* h4 
h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 14 (* h1 h1 h1) (* h4 h4) h5 (* h6 h6
 h6 h6) (* j2 j2 j2)) (* (* h1 h1 h1) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2)) 
(* 32 (* h1 h1 h1) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 224 (* h1 h1 h1) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 648 (* h1 h1 h1) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
1000 (* h1 h1 h1) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 886 (* 
h1 h1 h1) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 452 (* h1 h1 h1) 
h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 127 (* h1 h1 h1) h4 (* h5 h5 h5
 h5) (* h6 h6) (* j2 j2 j2)) (* 18 (* h1 h1 h1) h4 (* h5 h5 h5 h5) (* h6 h6) (* 
j2 j2)) (* (* h1 h1 h1) h4 (* h5 h5 h5 h5) (* h6 h6) j2) (* 72 (* h1 h1 h1) h4 
(* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 492 (* h1 h1 h1) h4
 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1390 (* h1 h1 h1) h4 
(* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2098 (* h1 h1 h1) h4 (* 
h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1823 (* h1 h1 h1) h4 (* h5 h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 916 (* h1 h1 h1) h4 (* h5 h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2)) (* 255 (* h1 h1 h1) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 
j2 j2)) (* 36 (* h1 h1 h1) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 2 (* h1 h1
 h1) h4 (* h5 h5 h5) (* h6 h6 h6) j2) (* 32 (* h1 h1 h1) h4 (* h5 h5) (* h6 h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 224 (* h1 h1 h1) h4 (* h5 h5) (* h6 h6
 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 648 (* h1 h1 h1) h4 (* h5 h5) (* h6 h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1000 (* h1 h1 h1) h4 (* h5 h5) (* h6 h6 h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 886 (* h1 h1 h1) h4 (* h5 h5) (* h6 h6 h6 h6) (* 
j2 j2 j2 j2 j2)) (* 452 (* h1 h1 h1) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2
)) (* 127 (* h1 h1 h1) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 18 (* h1 h1
 h1) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* (* h1 h1 h1) h4 (* h5 h5) (* h6 
h6 h6 h6) j2) (* 3072 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2 
j2 j2 j2)) (* 7680 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2 j2 
j2)) (* 6080 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2 j2)) (* 
2048 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2)) (* 304 (* h1 h1)
 (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2)) (* 16 (* h1 h1) (* h2 h2 h2 h2) 
(* h3 h3 h3) h5 (* j2 j2)) (* 2048 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h6 (* 
j2 j2 j2 j2 j2 j2 j2)) (* 6656 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h6 (* j2 
j2 j2 j2 j2 j2)) (* 6272 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2 
j2 j2)) (* 2528 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2 j2)) (* 
464 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2)) (* 32 (* h1 h1) (* 
h2 h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2)) (* 2304 (* h1 h1) (* h2 h2 h2 h2) (* h3 
h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6336 (* h1 h1) (* h2 h2 h2 h2) (* h3 
h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 5856 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) 
h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 2352 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h5 
(* j2 j2 j2 j2 j2)) (* 408 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2
 j2)) (* 24 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2)) (* 1024 (* 
h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4608 (* 
h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 5440 (* h1 
h1) (* h2 h2 h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2)) (* 2688 (* h1 h1) (* 
h2 h2 h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 592 (* h1 h1) (* h2 h2 h2 h2
) (* h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 48 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 
h6 (* j2 j2 j2)) (* 1536 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 5760 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* j2 
j2 j2 j2 j2 j2 j2)) (* 8128 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* j2 
j2 j2 j2 j2 j2)) (* 5472 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 
j2 j2 j2)) (* 1840 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2)
) (* 288 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2)) (* 16 (* h1
 h1) (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* j2 j2)) (* 3328 (* h1 h1) (* h2 h2 
h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 12224 (* h1 h1) (* h2 h2 
h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 16992 (* h1 h1) (* h2 h2 h2 
h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 11568 (* h1 h1) (* h2 h2 h2 h2) 
(* h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 4088 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) 
h5 h6 (* j2 j2 j2 j2)) (* 712 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 h6 (* j2 j2
 j2)) (* 48 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 h6 (* j2 j2)) (* 1024 (* h1 
h1) (* h2 h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4608 (* 
h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 7488 (* 
h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 5760 (* h1 
h1) (* h2 h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2256 (* h1 h1) 
(* h2 h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 432 (* h1 h1) (* h2 h2 
h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2)) (* 32 (* h1 h1) (* h2 h2 h2 h2) (* h3 
h3) (* h6 h6) (* j2 j2)) (* 576 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 2304 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 3552 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 2688 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* j2 
j2 j2 j2 j2 j2)) (* 1044 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 
j2 j2)) (* 192 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2)) (* 12 
(* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2)) (* 704 (* h1 h1) (* h2 
h2 h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3520 (* h1 h1) (* h2 h2
 h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6400 (* h1 h1) (* h2 h2 h2 
h2) h3 h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 5616 (* h1 h1) (* h2 h2 h2 h2) h3 
h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 2564 (* h1 h1) (* h2 h2 h2 h2) h3 h4 h5 h6 
(* j2 j2 j2 j2 j2)) (* 584 (* h1 h1) (* h2 h2 h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2)
) (* 52 (* h1 h1) (* h2 h2 h2 h2) h3 h4 h5 h6 (* j2 j2 j2)) (* 64 (* h1 h1) (* 
h2 h2 h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 624 (* h1 h1) 
(* h2 h2 h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1736 (* h1 h1) 
(* h2 h2 h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1940 (* h1 h1) (* 
h2 h2 h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1026 (* h1 h1) (* h2 h2 
h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 256 (* h1 h1) (* h2 h2 h2 h2) h3 
h4 (* h6 h6) (* j2 j2 j2 j2)) (* 24 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h6 h6) 
(* j2 j2 j2)) (* 192 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2
 j2 j2 j2 j2)) (* 960 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 1952 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2 
j2 j2 j2)) (* 2080 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2 
j2)) (* 1244 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 
412 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 68 (* h1 h1) 
(* h2 h2 h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2)) (* 4 (* h1 h1) (* h2 h2 h2 h2) h3 
(* h5 h5 h5) (* j2 j2)) (* 864 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 4192 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 8352 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2)) (* 8840 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) h6 (* j2 
j2 j2 j2 j2 j2)) (* 5354 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 
j2 j2)) (* 1848 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 
334 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2)) (* 24 (* h1 h1) (* 
h2 h2 h2 h2) h3 (* h5 h5) h6 (* j2 j2)) (* 640 (* h1 h1) (* h2 h2 h2 h2) h3 h5 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3312 (* h1 h1) (* h2 h2 h2 h2) h3 
h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 7048 (* h1 h1) (* h2 h2 h2 h2) h3 
h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 7956 (* h1 h1) (* h2 h2 h2 h2) h3 h5 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 5126 (* h1 h1) (* h2 h2 h2 h2) h3 h5 (* h6 
h6) (* j2 j2 j2 j2 j2)) (* 1880 (* h1 h1) (* h2 h2 h2 h2) h3 h5 (* h6 h6) (* j2 
j2 j2 j2)) (* 362 (* h1 h1) (* h2 h2 h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2)) (* 28 
(* h1 h1) (* h2 h2 h2 h2) h3 h5 (* h6 h6) (* j2 j2)) (* 64 (* h1 h1) (* h2 h2 h2
 h2) h3 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 432 (* h1 h1) (* h2 h2 
h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1144 (* h1 h1) (* h2 h2 
h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1532 (* h1 h1) (* h2 h2 h2 
h2) h3 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1126 (* h1 h1) (* h2 h2 h2 h2) h3 
(* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 458 (* h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6 h6
) (* j2 j2 j2 j2)) (* 96 (* h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2))
 (* 8 (* h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6 h6) (* j2 j2)) (* 128 (* h1 h1) (* 
h2 h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 704 (* h1 h1)
 (* h2 h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1600 (* h1 
h1) (* h2 h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1952 (* h1 
h1) (* h2 h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1384 (* h1 h1) 
(* h2 h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 572 (* h1 h1) (* h2 h2
 h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 128 (* h1 h1) (* h2 h2 h2 h2) h4 
(* h5 h5) h6 (* j2 j2 j2 j2)) (* 12 (* h1 h1) (* h2 h2 h2 h2) h4 (* h5 h5) h6 
(* j2 j2 j2)) (* 32 (* h1 h1) (* h2 h2 h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 288 (* h1 h1) (* h2 h2 h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 880 (* h1 h1) (* h2 h2 h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 1312 (* h1 h1) (* h2 h2 h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 1074 (* h1 h1) (* h2 h2 h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 494 (* h1 h1) (* h2 h2 h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
120 (* h1 h1) (* h2 h2 h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 12 (* h1 h1) 
(* h2 h2 h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 64 (* h1 h1) (* h2 h2 h2 h2) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 384 (* h1 h1) (* h2 h2 h2 
h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 992 (* h1 h1) (* h2 h2 h2
 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1440 (* h1 h1) (* h2 h2 h2 
h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1284 (* h1 h1) (* h2 h2 h2 h2) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 720 (* h1 h1) (* h2 h2 h2 h2) (* h5 h5
 h5) h6 (* j2 j2 j2 j2 j2)) (* 248 (* h1 h1) (* h2 h2 h2 h2) (* h5 h5 h5) h6 (* 
j2 j2 j2 j2)) (* 48 (* h1 h1) (* h2 h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 4
 (* h1 h1) (* h2 h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2)) (* 96 (* h1 h1) (* h2 h2 
h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 608 (* h1 h1) 
(* h2 h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1648 (* 
h1 h1) (* h2 h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2496 
(* h1 h1) (* h2 h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2310 
(* h1 h1) (* h2 h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1338 (* 
h1 h1) (* h2 h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 474 (* h1 h1) 
(* h2 h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 94 (* h1 h1) (* h2 h2 h2
 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 8 (* h1 h1) (* h2 h2 h2 h2) (* h5 h5) 
(* h6 h6) (* j2 j2)) (* 32 (* h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2
 j2 j2 j2 j2 j2 j2 j2)) (* 224 (* h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 656 (* h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 1056 (* h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 1026 (* h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 618 (* h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2
)) (* 226 (* h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 46 (* h1
 h1) (* h2 h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 4 (* h1 h1) (* h2 h2 h2 h2
) h5 (* h6 h6 h6) (* j2 j2)) (* 3072 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h5 
(* j2 j2 j2 j2 j2 j2 j2)) (* 9216 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* 
j2 j2 j2 j2 j2 j2)) (* 9152 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2 
j2 j2 j2)) (* 3552 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2 j2 j2)) 
(* 576 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2 j2)) (* 32 (* h1 h1) 
(* h2 h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2)) (* 2048 (* h1 h1) (* h2 h2 h2) (* h3 
h3 h3 h3) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 7680 (* h1 h1) (* h2 h2 h2) (* h3 h3 
h3 h3) h6 (* j2 j2 j2 j2 j2 j2)) (* 9088 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) 
h6 (* j2 j2 j2 j2 j2)) (* 4256 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h6 (* j2 
j2 j2 j2)) (* 864 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2 j2)) (* 64 
(* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2)) (* 9088 (* h1 h1) (* h2 h2 
h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 33888 (* h1 h1) (* h2 h2 
h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 44864 (* h1 h1) (* h2 h2 h2)
 (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 26072 (* h1 h1) (* h2 h2 h2) (* h3
 h3 h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 7280 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4
 h5 (* j2 j2 j2 j2)) (* 960 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 
j2)) (* 48 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2)) (* 3584 (* h1 h1
) (* h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 20480 (* h1 h1
) (* h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 37088 (* h1 h1) 
(* h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2)) (* 27088 (* h1 h1) (* h2 
h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 9336 (* h1 h1) (* h2 h2 h2) (* 
h3 h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 1528 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 
h6 (* j2 j2 j2)) (* 96 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2)) (* 
4704 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 22320 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2))
 (* 39688 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) 
(* 33636 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 
14584 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 3196 (* 
h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2)) (* 324 (* h1 h1) (* h2 
h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2)) (* 12 (* h1 h1) (* h2 h2 h2) (* h3 h3 
h3) (* h5 h5) j2) (* 10688 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 49328 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2
 j2 j2 j2 j2)) (* 85664 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2
 j2 j2)) (* 70772 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) 
(* 30284 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 6720 (* 
h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2)) (* 700 (* h1 h1) (* h2 h2 
h2) (* h3 h3 h3) h5 h6 (* j2 j2)) (* 24 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 
h6 j2) (* 3584 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 19712 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2
 j2 j2 j2)) (* 40928 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 41056 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2
 j2)) (* 21568 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2)) 
(* 6048 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2)) (* 856 (* h1
 h1) (* h2 h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2)) (* 48 (* h1 h1) (* h2 h2 h2)
 (* h3 h3 h3) (* h6 h6) j2) (* 1088 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h4 h4) 
h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8864 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* 
h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 17408 (* h1 h1) (* h2 h2 h2) (* h3 h3)
 (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 12712 (* h1 h1) (* h2 h2 h2) (* h3 h3
) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 4164 (* h1 h1) (* h2 h2 h2) (* h3 h3) 
(* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 632 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h4 
h4) h5 (* j2 j2 j2 j2)) (* 36 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* 
j2 j2 j2)) (* 192 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 3248 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 12240 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h4 h4) h6 (* j2
 j2 j2 j2 j2 j2 j2)) (* 12188 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h4 h4) h6 (* 
j2 j2 j2 j2 j2 j2)) (* 5100 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 
j2 j2 j2 j2)) (* 980 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 
j2)) (* 72 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2 j2)) (* 3296 
(* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 19168 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 41712 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2
 j2)) (* 43824 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 
j2)) (* 23894 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) 
(* 6766 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 924 
(* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 48 (* h1 h1) (* 
h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2)) (* 5200 (* h1 h1) (* h2 h2 h2) (* h3
 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 36600 (* h1 h1) (* h2 h2 h2) 
(* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 86596 (* h1 h1) (* h2 h2 h2) 
(* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 94354 (* h1 h1) (* h2 h2 h2) (* 
h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 53978 (* h1 h1) (* h2 h2 h2) (* h3 h3)
 h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 16740 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 h6
 (* j2 j2 j2 j2)) (* 2656 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2)
) (* 168 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2)) (* 576 (* h1 h1) 
(* h2 h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8016 (* 
h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 28736
 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
39172 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
25720 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 8720 
(* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 1464 (* h1 h1)
 (* h2 h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2)) (* 96 (* h1 h1) (* h2 h2 h2) 
(* h3 h3) h4 (* h6 h6) (* j2 j2)) (* 768 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 5424 (* h1 h1) (* h2 h2 h2) (* h3 h3) 
(* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 14984 (* h1 h1) (* h2 h2 h2) (* h3 
h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 21124 (* h1 h1) (* h2 h2 h2) (* h3
 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 16390 (* h1 h1) (* h2 h2 h2) (* h3 
h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 6984 (* h1 h1) (* h2 h2 h2) (* h3 h3) 
(* h5 h5 h5) (* j2 j2 j2 j2)) (* 1552 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5 
h5) (* j2 j2 j2)) (* 160 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2)
) (* 6 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) j2) (* 4448 (* h1 h1) (* h2
 h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 28016 (* h1 h1
) (* h2 h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 70224 (* 
h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 91316 
(* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 67210 
(* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 28478 (* h1
 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 6680 (* h1 h1) (* 
h2 h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 766 (* h1 h1) (* h2 h2 h2) (* 
h3 h3) (* h5 h5) h6 (* j2 j2)) (* 30 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) 
h6 j2) (* 3920 (* h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 26984 (* h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 71788 (* h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 97886 (* h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* j2
 j2 j2 j2 j2 j2)) (* 75868 (* h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 
j2 j2 j2 j2)) (* 34660 (* h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2
 j2)) (* 9170 (* h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 
1282 (* h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2)) (* 72 (* h1 h1) 
(* h2 h2 h2) (* h3 h3) h5 (* h6 h6) j2) (* 384 (* h1 h1) (* h2 h2 h2) (* h3 h3) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3936 (* h1 h1) (* h2 h2 h2) (* 
h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 13792 (* h1 h1) (* h2 h2 h2)
 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 22920 (* h1 h1) (* h2 h2 h2
) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 20512 (* h1 h1) (* h2 h2 h2) 
(* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 10344 (* h1 h1) (* h2 h2 h2) (* h3
 h3) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 2908 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* 
h6 h6 h6) (* j2 j2 j2)) (* 420 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6 h6) (* 
j2 j2)) (* 24 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6 h6) j2) (* 128 (* h1 h1)
 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2064 
(* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 6696 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 9028 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2
)) (* 5934 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) 
(* 1962 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 306
 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 18 (* h1 h1) 
(* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 128 (* h1 h1) (* h2 h2 h2) 
h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1920 (* h1 h1) (* h2 h2
 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8992 (* h1 h1) (* h2 
h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 15912 (* h1 h1) (* h2 
h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 13044 (* h1 h1) (* h2 h2 
h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 5366 (* h1 h1) (* h2 h2 h2) h3 
(* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 1075 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) 
h5 h6 (* j2 j2 j2 j2)) (* 84 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 
j2)) (* 64 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2
 j2 j2)) (* 1128 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 3864 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 j2 j2 j2
 j2 j2 j2)) (* 4234 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 j2 j2 j2
 j2 j2)) (* 2024 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2
)) (* 440 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 36 
(* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 64 (* h1 h1) (* 
h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1504 (* h1 h1
) (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 6384 (* h1 
h1) (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 11752 (* h1 
h1) (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 11280 (* h1 h1)
 (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 5920 (* h1 h1) (* h2 
h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 1664 (* h1 h1) (* h2 h2 h2) h3 
h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 228 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5 h5
) (* j2 j2 j2)) (* 12 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2)) (* 
928 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (* 8840 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2
)) (* 30124 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 50786 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 47583 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
25771 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 7955 (* 
h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 1287 (* h1 h1) (* h2 
h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2)) (* 84 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5
 h5) h6 (* j2 j2)) (* 384 (* h1 h1) (* h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 4944 (* h1 h1) (* h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 20520 (* h1 h1) (* h2 h2 h2) h3 h4 h5 (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 39972 (* h1 h1) (* h2 h2 h2) h3 h4 h5 (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 41882 (* h1 h1) (* h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 24790 (* h1 h1) (* h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 
j2 j2)) (* 8221 (* h1 h1) (* h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 
1409 (* h1 h1) (* h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2)) (* 96 (* h1 h1) (* 
h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2)) (* 96 (* h1 h1) (* h2 h2 h2) h3 h4 (* h6
 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1328 (* h1 h1) (* h2 h2 h2) h3 h4 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4696 (* h1 h1) (* h2 h2 h2) h3 h4 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 6932 (* h1 h1) (* h2 h2 h2) h3 h4 (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 5020 (* h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2)) (* 1868 (* h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2 
j2 j2)) (* 340 (* h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2 j2)) (* 24 (* 
h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2)) (* 96 (* h1 h1) (* h2 h2 h2) 
h3 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 528 (* h1 h1) (* h2 h2 h2)
 h3 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1192 (* h1 h1) (* h2 h2 h2) 
h3 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1420 (* h1 h1) (* h2 h2 h2) h3 
(* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 952 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5
 h5 h5) (* j2 j2 j2 j2 j2)) (* 352 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* 
j2 j2 j2 j2)) (* 64 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* j2 j2 j2)) (* 4
 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* j2 j2)) (* 384 (* h1 h1) (* h2 h2 
h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3584 (* h1 h1) (* 
h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 12880 (* h1 h1) 
(* h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 24200 (* h1 h1) 
(* h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 26492 (* h1 h1) (* 
h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 17526 (* h1 h1) (* h2 h2 
h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 6946 (* h1 h1) (* h2 h2 h2) h3 (* 
h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 1556 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) h6 
(* j2 j2 j2)) (* 170 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2)) (* 6 
(* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) h6 j2) (* 672 (* h1 h1) (* h2 h2 h2) h3 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 6376 (* h1 h1) (* h2 
h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 23604 (* h1 h1)
 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 46234 (* h1
 h1) (* h2 h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 53533 (* 
h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 38225 (* h1
 h1) (* h2 h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 16866 (* h1 h1) 
(* h2 h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 4430 (* h1 h1) (* h2 h2 
h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 626 (* h1 h1) (* h2 h2 h2) h3 (* h5 
h5) (* h6 h6) (* j2 j2)) (* 36 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* h6 h6) j2)
 (* 256 (* h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 2720 (* h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 10688 (* h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 21768 (* h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 25928 (* h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 18904 (* h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 8460 
(* h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 2238 (* h1 h1) (* 
h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 316 (* h1 h1) (* h2 h2 h2) h3 h5 
(* h6 h6 h6) (* j2 j2)) (* 18 (* h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6 h6) j2) (* 
32 (* h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
232 (* h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
672 (* h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1002 
(* h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 828 (* h1 h1
) (* h2 h2 h2) h3 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 378 (* h1 h1) (* h2 h2 
h2) h3 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 88 (* h1 h1) (* h2 h2 h2) h3 (* h6 h6
 h6 h6) (* j2 j2 j2)) (* 8 (* h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6 h6) (* j2 j2)) 
(* 224 (* h1 h1) (* h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 1408 (* h1 h1) (* h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 3440 (* h1 h1) (* h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 4288 (* h1 h1) (* h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2)) (* 2966 (* h1 h1) (* h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 
j2 j2 j2 j2)) (* 1144 (* h1 h1) (* h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 
j2 j2)) (* 228 (* h1 h1) (* h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) 
(* 18 (* h1 h1) (* h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 16 (* h1 h1
) (* h2 h2 h2) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 392 
(* h1 h1) (* h2 h2 h2) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 1588 (* h1 h1) (* h2 h2 h2) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 2654 (* h1 h1) (* h2 h2 h2) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2
)) (* 2218 (* h1 h1) (* h2 h2 h2) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 974 (* h1 h1) (* h2 h2 h2) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 213 
(* h1 h1) (* h2 h2 h2) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 18 (* h1 h1) 
(* h2 h2 h2) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 240 (* h1 h1) (* h2 h2 h2) 
h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1576 (* h1 h1) (* h2 h2
 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4340 (* h1 h1) (* h2 
h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6526 (* h1 h1) (* h2 
h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 5840 (* h1 h1) (* h2 h2 
h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 3172 (* h1 h1) (* h2 h2 h2) h4 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 1016 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5 
h5) h6 (* j2 j2 j2 j2)) (* 174 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5 h5) h6 (* j2 
j2 j2)) (* 12 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2)) (* 448 (* h1 
h1) (* h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
2920 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2
)) (* 8068 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2
 j2)) (* 12258 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 11123 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2
 j2)) (* 6131 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 1991 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 345 
(* h1 h1) (* h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 24 (* h1 h1) (* 
h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 32 (* h1 h1) (* h2 h2 h2) h4 h5 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 512 (* h1 h1) (* h2 h2 h2) h4
 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2096 (* h1 h1) (* h2 h2 h2) 
h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4008 (* h1 h1) (* h2 h2 h2) 
h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4222 (* h1 h1) (* h2 h2 h2) h4 
h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2578 (* h1 h1) (* h2 h2 h2) h4 h5 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 901 (* h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6 h6) 
(* j2 j2 j2 j2)) (* 165 (* h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2)) 
(* 12 (* h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2)) (* 32 (* h1 h1) (* h2
 h2 h2) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 208 (* h1 h1) 
(* h2 h2 h2) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 584 (* h1 h1)
 (* h2 h2 h2) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 924 (* h1 h1) 
(* h2 h2 h2) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 900 (* h1 h1) (* h2
 h2 h2) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 552 (* h1 h1) (* h2 h2 h2) 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 208 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5
 h5) h6 (* j2 j2 j2 j2)) (* 44 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5 h5) h6 (* j2 
j2 j2)) (* 4 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 224 (* h1 
h1) (* h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
1552 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2
)) (* 4664 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2
 j2)) (* 7956 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2
 j2)) (* 8460 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2
)) (* 5790 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
2536 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 680 (* h1
 h1) (* h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 100 (* h1 h1) (* h2 h2
 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 6 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5) 
(* h6 h6) j2) (* 224 (* h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 1552 (* h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4664 (* h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 7956 (* h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 8460 (* h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 5790 (* h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2)) (* 2536 (* h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2)) (* 680 (* h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 
j2)) (* 100 (* h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 6 (* h1 
h1) (* h2 h2 h2) (* h5 h5) (* h6 h6 h6) j2) (* 16 (* h1 h1) (* h2 h2 h2) h5 (* 
h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 120 (* h1 h1) (* h2 h2 h2) h5
 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 380 (* h1 h1) (* h2 h2 h2) 
h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 666 (* h1 h1) (* h2 h2 h2) h5
 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 708 (* h1 h1) (* h2 h2 h2) h5 (* 
h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 468 (* h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6
 h6) (* j2 j2 j2 j2 j2)) (* 188 (* h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6 h6) (* j2 
j2 j2 j2)) (* 42 (* h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 4 
(* h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2)) (* 6784 (* h1 h1) (* h2 h2)
 (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 25184 (* h1 h1) (* h2 h2)
 (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 34864 (* h1 h1) (* h2 h2) 
(* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 22736 (* h1 h1) (* h2 h2) (* h3 
h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 7328 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) 
h4 h5 (* j2 j2 j2 j2)) (* 1120 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 
j2 j2)) (* 64 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2)) (* 2560 (* h1
 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 15104 (* h1
 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 28064 (* h1 h1
) (* h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2)) (* 23136 (* h1 h1) (* 
h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 9248 (* h1 h1) (* h2 h2) (* 
h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 1760 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) 
h4 h6 (* j2 j2 j2)) (* 128 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2)) 
(* 3168 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 15264 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 
j2)) (* 28056 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2
)) (* 24960 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) 
(* 11560 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 2896 
(* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2)) (* 352 (* h1 h1) (* 
h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2)) (* 16 (* h1 h1) (* h2 h2) (* h3 h3 
h3 h3) (* h5 h5) j2) (* 7360 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 34640 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 
j2 j2 j2 j2 j2)) (* 62568 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 
j2 j2 j2)) (* 54488 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2)
) (* 24368 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 5840 
(* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2)) (* 704 (* h1 h1) (* h2 
h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2)) (* 32 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) 
h5 h6 j2) (* 2560 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 14336 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2
 j2 j2 j2 j2)) (* 31008 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 33456 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2
 j2 j2)) (* 19440 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2))
 (* 6144 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2)) (* 992 (* 
h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2)) (* 64 (* h1 h1) (* h2 h2) 
(* h3 h3 h3 h3) (* h6 h6) j2) (* 3376 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4)
 h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 21312 (* h1 h1) (* h2 h2) (* h3 h3 h3) 
(* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 44236 (* h1 h1) (* h2 h2) (* h3 h3 
h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 40244 (* h1 h1) (* h2 h2) (* h3 h3
 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 17820 (* h1 h1) (* h2 h2) (* h3 h3 
h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 4164 (* h1 h1) (* h2 h2) (* h3 h3 h3) 
(* h4 h4) h5 (* j2 j2 j2 j2)) (* 496 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) 
h5 (* j2 j2 j2)) (* 24 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2)) 
(* 384 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 6496 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 26080 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2
 j2 j2)) (* 34536 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 
j2 j2)) (* 20032 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2
)) (* 5856 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2)) (* 848
 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2)) (* 48 (* h1 h1) (* 
h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2)) (* 5696 (* h1 h1) (* h2 h2) (* h3 h3
 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 35512 (* h1 h1) (* h2 h2) 
(* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 84632 (* h1 h1) (* h2 
h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 99374 (* h1 h1) (* h2
 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 62096 (* h1 h1) (* h2 
h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 21202 (* h1 h1) (* h2 h2) 
(* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 3882 (* h1 h1) (* h2 h2) (* h3 h3 
h3) h4 (* h5 h5) (* j2 j2 j2)) (* 352 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h5 
h5) (* j2 j2)) (* 12 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) j2) (* 10688 
(* h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
74528 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
190016 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
233944 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 
153388 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 56532 
(* h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 11672 (* h1 h1) 
(* h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 1228 (* h1 h1) (* h2 h2) (* h3 
h3 h3) h4 h5 h6 (* j2 j2)) (* 48 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 h6 j2) 
(* 960 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 13072 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 52264 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 86792 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2
 j2 j2)) (* 72040 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 32232 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 
7856 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2)) (* 976 (* h1 h1
) (* h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2)) (* 48 (* h1 h1) (* h2 h2) (* h3
 h3 h3) h4 (* h6 h6) j2) (* 960 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 7200 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 21184 (* h1 h1) (* h2 h2) (* h3 h3 h3) 
(* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 31728 (* h1 h1) (* h2 h2) (* h3 h3 h3)
 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 26196 (* h1 h1) (* h2 h2) (* h3 h3 h3) 
(* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 12046 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5
 h5 h5) (* j2 j2 j2 j2)) (* 2942 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) 
(* j2 j2 j2)) (* 352 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2)) 
(* 16 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) j2) (* 7136 (* h1 h1) (* h2 
h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 48680 (* h1 h1)
 (* h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 132320 (* 
h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 185626 
(* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 146008 
(* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 65962 (* h1
 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 16684 (* h1 h1) (* 
h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 2160 (* h1 h1) (* h2 h2) (* h3
 h3 h3) (* h5 h5) h6 (* j2 j2)) (* 110 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5
) h6 j2) (* 7120 (* h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2 j2)) (* 51536 (* h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 147060 (* h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 217112 (* h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 181744 (* h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* 88920 (* h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2
 j2 j2 j2)) (* 25148 (* h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2))
 (* 3800 (* h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2)) (* 236 (* h1 
h1) (* h2 h2) (* h3 h3 h3) h5 (* h6 h6) j2) (* 576 (* h1 h1) (* h2 h2) (* h3 h3 
h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 5488 (* h1 h1) (* h2 h2) (* 
h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 19480 (* h1 h1) (* h2 h2)
 (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 34552 (* h1 h1) (* h2 h2
) (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 34128 (* h1 h1) (* h2 h2) 
(* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 19328 (* h1 h1) (* h2 h2) (* h3
 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 6112 (* h1 h1) (* h2 h2) (* h3 h3 h3) 
(* h6 h6 h6) (* j2 j2 j2)) (* 992 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6 h6) 
(* j2 j2)) (* 64 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6 h6) j2) (* 96 (* h1 
h1) (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
2016 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2
)) (* 6904 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2
 j2)) (* 9028 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2
 j2)) (* 5282 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2
)) (* 1536 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 
216 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 12 (* h1 
h1) (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 192 (* h1 h1) (* h2 h2)
 (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2616 (* h1 h1) (* 
h2 h2) (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6556 (* h1 h1) 
(* h2 h2) (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 5452 (* h1 h1) 
(* h2 h2) (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 2052 (* h1 h1) (* 
h2 h2) (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 360 (* h1 h1) (* h2 h2) 
(* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2)) (* 24 (* h1 h1) (* h2 h2) (* h3 h3) 
(* h4 h4 h4) h6 (* j2 j2 j2)) (* 576 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8160 (* h1 h1) (* h2 h2) (* h3 h3) 
(* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 30048 (* h1 h1) (* h2 h2)
 (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 48360 (* h1 h1) 
(* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 39608 (* h1
 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 17566 (* 
h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 4146 (* h1
 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 496 (* h1 h1) 
(* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 24 (* h1 h1) (* h2 h2) 
(* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 672 (* h1 h1) (* h2 h2) (* h3 h3) 
(* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 11568 (* h1 h1) (* h2 h2) 
(* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 52824 (* h1 h1) (* 
h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 98920 (* h1 h1)
 (* h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 90066 (* h1 h1
) (* h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 44592 (* h1 h1) 
(* h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 12194 (* h1 h1) (* h2
 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 1718 (* h1 h1) (* h2 h2) (* 
h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 96 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 
h4) h5 h6 (* j2 j2)) (* 640 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8664 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 28092 (* h1 h1) (* h2 h2) (* h3 h3) 
(* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 34028 (* h1 h1) (* h2 h2) (* h3
 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 19652 (* h1 h1) (* h2 h2) (* 
h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 5808 (* h1 h1) (* h2 h2) (* h3
 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 848 (* h1 h1) (* h2 h2) (* h3 h3) 
(* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 48 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) 
(* h6 h6) (* j2 j2)) (* 256 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4912 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5 
h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 22432 (* h1 h1) (* h2 h2) (* h3 h3) h4 
(* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 46244 (* h1 h1) (* h2 h2) (* h3 h3)
 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 50752 (* h1 h1) (* h2 h2) (* h3 h3
) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 31150 (* h1 h1) (* h2 h2) (* h3 h3) 
h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 10649 (* h1 h1) (* h2 h2) (* h3 h3) h4 
(* h5 h5 h5) (* j2 j2 j2 j2)) (* 1945 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5 
h5) (* j2 j2 j2)) (* 176 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2)
) (* 6 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) j2) (* 2400 (* h1 h1) (* h2
 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 27032 (* h1
 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
107108 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 208990 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2)) (* 227217 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 
j2)) (* 144761 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2))
 (* 54219 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 
11539 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 1269 (* h1 
h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 54 (* h1 h1) (* h2 h2) (* 
h3 h3) h4 (* h5 h5) h6 j2) (* 1248 (* h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 18464 (* h1 h1) (* h2 h2) (* h3 h3) h4 h5
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 86312 (* h1 h1) (* h2 h2) (* h3 h3
) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 188048 (* h1 h1) (* h2 h2) (* 
h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 221908 (* h1 h1) (* h2 h2) 
(* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 153122 (* h1 h1) (* h2 h2) 
(* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 62990 (* h1 h1) (* h2 h2) (* h3
 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 15012 (* h1 h1) (* h2 h2) (* h3 h3) h4 
h5 (* h6 h6) (* j2 j2 j2)) (* 1890 (* h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* h6 h6)
 (* j2 j2)) (* 96 (* h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* h6 h6) j2) (* 608 (* h1
 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 7288
 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
26284 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 42216 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 35092 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
15904 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 3912 (* 
h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2)) (* 488 (* h1 h1) (* h2 
h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2)) (* 24 (* h1 h1) (* h2 h2) (* h3 h3) h4 
(* h6 h6 h6) j2) (* 288 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 1872 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 5064 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 7356 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2)) (* 6140 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* 
j2 j2 j2 j2 j2)) (* 2908 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 
j2 j2)) (* 728 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 88
 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2)) (* 4 (* h1 h1) (* h2 
h2) (* h3 h3) (* h5 h5 h5 h5) j2) (* 832 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 9088 (* h1 h1) (* h2 h2) (* h3 h3) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 37384 (* h1 h1) (* h2 h2) (* 
h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 79672 (* h1 h1) (* h2 h2)
 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 98594 (* h1 h1) (* h2 h2
) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 73702 (* h1 h1) (* h2 h2) 
(* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 33000 (* h1 h1) (* h2 h2) (* h3
 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 8370 (* h1 h1) (* h2 h2) (* h3 h3) (* 
h5 h5 h5) h6 (* j2 j2 j2)) (* 1081 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) h6
 (* j2 j2)) (* 55 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) h6 j2) (* 1632 (* 
h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 18008 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 75996 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 167834 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 217601 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 173025 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 84368 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2)) (* 24207 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) 
(* h6 h6) (* j2 j2 j2)) (* 3704 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6
) (* j2 j2)) (* 231 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) j2) (* 672
 (* h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 8384 (* h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 37920 (* h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 87384 (* h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 116102 (* h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 93552 (* h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2
 j2 j2)) (* 46084 (* h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2))
 (* 13422 (* h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 2098 
(* h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 134 (* h1 h1) (* h2 
h2) (* h3 h3) h5 (* h6 h6 h6) j2) (* 160 (* h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1368 (* h1 h1) (* h2 h2) (* h3 h3) (* 
h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4652 (* h1 h1) (* h2 h2) (* h3 h3) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 8200 (* h1 h1) (* h2 h2) (* h3 h3) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 8180 (* h1 h1) (* h2 h2) (* h3 h3) (* 
h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 4704 (* h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 
h6 h6) (* j2 j2 j2 j2)) (* 1512 (* h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6 h6) 
(* j2 j2 j2)) (* 248 (* h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6 h6) (* j2 j2)) 
(* 16 (* h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6 h6) j2) (* 224 (* h1 h1) (* h2 
h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1572 (* h1 
h1) (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3956 
(* h1 h1) (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
4613 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
2652 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 768
 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 108 (* h1 
h1) (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 6 (* h1 h1) (* h2 h2
) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 64 (* h1 h1) (* h2 h2) h3 (* h4 h4 
h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1108 (* h1 h1) (* h2 h2) h3 (* 
h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 5028 (* h1 h1) (* h2 h2) h3 
(* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 8619 (* h1 h1) (* h2 h2) h3 
(* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 6573 (* h1 h1) (* h2 h2) h3 (* 
h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 2453 (* h1 h1) (* h2 h2) h3 (* h4 h4 
h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 440 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) h5 h6 
(* j2 j2 j2 j2)) (* 30 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2)) 
(* 16 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 424 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 1848 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 1964 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 860 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 168 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 12 (* 
h1 h1) (* h2 h2) h3 (* h4 h4 h4) (* h6 h6) (* j2 j2 j2)) (* 240 (* h1 h1) (* h2 
h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2360 (* h1 
h1) (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 7796 
(* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
12230 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 10096 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) 
(* 4467 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 
1045 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 124 (* h1
 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 6 (* h1 h1) (* h2 h2) 
h3 (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 1408 (* h1 h1) (* h2 h2) h3 (* h4 h4) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 11168 (* h1 h1) (* h2 h2) h3 
(* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 34356 (* h1 h1) (* h2 
h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 53220 (* h1 h1) 
(* h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 45511 (* h1 h1)
 (* h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 22193 (* h1 h1) 
(* h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 6077 (* h1 h1) (* h2 
h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 859 (* h1 h1) (* h2 h2) h3 (* 
h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 48 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 
h5) h6 (* j2 j2)) (* 240 (* h1 h1) (* h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 3960 (* h1 h1) (* h2 h2) h3 (* h4 h4) h5 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 18872 (* h1 h1) (* h2 h2) h3 (* h4 h4) h5 (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 38648 (* h1 h1) (* h2 h2) h3 (* h4 h4) h5
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 39422 (* h1 h1) (* h2 h2) h3 (* h4 h4) 
h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 21554 (* h1 h1) (* h2 h2) h3 (* h4 h4) h5
 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 6359 (* h1 h1) (* h2 h2) h3 (* h4 h4) h5 (* h6
 h6) (* j2 j2 j2 j2)) (* 941 (* h1 h1) (* h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2
 j2 j2)) (* 54 (* h1 h1) (* h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 32 
(* h1 h1) (* h2 h2) h3 (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 720 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 3420 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 5578 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 3866 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
1274 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 200 (* h1
 h1) (* h2 h2) h3 (* h4 h4) (* h6 h6 h6) (* j2 j2 j2)) (* 12 (* h1 h1) (* h2 h2)
 h3 (* h4 h4) (* h6 h6 h6) (* j2 j2)) (* 32 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 480 (* h1 h1) (* h2 h2) h3 h4 (* h5
 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2072 (* h1 h1) (* h2 h2) h3 h4 (* 
h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4192 (* h1 h1) (* h2 h2) h3 h4 (* 
h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 4564 (* h1 h1) (* h2 h2) h3 h4 (* h5 
h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2752 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5 
h5) (* j2 j2 j2 j2 j2)) (* 884 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 
j2 j2 j2)) (* 136 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2)) (* 8 
(* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2)) (* 1248 (* h1 h1) (* h2 h2)
 h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 10480 (* h1 h1) (* 
h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 35064 (* h1 h1) 
(* h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 61720 (* h1 h1) 
(* h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 62956 (* h1 h1) (* 
h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 38461 (* h1 h1) (* h2 h2)
 h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 14005 (* h1 h1) (* h2 h2) h3 h4 
(* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 2907 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) 
h6 (* j2 j2 j2)) (* 307 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2)) (* 
12 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) h6 j2) (* 2144 (* h1 h1) (* h2 h2) h3 
h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 17312 (* h1 h1) (* 
h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 58412 (* h1 
h1) (* h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 106856 
(* h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
115955 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
77086 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 31324
 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 7476 (* h1 h1
) (* h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 945 (* h1 h1) (* h2 h2) 
h3 h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 48 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5) 
(* h6 h6) j2) (* 288 (* h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 3844 (* h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 17740 (* h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 40183 (* h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 50511 (* h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 37014 (* h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)
) (* 15929 (* h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 3892 
(* h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 489 (* h1 h1) (* h2 
h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2)) (* 24 (* h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6
 h6) j2) (* 16 (* h1 h1) (* h2 h2) h3 h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2
 j2 j2)) (* 296 (* h1 h1) (* h2 h2) h3 h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 1284 (* h1 h1) (* h2 h2) h3 h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 2358 (* h1 h1) (* h2 h2) h3 h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 2118 (* h1 h1) (* h2 h2) h3 h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 948 (* 
h1 h1) (* h2 h2) h3 h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 200 (* h1 h1) (* h2 
h2) h3 h4 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 16 (* h1 h1) (* h2 h2) h3 h4 (* h6 h6
 h6 h6) (* j2 j2)) (* 160 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 1328 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 4616 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 8780 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2)) (* 9996 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2)) (* 6986 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 
j2 j2)) (* 2950 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 
710 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 86 (* h1 h1) (* 
h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 4 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5 
h5) h6 j2) (* 960 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 7888 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 27576 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 53628 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* h6
 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 63644 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 47551 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* h6
 h6) (* j2 j2 j2 j2 j2)) (* 22240 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2)) (* 6242 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 
j2)) (* 948 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 59 (* h1
 h1) (* h2 h2) h3 (* h5 h5 h5) (* h6 h6) j2) (* 960 (* h1 h1) (* h2 h2) h3 (* h5
 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 7796 (* h1 h1) (* h2 h2)
 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 27164 (* h1 h1) 
(* h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 53041 (* h1 
h1) (* h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 63620 (* h1
 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 48332 (* h1 
h1) (* h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 23114 (* h1 h1) 
(* h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 6666 (* h1 h1) (* h2 h2)
 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 1044 (* h1 h1) (* h2 h2) h3 (* h5 h5
) (* h6 h6 h6) (* j2 j2)) (* 67 (* h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6 h6) j2
) (* 112 (* h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2
 j2)) (* 992 (* h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 3712 (* h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 7698 (* h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 9716 (* h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 7703 (* h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 3816 
(* h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 1133 (* h1 h1) (* 
h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 182 (* h1 h1) (* h2 h2) h3 h5 (* 
h6 h6 h6 h6) (* j2 j2)) (* 12 (* h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6 h6) j2) (* 
40 (* h1 h1) (* h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 460 (* h1 h1) (* h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 1446 (* h1 h1) (* h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 2001 (* h1 h1) (* h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2)) (* 1398 (* h1 h1) (* h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 
j2 j2 j2)) (* 508 (* h1 h1) (* h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 
j2)) (* 90 (* h1 h1) (* h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 6 
(* h1 h1) (* h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 68 (* h1 h1) (* 
h2 h2) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 536 (* h1 h1
) (* h2 h2) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1145 (* h1
 h1) (* h2 h2) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1017 (* h1
 h1) (* h2 h2) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 429 (* h1 h1)
 (* h2 h2) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 84 (* h1 h1) (* h2 
h2) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 6 (* h1 h1) (* h2 h2) (* h4 h4
 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 128 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5 h5
) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1040 (* h1 h1) (* h2 h2) (* h4 h4) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3272 (* h1 h1) (* h2 h2) (* 
h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 5280 (* h1 h1) (* h2 h2) 
(* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 4790 (* h1 h1) (* h2 h2) 
(* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 2493 (* h1 h1) (* h2 h2) (* 
h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 723 (* h1 h1) (* h2 h2) (* h4 h4) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 106 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5 
h5) h6 (* j2 j2 j2)) (* 6 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2
)) (* 136 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2 j2 j2)) (* 1516 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 5522 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 9649 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 9163 (* h1 h1) (* h2 h2) (* h4 h4) (* h5
 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4895 (* h1 h1) (* h2 h2) (* h4 h4) (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1439 (* h1 h1) (* h2 h2) (* h4 h4) (* h5
 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 212 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) 
(* h6 h6) (* j2 j2 j2)) (* 12 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) 
(* j2 j2)) (* 156 (* h1 h1) (* h2 h2) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 1072 (* h1 h1) (* h2 h2) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 2651 (* h1 h1) (* h2 h2) (* h4 h4) h5 (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 3141 (* h1 h1) (* h2 h2) (* h4 h4) h5 (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 1944 (* h1 h1) (* h2 h2) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 
j2 j2 j2)) (* 632 (* h1 h1) (* h2 h2) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2))
 (* 100 (* h1 h1) (* h2 h2) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 6 (* h1 
h1) (* h2 h2) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2)) (* 64 (* h1 h1) (* h2 h2) h4 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 464 (* h1 h1) (* h2 h2)
 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1424 (* h1 h1) (* h2 
h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2404 (* h1 h1) (* h2 
h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2428 (* h1 h1) (* h2 h2) 
h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 1492 (* h1 h1) (* h2 h2) h4 (* 
h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 540 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5 h5
) h6 (* j2 j2 j2 j2)) (* 104 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2 
j2)) (* 8 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 256 (* h1 h1) 
(* h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2008 
(* h1 h1) (* h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 6696 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 12346 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 13736 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2
)) (* 9457 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
3976 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 969 (* h1
 h1) (* h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 122 (* h1 h1) (* h2 h2
) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 6 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5) 
(* h6 h6) j2) (* 152 (* h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 1476 (* h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 5570 (* h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 11075 (* h1 h1) (* h2 h2) h4 (* h5 h5) (* h6
 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 12916 (* h1 h1) (* h2 h2) h4 (* h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 9158 (* h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2)) (* 3920 (* h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6 h6)
 (* j2 j2 j2 j2)) (* 965 (* h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 
j2)) (* 122 (* h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 6 (* h1 
h1) (* h2 h2) h4 (* h5 h5) (* h6 h6 h6) j2) (* 88 (* h1 h1) (* h2 h2) h4 h5 (* 
h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 512 (* h1 h1) (* h2 h2) h4 h5 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1230 (* h1 h1) (* h2 h2) h4 h5 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1570 (* h1 h1) (* h2 h2) h4 h5 (* 
h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1140 (* h1 h1) (* h2 h2) h4 h5 (* h6 h6 
h6 h6) (* j2 j2 j2 j2 j2)) (* 466 (* h1 h1) (* h2 h2) h4 h5 (* h6 h6 h6 h6) (* 
j2 j2 j2 j2)) (* 98 (* h1 h1) (* h2 h2) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 8
 (* h1 h1) (* h2 h2) h4 h5 (* h6 h6 h6 h6) (* j2 j2)) (* 64 (* h1 h1) (* h2 h2) 
(* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 480 (* h1 h1) 
(* h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1568 (* 
h1 h1) (* h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2920 
(* h1 h1) (* h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3404 
(* h1 h1) (* h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2564 (* 
h1 h1) (* h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1240 (* h1 h1)
 (* h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 368 (* h1 h1) (* h2 h2)
 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 60 (* h1 h1) (* h2 h2) (* h5 h5 h5 
h5) (* h6 h6) (* j2 j2)) (* 4 (* h1 h1) (* h2 h2) (* h5 h5 h5 h5) (* h6 h6) j2) 
(* 128 (* h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 960 (* h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 3136 (* h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 5840 (* h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 6808 (* h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 5128 (* h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2)) (* 2480 (* h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) 
(* 736 (* h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 120 (* h1 
h1) (* h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 8 (* h1 h1) (* h2 h2) (* 
h5 h5 h5) (* h6 h6 h6) j2) (* 56 (* h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 432 (* h1 h1) (* h2 h2) (* h5 h5) (* h6 h6
 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1446 (* h1 h1) (* h2 h2) (* h5 h5) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2750 (* h1 h1) (* h2 h2) (* h5 
h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3264 (* h1 h1) (* h2 h2) (* h5 
h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2496 (* h1 h1) (* h2 h2) (* h5 h5)
 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1222 (* h1 h1) (* h2 h2) (* h5 h5) (* h6
 h6 h6 h6) (* j2 j2 j2 j2)) (* 366 (* h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6 h6)
 (* j2 j2 j2)) (* 60 (* h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) 
(* 4 (* h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6 h6) j2) (* 2288 (* h1 h1) h2 (* 
h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 9976 (* h1 h1) h2 
(* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 17424 (* h1 h1) h2 
(* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 15920 (* h1 h1) h2 (* 
h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 8304 (* h1 h1) h2 (* h3 h3 
h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 2480 (* h1 h1) h2 (* h3 h3 h3 h3) (* 
h4 h4) h5 (* j2 j2 j2 j2)) (* 384 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h5 (* 
j2 j2 j2)) (* 24 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2)) (* 192 (* 
h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3248 
(* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 9952 
(* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 13296 (* 
h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 9280 (* h1 h1) 
h2 (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 3488 (* h1 h1) h2 (* h3 
h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2)) (* 656 (* h1 h1) h2 (* h3 h3 h3 h3) (* 
h4 h4) h6 (* j2 j2 j2)) (* 48 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2
)) (* 2976 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 16176 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 35008 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)
) (* 39032 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 
24504 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 9008 (* 
h1 h1) h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 1952 (* h1 h1) h2 (* 
h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 236 (* h1 h1) h2 (* h3 h3 h3 h3) h4 
(* h5 h5) (* j2 j2)) (* 12 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h5 h5) j2) (* 6192
 (* h1 h1) h2 (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 36280 
(* h1 h1) h2 (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 85184 (* 
h1 h1) h2 (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 103160 (* h1 h1)
 h2 (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 70200 (* h1 h1) h2 (* h3 
h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 27888 (* h1 h1) h2 (* h3 h3 h3 h3) h4 
h5 h6 (* j2 j2 j2 j2)) (* 6568 (* h1 h1) h2 (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2
)) (* 864 (* h1 h1) h2 (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2)) (* 48 (* h1 h1) h2 
(* h3 h3 h3 h3) h4 h5 h6 j2) (* 448 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 5680 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 20912 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6
) (* j2 j2 j2 j2 j2 j2 j2)) (* 35728 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 32864 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 
j2 j2 j2 j2)) (* 17104 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)
) (* 5008 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2)) (* 768 (* h1 
h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2)) (* 48 (* h1 h1) h2 (* h3 h3 h3 h3
) h4 (* h6 h6) j2) (* 384 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 2496 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 6496 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 
j2 j2 j2 j2 j2)) (* 8672 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 
j2 j2 j2)) (* 6376 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2))
 (* 2640 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 628 (* h1
 h1) h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2)) (* 80 (* h1 h1) h2 (* h3 h3 
h3 h3) (* h5 h5 h5) (* j2 j2)) (* 4 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5 h5) j2
) (* 3552 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 22448 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 57584 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)
) (* 77104 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
58148 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 25340 (* 
h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 6436 (* h1 h1) h2 (* 
h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 880 (* h1 h1) h2 (* h3 h3 h3 h3) (* 
h5 h5) h6 (* j2 j2)) (* 52 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) h6 j2) (* 3840
 (* h1 h1) h2 (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
25168 (* h1 h1) h2 (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
68032 (* h1 h1) h2 (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
97888 (* h1 h1) h2 (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 81120 
(* h1 h1) h2 (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 39424 (* h1 h1)
 h2 (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 11040 (* h1 h1) h2 (* h3 h3
 h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 1656 (* h1 h1) h2 (* h3 h3 h3 h3) h5 (* h6
 h6) (* j2 j2)) (* 104 (* h1 h1) h2 (* h3 h3 h3 h3) h5 (* h6 h6) j2) (* 256 (* 
h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1984 
(* h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6368 
(* h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 11008 (* 
h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 11152 (* h1 h1)
 h2 (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 6736 (* h1 h1) h2 (* h3 
h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 2352 (* h1 h1) h2 (* h3 h3 h3 h3) (* 
h6 h6 h6) (* j2 j2 j2)) (* 432 (* h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 
j2)) (* 32 (* h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6 h6) j2) (* 192 (* h1 h1) h2 (* 
h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2496 (* h1 h1) 
h2 (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 7392 (* h1 h1
) h2 (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 9304 (* h1 h1)
 h2 (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 5952 (* h1 h1) h2 
(* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 2064 (* h1 h1) h2 (* h3 
h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 352 (* h1 h1) h2 (* h3 h3 h3) (* 
h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 24 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h5 
(* j2 j2 j2)) (* 288 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2
 j2 j2 j2 j2)) (* 2904 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 6464 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 
j2 j2 j2)) (* 6080 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 
j2)) (* 2776 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 
592 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2)) (* 48 (* h1 h1) 
h2 (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2)) (* 768 (* h1 h1) h2 (* h3 h3 h3) 
(* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8200 (* h1 h1) h2 (* 
h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 28292 (* h1 h1)
 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 45728 (* h1
 h1) h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 39100 (* 
h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 18600 (* h1
 h1) h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 5008 (* h1 h1) 
h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 712 (* h1 h1) h2 (* h3 
h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 42 (* h1 h1) h2 (* h3 h3 h3) (* h4 
h4) (* h5 h5) (* j2 j2)) (* 960 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 12864 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 h6 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 52192 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 96456 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 92248 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 h6 
(* j2 j2 j2 j2 j2 j2)) (* 48676 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 
j2 j2 j2 j2)) (* 14700 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)
) (* 2368 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 156 (* h1 
h1) h2 (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 800 (* h1 h1) h2 (* h3 h3 h3) 
(* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8496 (* h1 h1) h2 (* h3 
h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 25456 (* h1 h1) h2 
(* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 33816 (* h1 h1) h2
 (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 22680 (* h1 h1) h2 
(* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 7944 (* h1 h1) h2 (* h3 
h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 1392 (* h1 h1) h2 (* h3 h3 h3) 
(* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 96 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* 
h6 h6) (* j2 j2)) (* 320 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 4432 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 19112 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 39088 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 43284 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 
j2 j2 j2 j2 j2)) (* 27152 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 
j2 j2)) (* 9800 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 
2070 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2)) (* 241 (* h1 h1) h2
 (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2)) (* 12 (* h1 h1) h2 (* h3 h3 h3) h4 (* 
h5 h5 h5) j2) (* 2528 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 26272 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 101656 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6 (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 198816 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2)) (* 218834 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6 (* j2
 j2 j2 j2 j2 j2)) (* 141548 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 
j2 j2 j2)) (* 54672 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) 
(* 12482 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 1568 (* h1 
h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 84 (* h1 h1) h2 (* h3 h3 h3) 
h4 (* h5 h5) h6 j2) (* 1472 (* h1 h1) h2 (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 18832 (* h1 h1) h2 (* h3 h3 h3) h4 h5 (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 83112 (* h1 h1) h2 (* h3 h3 h3) h4 h5 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 180592 (* h1 h1) h2 (* h3 h3 h3) h4 h5 (* h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2)) (* 219188 (* h1 h1) h2 (* h3 h3 h3) h4 h5 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 157500 (* h1 h1) h2 (* h3 h3 h3) h4 h5 (* h6 h6) (* j2
 j2 j2 j2 j2)) (* 68360 (* h1 h1) h2 (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2
)) (* 17592 (* h1 h1) h2 (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 2464 (* 
h1 h1) h2 (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 144 (* h1 h1) h2 (* h3 h3 
h3) h4 h5 (* h6 h6) j2) (* 640 (* h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 6424 (* h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 22048 (* h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 36944 (* h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 34088 (* h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 
j2 j2)) (* 17840 (* h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 
5192 (* h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2)) (* 784 (* h1 h1) h2
 (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2)) (* 48 (* h1 h1) h2 (* h3 h3 h3) h4 (* 
h6 h6 h6) j2) (* 192 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2
 j2 j2 j2 j2)) (* 1248 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 3248 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 
j2 j2 j2)) (* 4336 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 
j2)) (* 3188 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 
1320 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 314 (* h1 h1)
 h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 40 (* h1 h1) h2 (* h3 h3 h3) 
(* h5 h5 h5 h5) (* j2 j2)) (* 2 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5 h5) j2) 
(* 768 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 8064 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 33088 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 70768 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2)) (* 87076 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 63628 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 27522 
(* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 6859 (* h1 h1) h2 
(* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 935 (* h1 h1) h2 (* h3 h3 h3) (* 
h5 h5 h5) h6 (* j2 j2)) (* 54 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) h6 j2) (* 
1632 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2
 j2)) (* 17160 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 71372 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 157152 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 203276 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 160252 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2)) (* 76734 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2
 j2 j2)) (* 21442 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) 
(* 3204 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 196 (* h1 h1
) h2 (* h3 h3 h3) (* h5 h5) (* h6 h6) j2) (* 704 (* h1 h1) h2 (* h3 h3 h3) h5 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8064 (* h1 h1) h2 (* h3 h3 h3
) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 35216 (* h1 h1) h2 (* h3 h3
 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 80536 (* h1 h1) h2 (* h3 h3
 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 108096 (* h1 h1) h2 (* h3 h3 
h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 88860 (* h1 h1) h2 (* h3 h3 h3) h5
 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 44752 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6
 h6) (* j2 j2 j2 j2)) (* 13316 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 
j2 j2)) (* 2152 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 144 (* 
h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6 h6) j2) (* 128 (* h1 h1) h2 (* h3 h3 h3) (* 
h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 992 (* h1 h1) h2 (* h3 h3 h3) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3184 (* h1 h1) h2 (* h3 h3 h3) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 5504 (* h1 h1) h2 (* h3 h3 h3) (* 
h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 5576 (* h1 h1) h2 (* h3 h3 h3) (* h6 h6 
h6 h6) (* j2 j2 j2 j2 j2)) (* 3368 (* h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6 h6) (* 
j2 j2 j2 j2)) (* 1176 (* h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2)) 
(* 216 (* h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2)) (* 16 (* h1 h1) h2 
(* h3 h3 h3) (* h6 h6 h6 h6) j2) (* 48 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4 h4) h5
 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 372 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4 h4
) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 786 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4 
h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 694 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4 h4
) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 314 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4 h4) h5 
(* j2 j2 j2 j2 j2 j2)) (* 70 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 
j2 j2 j2)) (* 6 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 48
 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
384 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
600 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 388 
(* h1 h1) h2 (* h3 h3) (* h4 h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 112 (* h1 h1
) h2 (* h3 h3) (* h4 h4 h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 12 (* h1 h1) h2 (* h3 
h3) (* h4 h4 h4 h4) h6 (* j2 j2 j2 j2)) (* 512 (* h1 h1) h2 (* h3 h3) (* h4 h4 
h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3428 (* h1 h1) h2 (* h3 h3) 
(* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8534 (* h1 h1) h2 (* 
h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 10332 (* h1 h1) h2
 (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 6549 (* h1 h1) h2
 (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2161 (* h1 h1) h2 
(* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 359 (* h1 h1) h2 (* h3 
h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 24 (* h1 h1) h2 (* h3 h3) (* h4 
h4 h4) (* h5 h5) (* j2 j2 j2)) (* 320 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 h6 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3912 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) 
h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 13740 (* h1 h1) h2 (* h3 h3) (* h4 h4 
h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 21056 (* h1 h1) h2 (* h3 h3) (* h4 h4 
h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 15944 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4)
 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 6298 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 h6 
(* j2 j2 j2 j2 j2)) (* 1246 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 
j2 j2)) (* 96 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 176 (* 
h1 h1) h2 (* h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
2032 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 5460 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 5692 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
2704 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 592 
(* h1 h1) h2 (* h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 48 (* h1 h1) 
h2 (* h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2)) (* 544 (* h1 h1) h2 (* h3 h3) 
(* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4536 (* h1 h1) h2 
(* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 14492 (* h1 
h1) h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 23152 
(* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 20066
 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 9640 
(* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 2572 (* h1 
h1) h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 361 (* h1 h1) h2 (* 
h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 21 (* h1 h1) h2 (* h3 h3) (* h4 
h4) (* h5 h5 h5) (* j2 j2)) (* 2336 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 19156 (* h1 h1) h2 (* h3 h3) (* h4 h4) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 60958 (* h1 h1) h2 (* h3 h3) (* 
h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 98724 (* h1 h1) h2 (* h3 h3)
 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 89088 (* h1 h1) h2 (* h3 h3
) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 46176 (* h1 h1) h2 (* h3 h3) 
(* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 13560 (* h1 h1) h2 (* h3 h3) (* h4
 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 2118 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* 
h5 h5) h6 (* j2 j2 j2)) (* 135 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) h6 (* 
j2 j2)) (* 720 (* h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 9588 (* h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 40458 (* h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 79334 (* h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 82236 (* h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* h6
 h6) (* j2 j2 j2 j2 j2 j2)) (* 47932 (* h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* h6 
h6) (* j2 j2 j2 j2 j2)) (* 15580 (* h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* h6 h6) 
(* j2 j2 j2 j2)) (* 2614 (* h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 
j2)) (* 174 (* h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 208 (* 
h1 h1) h2 (* h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
2672 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 9372 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 14200 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 10496 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
3876 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 696 (* h1
 h1) h2 (* h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2)) (* 48 (* h1 h1) h2 (* h3 
h3) (* h4 h4) (* h6 h6 h6) (* j2 j2)) (* 96 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1056 (* h1 h1) h2 (* h3 h3) h4 (* 
h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4312 (* h1 h1) h2 (* h3 h3) h4 
(* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 8840 (* h1 h1) h2 (* h3 h3) h4 
(* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 10032 (* h1 h1) h2 (* h3 h3) h4 (* 
h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 6470 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 
h5 h5) (* j2 j2 j2 j2 j2)) (* 2378 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* 
j2 j2 j2 j2)) (* 509 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2)) (* 
60 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2)) (* 3 (* h1 h1) h2 (* h3 
h3) h4 (* h5 h5 h5 h5) j2) (* 1904 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 16400 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 57220 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 105640 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5
 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 113084 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 72558 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) h6
 (* j2 j2 j2 j2 j2)) (* 28021 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2
 j2 j2)) (* 6361 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 792 
(* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2)) (* 42 (* h1 h1) h2 (* h3 h3
) h4 (* h5 h5 h5) h6 j2) (* 3136 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 27064 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 96624 (* h1 h1) h2 (* h3 h3) h4 (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 186266 (* h1 h1) h2 (* h3 h3) 
h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 212600 (* h1 h1) h2 (* h3 h3
) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 148341 (* h1 h1) h2 (* h3 h3)
 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 63038 (* h1 h1) h2 (* h3 h3) h4 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 15841 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5
) (* h6 h6) (* j2 j2 j2)) (* 2162 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* h6 h6) 
(* j2 j2)) (* 123 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* h6 h6) j2) (* 672 (* h1
 h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8240 
(* h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
36464 (* h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
81536 (* h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
103800 (* h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 79040
 (* h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 36350 (* h1 h1
) h2 (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 9820 (* h1 h1) h2 (* h3 h3
) h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 1420 (* h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6
 h6) (* j2 j2)) (* 84 (* h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6) j2) (* 80 (* h1 
h1) h2 (* h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1024 (* 
h1 h1) h2 (* h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4112 (* 
h1 h1) h2 (* h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 7752 (* h1 
h1) h2 (* h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 7764 (* h1 h1) h2 
(* h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 4276 (* h1 h1) h2 (* h3 h3) 
h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 1280 (* h1 h1) h2 (* h3 h3) h4 (* h6 h6 
h6 h6) (* j2 j2 j2)) (* 196 (* h1 h1) h2 (* h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2))
 (* 12 (* h1 h1) h2 (* h3 h3) h4 (* h6 h6 h6 h6) j2) (* 256 (* h1 h1) h2 (* h3 
h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2272 (* h1 h1) h2 
(* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8448 (* h1 h1) 
h2 (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 17112 (* h1 h1) 
h2 (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 20572 (* h1 h1) h2 
(* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 15010 (* h1 h1) h2 (* h3 
h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 6550 (* h1 h1) h2 (* h3 h3) (* h5 
h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 1643 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) h6 
(* j2 j2 j2)) (* 224 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 13 
(* h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) h6 j2) (* 1312 (* h1 h1) h2 (* h3 h3) (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 11400 (* h1 h1) h2 (* 
h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 42116 (* h1 h1)
 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 86196 (* h1
 h1) h2 (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 106862 (* 
h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 82481 (* h1
 h1) h2 (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 39219 (* h1 h1) 
h2 (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 10959 (* h1 h1) h2 (* h3
 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 1625 (* h1 h1) h2 (* h3 h3) (* h5 
h5 h5) (* h6 h6) (* j2 j2)) (* 98 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* h6 h6) 
j2) (* 1312 (* h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 11376 (* h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2
 j2 j2 j2 j2 j2 j2)) (* 42268 (* h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 87796 (* h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2)) (* 111558 (* h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 89164 (* h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6 h6
) (* j2 j2 j2 j2 j2)) (* 44358 (* h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2)) (* 13105 (* h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2
)) (* 2080 (* h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 135 (* h1
 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6 h6) j2) (* 224 (* h1 h1) h2 (* h3 h3) h5 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2192 (* h1 h1) h2 (* h3 h3
) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8944 (* h1 h1) h2 (* h3 
h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 19960 (* h1 h1) h2 (* h3 
h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 26732 (* h1 h1) h2 (* h3 h3)
 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 22148 (* h1 h1) h2 (* h3 h3) h5 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 11288 (* h1 h1) h2 (* h3 h3) h5 (* h6 h6 
h6 h6) (* j2 j2 j2 j2)) (* 3410 (* h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 
j2 j2)) (* 560 (* h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2)) (* 38 (* h1 
h1) h2 (* h3 h3) h5 (* h6 h6 h6 h6) j2) (* 40 (* h1 h1) h2 h3 (* h4 h4 h4 h4) 
(* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 200 (* h1 h1) h2 h3 (* h4 h4 h4 
h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 394 (* h1 h1) h2 h3 (* h4 h4 h4
 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 372 (* h1 h1) h2 h3 (* h4 h4 h4 
h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 168 (* h1 h1) h2 h3 (* h4 h4 h4 h4) 
(* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 36 (* h1 h1) h2 h3 (* h4 h4 h4 h4) (* h5 h5)
 (* j2 j2 j2 j2 j2)) (* 3 (* h1 h1) h2 h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 
j2)) (* 148 (* h1 h1) h2 h3 (* h4 h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 580 (* h1 h1) h2 h3 (* h4 h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
835 (* h1 h1) h2 h3 (* h4 h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 513 (* h1
 h1) h2 h3 (* h4 h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 143 (* h1 h1) h2 h3 
(* h4 h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 15 (* h1 h1) h2 h3 (* h4 h4 h4 h4) 
h5 h6 (* j2 j2 j2 j2)) (* 48 (* h1 h1) h2 h3 (* h4 h4 h4 h4) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 184 (* h1 h1) h2 h3 (* h4 h4 h4 h4) (* h6 h6) (* j2 j2 j2
 j2 j2 j2 j2)) (* 158 (* h1 h1) h2 h3 (* h4 h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 52 (* h1 h1) h2 h3 (* h4 h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 6
 (* h1 h1) h2 h3 (* h4 h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 128 (* h1 h1) h2 
h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 768 (* h1 h1)
 h2 h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1896 (* h1 
h1) h2 h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2396 (* h1 
h1) h2 h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1596 (* h1 h1) 
h2 h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 540 (* h1 h1) h2 h3 
(* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 90 (* h1 h1) h2 h3 (* h4 h4 h4)
 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 6 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5 h5) 
(* j2 j2 j2)) (* 264 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 2412 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 7552 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 11012 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2)) (* 8198 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 
j2 j2 j2)) (* 3221 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2))
 (* 632 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 48 (* h1 
h1) h2 h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 632 (* h1 h1) h2 h3 (* h4 
h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3678 (* h1 h1) h2 h3 (* 
h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 7663 (* h1 h1) h2 h3 (* 
h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 7049 (* h1 h1) h2 h3 (* h4 
h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3170 (* h1 h1) h2 h3 (* h4 h4 h4) 
h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 678 (* h1 h1) h2 h3 (* h4 h4 h4) h5 (* h6 h6
) (* j2 j2 j2 j2)) (* 54 (* h1 h1) h2 h3 (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2))
 (* 112 (* h1 h1) h2 h3 (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 592 (* h1 h1) h2 h3 (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
972 (* h1 h1) h2 h3 (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 572 (* 
h1 h1) h2 h3 (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 140 (* h1 h1) h2 
h3 (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 12 (* h1 h1) h2 h3 (* h4 h4 h4)
 (* h6 h6 h6) (* j2 j2 j2)) (* 64 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 456 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5 h5)
 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1380 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5 
h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2264 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5 
h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 2140 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2)) (* 1154 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 
j2 j2 j2 j2)) (* 337 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) 
(* 50 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 3 (* h1 h1) h2 
h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 648 (* h1 h1) h2 h3 (* h4 h4) (* h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 5136 (* h1 h1) h2 h3 (* h4 h4) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 16254 (* h1 h1) h2 h3 (* h4 
h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 26550 (* h1 h1) h2 h3 (* h4 
h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 24305 (* h1 h1) h2 h3 (* h4 h4)
 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 12784 (* h1 h1) h2 h3 (* h4 h4) (* h5
 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 3839 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) h6
 (* j2 j2 j2 j2)) (* 610 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2))
 (* 39 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 584 (* h1 h1) h2 
h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 6036 (* 
h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
22694 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2))
 (* 41989 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 42452 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 24416 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
7928 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 1325 (* 
h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 87 (* h1 h1) h2 h3 
(* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 860 (* h1 h1) h2 h3 (* h4 h4) h5 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 5706 (* h1 h1) h2 h3 (* h4 h4) h5 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 14540 (* h1 h1) h2 h3 (* h4 h4) h5 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 18126 (* h1 h1) h2 h3 (* h4 h4) h5 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 11946 (* h1 h1) h2 h3 (* h4 h4) h5 (* h6 h6 
h6) (* j2 j2 j2 j2 j2)) (* 4250 (* h1 h1) h2 h3 (* h4 h4) h5 (* h6 h6 h6) (* j2 
j2 j2 j2)) (* 752 (* h1 h1) h2 h3 (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 51 
(* h1 h1) h2 h3 (* h4 h4) h5 (* h6 h6 h6) (* j2 j2)) (* 64 (* h1 h1) h2 h3 (* h4
 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 408 (* h1 h1) h2 h3 (* h4 
h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 894 (* h1 h1) h2 h3 (* h4 h4) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 864 (* h1 h1) h2 h3 (* h4 h4) (* h6 h6
 h6 h6) (* j2 j2 j2 j2 j2)) (* 388 (* h1 h1) h2 h3 (* h4 h4) (* h6 h6 h6 h6) (* 
j2 j2 j2 j2)) (* 80 (* h1 h1) h2 h3 (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 6
 (* h1 h1) h2 h3 (* h4 h4) (* h6 h6 h6 h6) (* j2 j2)) (* 256 (* h1 h1) h2 h3 h4 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2088 (* h1 h1) h2 h3 h4
 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 7108 (* h1 h1) h2 h3 h4 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 13116 (* h1 h1) h2 h3 h4 (* 
h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 14298 (* h1 h1) h2 h3 h4 (* h5 h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 9450 (* h1 h1) h2 h3 h4 (* h5 h5 h5 h5) h6 
(* j2 j2 j2 j2 j2)) (* 3766 (* h1 h1) h2 h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2
)) (* 880 (* h1 h1) h2 h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 112 (* h1 h1) 
h2 h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 6 (* h1 h1) h2 h3 h4 (* h5 h5 h5 h5) 
h6 j2) (* 912 (* h1 h1) h2 h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 7676 (* h1 h1) h2 h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 27070 (* h1 h1) h2 h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 51976 (* h1 h1) h2 h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 59376 (* h1 h1) h2 h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 41606 (* h1 h1) h2 h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
17874 (* h1 h1) h2 h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 4570 (* h1 
h1) h2 h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 632 (* h1 h1) h2 h3 h4 (* 
h5 h5 h5) (* h6 h6) (* j2 j2)) (* 36 (* h1 h1) h2 h3 h4 (* h5 h5 h5) (* h6 h6) 
j2) (* 536 (* h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 5312 (* h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 21114 (* h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 44442 (* h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 54680 (* h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)
) (* 40842 (* h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
18594 (* h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 5006 (* h1 
h1) h2 h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 720 (* h1 h1) h2 h3 h4 (* 
h5 h5) (* h6 h6 h6) (* j2 j2)) (* 42 (* h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6 h6) 
j2) (* 376 (* h1 h1) h2 h3 h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (* 2568 (* h1 h1) h2 h3 h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
7192 (* h1 h1) h2 h3 h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 10680 
(* h1 h1) h2 h3 h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 9132 (* h1 h1) 
h2 h3 h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 4596 (* h1 h1) h2 h3 h4 h5 
(* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 1333 (* h1 h1) h2 h3 h4 h5 (* h6 h6 h6 h6) 
(* j2 j2 j2)) (* 201 (* h1 h1) h2 h3 h4 h5 (* h6 h6 h6 h6) (* j2 j2)) (* 12 (* 
h1 h1) h2 h3 h4 h5 (* h6 h6 h6 h6) j2) (* 192 (* h1 h1) h2 h3 (* h5 h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1616 (* h1 h1) h2 h3 (* h5 h5 h5
 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 5816 (* h1 h1) h2 h3 (* h5 h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 11688 (* h1 h1) h2 h3 (* h5 h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 14352 (* h1 h1) h2 h3 (* h5 h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 11060 (* h1 h1) h2 h3 (* h5 h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 5281 (* h1 h1) h2 h3 (* h5 h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2)) (* 1483 (* h1 h1) h2 h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2))
 (* 219 (* h1 h1) h2 h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 13 (* h1 h1) h2 
h3 (* h5 h5 h5 h5) (* h6 h6) j2) (* 392 (* h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3300 (* h1 h1) h2 h3 (* h5 h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 11928 (* h1 h1) h2 h3 (* h5 h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 24192 (* h1 h1) h2 h3 (* h5 h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 30167 (* h1 h1) h2 h3 (* h5 h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 23809 (* h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6 h6)
 (* j2 j2 j2 j2 j2)) (* 11785 (* h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2
 j2 j2)) (* 3491 (* h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 556 
(* h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 36 (* h1 h1) h2 h3 (* h5
 h5 h5) (* h6 h6 h6) j2) (* 176 (* h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1512 (* h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 5576 (* h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 11532 (* h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6 h6
) (* j2 j2 j2 j2 j2 j2 j2)) (* 14652 (* h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 11772 (* h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 
j2 j2 j2 j2)) (* 5927 (* h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2))
 (* 1785 (* h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 289 (* h1 h1
) h2 h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 19 (* h1 h1) h2 h3 (* h5 h5) (* 
h6 h6 h6 h6) j2) (* 32 (* h1 h1) h2 (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 128 (* h1 h1) h2 (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2
 j2 j2 j2 j2)) (* 180 (* h1 h1) h2 (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2)) (* 110 (* h1 h1) h2 (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2
)) (* 30 (* h1 h1) h2 (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 3 (* 
h1 h1) h2 (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 42 (* h1 h1) h2 (* h4
 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 107 (* h1 h1) h2 (* h4 
h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 85 (* h1 h1) h2 (* h4 h4 h4 
h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 27 (* h1 h1) h2 (* h4 h4 h4 h4) h5 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 3 (* h1 h1) h2 (* h4 h4 h4 h4) h5 (* h6 h6) (* 
j2 j2 j2 j2)) (* 8 (* h1 h1) h2 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 148 (* h1 h1) h2 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 596 (* h1 h1) h2 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 1022 (* h1 h1) h2 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2)) (* 872 (* h1 h1) h2 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2
 j2)) (* 378 (* h1 h1) h2 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 78
 (* h1 h1) h2 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 6 (* h1 h1) h2 
(* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 144 (* h1 h1) h2 (* h4 h4 h4) (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 806 (* h1 h1) h2 (* h4 h4 h4
) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1637 (* h1 h1) h2 (* h4 h4
 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1545 (* h1 h1) h2 (* h4 h4
 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 713 (* h1 h1) h2 (* h4 h4 h4)
 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 153 (* h1 h1) h2 (* h4 h4 h4) (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2)) (* 12 (* h1 h1) h2 (* h4 h4 h4) (* h5 h5) (* h6 
h6) (* j2 j2 j2)) (* 110 (* h1 h1) h2 (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 411 (* h1 h1) h2 (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2
 j2 j2 j2)) (* 540 (* h1 h1) h2 (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 301 (* h1 h1) h2 (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 72 
(* h1 h1) h2 (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 6 (* h1 h1) h2 (* 
h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 8 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 100 (* h1 h1) h2 (* h4 h4) (* h5 h5
 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 428 (* h1 h1) h2 (* h4 h4) (* h5 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 898 (* h1 h1) h2 (* h4 h4) (* h5 h5
 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1038 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 680 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5 h5) h6 
(* j2 j2 j2 j2 j2)) (* 245 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2
 j2)) (* 44 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 3 (* h1 
h1) h2 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 32 (* h1 h1) h2 (* h4 h4) (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 480 (* h1 h1) h2 (* h4
 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2096 (* h1 h1) h2
 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4318 (* h1 h1)
 h2 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4837 (* h1 h1)
 h2 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3054 (* h1 h1) h2
 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1057 (* h1 h1) h2 (* h4
 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 182 (* h1 h1) h2 (* h4 h4) (* h5
 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 12 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5) (* h6 
h6) (* j2 j2)) (* 208 (* h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 1298 (* h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 3211 (* h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 4045 (* h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 2765 (* h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2)) (* 1008 (* h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2)) (* 179 (* h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 12 
(* h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 68 (* h1 h1) h2 (* 
h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 310 (* h1 h1) h2 (* h4
 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 548 (* h1 h1) h2 (* h4 h4) 
h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 471 (* h1 h1) h2 (* h4 h4) h5 (* h6
 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 203 (* h1 h1) h2 (* h4 h4) h5 (* h6 h6 h6 h6) 
(* j2 j2 j2 j2)) (* 41 (* h1 h1) h2 (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) 
(* 3 (* h1 h1) h2 (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2)) (* 24 (* h1 h1) h2 h4 
(* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 244 (* h1 h1) h2
 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1004 (* h1 h1) 
h2 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2228 (* h1 h1) 
h2 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2948 (* h1 h1) h2 
h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2402 (* h1 h1) h2 h4 (* 
h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1193 (* h1 h1) h2 h4 (* h5 h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2)) (* 343 (* h1 h1) h2 h4 (* h5 h5 h5 h5) (* h6 h6) 
(* j2 j2 j2)) (* 51 (* h1 h1) h2 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 3 
(* h1 h1) h2 h4 (* h5 h5 h5 h5) (* h6 h6) j2) (* 40 (* h1 h1) h2 h4 (* h5 h5 h5)
 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 452 (* h1 h1) h2 h4 (* h5 h5
 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1944 (* h1 h1) h2 h4 (* h5 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4398 (* h1 h1) h2 h4 (* h5 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 5865 (* h1 h1) h2 h4 (* h5 h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4791 (* h1 h1) h2 h4 (* h5 h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2381 (* h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2)) (* 685 (* h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) 
(* 102 (* h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 6 (* h1 h1) h2 h4
 (* h5 h5 h5) (* h6 h6 h6) j2) (* 96 (* h1 h1) h2 h4 (* h5 h5) (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 620 (* h1 h1) h2 h4 (* h5 h5) (* h6 h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1688 (* h1 h1) h2 h4 (* h5 h5) (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 2507 (* h1 h1) h2 h4 (* h5 h5) (* h6 h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 2195 (* h1 h1) h2 h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 
j2 j2 j2)) (* 1142 (* h1 h1) h2 h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) 
(* 338 (* h1 h1) h2 h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 51 (* h1 h1) 
h2 h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 3 (* h1 h1) h2 h4 (* h5 h5) (* h6 
h6 h6 h6) j2) (* 16 (* h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 128 (* h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 448 (* h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 898 (* h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2
 j2 j2 j2)) (* 1132 (* h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 926 (* h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 488
 (* h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 158 (* h1 h1) h2 
(* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 28 (* h1 h1) h2 (* h5 h5 h5 h5) 
(* h6 h6 h6) (* j2 j2)) (* 2 (* h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6 h6) j2) (* 16
 (* h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 128 (* h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (* 448 (* h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 898 (* h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
1132 (* h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 926 (* 
h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 488 (* h1 h1) h2 
(* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 158 (* h1 h1) h2 (* h5 h5 h5) 
(* h6 h6 h6 h6) (* j2 j2 j2)) (* 28 (* h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6 h6) 
(* j2 j2)) (* 2 (* h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6 h6) j2) (* 96 (* h1 h1) 
(* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 480 (* h1 
h1) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 992 (* h1
 h1) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1112 (* h1 
h1) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 744 (* h1 h1) 
(* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 304 (* h1 h1) (* h3 h3
 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 72 (* h1 h1) (* h3 h3 h3 h3) (* 
h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 8 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* 
j2 j2 j2)) (* 96 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 432 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 800 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 
j2)) (* 784 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 
432 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 128 (* h1 
h1) (* h3 h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2)) (* 16 (* h1 h1) (* h3 h3 h3
 h3) (* h4 h4 h4) h6 (* j2 j2 j2)) (* 320 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) 
(* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1920 (* h1 h1) (* h3 h3 h3 h3) 
(* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4704 (* h1 h1) (* h3 h3 
h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6160 (* h1 h1) (* h3 
h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 4768 (* h1 h1) (* h3 
h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2280 (* h1 h1) (* h3 h3 
h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 672 (* h1 h1) (* h3 h3 h3 h3) 
(* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 112 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) 
(* h5 h5) (* j2 j2 j2)) (* 8 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2
 j2)) (* 416 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 3216 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 9848 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 15760 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 
j2 j2 j2)) (* 14544 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 
j2)) (* 7984 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 
2560 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 440 (* h1 h1)
 (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 32 (* h1 h1) (* h3 h3 h3 h3) 
(* h4 h4) h5 h6 (* j2 j2)) (* 224 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1392 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3520 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4704 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3584 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) (* 
h6 h6) (* j2 j2 j2 j2 j2)) (* 1552 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) (* h6 h6)
 (* j2 j2 j2 j2)) (* 352 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 
j2)) (* 32 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2)) (* 128 (* h1
 h1) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 896 
(* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
2592 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
4048 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 3776
 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2224 (* h1 
h1) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 852 (* h1 h1) (* h3 
h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 208 (* h1 h1) (* h3 h3 h3 h3) h4 
(* h5 h5 h5) (* j2 j2 j2)) (* 30 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2
 j2)) (* 2 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5 h5) j2) (* 928 (* h1 h1) (* h3 
h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 7008 (* h1 h1) 
(* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 21792 (* h1 
h1) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 36232 (* h1 
h1) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 35128 (* h1 h1)
 (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 20508 (* h1 h1) (* h3
 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 7300 (* h1 h1) (* h3 h3 h3 h3)
 h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 1592 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5)
 h6 (* j2 j2 j2)) (* 204 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2)) 
(* 12 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) h6 j2) (* 576 (* h1 h1) (* h3 h3 h3
 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 5024 (* h1 h1) (* h3 
h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 18032 (* h1 h1) (* 
h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 34720 (* h1 h1) (* 
h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 39248 (* h1 h1) (* h3 
h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 26864 (* h1 h1) (* h3 h3 h3 
h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 11144 (* h1 h1) (* h3 h3 h3 h3) h4 h5
 (* h6 h6) (* j2 j2 j2 j2)) (* 2752 (* h1 h1) (* h3 h3 h3 h3) h4 h5 (* h6 h6) 
(* j2 j2 j2)) (* 384 (* h1 h1) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 24 
(* h1 h1) (* h3 h3 h3 h3) h4 h5 (* h6 h6) j2) (* 128 (* h1 h1) (* h3 h3 h3 h3) 
h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 896 (* h1 h1) (* h3 h3 h3 h3)
 h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2656 (* h1 h1) (* h3 h3 h3 h3) 
h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4352 (* h1 h1) (* h3 h3 h3 h3) h4 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4304 (* h1 h1) (* h3 h3 h3 h3) h4 (* h6 
h6 h6) (* j2 j2 j2 j2 j2)) (* 2624 (* h1 h1) (* h3 h3 h3 h3) h4 (* h6 h6 h6) (* 
j2 j2 j2 j2)) (* 960 (* h1 h1) (* h3 h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2)) (* 
192 (* h1 h1) (* h3 h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2)) (* 16 (* h1 h1) (* h3 
h3 h3 h3) h4 (* h6 h6 h6) j2) (* 256 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2048 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5 h5
) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 6848 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 12384 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 13120 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5 h5)
 h6 (* j2 j2 j2 j2 j2 j2)) (* 8304 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2)) (* 3128 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 
j2)) (* 696 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 84 (* h1 
h1) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2)) (* 4 (* h1 h1) (* h3 h3 h3 h3) 
(* h5 h5 h5) h6 j2) (* 576 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4736 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 16416 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 31248 (* h1 h1) (* h3 h3 h3 h3) (* h5
 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 35664 (* h1 h1) (* h3 h3 h3 h3) (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 25056 (* h1 h1) (* h3 h3 h3 h3) (* h5
 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 10728 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2)) (* 2664 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6)
 (* j2 j2 j2)) (* 336 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) 
(* 16 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) j2) (* 256 (* h1 h1) (* h3 
h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2176 (* h1 h1) 
(* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 7936 (* h1 h1
) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 16192 (* h1 h1
) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 20192 (* h1 h1) 
(* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 15776 (* h1 h1) (* h3 
h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 7600 (* h1 h1) (* h3 h3 h3 h3) 
h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 2128 (* h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6 
h6) (* j2 j2 j2)) (* 304 (* h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2)) 
(* 16 (* h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6 h6) j2) (* 48 (* h1 h1) (* h3 h3 h3)
 (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 192 (* h1 h1) (* h3 h3
 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 304 (* h1 h1) (* h3 
h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 252 (* h1 h1) (* h3 h3
 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 120 (* h1 h1) (* h3 h3 h3) 
(* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 32 (* h1 h1) (* h3 h3 h3) (* h4 h4 
h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 4 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* 
j2 j2 j2 j2)) (* 48 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4 h4) h6 (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 168 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4 h4) h6 (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 232 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4 h4) h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 160 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 56 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 8 (* h1 
h1) (* h3 h3 h3) (* h4 h4 h4 h4) h6 (* j2 j2 j2 j2)) (* 288 (* h1 h1) (* h3 h3 
h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1504 (* h1 h1) 
(* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3120 (* 
h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3344 
(* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 2048 
(* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 748 (* 
h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 154 (* h1 h1) 
(* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 14 (* h1 h1) (* h3 h3 h3
) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 256 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4
) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2032 (* h1 h1) (* h3 h3 h3) (* h4 
h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 5784 (* h1 h1) (* h3 h3 h3) (* 
h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 8016 (* h1 h1) (* h3 h3 h3) (* 
h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 6028 (* h1 h1) (* h3 h3 h3) (* h4 
h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 2528 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) 
h5 h6 (* j2 j2 j2 j2 j2)) (* 560 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2
 j2 j2 j2)) (* 52 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 160
 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 896 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 1944 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 2096 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 1176 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 320
 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 32 (* h1 h1) 
(* h3 h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2)) (* 304 (* h1 h1) (* h3 h3 h3) 
(* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1904 (* h1 h1) (* 
h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4864 (* h1 
h1) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6596 (* 
h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 5216 (* 
h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2508 (* h1 
h1) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 734 (* h1 h1) (* 
h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 119 (* h1 h1) (* h3 h3 h3) 
(* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 8 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5
 h5 h5) (* j2 j2)) (* 1152 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8392 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 24644 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 37724 (* h1 h1) (* h3 h3 h3) (* h4 h4)
 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 32736 (* h1 h1) (* h3 h3 h3) (* h4 h4
) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 16624 (* h1 h1) (* h3 h3 h3) (* h4 h4) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 4954 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 
h5) h6 (* j2 j2 j2 j2)) (* 810 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* 
j2 j2 j2)) (* 56 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 496
 (* h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 4784 (* h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 17248 (* h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 31336 (* h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 31812 (* h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2
 j2 j2 j2)) (* 18740 (* h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 
j2 j2)) (* 6432 (* h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) 
(* 1220 (* h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 96 (* h1 
h1) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 176 (* h1 h1) (* h3 h3 h3)
 (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1176 (* h1 h1) (* h3 
h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3152 (* h1 h1) (* 
h3 h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4440 (* h1 h1) (* 
h3 h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3552 (* h1 h1) (* h3 
h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1600 (* h1 h1) (* h3 h3 h3)
 (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 368 (* h1 h1) (* h3 h3 h3) (* h4 h4)
 (* h6 h6 h6) (* j2 j2 j2)) (* 32 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h6 h6 h6) 
(* j2 j2)) (* 64 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 448 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2
 j2 j2 j2 j2)) (* 1296 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 2024 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 
j2 j2 j2)) (* 1888 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 
j2)) (* 1112 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 
426 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 104 (* h1 h1) 
(* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2)) (* 15 (* h1 h1) (* h3 h3 h3) h4 
(* h5 h5 h5 h5) (* j2 j2)) (* (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5 h5) j2) (* 
896 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (* 6992 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2
)) (* 22552 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 38888 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 38836 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
22970 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 8104 (* 
h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 1739 (* h1 h1) (* h3 
h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 219 (* h1 h1) (* h3 h3 h3) h4 (* h5 
h5 h5) h6 (* j2 j2)) (* 13 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) h6 j2) (* 1440
 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 11720 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2
 j2 j2)) (* 39940 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 74148 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2
 j2 j2 j2 j2)) (* 81876 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 55176 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2
 j2 j2)) (* 22408 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2))
 (* 5282 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 696 (* 
h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 42 (* h1 h1) (* h3 h3 
h3) h4 (* h5 h5) (* h6 h6) j2) (* 416 (* h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4032 (* h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 15696 (* h1 h1) (* h3 h3 h3) h4 h5 (* h6
 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 32560 (* h1 h1) (* h3 h3 h3) h4 h5 (* h6
 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 39824 (* h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6
 h6) (* j2 j2 j2 j2 j2 j2)) (* 29812 (* h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2)) (* 13704 (* h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 
j2 j2)) (* 3808 (* h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 612 
(* h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2)) (* 44 (* h1 h1) (* h3 h3 h3
) h4 h5 (* h6 h6 h6) j2) (* 64 (* h1 h1) (* h3 h3 h3) h4 (* h6 h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 448 (* h1 h1) (* h3 h3 h3) h4 (* h6 h6 h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 1328 (* h1 h1) (* h3 h3 h3) h4 (* h6 h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 2176 (* h1 h1) (* h3 h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 2152 (* h1 h1) (* h3 h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 
j2)) (* 1312 (* h1 h1) (* h3 h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 480 
(* h1 h1) (* h3 h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 96 (* h1 h1) (* h3 h3
 h3) h4 (* h6 h6 h6 h6) (* j2 j2)) (* 8 (* h1 h1) (* h3 h3 h3) h4 (* h6 h6 h6 h6
) j2) (* 128 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 1024 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 3424 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 6192 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2)) (* 6560 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2)) (* 4152 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
1564 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 348 (* h1 h1)
 (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 42 (* h1 h1) (* h3 h3 h3) (* 
h5 h5 h5 h5) h6 (* j2 j2)) (* 2 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5 h5) h6 j2) 
(* 576 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 4832 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 17168 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 33600 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 39424 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2
 j2 j2 j2 j2 j2)) (* 28292 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2)) (* 12172 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2
 j2)) (* 2972 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 374
 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 18 (* h1 h1) (* h3 
h3 h3) (* h5 h5 h5) (* h6 h6) j2) (* 576 (* h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4832 (* h1 h1) (* h3 h3 h3) (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 17376 (* h1 h1) (* h3 h3 h3)
 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 35024 (* h1 h1) (* h3 h3
 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 43320 (* h1 h1) (* h3 
h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 33712 (* h1 h1) (* h3 h3
 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 16188 (* h1 h1) (* h3 h3 h3) 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 4484 (* h1 h1) (* h3 h3 h3) (* h5 h5)
 (* h6 h6 h6) (* j2 j2 j2)) (* 624 (* h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6)
 (* j2 j2)) (* 32 (* h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) j2) (* 128 (* h1
 h1) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1088 
(* h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
3968 (* h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
8096 (* h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
10096 (* h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 7888 
(* h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 3800 (* h1 h1) 
(* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 1064 (* h1 h1) (* h3 h3 h3) 
h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 152 (* h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6 h6
) (* j2 j2)) (* 8 (* h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6 h6) j2) (* 48 (* h1 h1) 
(* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 216 
(* h1 h1) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 372 (* h1 h1) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 316 (* h1 h1) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2))
 (* 146 (* h1 h1) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 
37 (* h1 h1) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 4 (* h1 
h1) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 164 (* h1 h1) (* h3 
h3) (* h4 h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 566 (* h1 h1) (* h3
 h3) (* h4 h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 724 (* h1 h1) (* h3 
h3) (* h4 h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 448 (* h1 h1) (* h3 h3) 
(* h4 h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 136 (* h1 h1) (* h3 h3) (* h4 h4
 h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 16 (* h1 h1) (* h3 h3) (* h4 h4 h4 h4) h5 
h6 (* j2 j2 j2 j2)) (* 56 (* h1 h1) (* h3 h3) (* h4 h4 h4 h4) (* h6 h6) (* j2 j2
 j2 j2 j2 j2 j2 j2)) (* 148 (* h1 h1) (* h3 h3) (* h4 h4 h4 h4) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 140 (* h1 h1) (* h3 h3) (* h4 h4 h4 h4) (* h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 56 (* h1 h1) (* h3 h3) (* h4 h4 h4 h4) (* h6 h6) (* j2 j2 j2
 j2 j2)) (* 8 (* h1 h1) (* h3 h3) (* h4 h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 
136 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 728 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 1544 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 1686 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 
j2 j2 j2 j2)) (* 1046 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 
j2 j2 j2)) (* 384 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 
j2)) (* 79 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 7 
(* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 256 (* h1 h1) (* 
h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2044 (* 
h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
5974 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 8446 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 6275 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
2498 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 524 
(* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 45 (* h1 h1) 
(* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 612 (* h1 h1) (* h3 h3) (* 
h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3110 (* h1 h1) (* h3 
h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 5996 (* h1 h1) (* 
h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 5598 (* h1 h1) (* 
h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2704 (* h1 h1) (* h3 
h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 646 (* h1 h1) (* h3 h3) (* 
h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 58 (* h1 h1) (* h3 h3) (* h4 h4 h4) 
h5 (* h6 h6) (* j2 j2 j2)) (* 128 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 504 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h6 h6 h6
) (* j2 j2 j2 j2 j2 j2 j2)) (* 740 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2)) (* 500 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2)) (* 152 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 
j2 j2)) (* 16 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2)) (* 64 
(* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (* 416 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2
 j2)) (* 1104 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 1552 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2
 j2 j2)) (* 1264 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2
 j2)) (* 620 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) 
(* 184 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 30 (* 
h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 2 (* h1 h1) (* h3 h3
) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 544 (* h1 h1) (* h3 h3) (* h4 h4) (* 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3992 (* h1 h1) (* h3 h3) (* 
h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 11972 (* h1 h1) (* h3 
h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 18896 (* h1 h1) 
(* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 16922 (* h1 h1)
 (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 8751 (* h1 h1) 
(* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 2597 (* h1 h1) (* h3 
h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 418 (* h1 h1) (* h3 h3) (* h4 
h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 28 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 
h5) h6 (* j2 j2)) (* 496 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4696 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 16928 (* h1 h1) (* h3 h3) (* h4 h4)
 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 30936 (* h1 h1) (* h3 h3) 
(* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 31543 (* h1 h1) (* h3
 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 18434 (* h1 h1) (* 
h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 6087 (* h1 h1) (* h3
 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 1099 (* h1 h1) (* h3 h3) 
(* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 82 (* h1 h1) (* h3 h3) (* h4 h4) 
(* h5 h5) (* h6 h6) (* j2 j2)) (* 752 (* h1 h1) (* h3 h3) (* h4 h4) h5 (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4608 (* h1 h1) (* h3 h3) (* h4 h4) h5 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 11168 (* h1 h1) (* h3 h3) (* h4 h4) h5
 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 13770 (* h1 h1) (* h3 h3) (* h4 h4) 
h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 9304 (* h1 h1) (* h3 h3) (* h4 h4) h5 
(* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 3496 (* h1 h1) (* h3 h3) (* h4 h4) h5 (* h6 
h6 h6) (* j2 j2 j2 j2)) (* 700 (* h1 h1) (* h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* 
j2 j2 j2)) (* 56 (* h1 h1) (* h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2)) (* 72 
(* h1 h1) (* h3 h3) (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
356 (* h1 h1) (* h3 h3) (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
696 (* h1 h1) (* h3 h3) (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 684 
(* h1 h1) (* h3 h3) (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 352 (* h1 
h1) (* h3 h3) (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 88 (* h1 h1) (* h3 
h3) (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 8 (* h1 h1) (* h3 h3) (* h4 h4) 
(* h6 h6 h6 h6) (* j2 j2)) (* 192 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1536 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 5096 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5
) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 9060 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5)
 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 9324 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 5646 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* 2009 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2))
 (* 429 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 53 (* h1 h1) 
(* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 3 (* h1 h1) (* h3 h3) h4 (* h5 h5 
h5 h5) h6 j2) (* 680 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 5584 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 19360 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 36798 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 41698 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 28727 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 11793 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* h6
 h6) (* j2 j2 j2 j2)) (* 2759 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2)) (* 358 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 21
 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) j2) (* 416 (* h1 h1) (* h3 h3) h4
 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3976 (* h1 h1) (* 
h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 15492 (* h1 
h1) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 32400 
(* h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 39974
 (* h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 29978 
(* h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 13564 (* h1
 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 3597 (* h1 h1) (* 
h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 541 (* h1 h1) (* h3 h3) h4 (* 
h5 h5) (* h6 h6 h6) (* j2 j2)) (* 36 (* h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6 
h6) j2) (* 304 (* h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2
 j2 j2)) (* 2048 (* h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 5680 (* h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 8380 (* h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 7120 (* h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 3556 
(* h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 1038 (* h1 h1) (* 
h3 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 170 (* h1 h1) (* h3 h3) h4 h5 (* 
h6 h6 h6 h6) (* j2 j2)) (* 12 (* h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6 h6) j2) (* 
128 (* h1 h1) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 1088 (* h1 h1) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 3920 (* h1 h1) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 7784 (* h1 h1) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 9264 (* h1 h1) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 6728 (* h1 h1) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 2910 (* h1 h1) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 
704 (* h1 h1) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 86 (* h1 h1) 
(* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 4 (* h1 h1) (* h3 h3) (* h5 h5
 h5 h5) (* h6 h6) j2) (* 272 (* h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2320 (* h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8488 (* h1 h1) (* h3 h3) (* h5 h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 17388 (* h1 h1) (* h3 h3) (* h5 h5 h5)
 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 21808 (* h1 h1) (* h3 h3) (* h5 h5 h5
) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 17164 (* h1 h1) (* h3 h3) (* h5 h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 8318 (* h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2)) (* 2316 (* h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) 
(* j2 j2 j2)) (* 318 (* h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) 
(* 16 (* h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) j2) (* 128 (* h1 h1) (* h3 
h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1120 (* h1 
h1) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4192 
(* h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
8752 (* h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
11128 (* h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
8816 (* h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 4264 
(* h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 1176 (* h1 h1)
 (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 160 (* h1 h1) (* h3 h3) 
(* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 8 (* h1 h1) (* h3 h3) (* h5 h5) (* h6 h6
 h6 h6) j2) (* 8 (* h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 40 (* h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 76 (* h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 70 (* h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 
j2)) (* 34 (* h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 9
 (* h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* (* h1 h1) h3 
(* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 68 (* h1 h1) h3 (* h4 h4 h4 h4)
 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 270 (* h1 h1) h3 (* h4 h4 h4 h4
) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 386 (* h1 h1) h3 (* h4 h4 h4 h4) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 245 (* h1 h1) h3 (* h4 h4 h4 h4) (* h5
 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 72 (* h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5) h6 
(* j2 j2 j2 j2 j2)) (* 8 (* h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 
j2)) (* 82 (* h1 h1) h3 (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 223 (* h1 h1) h3 (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
194 (* h1 h1) h3 (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 70 (* h1
 h1) h3 (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 9 (* h1 h1) h3 (* h4
 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 12 (* h1 h1) h3 (* h4 h4 h4 h4) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 22 (* h1 h1) h3 (* h4 h4 h4 h4) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 12 (* h1 h1) h3 (* h4 h4 h4 h4) (* h6 h6 h6) (* j2
 j2 j2 j2 j2)) (* 2 (* h1 h1) h3 (* h4 h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2)) 
(* 8 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 48 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 116 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 146 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
104 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 43 (* h1
 h1) h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 10 (* h1 h1) h3 (* 
h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* (* h1 h1) h3 (* h4 h4 h4) (* h5 h5
 h5 h5) (* j2 j2 j2)) (* 48 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 432 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2
 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1388 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 2130 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2)) (* 1691 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2)) (* 702 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2
 j2)) (* 150 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 13 
(* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 272 (* h1 h1) h3 (* 
h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1484 (* h1 h1) 
h3 (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3027 (* h1 
h1) h3 (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2932 (* h1 
h1) h3 (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1431 (* h1 h1)
 h3 (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 334 (* h1 h1) h3 (* 
h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 29 (* h1 h1) h3 (* h4 h4 h4) 
(* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 202 (* h1 h1) h3 (* h4 h4 h4) h5 (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 791 (* h1 h1) h3 (* h4 h4 h4) h5 (* h6 h6 h6
) (* j2 j2 j2 j2 j2 j2 j2)) (* 1101 (* h1 h1) h3 (* h4 h4 h4) h5 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 659 (* h1 h1) h3 (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2
 j2 j2 j2)) (* 176 (* h1 h1) h3 (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) 
(* 17 (* h1 h1) h3 (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 12 (* h1 h1) h3
 (* h4 h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 34 (* h1 h1) h3 (* h4
 h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 34 (* h1 h1) h3 (* h4 h4 h4) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 14 (* h1 h1) h3 (* h4 h4 h4) (* h6 h6 h6 
h6) (* j2 j2 j2 j2)) (* 2 (* h1 h1) h3 (* h4 h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2)
) (* 40 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 328 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2
 j2)) (* 1112 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 2002 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2))
 (* 2048 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
1188 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 375 (* h1 
h1) h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 61 (* h1 h1) h3 (* h4 h4
) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 4 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) 
h6 (* j2 j2)) (* 104 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 1076 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4122 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 7920 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 8441 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 5147 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2)) (* 1779 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2)) (* 327 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 
j2)) (* 24 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 356 (* h1
 h1) h3 (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2234
 (* h1 h1) h3 (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
5569 (* h1 h1) h3 (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
7066 (* h1 h1) h3 (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
4885 (* h1 h1) h3 (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1844 
(* h1 h1) h3 (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 362 (* h1 h1) 
h3 (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 28 (* h1 h1) h3 (* h4 h4) 
(* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 120 (* h1 h1) h3 (* h4 h4) h5 (* h6 h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 578 (* h1 h1) h3 (* h4 h4) h5 (* h6 h6 h6 h6
) (* j2 j2 j2 j2 j2 j2 j2)) (* 1076 (* h1 h1) h3 (* h4 h4) h5 (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 971 (* h1 h1) h3 (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2
 j2 j2 j2)) (* 442 (* h1 h1) h3 (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) 
(* 97 (* h1 h1) h3 (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 8 (* h1 h1) h3 
(* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2)) (* 64 (* h1 h1) h3 h4 (* h5 h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 568 (* h1 h1) h3 h4 (* h5 h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2124 (* h1 h1) h3 h4 (* h5 h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4340 (* h1 h1) h3 h4 (* h5 h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 5256 (* h1 h1) h3 h4 (* h5 h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3833 (* h1 h1) h3 h4 (* h5 h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2)) (* 1644 (* h1 h1) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2)) (* 396 (* h1 h1) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 
52 (* h1 h1) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 3 (* h1 h1) h3 h4 (* 
h5 h5 h5 h5) (* h6 h6) j2) (* 96 (* h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 948 (* h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3804 (* h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 8190 (* h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2)) (* 10409 (* h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 8059 (* h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2)) (* 3790 (* h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2))
 (* 1056 (* h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 165 (* h1 h1
) h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 11 (* h1 h1) h3 h4 (* h5 h5 h5) 
(* h6 h6 h6) j2) (* 152 (* h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 1024 (* h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 2868 (* h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 4308 (* h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 3744 (* h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 1905 (* h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 556 (* h1 
h1) h3 h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 89 (* h1 h1) h3 h4 (* h5 h5
) (* h6 h6 h6 h6) (* j2 j2)) (* 6 (* h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6 h6) j2) 
(* 32 (* h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2
)) (* 272 (* h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 1000 (* h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 2072 (* h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2))
 (* 2640 (* h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
2114 (* h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1040 (* h1
 h1) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 292 (* h1 h1) h3 (* h5 
h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 40 (* h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6
 h6) (* j2 j2)) (* 2 (* h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6 h6) j2) (* 32 (* h1 
h1) h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 272 
(* h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
1000 (* h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
2072 (* h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2640
 (* h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2114 (* h1 
h1) h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1040 (* h1 h1) h3 (* 
h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 292 (* h1 h1) h3 (* h5 h5 h5) (* 
h6 h6 h6 h6) (* j2 j2 j2)) (* 40 (* h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2
 j2)) (* 2 (* h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6 h6) j2) (* 4 (* h1 h1) (* h4 h4
 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 20 (* h1 h1) (* h4 h4
 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 36 (* h1 h1) (* h4 h4 h4
 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 28 (* h1 h1) (* h4 h4 h4 h4) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 9 (* h1 h1) (* h4 h4 h4 h4) (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2)) (* (* h1 h1) (* h4 h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2
 j2 j2)) (* 12 (* h1 h1) (* h4 h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 40 (* h1 h1) (* h4 h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2)) (* 42 (* h1 h1) (* h4 h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 16 (* h1 h1) (* h4 h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
2 (* h1 h1) (* h4 h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 6 (* h1 h1) 
(* h4 h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 14 (* h1 h1) (* h4 
h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 7 (* h1 h1) (* h4 h4 h4 h4) 
h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* (* h1 h1) (* h4 h4 h4 h4) h5 (* h6 h6 h6)
 (* j2 j2 j2 j2)) (* 4 (* h1 h1) (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 24 (* h1 h1) (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 56 (* h1 h1) (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 64 (* h1 h1) (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 37 (* h1 h1) (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 10 (* h1 
h1) (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* (* h1 h1) (* h4 h4 h4) 
(* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 16 (* h1 h1) (* h4 h4 h4) (* h5 h5 h5) (* h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 110 (* h1 h1) (* h4 h4 h4) (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 276 (* h1 h1) (* h4 h4 h4) (* h5 h5 h5
) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 321 (* h1 h1) (* h4 h4 h4) (* h5 h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 180 (* h1 h1) (* h4 h4 h4) (* h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2)) (* 45 (* h1 h1) (* h4 h4 h4) (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2)) (* 4 (* h1 h1) (* h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)
) (* 30 (* h1 h1) (* h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 134 (* h1 h1) (* h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 215 (* h1 h1) (* h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 149 (* h1 h1) (* h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 42 
(* h1 h1) (* h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 4 (* h1 h1) 
(* h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 6 (* h1 h1) (* h4 h4 h4) h5
 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 20 (* h1 h1) (* h4 h4 h4) h5 (* h6
 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 21 (* h1 h1) (* h4 h4 h4) h5 (* h6 h6 h6 h6
) (* j2 j2 j2 j2 j2)) (* 8 (* h1 h1) (* h4 h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2
 j2)) (* (* h1 h1) (* h4 h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 12 (* h1 h1)
 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 84 (* h1
 h1) (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 238 (* 
h1 h1) (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 350 (* 
h1 h1) (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 284 (* h1 
h1) (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 124 (* h1 h1) (* 
h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 26 (* h1 h1) (* h4 h4) (* 
h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 2 (* h1 h1) (* h4 h4) (* h5 h5 h5 h5) 
(* h6 h6) (* j2 j2)) (* 20 (* h1 h1) (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 148 (* h1 h1) (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 436 (* h1 h1) (* h4 h4) (* h5 h5 h5) (* h6 h6 h6
) (* j2 j2 j2 j2 j2 j2 j2)) (* 658 (* h1 h1) (* h4 h4) (* h5 h5 h5) (* h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2)) (* 543 (* h1 h1) (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2)) (* 240 (* h1 h1) (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2)) (* 51 (* h1 h1) (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 4 
(* h1 h1) (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 18 (* h1 h1) (* h4 
h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 96 (* h1 h1) (* h4
 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 199 (* h1 h1) (* h4 
h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 202 (* h1 h1) (* h4 h4) 
(* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 103 (* h1 h1) (* h4 h4) (* h5 
h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 24 (* h1 h1) (* h4 h4) (* h5 h5) (* h6 
h6 h6 h6) (* j2 j2 j2)) (* 2 (* h1 h1) (* h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2
 j2)) (* 8 (* h1 h1) h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 60 (* h1 h1) h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 190 (* h1 h1) h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
330 (* h1 h1) h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 341 (* 
h1 h1) h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 212 (* h1 h1) h4 
(* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 76 (* h1 h1) h4 (* h5 h5 h5 h5)
 (* h6 h6 h6) (* j2 j2 j2)) (* 14 (* h1 h1) h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* 
j2 j2)) (* (* h1 h1) h4 (* h5 h5 h5 h5) (* h6 h6 h6) j2) (* 8 (* h1 h1) h4 (* h5
 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 60 (* h1 h1) h4 (* h5
 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 190 (* h1 h1) h4 (* h5 
h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 330 (* h1 h1) h4 (* h5 h5 h5
) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 341 (* h1 h1) h4 (* h5 h5 h5) (* h6 
h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 212 (* h1 h1) h4 (* h5 h5 h5) (* h6 h6 h6 h6) 
(* j2 j2 j2 j2)) (* 76 (* h1 h1) h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) 
(* 14 (* h1 h1) h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* (* h1 h1) h4 (* h5
 h5 h5) (* h6 h6 h6 h6) j2) (* 3072 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 
j2 j2 j2 j2 j2 j2)) (* 7680 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2
 j2 j2)) (* 6080 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 
2048 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2)) (* 304 h1 (* h2 h2 
h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2)) (* 16 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4
 h5 (* j2 j2)) (* 1024 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 5376 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2)) (* 
5696 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 2416 h1 (* h2 
h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 456 h1 (* h2 h2 h2 h2) (* h3 h3
 h3) h4 h6 (* j2 j2 j2)) (* 32 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2)) 
(* 1152 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
4320 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 5712 h1
 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 3240 h1 (* h2 h2 
h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 836 h1 (* h2 h2 h2 h2) (* h3 
h3 h3) (* h5 h5) (* j2 j2 j2)) (* 96 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) 
(* j2 j2)) (* 4 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) j2) (* 2816 h1 (* h2 
h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 9600 h1 (* h2 h2 h2 h2
) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 11888 h1 (* h2 h2 h2 h2) (* h3 h3
 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 6688 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h5 h6 (* 
j2 j2 j2 j2)) (* 1788 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2)) (* 212
 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2)) (* 8 h1 (* h2 h2 h2 h2) (* h3 
h3 h3) h5 h6 j2) (* 1024 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 4352 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 6464 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 4400 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 1496 h1 
(* h2 h2 h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2)) (* 248 h1 (* h2 h2 h2 h2) 
(* h3 h3 h3) (* h6 h6) (* j2 j2)) (* 16 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h6 h6
) j2) (* 1152 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 3168 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2))
 (* 2928 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 
1176 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 204 h1 (* 
h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 12 h1 (* h2 h2 h2 h2) 
(* h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 256 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 
h4) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1920 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 
h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2512 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) 
h6 (* j2 j2 j2 j2 j2 j2)) (* 1296 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h6 (* 
j2 j2 j2 j2 j2)) (* 292 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2
)) (* 24 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2 j2)) (* 1536 h1 (* 
h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 5760 h1 (* 
h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 8128 h1 (* h2 
h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 5472 h1 (* h2 h2 h2 
h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 1840 h1 (* h2 h2 h2 h2) (* h3 
h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 288 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 
h5) (* j2 j2 j2)) (* 16 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2)) (* 
2816 h1 (* h2 h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 11328
 h1 (* h2 h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 16672 h1 (* 
h2 h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 11856 h1 (* h2 h2 h2 
h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 4360 h1 (* h2 h2 h2 h2) (* h3 h3) 
h4 h5 h6 (* j2 j2 j2 j2)) (* 792 h1 (* h2 h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 
j2)) (* 56 h1 (* h2 h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2)) (* 512 h1 (* h2 h2 
h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3328 h1 (* h2 h2 
h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 6304 h1 (* h2 h2 h2 
h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 5248 h1 (* h2 h2 h2 h2) (* 
h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2152 h1 (* h2 h2 h2 h2) (* h3 h3) h4 
(* h6 h6) (* j2 j2 j2 j2)) (* 424 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h6 h6) (* 
j2 j2 j2)) (* 32 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2)) (* 288 h1 
(* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1440 h1 
(* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 2832 h1 (* 
h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2784 h1 (* h2 h2 
h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 1442 h1 (* h2 h2 h2 h2) (* 
h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 382 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 
h5 h5) (* j2 j2 j2)) (* 46 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2)) 
(* 2 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) j2) (* 1600 h1 (* h2 h2 h2 h2) 
(* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 7376 h1 (* h2 h2 h2 h2) 
(* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 13608 h1 (* h2 h2 h2 h2) (* 
h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 12884 h1 (* h2 h2 h2 h2) (* h3 h3)
 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 6658 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5)
 h6 (* j2 j2 j2 j2)) (* 1834 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 
j2)) (* 238 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2)) (* 10 h1 (* h2 
h2 h2 h2) (* h3 h3) (* h5 h5) h6 j2) (* 1664 h1 (* h2 h2 h2 h2) (* h3 h3) h5 (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 7712 h1 (* h2 h2 h2 h2) (* h3 h3) h5 (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 14432 h1 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 14096 h1 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* 7736 h1 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 
j2 j2)) (* 2378 h1 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 378 
h1 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2)) (* 24 h1 (* h2 h2 h2 h2) 
(* h3 h3) h5 (* h6 h6) j2) (* 256 h1 (* h2 h2 h2 h2) (* h3 h3) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 1408 h1 (* h2 h2 h2 h2) (* h3 h3) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 3024 h1 (* h2 h2 h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 3312 h1 (* h2 h2 h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 
j2 j2)) (* 2004 h1 (* h2 h2 h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 
672 h1 (* h2 h2 h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2)) (* 116 h1 (* h2 h2 
h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2)) (* 8 h1 (* h2 h2 h2 h2) (* h3 h3) (* h6
 h6 h6) j2) (* 288 h1 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 1152 h1 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 1776 h1 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 
j2 j2 j2)) (* 1344 h1 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 
j2)) (* 522 h1 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 96 
h1 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 6 h1 (* h2 h2 h2 
h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 176 h1 (* h2 h2 h2 h2) h3 (* h4 h4) 
h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1312 h1 (* h2 h2 h2 h2) h3 (* h4 h4) h5
 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2800 h1 (* h2 h2 h2 h2) h3 (* h4 h4) h5 h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 2676 h1 (* h2 h2 h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2
 j2 j2 j2 j2)) (* 1289 h1 (* h2 h2 h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2))
 (* 305 h1 (* h2 h2 h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 28 h1 (* h2 h2
 h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2)) (* 128 h1 (* h2 h2 h2 h2) h3 (* h4 h4) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 608 h1 (* h2 h2 h2 h2) h3 (* h4 h4) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 816 h1 (* h2 h2 h2 h2) h3 (* h4 h4) (* h6
 h6) (* j2 j2 j2 j2 j2 j2)) (* 472 h1 (* h2 h2 h2 h2) h3 (* h4 h4) (* h6 h6) (* 
j2 j2 j2 j2 j2)) (* 124 h1 (* h2 h2 h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 j2 j2 j2
)) (* 12 h1 (* h2 h2 h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 192 h1 (* h2
 h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 960 h1 (* h2 h2
 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1952 h1 (* h2 h2 h2 
h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 2080 h1 (* h2 h2 h2 h2) h3 
h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1244 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5
 h5) (* j2 j2 j2 j2 j2)) (* 412 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 
j2 j2)) (* 68 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2)) (* 4 h1 (* h2 
h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2)) (* 720 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5
) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3760 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 7904 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 8724 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2
 j2 j2 j2 j2)) (* 5479 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2))
 (* 1960 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 369 h1 (* h2 
h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2)) (* 28 h1 (* h2 h2 h2 h2) h3 h4 (* h5 
h5) h6 (* j2 j2)) (* 352 h1 (* h2 h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2 j2)) (* 2320 h1 (* h2 h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 5760 h1 (* h2 h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2
)) (* 7224 h1 (* h2 h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 5022 
h1 (* h2 h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1953 h1 (* h2 h2 h2
 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 395 h1 (* h2 h2 h2 h2) h3 h4 h5 (* 
h6 h6) (* j2 j2 j2)) (* 32 h1 (* h2 h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2)) (* 
128 h1 (* h2 h2 h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 608 h1
 (* h2 h2 h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1072 h1 (* h2 
h2 h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 920 h1 (* h2 h2 h2 h2) h3
 h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 412 h1 (* h2 h2 h2 h2) h3 h4 (* h6 h6 h6
) (* j2 j2 j2 j2)) (* 92 h1 (* h2 h2 h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2 j2)) (* 
8 h1 (* h2 h2 h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2)) (* 224 h1 (* h2 h2 h2 h2) h3 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1280 h1 (* h2 h2 h2 h2) h3 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3072 h1 (* h2 h2 h2 h2) h3 (* h5
 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 4024 h1 (* h2 h2 h2 h2) h3 (* h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2)) (* 3122 h1 (* h2 h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2
 j2 j2 j2)) (* 1450 h1 (* h2 h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 
384 h1 (* h2 h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 50 h1 (* h2 h2 h2 h2)
 h3 (* h5 h5 h5) h6 (* j2 j2)) (* 2 h1 (* h2 h2 h2 h2) h3 (* h5 h5 h5) h6 j2) 
(* 432 h1 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (* 2544 h1 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 6336 h1 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
8700 h1 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 7185 h1
 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 3642 h1 (* h2 h2 
h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 1101 h1 (* h2 h2 h2 h2) h3 (* 
h5 h5) (* h6 h6) (* j2 j2 j2)) (* 180 h1 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6) 
(* j2 j2)) (* 12 h1 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6) j2) (* 176 h1 (* h2 
h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1072 h1 (* h2 h2
 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2752 h1 (* h2 h2 h2 
h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3884 h1 (* h2 h2 h2 h2) h3 
h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3289 h1 (* h2 h2 h2 h2) h3 h5 (* h6 h6
 h6) (* j2 j2 j2 j2 j2)) (* 1706 h1 (* h2 h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 
j2 j2)) (* 527 h1 (* h2 h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 88 h1 (* 
h2 h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2)) (* 6 h1 (* h2 h2 h2 h2) h3 h5 (* h6 
h6 h6) j2) (* 32 h1 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 224 h1 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2
 j2 j2 j2 j2)) (* 592 h1 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 800 h1 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2
 j2 j2)) (* 610 h1 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2))
 (* 266 h1 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 62 h1 
(* h2 h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 6 h1 (* h2 h2 h2 h2) 
(* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 48 h1 (* h2 h2 h2 h2) (* h4 h4) h5 (* h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 240 h1 (* h2 h2 h2 h2) (* h4 h4) h5 (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 456 h1 (* h2 h2 h2 h2) (* h4 h4) h5 (* h6
 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 432 h1 (* h2 h2 h2 h2) (* h4 h4) h5 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 219 h1 (* h2 h2 h2 h2) (* h4 h4) h5 (* h6 h6) (* j2 j2
 j2 j2 j2)) (* 57 h1 (* h2 h2 h2 h2) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 
6 h1 (* h2 h2 h2 h2) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 32 h1 (* h2 h2 h2 
h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 224 h1 (* h2 h2 h2 
h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 656 h1 (* h2 h2 h2 h2)
 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1056 h1 (* h2 h2 h2 h2) h4 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1026 h1 (* h2 h2 h2 h2) h4 (* h5 h5
 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 618 h1 (* h2 h2 h2 h2) h4 (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2)) (* 226 h1 (* h2 h2 h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) 
(* 46 h1 (* h2 h2 h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 4 h1 (* h2 h2 h2 h2
) h4 (* h5 h5 h5) h6 (* j2 j2)) (* 64 h1 (* h2 h2 h2 h2) h4 (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 432 h1 (* h2 h2 h2 h2) h4 (* h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1248 h1 (* h2 h2 h2 h2) h4 (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2008 h1 (* h2 h2 h2 h2) h4 (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1964 h1 (* h2 h2 h2 h2) h4 (* h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 1195 h1 (* h2 h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2)) (* 442 h1 (* h2 h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2
)) (* 91 h1 (* h2 h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 8 h1 (* h2 
h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 48 h1 (* h2 h2 h2 h2) h4 h5 (* h6
 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 256 h1 (* h2 h2 h2 h2) h4 h5 (* h6 h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 568 h1 (* h2 h2 h2 h2) h4 h5 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 680 h1 (* h2 h2 h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 475 h1 (* h2 h2 h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 194 h1 (* h2 h2 h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 43 h1 (* h2 h2 
h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 4 h1 (* h2 h2 h2 h2) h4 h5 (* h6 h6 
h6) (* j2 j2)) (* 32 h1 (* h2 h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 224 h1 (* h2 h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 688 h1 (* h2 h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 1216 h1 (* h2 h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 1362 h1 (* h2 h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 1002 h1 (* h2 h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 484 h1 (* h2 h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 148 h1 (* 
h2 h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 26 h1 (* h2 h2 h2 h2) (* h5
 h5 h5) (* h6 h6) (* j2 j2)) (* 2 h1 (* h2 h2 h2 h2) (* h5 h5 h5) (* h6 h6) j2) 
(* 32 h1 (* h2 h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2
)) (* 224 h1 (* h2 h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 688 h1 (* h2 h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 1216 h1 (* h2 h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 1362 h1 (* h2 h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1002
 h1 (* h2 h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 484 h1 (* h2 
h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 148 h1 (* h2 h2 h2 h2) (* 
h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 26 h1 (* h2 h2 h2 h2) (* h5 h5) (* h6 h6 h6
) (* j2 j2)) (* 2 h1 (* h2 h2 h2 h2) (* h5 h5) (* h6 h6 h6) j2) (* 3072 h1 (* h2
 h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 9216 h1 (* h2 h2 h2) 
(* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 9152 h1 (* h2 h2 h2) (* h3 h3 h3
 h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 3552 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 (* 
j2 j2 j2 j2)) (* 576 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2)) (* 32 
h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2)) (* 1024 h1 (* h2 h2 h2) (* h3 
h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 5888 h1 (* h2 h2 h2) (* h3 h3 h3 h3
) h4 h6 (* j2 j2 j2 j2 j2 j2)) (* 8128 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h6 (* 
j2 j2 j2 j2 j2)) (* 4048 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2)) 
(* 848 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2)) (* 64 h1 (* h2 h2 h2)
 (* h3 h3 h3 h3) h4 h6 (* j2 j2)) (* 1152 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 
h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 4896 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) 
(* j2 j2 j2 j2 j2 j2)) (* 7584 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 
j2 j2 j2 j2)) (* 5160 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2))
 (* 1496 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2)) (* 184 h1 (* h2
 h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2)) (* 8 h1 (* h2 h2 h2) (* h3 h3 h3 h3
) (* h5 h5) j2) (* 2816 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 11008 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2)) 
(* 15984 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 10584 h1 
(* h2 h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 3184 h1 (* h2 h2 h2) (* 
h3 h3 h3 h3) h5 h6 (* j2 j2 j2)) (* 408 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h5 h6 
(* j2 j2)) (* 16 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h5 h6 j2) (* 1024 h1 (* h2 h2 
h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4864 h1 (* h2 h2 h2) 
(* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 8384 h1 (* h2 h2 h2) (* h3 
h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 6672 h1 (* h2 h2 h2) (* h3 h3 h3 h3) 
(* h6 h6) (* j2 j2 j2 j2)) (* 2560 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* 
j2 j2 j2)) (* 464 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2)) (* 32 h1 
(* h2 h2 h2) (* h3 h3 h3 h3) (* h6 h6) j2) (* 3968 h1 (* h2 h2 h2) (* h3 h3 h3) 
(* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 13920 h1 (* h2 h2 h2) (* h3 h3 h3) 
(* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 17440 h1 (* h2 h2 h2) (* h3 h3 h3) (* 
h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 9712 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) 
h5 (* j2 j2 j2 j2 j2)) (* 2596 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 
j2 j2 j2)) (* 328 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 16 
h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2)) (* 512 h1 (* h2 h2 h2) (* 
h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6144 h1 (* h2 h2 h2) (* 
h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 12704 h1 (* h2 h2 h2) (* h3 
h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 9584 h1 (* h2 h2 h2) (* h3 h3 h3) 
(* h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 3296 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) 
h6 (* j2 j2 j2 j2)) (* 528 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2
)) (* 32 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2)) (* 4272 h1 (* h2 
h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 19512 h1 (* h2 
h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 33172 h1 (* h2 h2 
h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 26778 h1 (* h2 h2 h2) 
(* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 11152 h1 (* h2 h2 h2) (* h3 h3 
h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 2350 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 
h5) (* j2 j2 j2)) (* 228 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2)) 
(* 8 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) j2) (* 8960 h1 (* h2 h2 h2) (* h3
 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 42304 h1 (* h2 h2 h2) (* h3 h3 
h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 75264 h1 (* h2 h2 h2) (* h3 h3 h3) h4 
h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 63720 h1 (* h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* 
j2 j2 j2 j2 j2)) (* 28380 h1 (* h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2))
 (* 6708 h1 (* h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 772 h1 (* h2 h2 
h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2)) (* 32 h1 (* h2 h2 h2) (* h3 h3 h3) h4 h5 h6
 j2) (* 1024 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 9216 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2))
 (* 23872 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
26784 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 14848 h1 
(* h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 4232 h1 (* h2 h2 h2) 
(* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2)) (* 592 h1 (* h2 h2 h2) (* h3 h3 h3) h4 
(* h6 h6) (* j2 j2)) (* 32 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6) j2) (* 576 
h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3312 
h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 7320 h1 
(* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 7908 h1 (* h2 
h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 4462 h1 (* h2 h2 h2) (* 
h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 1328 h1 (* h2 h2 h2) (* h3 h3 h3) (* 
h5 h5 h5) (* j2 j2 j2)) (* 174 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 
j2)) (* 8 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) j2) (* 4400 h1 (* h2 h2 h2) 
(* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 23704 h1 (* h2 h2 h2) 
(* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 50140 h1 (* h2 h2 h2) (* 
h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 53370 h1 (* h2 h2 h2) (* h3 h3 
h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 30614 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5
 h5) h6 (* j2 j2 j2 j2)) (* 9428 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2
 j2 j2)) (* 1410 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2)) (* 74 h1 
(* h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 j2) (* 4992 h1 (* h2 h2 h2) (* h3 h3 h3) 
h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 26784 h1 (* h2 h2 h2) (* h3 h3 h3) 
h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 57424 h1 (* h2 h2 h2) (* h3 h3 h3) h5 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 62984 h1 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 
h6) (* j2 j2 j2 j2 j2)) (* 38044 h1 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2
 j2 j2 j2)) (* 12756 h1 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 
2220 h1 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2)) (* 156 h1 (* h2 h2 h2)
 (* h3 h3 h3) h5 (* h6 h6) j2) (* 512 h1 (* h2 h2 h2) (* h3 h3 h3) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3072 h1 (* h2 h2 h2) (* h3 h3 h3) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 7328 h1 (* h2 h2 h2) (* h3 h3 h3) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 9008 h1 (* h2 h2 h2) (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 
j2 j2 j2)) (* 6128 h1 (* h2 h2 h2) (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2)) 
(* 2288 h1 (* h2 h2 h2) (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2)) (* 432 h1 (* h2 
h2 h2) (* h3 h3 h3) (* h6 h6 h6) (* j2 j2)) (* 32 h1 (* h2 h2 h2) (* h3 h3 h3) 
(* h6 h6 h6) j2) (* 272 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 2264 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 4412 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 
j2 j2 j2 j2)) (* 3138 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 
j2 j2)) (* 988 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 
144 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 8 h1 (* h2 h2 
h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 448 h1 (* h2 h2 h2) (* h3 h3) (* 
h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2704 h1 (* h2 h2 h2) (* h3 h3) (* 
h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2856 h1 (* h2 h2 h2) (* h3 h3) (* h4 
h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 1192 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) 
h6 (* j2 j2 j2 j2 j2)) (* 224 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h6 (* j2 j2
 j2 j2)) (* 16 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2)) (* 1408 
h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 7952 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 16856 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 
j2)) (* 17236 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2
)) (* 9106 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 
2474 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 320 h1 
(* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 16 h1 (* h2 h2 h2) 
(* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 1344 h1 (* h2 h2 h2) (* h3 h3) (* h4
 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 12528 h1 (* h2 h2 h2) (* h3 h3) 
(* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 32536 h1 (* h2 h2 h2) (* h3 h3) 
(* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 36748 h1 (* h2 h2 h2) (* h3 h3) (* 
h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 21366 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4)
 h5 h6 (* j2 j2 j2 j2 j2)) (* 6658 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* 
j2 j2 j2 j2)) (* 1046 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) 
(* 64 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 1408 h1 (* h2 h2 
h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 8448 h1 (* h2 
h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 13176 h1 (* h2
 h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 9076 h1 (* h2 h2
 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 3108 h1 (* h2 h2 h2) 
(* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 512 h1 (* h2 h2 h2) (* h3 h3) 
(* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 32 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* 
h6 h6) (* j2 j2)) (* 768 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 5064 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 13148 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 
j2 j2 j2 j2 j2)) (* 17494 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 
j2 j2 j2)) (* 12889 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)
) (* 5264 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 1129 h1 
(* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2)) (* 112 h1 (* h2 h2 h2) (* 
h3 h3) h4 (* h5 h5 h5) (* j2 j2)) (* 4 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5)
 j2) (* 3248 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 21888 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 57816 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2)) (* 78364 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 59831 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 26291 
h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 6441 h1 (* h2 h2 
h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 791 h1 (* h2 h2 h2) (* h3 h3) h4 
(* h5 h5) h6 (* j2 j2)) (* 36 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 j2) (* 
1872 h1 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 16472 h1 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 50076 h1 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
74186 h1 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 60888 
h1 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 29034 h1 (* h2 
h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 7928 h1 (* h2 h2 h2) (* h3 
h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 1130 h1 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 
h6) (* j2 j2)) (* 64 h1 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) j2) (* 1088 h1 
(* h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6448 h1 
(* h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 13224 h1 (* 
h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 13080 h1 (* h2 h2 
h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 6940 h1 (* h2 h2 h2) (* h3 
h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1996 h1 (* h2 h2 h2) (* h3 h3) h4 (* h6 
h6 h6) (* j2 j2 j2)) (* 288 h1 (* h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2))
 (* 16 h1 (* h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6) j2) (* 144 h1 (* h2 h2 h2) (* 
h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 792 h1 (* h2 h2 h2) (* h3
 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1740 h1 (* h2 h2 h2) (* h3 h3)
 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1938 h1 (* h2 h2 h2) (* h3 h3) (* h5 
h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 1144 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) 
(* j2 j2 j2 j2)) (* 340 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2)) 
(* 44 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2)) (* 2 h1 (* h2 h2 h2) 
(* h3 h3) (* h5 h5 h5 h5) j2) (* 864 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 6216 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 18372 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 29118 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 26921 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* 14692 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)
) (* 4524 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 692 h1 (* 
h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2)) (* 37 h1 (* h2 h2 h2) (* h3 h3) 
(* h5 h5 h5) h6 j2) (* 1840 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 13440 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 40312 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6
 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 65148 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 62151 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6
 h6) (* j2 j2 j2 j2 j2)) (* 35815 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2)) (* 12141 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2
 j2)) (* 2204 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 163 h1
 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) j2) (* 800 h1 (* h2 h2 h2) (* h3 h3)
 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 6400 h1 (* h2 h2 h2) (* h3 
h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 20240 h1 (* h2 h2 h2) (* h3 
h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 33688 h1 (* h2 h2 h2) (* h3 h3)
 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 32570 h1 (* h2 h2 h2) (* h3 h3) h5 
(* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 18818 h1 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 
h6) (* j2 j2 j2 j2)) (* 6364 h1 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 
j2)) (* 1154 h1 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 86 h1 (* h2
 h2 h2) (* h3 h3) h5 (* h6 h6 h6) j2) (* 128 h1 (* h2 h2 h2) (* h3 h3) (* h6 h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 768 h1 (* h2 h2 h2) (* h3 h3) (* h6 h6 h6
 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1832 h1 (* h2 h2 h2) (* h3 h3) (* h6 h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2)) (* 2252 h1 (* h2 h2 h2) (* h3 h3) (* h6 h6 h6 h6) (* j2 
j2 j2 j2 j2)) (* 1532 h1 (* h2 h2 h2) (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2))
 (* 572 h1 (* h2 h2 h2) (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 108 h1 (* h2 
h2 h2) (* h3 h3) (* h6 h6 h6 h6) (* j2 j2)) (* 8 h1 (* h2 h2 h2) (* h3 h3) (* h6
 h6 h6 h6) j2) (* 32 h1 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 528 h1 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 1704 h1 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 2268 h1 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 
j2 j2 j2 j2 j2)) (* 1460 h1 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 
j2 j2 j2)) (* 468 h1 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) 
(* 70 h1 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 4 h1 (* h2 
h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 200 h1 (* h2 h2 h2) h3 (* h4 
h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1748 h1 (* h2 h2 h2) h3 (* h4 h4
 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3638 h1 (* h2 h2 h2) h3 (* h4 h4 h4) 
h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 3155 h1 (* h2 h2 h2) h3 (* h4 h4 h4) h5 h6 
(* j2 j2 j2 j2 j2 j2)) (* 1318 h1 (* h2 h2 h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2
 j2 j2)) (* 262 h1 (* h2 h2 h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 20 h1 
(* h2 h2 h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 96 h1 (* h2 h2 h2) h3 (* h4 
h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 720 h1 (* h2 h2 h2) h3 (* h4 h4
 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 920 h1 (* h2 h2 h2) h3 (* h4 h4 h4) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 460 h1 (* h2 h2 h2) h3 (* h4 h4 h4) (* h6 h6
) (* j2 j2 j2 j2 j2)) (* 100 h1 (* h2 h2 h2) h3 (* h4 h4 h4) (* h6 h6) (* j2 j2 
j2 j2)) (* 8 h1 (* h2 h2 h2) h3 (* h4 h4 h4) (* h6 h6) (* j2 j2 j2)) (* 32 h1 
(* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 632
 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
2580 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
4626 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 4329
 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2206 h1 (* 
h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 597 h1 (* h2 h2 h2) 
h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 78 h1 (* h2 h2 h2) h3 (* h4 h4) 
(* h5 h5 h5) (* j2 j2 j2)) (* 4 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 
j2)) (* 224 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2
 j2 j2)) (* 2784 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 10624 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 19008 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 18422 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)
) (* 10166 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 3159
 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 507 h1 (* h2 h2 
h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 32 h1 (* h2 h2 h2) h3 (* h4 h4) 
(* h5 h5) h6 (* j2 j2)) (* 680 h1 (* h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 5172 h1 (* h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 12854 h1 (* h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 15119 h1 (* h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 9472 h1 (* h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 
j2 j2)) (* 3215 h1 (* h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 
549 h1 (* h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 36 h1 (* h2 h2 h2
) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 160 h1 (* h2 h2 h2) h3 (* h4 h4) (* h6
 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1088 h1 (* h2 h2 h2) h3 (* h4 h4) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2040 h1 (* h2 h2 h2) h3 (* h4 h4) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 1640 h1 (* h2 h2 h2) h3 (* h4 h4) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2)) (* 636 h1 (* h2 h2 h2) h3 (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2
)) (* 116 h1 (* h2 h2 h2) h3 (* h4 h4) (* h6 h6 h6) (* j2 j2 j2)) (* 8 h1 (* h2 
h2 h2) h3 (* h4 h4) (* h6 h6 h6) (* j2 j2)) (* 96 h1 (* h2 h2 h2) h3 h4 (* h5 h5
 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 528 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5
 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1192 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 1420 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2
 j2 j2 j2 j2)) (* 952 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) 
(* 352 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 64 h1 (* h2 h2 
h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2)) (* 4 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5 
h5) (* j2 j2)) (* 192 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2
 j2 j2 j2 j2)) (* 2280 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 9244 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 18754 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)
) (* 21765 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 15177
 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 6360 h1 (* h2 h2 
h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 1527 h1 (* h2 h2 h2) h3 h4 (* h5 
h5 h5) h6 (* j2 j2 j2)) (* 185 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2)) 
(* 8 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5) h6 j2) (* 352 h1 (* h2 h2 h2) h3 h4 (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3792 h1 (* h2 h2 h2) h3 
h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 15448 h1 (* h2 h2 h2) 
h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 32556 h1 (* h2 h2 h2) 
h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 39956 h1 (* h2 h2 h2) h3 
h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 29956 h1 (* h2 h2 h2) h3 h4 (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 13796 h1 (* h2 h2 h2) h3 h4 (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2)) (* 3765 h1 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* 
j2 j2 j2)) (* 549 h1 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 32 h1 
(* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) j2) (* 568 h1 (* h2 h2 h2) h3 h4 h5 (* h6
 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4052 h1 (* h2 h2 h2) h3 h4 h5 (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 11302 h1 (* h2 h2 h2) h3 h4 h5 (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 16431 h1 (* h2 h2 h2) h3 h4 h5 (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 13731 h1 (* h2 h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 
j2 j2)) (* 6767 h1 (* h2 h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1914 
h1 (* h2 h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 281 h1 (* h2 h2 h2) h3 h4
 h5 (* h6 h6 h6) (* j2 j2)) (* 16 h1 (* h2 h2 h2) h3 h4 h5 (* h6 h6 h6) j2) (* 
64 h1 (* h2 h2 h2) h3 h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 336 h1 
(* h2 h2 h2) h3 h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 672 h1 (* h2 h2 
h2) h3 h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 660 h1 (* h2 h2 h2) h3 h4 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 336 h1 (* h2 h2 h2) h3 h4 (* h6 h6 h6 h6)
 (* j2 j2 j2 j2)) (* 84 h1 (* h2 h2 h2) h3 h4 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 8
 h1 (* h2 h2 h2) h3 h4 (* h6 h6 h6 h6) (* j2 j2)) (* 112 h1 (* h2 h2 h2) h3 (* 
h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 696 h1 (* h2 h2 h2) h3 (* h5 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1828 h1 (* h2 h2 h2) h3 (* h5 h5 h5
 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2634 h1 (* h2 h2 h2) h3 (* h5 h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 2256 h1 (* h2 h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2
 j2 j2)) (* 1158 h1 (* h2 h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 338 
h1 (* h2 h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 48 h1 (* h2 h2 h2) h3 (* 
h5 h5 h5 h5) h6 (* j2 j2)) (* 2 h1 (* h2 h2 h2) h3 (* h5 h5 h5 h5) h6 j2) (* 160
 h1 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 1616 h1 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 6576 h1 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2))
 (* 14532 h1 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 19458 h1 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
16464 h1 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 8819 h1 
(* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 2881 h1 (* h2 h2 h2) 
h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 519 h1 (* h2 h2 h2) h3 (* h5 h5 h5) 
(* h6 h6) (* j2 j2)) (* 39 h1 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) j2) (* 160 
h1 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
1600 h1 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 6512 h1 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 14464 h1 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
19526 h1 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 16700 
h1 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 9067 h1 (* h2 
h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 3013 h1 (* h2 h2 h2) h3 (* 
h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 555 h1 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 
h6) (* j2 j2)) (* 43 h1 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) j2) (* 88 h1 (* 
h2 h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 580 h1 (* h2 
h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1622 h1 (* h2 h2 h2
) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2507 h1 (* h2 h2 h2) h3 h5 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2333 h1 (* h2 h2 h2) h3 h5 (* h6 h6 h6
 h6) (* j2 j2 j2 j2 j2)) (* 1331 h1 (* h2 h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 
j2 j2)) (* 451 h1 (* h2 h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 82 h1 (* 
h2 h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2)) (* 6 h1 (* h2 h2 h2) h3 h5 (* h6 h6 
h6 h6) j2) (* 16 h1 (* h2 h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 200 h1 (* h2 h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2
 j2 j2 j2 j2)) (* 628 h1 (* h2 h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 886 h1 (* h2 h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2
 j2 j2)) (* 654 h1 (* h2 h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2))
 (* 260 h1 (* h2 h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 52 h1 
(* h2 h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 4 h1 (* h2 h2 h2) (* 
h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 24 h1 (* h2 h2 h2) (* h4 h4 h4) h5 (* h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 212 h1 (* h2 h2 h2) (* h4 h4 h4) h5 (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 474 h1 (* h2 h2 h2) (* h4 h4 h4) h5 (* h6
 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 455 h1 (* h2 h2 h2) (* h4 h4 h4) h5 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 214 h1 (* h2 h2 h2) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2
 j2 j2 j2)) (* 48 h1 (* h2 h2 h2) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 
4 h1 (* h2 h2 h2) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 32 h1 (* h2 h2 h2) 
(* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 312 h1 (* h2 h2 
h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1076 h1 (* h2 
h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1866 h1 (* h2 
h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1833 h1 (* h2 h2 
h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 1056 h1 (* h2 h2 h2) (* 
h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 349 h1 (* h2 h2 h2) (* h4 h4) (* 
h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 60 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5) h6 
(* j2 j2 j2)) (* 4 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 48 h1
 (* h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 536 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 1964 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 3530 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 3550 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 2078 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 694 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 120 h1 
(* h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 8 h1 (* h2 h2 h2) 
(* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 48 h1 (* h2 h2 h2) (* h4 h4) h5 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 352 h1 (* h2 h2 h2) (* h4 h4) h5 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 912 h1 (* h2 h2 h2) (* h4 h4) h5 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1156 h1 (* h2 h2 h2) (* h4 h4) h5 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 793 h1 (* h2 h2 h2) (* h4 h4) h5 (* h6 h6 h6
) (* j2 j2 j2 j2 j2)) (* 297 h1 (* h2 h2 h2) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 
j2 j2)) (* 56 h1 (* h2 h2 h2) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 4 h1 
(* h2 h2 h2) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2)) (* 16 h1 (* h2 h2 h2) h4 (* h5
 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 120 h1 (* h2 h2 h2) h4 (* h5
 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 380 h1 (* h2 h2 h2) h4 (* h5 h5
 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 666 h1 (* h2 h2 h2) h4 (* h5 h5 h5 h5
) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 708 h1 (* h2 h2 h2) h4 (* h5 h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2)) (* 468 h1 (* h2 h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 
j2)) (* 188 h1 (* h2 h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 42 h1 (* 
h2 h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 4 h1 (* h2 h2 h2) h4 (* h5 h5 
h5 h5) h6 (* j2 j2)) (* 64 h1 (* h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2
 j2 j2 j2 j2 j2 j2 j2)) (* 544 h1 (* h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 1936 h1 (* h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 3800 h1 (* h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 4536 h1 (* h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 3408 h1 (* h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2)) (* 1604 h1 (* h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 
452 h1 (* h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 68 h1 (* h2 h2 h2
) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 4 h1 (* h2 h2 h2) h4 (* h5 h5 h5) (* 
h6 h6) j2) (* 48 h1 (* h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 456 h1 (* h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2 j2)) (* 1732 h1 (* h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 3542 h1 (* h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 4344 h1 (* h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 3324 h1 (* h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
1584 h1 (* h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 450 h1 (* h2 
h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 68 h1 (* h2 h2 h2) h4 (* h5 h5
) (* h6 h6 h6) (* j2 j2)) (* 4 h1 (* h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6) j2) (* 
24 h1 (* h2 h2 h2) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 140 
h1 (* h2 h2 h2) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 342 h1 (* 
h2 h2 h2) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 453 h1 (* h2 h2 h2)
 h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 351 h1 (* h2 h2 h2) h4 h5 (* h6
 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 159 h1 (* h2 h2 h2) h4 h5 (* h6 h6 h6 h6) (* 
j2 j2 j2 j2)) (* 39 h1 (* h2 h2 h2) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 4 h1 
(* h2 h2 h2) h4 h5 (* h6 h6 h6 h6) (* j2 j2)) (* 16 h1 (* h2 h2 h2) (* h5 h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 120 h1 (* h2 h2 h2) (* h5 h5
 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 396 h1 (* h2 h2 h2) (* h5 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 754 h1 (* h2 h2 h2) (* h5 h5
 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 912 h1 (* h2 h2 h2) (* h5 h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 726 h1 (* h2 h2 h2) (* h5 h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2)) (* 380 h1 (* h2 h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2)) (* 126 h1 (* h2 h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 
24 h1 (* h2 h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 2 h1 (* h2 h2 h2) (* 
h5 h5 h5 h5) (* h6 h6) j2) (* 32 h1 (* h2 h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 240 h1 (* h2 h2 h2) (* h5 h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 792 h1 (* h2 h2 h2) (* h5 h5 h5) (* h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1508 h1 (* h2 h2 h2) (* h5 h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 1824 h1 (* h2 h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 1452 h1 (* h2 h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2)) (* 760 h1 (* h2 h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 
252 h1 (* h2 h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 48 h1 (* h2 h2 h2
) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 4 h1 (* h2 h2 h2) (* h5 h5 h5) (* h6 
h6 h6) j2) (* 16 h1 (* h2 h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 120 h1 (* h2 h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2 j2)) (* 396 h1 (* h2 h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 754 h1 (* h2 h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2
 j2 j2)) (* 912 h1 (* h2 h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2))
 (* 726 h1 (* h2 h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 380 h1 
(* h2 h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 126 h1 (* h2 h2 h2) 
(* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 24 h1 (* h2 h2 h2) (* h5 h5) (* h6 h6
 h6 h6) (* j2 j2)) (* 2 h1 (* h2 h2 h2) (* h5 h5) (* h6 h6 h6 h6) j2) (* 2816 h1
 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 10432 h1
 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 14336 h1 
(* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 9184 h1 (* h2 
h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 2864 h1 (* h2 h2) (* h3 
h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 424 h1 (* h2 h2) (* h3 h3 h3 h3) (* 
h4 h4) h5 (* j2 j2 j2)) (* 24 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2
)) (* 256 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2 j2))
 (* 4224 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
9744 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 8704 h1
 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 3552 h1 (* h2 h2)
 (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2)) (* 672 h1 (* h2 h2) (* h3 h3 h3 
h3) (* h4 h4) h6 (* j2 j2 j2)) (* 48 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h6 
(* j2 j2)) (* 2736 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 13104 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 
j2 j2)) (* 23772 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)
) (* 20640 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 9196
 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 2212 h1 (* h2 h2)
 (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 264 h1 (* h2 h2) (* h3 h3 h3 h3) 
h4 (* h5 h5) (* j2 j2)) (* 12 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) j2) (* 
6144 h1 (* h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 30208
 h1 (* h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 57344 h1 (* 
h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 52864 h1 (* h2 h2) (* 
h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 25408 h1 (* h2 h2) (* h3 h3 h3 h3) 
h4 h5 h6 (* j2 j2 j2 j2)) (* 6680 h1 (* h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2
 j2)) (* 904 h1 (* h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2)) (* 48 h1 (* h2 h2)
 (* h3 h3 h3 h3) h4 h5 h6 j2) (* 512 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 5888 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 17184 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 21856 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 
j2 j2 j2)) (* 13952 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) 
(* 4608 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2)) (* 752 h1 (* h2 
h2) (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2)) (* 48 h1 (* h2 h2) (* h3 h3 h3 h3) 
h4 (* h6 h6) j2) (* 288 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2
 j2 j2 j2 j2)) (* 1728 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 
j2 j2 j2)) (* 4056 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 
j2)) (* 4680 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 
2732 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 756 h1 (* h2 
h2) (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2)) (* 92 h1 (* h2 h2) (* h3 h3 h3 h3
) (* h5 h5 h5) (* j2 j2)) (* 4 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) j2) (* 
2800 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
15712 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
34916 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 39064 
h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 23224 h1 (* h2 
h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 7256 h1 (* h2 h2) (* h3 h3 
h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 1164 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5)
 h6 (* j2 j2)) (* 72 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 j2) (* 3328 h1 
(* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 18624 h1 
(* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 42080 h1 (* 
h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 48896 h1 (* h2 h2)
 (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 31056 h1 (* h2 h2) (* h3 h3
 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 10736 h1 (* h2 h2) (* h3 h3 h3 h3) h5 
(* h6 h6) (* j2 j2 j2)) (* 1936 h1 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 
j2)) (* 144 h1 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) j2) (* 256 h1 (* h2 h2) 
(* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1664 h1 (* h2 h2) 
(* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4368 h1 (* h2 h2) (* 
h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 5984 h1 (* h2 h2) (* h3 h3 
h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 4576 h1 (* h2 h2) (* h3 h3 h3 h3) (* 
h6 h6 h6) (* j2 j2 j2 j2)) (* 1920 h1 (* h2 h2) (* h3 h3 h3 h3) (* h6 h6 h6) (* 
j2 j2 j2)) (* 400 h1 (* h2 h2) (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2)) (* 32 h1 
(* h2 h2) (* h3 h3 h3 h3) (* h6 h6 h6) j2) (* 544 h1 (* h2 h2) (* h3 h3 h3) (* 
h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3456 h1 (* h2 h2) (* h3 h3 h3) 
(* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 7064 h1 (* h2 h2) (* h3 h3 h3) 
(* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 6016 h1 (* h2 h2) (* h3 h3 h3) (* 
h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 2216 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 
h4) h5 (* j2 j2 j2 j2 j2)) (* 376 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* 
j2 j2 j2 j2)) (* 24 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 
768 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
3872 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 5176
 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 2600 h1 (* 
h2 h2) (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 576 h1 (* h2 h2) (* 
h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2)) (* 48 h1 (* h2 h2) (* h3 h3 h3) (* h4
 h4 h4) h6 (* j2 j2 j2)) (* 1952 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 11544 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 26104 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4)
 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 28982 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4
) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 16846 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) 
(* h5 h5) (* j2 j2 j2 j2 j2)) (* 5068 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 
h5) (* j2 j2 j2 j2)) (* 738 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 
j2 j2)) (* 42 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 2160 
h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
18064 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
49404 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
61520 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 38980 
h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 13156 h1 (* h2 
h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 2268 h1 (* h2 h2) (* h3 h3 
h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 156 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 
h6 (* j2 j2)) (* 2048 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 11808 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2
 j2 j2 j2 j2 j2)) (* 21192 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 17136 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2
 j2 j2 j2)) (* 6848 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2
)) (* 1312 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 96 h1 
(* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2)) (* 960 h1 (* h2 h2) (* h3 
h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 6768 h1 (* h2 h2) (* 
h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 18808 h1 (* h2 h2) (* 
h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 26616 h1 (* h2 h2) (* h3 
h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 20778 h1 (* h2 h2) (* h3 h3 h3)
 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 9109 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 
h5 h5) (* j2 j2 j2 j2)) (* 2162 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 
j2 j2)) (* 259 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2)) (* 12 h1 (* 
h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) j2) (* 4336 h1 (* h2 h2) (* h3 h3 h3) h4 (* 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 30664 h1 (* h2 h2) (* h3 h3 h3) h4 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 85580 h1 (* h2 h2) (* h3 h3 h3) h4 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 122610 h1 (* h2 h2) (* h3 h3 h3) h4 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 98344 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 
h5) h6 (* j2 j2 j2 j2 j2)) (* 45424 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 
(* j2 j2 j2 j2)) (* 11742 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)
) (* 1570 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 84 h1 (* h2 h2
) (* h3 h3 h3) h4 (* h5 h5) h6 j2) (* 2688 h1 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 23088 h1 (* h2 h2) (* h3 h3 h3) h4 h5 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 73472 h1 (* h2 h2) (* h3 h3 h3) h4 h5 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 116868 h1 (* h2 h2) (* h3 h3 h3) h4 h5 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 103136 h1 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6
 h6) (* j2 j2 j2 j2 j2)) (* 52400 h1 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* 
j2 j2 j2 j2)) (* 15188 h1 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) 
(* 2320 h1 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 144 h1 (* h2 h2)
 (* h3 h3 h3) h4 h5 (* h6 h6) j2) (* 1408 h1 (* h2 h2) (* h3 h3 h3) h4 (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 8640 h1 (* h2 h2) (* h3 h3 h3) h4 (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 19512 h1 (* h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2)) (* 21896 h1 (* h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6) (* j2
 j2 j2 j2 j2)) (* 13344 h1 (* h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2
)) (* 4416 h1 (* h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2)) (* 736 h1 (* 
h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2)) (* 48 h1 (* h2 h2) (* h3 h3 h3) 
h4 (* h6 h6 h6) j2) (* 144 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 864 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 
j2 j2 j2 j2)) (* 2028 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 
j2 j2)) (* 2340 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) 
(* 1366 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 378 h1 (* 
h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 46 h1 (* h2 h2) (* h3 h3 h3
) (* h5 h5 h5 h5) (* j2 j2)) (* 2 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) j2) 
(* 1056 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 8128 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2))
 (* 25544 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 42624 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
41126 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 23375 h1 
(* h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 7533 h1 (* h2 h2) (* 
h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 1200 h1 (* h2 h2) (* h3 h3 h3) (* h5 
h5 h5) h6 (* j2 j2)) (* 74 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 j2) (* 2384
 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 18320 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 57612 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2
 j2)) (* 97052 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 95888 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 57000 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 19886
 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 3674 h1 (* h2 h2
) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 276 h1 (* h2 h2) (* h3 h3 h3) 
(* h5 h5) (* h6 h6) j2) (* 1072 h1 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 8672 h1 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 28460 h1 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 50044 h1 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 51812 h1 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 
j2 j2)) (* 32340 h1 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 
11832 h1 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 2304 h1 (* h2 
h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 184 h1 (* h2 h2) (* h3 h3 h3) h5 
(* h6 h6 h6) j2) (* 128 h1 (* h2 h2) (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2
 j2 j2 j2 j2)) (* 832 h1 (* h2 h2) (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 2184 h1 (* h2 h2) (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 2992 h1 (* h2 h2) (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
2288 h1 (* h2 h2) (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 960 h1 (* h2 
h2) (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 200 h1 (* h2 h2) (* h3 h3 h3) 
(* h6 h6 h6 h6) (* j2 j2)) (* 16 h1 (* h2 h2) (* h3 h3 h3) (* h6 h6 h6 h6) j2) 
(* 136 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (* 536 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 702 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 
362 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 80 h1 
(* h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 6 h1 (* h2 h2) (* 
h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 160 h1 (* h2 h2) (* h3 h3) (* h4 
h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 504 h1 (* h2 h2) (* h3 h3) (* h4 h4
 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 388 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4 
h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 116 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) h6 
(* j2 j2 j2 j2 j2)) (* 12 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) h6 (* j2 j2 j2 
j2)) (* 96 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2
 j2 j2 j2)) (* 1424 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 5180 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2
 j2 j2 j2 j2 j2 j2)) (* 7868 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2
 j2 j2 j2 j2 j2 j2)) (* 5761 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2
 j2 j2 j2 j2 j2)) (* 2149 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2
 j2 j2 j2)) (* 369 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)
) (* 24 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 1056 h1 
(* h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 6776 
h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 13964 
h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 12276 h1 
(* h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 5386 h1 (* h2 
h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 1152 h1 (* h2 h2) (* h3 
h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 96 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4
) h5 h6 (* j2 j2 j2)) (* 704 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 3416 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 4404 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 2352 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h6 h6) (* 
j2 j2 j2 j2 j2)) (* 552 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 
j2 j2)) (* 48 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2)) (* 96 
h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (* 1664 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 7272 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 14280 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2
 j2 j2 j2)) (* 14684 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 
j2 j2 j2)) (* 8246 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 
j2)) (* 2489 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 
364 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 21 h1 (* h2 
h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 480 h1 (* h2 h2) (* h3 h3) 
(* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 6512 h1 (* h2 h2) 
(* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 27704 h1 (* 
h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 54668 h1
 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 57564 
h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 34188 h1
 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 11350 h1 (* 
h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 1947 h1 (* h2 h2) 
(* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 135 h1 (* h2 h2) (* h3 h3) (* 
h4 h4) (* h5 h5) h6 (* j2 j2)) (* 2304 h1 (* h2 h2) (* h3 h3) (* h4 h4) h5 (* h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 16344 h1 (* h2 h2) (* h3 h3) (* h4 h4) 
h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 41436 h1 (* h2 h2) (* h3 h3) (* h4 
h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 50596 h1 (* h2 h2) (* h3 h3) (* h4
 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 33656 h1 (* h2 h2) (* h3 h3) (* h4 
h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 12388 h1 (* h2 h2) (* h3 h3) (* h4 h4) 
h5 (* h6 h6) (* j2 j2 j2 j2)) (* 2336 h1 (* h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 
h6) (* j2 j2 j2)) (* 174 h1 (* h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2)
) (* 832 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 4760 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 8884 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)
) (* 7560 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
3176 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 632 h1 
(* h2 h2) (* h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2)) (* 48 h1 (* h2 h2) (* 
h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2)) (* 288 h1 (* h2 h2) (* h3 h3) h4 (* h5 
h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1800 h1 (* h2 h2) (* h3 h3) h4 (* 
h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4632 h1 (* h2 h2) (* h3 h3) h4 (* 
h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 6342 h1 (* h2 h2) (* h3 h3) h4 (* h5 
h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 4970 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 
h5) (* j2 j2 j2 j2 j2)) (* 2225 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 
j2 j2 j2)) (* 539 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2)) (* 65 
h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2)) (* 3 h1 (* h2 h2) (* h3 h3)
 h4 (* h5 h5 h5 h5) j2) (* 384 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 5072 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 22804 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 50908 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 64455 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 48746 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* 22108 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)
) (* 5760 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 777 h1 (* 
h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2)) (* 42 h1 (* h2 h2) (* h3 h3) h4 
(* h5 h5 h5) h6 j2) (* 672 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8272 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 37740 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 87484 h1 (* h2 h2) (* h3 h3) h4 (* h5
 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 116341 h1 (* h2 h2) (* h3 h3) h4 (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 93371 h1 (* h2 h2) (* h3 h3) h4 (* h5
 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 45515 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2)) (* 13001 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6
) (* j2 j2 j2)) (* 1980 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2))
 (* 123 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) j2) (* 1696 h1 (* h2 h2) 
(* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 12496 h1 (* h2 
h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 36380 h1 (* h2 
h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 55390 h1 (* h2 h2)
 (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 48898 h1 (* h2 h2) (* h3
 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 25834 h1 (* h2 h2) (* h3 h3) h4 
h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 7954 h1 (* h2 h2) (* h3 h3) h4 h5 (* h6 h6 
h6) (* j2 j2 j2)) (* 1292 h1 (* h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2)) 
(* 84 h1 (* h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) j2) (* 288 h1 (* h2 h2) (* h3 h3
) h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1752 h1 (* h2 h2) (* h3 h3)
 h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4116 h1 (* h2 h2) (* h3 h3) h4 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4876 h1 (* h2 h2) (* h3 h3) h4 (* h6 
h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 3132 h1 (* h2 h2) (* h3 h3) h4 (* h6 h6 h6 h6) 
(* j2 j2 j2 j2)) (* 1080 h1 (* h2 h2) (* h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2))
 (* 184 h1 (* h2 h2) (* h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2)) (* 12 h1 (* h2 h2) 
(* h3 h3) h4 (* h6 h6 h6 h6) j2) (* 320 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2232 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5
) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6552 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5)
 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 10502 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6
 (* j2 j2 j2 j2 j2 j2)) (* 9952 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* 5620 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2))
 (* 1802 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 290 h1 (* h2
 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 18 h1 (* h2 h2) (* h3 h3) (* h5 
h5 h5 h5) h6 j2) (* 288 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 3312 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 15028 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 36520 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 53241 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5
) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 48681 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 27983 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6
 h6) (* j2 j2 j2 j2)) (* 9713 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2)) (* 1824 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 
138 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) j2) (* 288 h1 (* h2 h2) (* h3 
h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3280 h1 (* h2 
h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 14984 h1
 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
36952 h1 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 54968 h1 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 51553 h1 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
30592 h1 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 11065 h1
 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 2198 h1 (* h2 h2) 
(* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 180 h1 (* h2 h2) (* h3 h3) (* h5 
h5) (* h6 h6 h6) j2) (* 312 h1 (* h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 2344 h1 (* h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 7374 h1 (* h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 12656 h1 (* h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 12924 h1 (* h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 
j2)) (* 8016 h1 (* h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 2942 
h1 (* h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 584 h1 (* h2 h2) (* 
h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2)) (* 48 h1 (* h2 h2) (* h3 h3) h5 (* h6 h6 h6
 h6) j2) (* 16 h1 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2
 j2 j2 j2)) (* 124 h1 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 316 h1 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 351 h1 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 
j2 j2)) (* 177 h1 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) 
(* 39 h1 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 3 h1 (* 
h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 56 h1 (* h2 h2) h3 (* h4
 h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 360 h1 (* h2 h2) h3 (* h4 h4
 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 646 h1 (* h2 h2) h3 (* h4 h4 h4 h4
) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 452 h1 (* h2 h2) h3 (* h4 h4 h4 h4) h5 h6 
(* j2 j2 j2 j2 j2 j2)) (* 136 h1 (* h2 h2) h3 (* h4 h4 h4 h4) h5 h6 (* j2 j2 j2 
j2 j2)) (* 15 h1 (* h2 h2) h3 (* h4 h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 16 h1 
(* h2 h2) h3 (* h4 h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 136 h1 
(* h2 h2) h3 (* h4 h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 140 h1 (* h2
 h2) h3 (* h4 h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 50 h1 (* h2 h2) h3 
(* h4 h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 6 h1 (* h2 h2) h3 (* h4 h4 h4 
h4) (* h6 h6) (* j2 j2 j2 j2)) (* 32 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 376 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 
h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1264 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1902 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1432 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 
h5) (* j2 j2 j2 j2 j2 j2)) (* 536 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) (* 
j2 j2 j2 j2 j2)) (* 92 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)
) (* 6 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 112 h1 (* h2 
h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1280 h1 
(* h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4584 
h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 7362 
h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 6030 h1 
(* h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 2613 h1 (* h2 
h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 567 h1 (* h2 h2) h3 (* 
h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 48 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5
 h5) h6 (* j2 j2 j2)) (* 240 h1 (* h2 h2) h3 (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 1948 h1 (* h2 h2) h3 (* h4 h4 h4) h5 (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 4780 h1 (* h2 h2) h3 (* h4 h4 h4) h5 (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 4975 h1 (* h2 h2) h3 (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 2507 h1 (* h2 h2) h3 (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 601 h1 (* h2 h2) h3 (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 54 h1 
(* h2 h2) h3 (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 32 h1 (* h2 h2) h3 (* h4
 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 352 h1 (* h2 h2) h3 (* h4 
h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 716 h1 (* h2 h2) h3 (* h4 h4 h4
) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 482 h1 (* h2 h2) h3 (* h4 h4 h4) (* h6 
h6 h6) (* j2 j2 j2 j2 j2)) (* 128 h1 (* h2 h2) h3 (* h4 h4 h4) (* h6 h6 h6) (* 
j2 j2 j2 j2)) (* 12 h1 (* h2 h2) h3 (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2)) (* 
16 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 216 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (* 892 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 1750 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
1856 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1091 h1
 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 341 h1 (* h2 h2) 
h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 51 h1 (* h2 h2) h3 (* h4 h4) 
(* h5 h5 h5 h5) (* j2 j2 j2)) (* 3 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) (* 
j2 j2)) (* 192 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2
 j2 j2 j2)) (* 2216 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 8448 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 15624 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2)) (* 15931 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2)) (* 9343 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
3122 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 549 h1 (* h2 
h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 39 h1 (* h2 h2) h3 (* h4 h4) 
(* h5 h5 h5) h6 (* j2 j2)) (* 240 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2824 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 11628 h1 (* h2 h2) h3 (* h4 h4) (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 23332 h1 (* h2 h2) h3 (* h4 h4)
 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 25837 h1 (* h2 h2) h3 (* h4 h4
) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 16506 h1 (* h2 h2) h3 (* h4 h4) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 6020 h1 (* h2 h2) h3 (* h4 h4) (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2)) (* 1150 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5) (* h6
 h6) (* j2 j2 j2)) (* 87 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)
) (* 312 h1 (* h2 h2) h3 (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2
)) (* 2616 h1 (* h2 h2) h3 (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 7690 h1 (* h2 h2) h3 (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 10800 h1 (* h2 h2) h3 (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
8047 h1 (* h2 h2) h3 (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 3237 h1 
(* h2 h2) h3 (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 655 h1 (* h2 h2) h3 
(* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 51 h1 (* h2 h2) h3 (* h4 h4) h5 (* h6
 h6 h6) (* j2 j2)) (* 16 h1 (* h2 h2) h3 (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 216 h1 (* h2 h2) h3 (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2
 j2 j2 j2)) (* 608 h1 (* h2 h2) h3 (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 676 h1 (* h2 h2) h3 (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 336
 h1 (* h2 h2) h3 (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 74 h1 (* h2 h2) 
h3 (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 6 h1 (* h2 h2) h3 (* h4 h4) (* h6 
h6 h6 h6) (* j2 j2)) (* 80 h1 (* h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 832 h1 (* h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 3324 h1 (* h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 6976 h1 (* h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2)) (* 8602 h1 (* h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
6481 h1 (* h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 2969 h1 (* h2 
h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 789 h1 (* h2 h2) h3 h4 (* h5 h5
 h5 h5) h6 (* j2 j2 j2)) (* 109 h1 (* h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2))
 (* 6 h1 (* h2 h2) h3 h4 (* h5 h5 h5 h5) h6 j2) (* 288 h1 (* h2 h2) h3 h4 (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3016 h1 (* h2 h2) h3 h4 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 12268 h1 (* h2 h2) h3 
h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 26306 h1 (* h2 h2) h3 
h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 33259 h1 (* h2 h2) h3 h4 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 25901 h1 (* h2 h2) h3 h4 (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 12481 h1 (* h2 h2) h3 h4 (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2)) (* 3601 h1 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2)) (* 564 h1 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 36 h1 
(* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) j2) (* 208 h1 (* h2 h2) h3 h4 (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2256 h1 (* h2 h2) h3 h4 (* h5
 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 9696 h1 (* h2 h2) h3 h4 (* 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 22082 h1 (* h2 h2) h3 h4 (* 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 29708 h1 (* h2 h2) h3 h4 (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 24643 h1 (* h2 h2) h3 h4 (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 12642 h1 (* h2 h2) h3 h4 (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2)) (* 3867 h1 (* h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 
j2)) (* 636 h1 (* h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 42 h1 (* h2 
h2) h3 h4 (* h5 h5) (* h6 h6 h6) j2) (* 128 h1 (* h2 h2) h3 h4 h5 (* h6 h6 h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1028 h1 (* h2 h2) h3 h4 h5 (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3308 h1 (* h2 h2) h3 h4 h5 (* h6 h6 h6 h6) (* j2
 j2 j2 j2 j2 j2 j2)) (* 5609 h1 (* h2 h2) h3 h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 5492 h1 (* h2 h2) h3 h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
3173 h1 (* h2 h2) h3 h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 1050 h1 (* h2 h2)
 h3 h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 180 h1 (* h2 h2) h3 h4 h5 (* h6 h6 h6
 h6) (* j2 j2)) (* 12 h1 (* h2 h2) h3 h4 h5 (* h6 h6 h6 h6) j2) (* 64 h1 (* h2 
h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 600 h1 
(* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2392 
h1 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 5342 
h1 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 7372 h1 
(* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6510 h1 (* h2 
h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 3664 h1 (* h2 h2) h3 (* 
h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 1258 h1 (* h2 h2) h3 (* h5 h5 h5 h5) 
(* h6 h6) (* j2 j2 j2)) (* 236 h1 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 
j2)) (* 18 h1 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) j2) (* 128 h1 (* h2 h2) h3 
(* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1200 h1 (* h2 h2
) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4812 h1 (* h2 
h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 10858 h1 (* h2 
h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 15204 h1 (* h2 h2)
 h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 13690 h1 (* h2 h2) h3 
(* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 7908 h1 (* h2 h2) h3 (* h5 h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 2814 h1 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 
h6) (* j2 j2 j2)) (* 556 h1 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) 
(* 46 h1 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) j2) (* 64 h1 (* h2 h2) h3 (* h5 
h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 588 h1 (* h2 h2) h3 
(* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2336 h1 (* h2 h2) 
h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 5261 h1 (* h2 h2) 
h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 7392 h1 (* h2 h2) h3 
(* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6706 h1 (* h2 h2) h3 (* h5 
h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 3916 h1 (* h2 h2) h3 (* h5 h5) (* h6 
h6 h6 h6) (* j2 j2 j2 j2)) (* 1413 h1 (* h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* 
j2 j2 j2)) (* 284 h1 (* h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 24 h1 
(* h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) j2) (* 28 h1 (* h2 h2) (* h4 h4 h4 h4) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 104 h1 (* h2 h2) (* h4 h4 h4 h4)
 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 143 h1 (* h2 h2) (* h4 h4 h4 h4) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 91 h1 (* h2 h2) (* h4 h4 h4 h4) (* h5 
h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 27 h1 (* h2 h2) (* h4 h4 h4 h4) (* h5 h5) h6 
(* j2 j2 j2 j2 j2)) (* 3 h1 (* h2 h2) (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 
j2)) (* 32 h1 (* h2 h2) (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 80 h1 (* h2 h2) (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
68 h1 (* h2 h2) (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 24 h1 (* 
h2 h2) (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 3 h1 (* h2 h2) (* h4 
h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 8 h1 (* h2 h2) (* h4 h4 h4) (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 120 h1 (* h2 h2) (* h4 h4 h4) (* h5
 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 442 h1 (* h2 h2) (* h4 h4 h4) (* 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 732 h1 (* h2 h2) (* h4 h4 h4) (* h5
 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 634 h1 (* h2 h2) (* h4 h4 h4) (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 294 h1 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2)) (* 68 h1 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 
j2)) (* 6 h1 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 108 h1 (* 
h2 h2) (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 572 
h1 (* h2 h2) (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
1139 h1 (* h2 h2) (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
1104 h1 (* h2 h2) (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 550
 h1 (* h2 h2) (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 133 h1 (* 
h2 h2) (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 12 h1 (* h2 h2) (* 
h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 80 h1 (* h2 h2) (* h4 h4 h4) h5 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 288 h1 (* h2 h2) (* h4 h4 h4) h5 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 380 h1 (* h2 h2) (* h4 h4 h4) h5 (* h6
 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 228 h1 (* h2 h2) (* h4 h4 h4) h5 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2)) (* 62 h1 (* h2 h2) (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 
j2)) (* 6 h1 (* h2 h2) (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 8 h1 (* h2 
h2) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 88 h1 (* 
h2 h2) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 346 h1 
(* h2 h2) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 688 h1 
(* h2 h2) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 778 h1 (* h2
 h2) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 517 h1 (* h2 h2) (* 
h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 197 h1 (* h2 h2) (* h4 h4) (* 
h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 39 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5 h5) h6
 (* j2 j2 j2)) (* 3 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 24 
h1 (* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (* 312 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
 j2)) (* 1302 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 2664 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2)) (* 3060 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2
 j2)) (* 2052 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 786 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 156 h1 
(* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 12 h1 (* h2 h2) (* 
h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 132 h1 (* h2 h2) (* h4 h4) (* h5 h5)
 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 804 h1 (* h2 h2) (* h4 h4) (* 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1977 h1 (* h2 h2) (* h4 h4) 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2544 h1 (* h2 h2) (* h4 h4) 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1842 h1 (* h2 h2) (* h4 h4) (* 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 744 h1 (* h2 h2) (* h4 h4) (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2)) (* 153 h1 (* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2)) (* 12 h1 (* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2))
 (* 48 h1 (* h2 h2) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 216 h1 (* h2 h2) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
384 h1 (* h2 h2) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 342 h1 
(* h2 h2) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 159 h1 (* h2 h2) 
(* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 36 h1 (* h2 h2) (* h4 h4) h5 
(* h6 h6 h6 h6) (* j2 j2 j2)) (* 3 h1 (* h2 h2) (* h4 h4) h5 (* h6 h6 h6 h6) (* 
j2 j2)) (* 16 h1 (* h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 152 h1 (* h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2 j2)) (* 604 h1 (* h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 1326 h1 (* h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 1776 h1 (* h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2))
 (* 1503 h1 (* h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 800 h1
 (* h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 256 h1 (* h2 h2) h4 
(* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 44 h1 (* h2 h2) h4 (* h5 h5 h5 h5) 
(* h6 h6) (* j2 j2)) (* 3 h1 (* h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6) j2) (* 24 h1
 (* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
256 h1 (* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 1086 h1 (* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 2482 h1 (* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
3412 h1 (* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2938 h1
 (* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1582 h1 (* h2 h2)
 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 510 h1 (* h2 h2) h4 (* h5 h5 
h5) (* h6 h6 h6) (* j2 j2 j2)) (* 88 h1 (* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6) 
(* j2 j2)) (* 6 h1 (* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6) j2) (* 52 h1 (* h2 h2)
 h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 340 h1 (* h2 h2
) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 945 h1 (* h2 h2) 
h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1452 h1 (* h2 h2) h4 
(* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1341 h1 (* h2 h2) h4 (* h5 
h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 756 h1 (* h2 h2) h4 (* h5 h5) (* h6 
h6 h6 h6) (* j2 j2 j2 j2)) (* 251 h1 (* h2 h2) h4 (* h5 h5) (* h6 h6 h6 h6) (* 
j2 j2 j2)) (* 44 h1 (* h2 h2) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 3 h1 
(* h2 h2) h4 (* h5 h5) (* h6 h6 h6 h6) j2) (* 8 h1 (* h2 h2) (* h5 h5 h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 64 h1 (* h2 h2) (* h5 h5 h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 226 h1 (* h2 h2) (* h5 h5 h5 h5)
 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 462 h1 (* h2 h2) (* h5 h5 h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 602 h1 (* h2 h2) (* h5 h5 h5 h5) (* h6
 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 518 h1 (* h2 h2) (* h5 h5 h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2)) (* 294 h1 (* h2 h2) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2
 j2)) (* 106 h1 (* h2 h2) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 22 h1 
(* h2 h2) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 2 h1 (* h2 h2) (* h5 h5 h5 
h5) (* h6 h6 h6) j2) (* 8 h1 (* h2 h2) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 64 h1 (* h2 h2) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 226 h1 (* h2 h2) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2
 j2 j2 j2 j2 j2 j2)) (* 462 h1 (* h2 h2) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 602 h1 (* h2 h2) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2
 j2 j2)) (* 518 h1 (* h2 h2) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 294 h1 (* h2 h2) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 106 h1 (* 
h2 h2) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 22 h1 (* h2 h2) (* h5 h5 h5
) (* h6 h6 h6 h6) (* j2 j2)) (* 2 h1 (* h2 h2) (* h5 h5 h5) (* h6 h6 h6 h6) j2) 
(* 272 h1 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
1192 h1 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2048 
h1 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 1768 h1 h2 
(* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 816 h1 h2 (* h3 h3 h3 
h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 192 h1 h2 (* h3 h3 h3 h3) (* h4 h4 h4
) h5 (* j2 j2 j2 j2)) (* 16 h1 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2)) 
(* 320 h1 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
1104 h1 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1472 h1 
h2 (* h3 h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 944 h1 h2 (* h3 h3 
h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 288 h1 h2 (* h3 h3 h3 h3) (* h4 h4
 h4) h6 (* j2 j2 j2 j2)) (* 32 h1 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2
)) (* 832 h1 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 4512 h1 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 9568 h1 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2))
 (* 10144 h1 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 
5744 h1 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 1736 h1 h2
 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 264 h1 h2 (* h3 h3 h3 
h3) (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 16 h1 h2 (* h3 h3 h3 h3) (* h4 h4) (* 
h5 h5) (* j2 j2)) (* 992 h1 h2 (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2
 j2 j2 j2 j2)) (* 6848 h1 h2 (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 17744 h1 h2 (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 
j2)) (* 22288 h1 h2 (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 
14648 h1 h2 (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 5088 h1 h2 
(* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 904 h1 h2 (* h3 h3 h3 h3) 
(* h4 h4) h5 h6 (* j2 j2 j2)) (* 64 h1 h2 (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 
j2)) (* 768 h1 h2 (* h3 h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 3776 h1 h2 (* h3 h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 7168 h1 h2 (* h3 h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6688
 h1 h2 (* h3 h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 3200 h1 h2 (* 
h3 h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 736 h1 h2 (* h3 h3 h3 h3) 
(* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 64 h1 h2 (* h3 h3 h3 h3) (* h4 h4) (* h6 h6
) (* j2 j2)) (* 384 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 2496 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2
 j2)) (* 6496 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 8672 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 6376 h1 
h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 2640 h1 h2 (* h3 h3 h3
 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 628 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5 
h5) (* j2 j2 j2)) (* 80 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2)) (* 4 h1
 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) j2) (* 1808 h1 h2 (* h3 h3 h3 h3) h4 (* h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 12072 h1 h2 (* h3 h3 h3 h3) h4 (* h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 32288 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 44388 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2)) (* 33696 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 
j2 j2)) (* 14428 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 3524 
h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 452 h1 h2 (* h3 h3 h3 h3)
 h4 (* h5 h5) h6 (* j2 j2)) (* 24 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5) h6 j2) (* 
1168 h1 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
8936 h1 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 27408
 h1 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 43456 h1 h2 
(* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 38512 h1 h2 (* h3 h3 
h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 19360 h1 h2 (* h3 h3 h3 h3) h4 h5 
(* h6 h6) (* j2 j2 j2 j2)) (* 5408 h1 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 
j2 j2)) (* 792 h1 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 48 h1 h2 (* 
h3 h3 h3 h3) h4 h5 (* h6 h6) j2) (* 448 h1 h2 (* h3 h3 h3 h3) h4 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2608 h1 h2 (* h3 h3 h3 h3) h4 (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2 j2)) (* 6192 h1 h2 (* h3 h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 7728 h1 h2 (* h3 h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
5424 h1 h2 (* h3 h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 2112 h1 h2 (* h3 
h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2)) (* 416 h1 h2 (* h3 h3 h3 h3) h4 (* h6 h6
 h6) (* j2 j2)) (* 32 h1 h2 (* h3 h3 h3 h3) h4 (* h6 h6 h6) j2) (* 416 h1 h2 (* 
h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3024 h1 h2 (* h3
 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 9008 h1 h2 (* h3 h3 
h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 14120 h1 h2 (* h3 h3 h3 h3) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 12436 h1 h2 (* h3 h3 h3 h3) (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2)) (* 6104 h1 h2 (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 
j2 j2 j2)) (* 1590 h1 h2 (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 216 h1
 h2 (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2)) (* 14 h1 h2 (* h3 h3 h3 h3) (* h5
 h5 h5) h6 j2) (* 976 h1 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 7192 h1 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 21808 h1 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 35152 h1 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 32444 h1 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 17272 h1 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 5156 h1 
h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 824 h1 h2 (* h3 h3 h3 h3
) (* h5 h5) (* h6 h6) (* j2 j2)) (* 56 h1 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6)
 j2) (* 448 h1 h2 (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 3344 h1 h2 (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
10544 h1 h2 (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 18192 
h1 h2 (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 18584 h1 h2 (* 
h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 11344 h1 h2 (* h3 h3 h3 h3) 
h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 3968 h1 h2 (* h3 h3 h3 h3) h5 (* h6 h6 h6) 
(* j2 j2 j2)) (* 720 h1 h2 (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 56 h1 
h2 (* h3 h3 h3 h3) h5 (* h6 h6 h6) j2) (* 136 h1 h2 (* h3 h3 h3) (* h4 h4 h4 h4)
 h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 460 h1 h2 (* h3 h3 h3) (* h4 h4 h4 h4) h5
 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 564 h1 h2 (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2
 j2 j2 j2 j2 j2 j2)) (* 320 h1 h2 (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2
 j2 j2)) (* 88 h1 h2 (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 8 h1
 h2 (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 160 h1 h2 (* h3 h3 h3) 
(* h4 h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 392 h1 h2 (* h3 h3 h3) (* h4 
h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 344 h1 h2 (* h3 h3 h3) (* h4 h4 h4 h4)
 h6 (* j2 j2 j2 j2 j2 j2)) (* 128 h1 h2 (* h3 h3 h3) (* h4 h4 h4 h4) h6 (* j2 j2
 j2 j2 j2)) (* 16 h1 h2 (* h3 h3 h3) (* h4 h4 h4 h4) h6 (* j2 j2 j2 j2)) (* 96 
h1 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
1088 h1 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 3752 h1 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 5848 h1 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
4580 h1 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1824 h1
 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 360 h1 h2 (* h3 
h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 28 h1 h2 (* h3 h3 h3) (* h4 h4
 h4) (* h5 h5) (* j2 j2 j2)) (* 968 h1 h2 (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 5260 h1 h2 (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2
 j2 j2 j2 j2 j2 j2)) (* 10592 h1 h2 (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 
j2 j2 j2 j2)) (* 9920 h1 h2 (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2
)) (* 4600 h1 h2 (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 1084 h1 
h2 (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 104 h1 h2 (* h3 h3 h3) 
(* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 640 h1 h2 (* h3 h3 h3) (* h4 h4 h4) (* h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2504 h1 h2 (* h3 h3 h3) (* h4 h4 h4) (* h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2)) (* 3560 h1 h2 (* h3 h3 h3) (* h4 h4 h4) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 2256 h1 h2 (* h3 h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 
j2 j2 j2)) (* 624 h1 h2 (* h3 h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 
64 h1 h2 (* h3 h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2)) (* 96 h1 h2 (* h3 h3 
h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1256 h1 h2 (* 
h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 5228 h1 h2 
(* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 10256 h1 h2 
(* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 10672 h1 h2 (* 
h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 6022 h1 h2 (* h3 h3 
h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 1785 h1 h2 (* h3 h3 h3) (* h4 
h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 264 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 
h5) (* j2 j2 j2)) (* 16 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 
416 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (* 5040 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2
)) (* 20848 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 41744 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 45276 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
27462 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 9192 h1 
h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 1586 h1 h2 (* h3 h3 
h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 112 h1 h2 (* h3 h3 h3) (* h4 h4) (* 
h5 h5) h6 (* j2 j2)) (* 1944 h1 h2 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 12596 h1 h2 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 31704 h1 h2 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 40316 h1 h2 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 28388 h1 h2 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 11212 h1 h2 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 2304
 h1 h2 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 192 h1 h2 (* h3 h3 
h3) (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 704 h1 h2 (* h3 h3 h3) (* h4 h4) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3512 h1 h2 (* h3 h3 h3) (* h4 h4) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 6760 h1 h2 (* h3 h3 h3) (* h4 h4) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 6416 h1 h2 (* h3 h3 h3) (* h4 h4) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2)) (* 3120 h1 h2 (* h3 h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 
j2)) (* 720 h1 h2 (* h3 h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2)) (* 64 h1 h2 
(* h3 h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2)) (* 192 h1 h2 (* h3 h3 h3) h4 (* 
h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1248 h1 h2 (* h3 h3 h3) h4 (* h5
 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3248 h1 h2 (* h3 h3 h3) h4 (* h5 h5 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 4336 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2)) (* 3188 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2
 j2 j2)) (* 1320 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 314 
h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2)) (* 40 h1 h2 (* h3 h3 h3) h4 
(* h5 h5 h5 h5) (* j2 j2)) (* 2 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) j2) (* 320
 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
3848 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
17012 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
38008 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 47882 
h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 35288 h1 h2 (* 
h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 15206 h1 h2 (* h3 h3 h3) h4 
(* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 3719 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5) h6 
(* j2 j2 j2)) (* 484 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2)) (* 26 h1 
h2 (* h3 h3 h3) h4 (* h5 h5 h5) h6 j2) (* 544 h1 h2 (* h3 h3 h3) h4 (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 6368 h1 h2 (* h3 h3 h3) h4 (* h5
 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 28624 h1 h2 (* h3 h3 h3) h4 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 66856 h1 h2 (* h3 h3 h3) h4 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 90262 h1 h2 (* h3 h3 h3) h4 (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 73004 h1 h2 (* h3 h3 h3) h4 (* h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 35130 h1 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6
) (* j2 j2 j2 j2)) (* 9638 h1 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2
)) (* 1396 h1 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 84 h1 h2 (* 
h3 h3 h3) h4 (* h5 h5) (* h6 h6) j2) (* 1336 h1 h2 (* h3 h3 h3) h4 h5 (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 9484 h1 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 27636 h1 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 43080 h1 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 39396 h1 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 
j2)) (* 21692 h1 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 7024 h1 
h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 1224 h1 h2 (* h3 h3 h3) h4 
h5 (* h6 h6 h6) (* j2 j2)) (* 88 h1 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6) j2) (* 
224 h1 h2 (* h3 h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1304 
h1 h2 (* h3 h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3096 h1 h2 
(* h3 h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3864 h1 h2 (* h3 h3 h3
) h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2712 h1 h2 (* h3 h3 h3) h4 (* h6 h6 
h6 h6) (* j2 j2 j2 j2)) (* 1056 h1 h2 (* h3 h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 
j2)) (* 208 h1 h2 (* h3 h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2)) (* 16 h1 h2 (* h3 
h3 h3) h4 (* h6 h6 h6 h6) j2) (* 208 h1 h2 (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2
 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1512 h1 h2 (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 4504 h1 h2 (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2
 j2 j2 j2 j2)) (* 7060 h1 h2 (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2)) (* 6218 h1 h2 (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 3052 
h1 h2 (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 795 h1 h2 (* h3 h3 h3)
 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 108 h1 h2 (* h3 h3 h3) (* h5 h5 h5 h5) h6 
(* j2 j2)) (* 7 h1 h2 (* h3 h3 h3) (* h5 h5 h5 h5) h6 j2) (* 224 h1 h2 (* h3 h3 
h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2496 h1 h2 (* 
h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 11256 h1 h2 
(* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 27256 h1 h2 
(* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 39178 h1 h2 (* 
h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 34572 h1 h2 (* h3 h3 
h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 18564 h1 h2 (* h3 h3 h3) (* h5
 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 5749 h1 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6
 h6) (* j2 j2 j2)) (* 914 h1 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2)) 
(* 63 h1 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) j2) (* 224 h1 h2 (* h3 h3 h3) 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2480 h1 h2 (* h3 h3
 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 11240 h1 h2 (* h3
 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 27788 h1 h2 (* h3
 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 41600 h1 h2 (* h3 h3
 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 39142 h1 h2 (* h3 h3 h3) 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 22996 h1 h2 (* h3 h3 h3) (* h5 h5)
 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 8010 h1 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6)
 (* j2 j2 j2)) (* 1472 h1 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 
112 h1 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) j2) (* 224 h1 h2 (* h3 h3 h3) h5 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1672 h1 h2 (* h3 h3 h3) h5 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 5272 h1 h2 (* h3 h3 h3) h5 (* h6
 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 9096 h1 h2 (* h3 h3 h3) h5 (* h6 h6 h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 9292 h1 h2 (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 
j2 j2 j2 j2)) (* 5672 h1 h2 (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 
1984 h1 h2 (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 360 h1 h2 (* h3 h3 
h3) h5 (* h6 h6 h6 h6) (* j2 j2)) (* 28 h1 h2 (* h3 h3 h3) h5 (* h6 h6 h6 h6) j2
) (* 32 h1 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 224 h1 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2
 j2)) (* 556 h1 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 640 h1 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 357 h1 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 88 h1
 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 8 h1 h2 (* h3 h3)
 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 112 h1 h2 (* h3 h3) (* h4 h4 h4 
h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 616 h1 h2 (* h3 h3) (* h4 h4 h4 h4)
 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1096 h1 h2 (* h3 h3) (* h4 h4 h4 h4) h5 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 800 h1 h2 (* h3 h3) (* h4 h4 h4 h4) h5 h6 (* j2 
j2 j2 j2 j2 j2)) (* 260 h1 h2 (* h3 h3) (* h4 h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2)
) (* 32 h1 h2 (* h3 h3) (* h4 h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 32 h1 h2 (* h3
 h3) (* h4 h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 208 h1 h2 (* h3 
h3) (* h4 h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 260 h1 h2 (* h3 h3) 
(* h4 h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 112 h1 h2 (* h3 h3) (* h4 h4
 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 16 h1 h2 (* h3 h3) (* h4 h4 h4 h4) (* 
h6 h6) (* j2 j2 j2 j2)) (* 64 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2
 j2 j2 j2 j2 j2 j2 j2 j2)) (* 588 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1910 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2936 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 2308 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* 
j2 j2 j2 j2 j2 j2)) (* 924 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2
 j2 j2)) (* 180 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 14
 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 176 h1 h2 (* h3 h3) 
(* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1848 h1 h2 (* h3
 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 6564 h1 h2 (* 
h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 10910 h1 h2 (* 
h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 9379 h1 h2 (* h3 
h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 4273 h1 h2 (* h3 h3) (* 
h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 967 h1 h2 (* h3 h3) (* h4 h4 h4) 
(* h5 h5) h6 (* j2 j2 j2 j2)) (* 90 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 
(* j2 j2 j2)) (* 408 h1 h2 (* h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2 j2)) (* 2908 h1 h2 (* h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 7092 h1 h2 (* h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 7844 h1 h2 (* h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 4336 h1 h2 (* h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
1150 h1 h2 (* h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 116 h1 h2 (* 
h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 64 h1 h2 (* h3 h3) (* h4 h4 h4
) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 528 h1 h2 (* h3 h3) (* h4 h4 h4) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1140 h1 h2 (* h3 h3) (* h4 h4 h4) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 920 h1 h2 (* h3 h3) (* h4 h4 h4) (* h6 h6 h6
) (* j2 j2 j2 j2 j2)) (* 288 h1 h2 (* h3 h3) (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 
j2 j2)) (* 32 h1 h2 (* h3 h3) (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2)) (* 32 h1 
h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 328
 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
1268 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
2456 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 2590
 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1490 h1 h2 
(* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 446 h1 h2 (* h3 h3) 
(* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 66 h1 h2 (* h3 h3) (* h4 h4) (* h5
 h5 h5 h5) (* j2 j2 j2)) (* 4 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2
)) (* 288 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 3044 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 11638 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 22054 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 23053 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)
) (* 13743 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 4606
 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 793 h1 h2 (* h3 
h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 56 h1 h2 (* h3 h3) (* h4 h4) (* 
h5 h5 h5) h6 (* j2 j2)) (* 336 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3848 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 15976 h1 h2 (* h3 h3) (* h4 h4) (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 33094 h1 h2 (* h3 h3) (* h4 h4) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 38290 h1 h2 (* h3 h3) (* h4 h4)
 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 25714 h1 h2 (* h3 h3) (* h4 h4) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 9836 h1 h2 (* h3 h3) (* h4 h4) (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2)) (* 1983 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5) (* h6
 h6) (* j2 j2 j2)) (* 164 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2
)) (* 480 h1 h2 (* h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 3784 h1 h2 (* h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 11164 h1 h2 (* h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 16308 h1 h2 (* h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
12954 h1 h2 (* h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 5652 h1 
h2 (* h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1264 h1 h2 (* h3 h3) 
(* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 112 h1 h2 (* h3 h3) (* h4 h4) h5 (* 
h6 h6 h6) (* j2 j2)) (* 32 h1 h2 (* h3 h3) (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 320 h1 h2 (* h3 h3) (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 928 h1 h2 (* h3 h3) (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2
 j2)) (* 1148 h1 h2 (* h3 h3) (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
660 h1 h2 (* h3 h3) (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 168 h1 h2 (* 
h3 h3) (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 16 h1 h2 (* h3 h3) (* h4 h4) 
(* h6 h6 h6 h6) (* j2 j2)) (* 112 h1 h2 (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2
 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1128 h1 h2 (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 4528 h1 h2 (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2
 j2 j2 j2 j2 j2 j2)) (* 9572 h1 h2 (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2)) (* 11718 h1 h2 (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2)) (* 8545 h1 h2 (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 3669 
h1 h2 (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 889 h1 h2 (* h3 h3) h4
 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 113 h1 h2 (* h3 h3) h4 (* h5 h5 h5 h5) h6 
(* j2 j2)) (* 6 h1 h2 (* h3 h3) h4 (* h5 h5 h5 h5) h6 j2) (* 384 h1 h2 (* h3 h3)
 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3988 h1 h2 (* 
h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 16554 h1 h2 
(* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 36452 h1 h2 
(* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 47088 h1 h2 (* 
h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 36960 h1 h2 (* h3 h3)
 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 17552 h1 h2 (* h3 h3) h4 (* h5
 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 4834 h1 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6
 h6) (* j2 j2 j2)) (* 698 h1 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) 
(* 42 h1 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) j2) (* 272 h1 h2 (* h3 h3) h4 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3000 h1 h2 (* h3 h3
) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 13204 h1 h2 (* h3
 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 30996 h1 h2 (* h3
 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 43122 h1 h2 (* h3 h3
) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 36966 h1 h2 (* h3 h3) h4 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 19476 h1 h2 (* h3 h3) h4 (* h5 h5)
 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 6063 h1 h2 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6)
 (* j2 j2 j2)) (* 1023 h1 h2 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 
72 h1 h2 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) j2) (* 184 h1 h2 (* h3 h3) h4 h5 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1492 h1 h2 (* h3 h3) h4 h5 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4944 h1 h2 (* h3 h3) h4 h5 (* h6
 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 8696 h1 h2 (* h3 h3) h4 h5 (* h6 h6 h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 8832 h1 h2 (* h3 h3) h4 h5 (* h6 h6 h6 h6) (* j2 
j2 j2 j2 j2)) (* 5274 h1 h2 (* h3 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 
1804 h1 h2 (* h3 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 326 h1 h2 (* h3 h3) 
h4 h5 (* h6 h6 h6 h6) (* j2 j2)) (* 24 h1 h2 (* h3 h3) h4 h5 (* h6 h6 h6 h6) j2)
 (* 80 h1 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 768 h1 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
 j2)) (* 3132 h1 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 7076 h1 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2))
 (* 9692 h1 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
8269 h1 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 4337 h1 h2
 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 1325 h1 h2 (* h3 h3) 
(* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 211 h1 h2 (* h3 h3) (* h5 h5 h5 h5) 
(* h6 h6) (* j2 j2)) (* 14 h1 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) j2) (* 160 
h1 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
1556 h1 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 6490 h1 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 15178 h1 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
21850 h1 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 19985 
h1 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 11537 h1 h2 (* 
h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 4013 h1 h2 (* h3 h3) (* h5 
h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 751 h1 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 
h6) (* j2 j2)) (* 56 h1 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) j2) (* 80 h1 h2 
(* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 776 h1
 h2 (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3236 
h1 h2 (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 7580 
h1 h2 (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 10940 h1 
h2 (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 10034 h1 h2 (* 
h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 5806 h1 h2 (* h3 h3) (* 
h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 2022 h1 h2 (* h3 h3) (* h5 h5) (* h6 
h6 h6 h6) (* j2 j2 j2)) (* 378 h1 h2 (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 
j2)) (* 28 h1 h2 (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) j2) (* 8 h1 h2 h3 (* h4 h4 
h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 48 h1 h2 h3 (* h4 h4 
h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 118 h1 h2 h3 (* h4 h4 h4 
h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 144 h1 h2 h3 (* h4 h4 h4 h4) 
(* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 86 h1 h2 h3 (* h4 h4 h4 h4) (* h5 h5 
h5) (* j2 j2 j2 j2 j2 j2)) (* 22 h1 h2 h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 
j2 j2 j2)) (* 2 h1 h2 h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 84 h1 
h2 h3 (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 360 h1 h2 
h3 (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 565 h1 h2 h3 (* 
h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 399 h1 h2 h3 (* h4 h4 h4 
h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 130 h1 h2 h3 (* h4 h4 h4 h4) (* h5 h5
) h6 (* j2 j2 j2 j2 j2)) (* 16 h1 h2 h3 (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2
 j2)) (* 92 h1 h2 h3 (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 296 h1 h2 h3 (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 301 h1
 h2 h3 (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 124 h1 h2 h3 (* h4
 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 18 h1 h2 h3 (* h4 h4 h4 h4) h5 
(* h6 h6) (* j2 j2 j2 j2)) (* 8 h1 h2 h3 (* h4 h4 h4 h4) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 40 h1 h2 h3 (* h4 h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 24 h1 h2 h3 (* h4 h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 4 h1 h2 
h3 (* h4 h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 8 h1 h2 h3 (* h4 h4 h4) (* 
h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 56 h1 h2 h3 (* h4 h4 h4) (* 
h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 166 h1 h2 h3 (* h4 h4 h4) (* h5 
h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 262 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5 
h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 230 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2
 j2 j2 j2 j2 j2)) (* 108 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2
)) (* 24 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 2 h1 h2 h3 
(* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 48 h1 h2 h3 (* h4 h4 h4) (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 496 h1 h2 h3 (* h4 h4 h4) (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1742 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5
) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2889 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 2503 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2
 j2 j2 j2 j2)) (* 1153 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2))
 (* 271 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 26 h1 h2 h3 
(* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 300 h1 h2 h3 (* h4 h4 h4) (* h5 h5
) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1730 h1 h2 h3 (* h4 h4 h4) (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3784 h1 h2 h3 (* h4 h4 h4) (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3978 h1 h2 h3 (* h4 h4 h4) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2149 h1 h2 h3 (* h4 h4 h4) (* h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2)) (* 575 h1 h2 h3 (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 
j2 j2 j2)) (* 58 h1 h2 h3 (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 216 
h1 h2 h3 (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 936 h1 h2 
h3 (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1432 h1 h2 h3 (* h4
 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 965 h1 h2 h3 (* h4 h4 h4) h5 
(* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 303 h1 h2 h3 (* h4 h4 h4) h5 (* h6 h6 h6) 
(* j2 j2 j2 j2)) (* 34 h1 h2 h3 (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 8 
h1 h2 h3 (* h4 h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 48 h1 h2 h3 
(* h4 h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 64 h1 h2 h3 (* h4 h4 h4) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 28 h1 h2 h3 (* h4 h4 h4) (* h6 h6 h6 h6) 
(* j2 j2 j2 j2)) (* 4 h1 h2 h3 (* h4 h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 40 
h1 h2 h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 380 
h1 h2 h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1420 h1
 h2 h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2740 h1 h2 
h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2979 h1 h2 h3 (* h4
 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 1855 h1 h2 h3 (* h4 h4) (* h5 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 641 h1 h2 h3 (* h4 h4) (* h5 h5 h5 h5) h6 
(* j2 j2 j2 j2)) (* 113 h1 h2 h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 8
 h1 h2 h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 96 h1 h2 h3 (* h4 h4) (* h5
 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1084 h1 h2 h3 (* h4 h4) 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4452 h1 h2 h3 (* h4 h4
) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 9183 h1 h2 h3 (* h4 h4)
 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 10644 h1 h2 h3 (* h4 h4) 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 7183 h1 h2 h3 (* h4 h4) (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2786 h1 h2 h3 (* h4 h4) (* h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2)) (* 576 h1 h2 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 
j2 j2)) (* 48 h1 h2 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 348 h1 h2 
h3 (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2324 h1 
h2 h3 (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6191 h1 
h2 h3 (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 8506 h1 h2 
h3 (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6521 h1 h2 h3 (* 
h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2806 h1 h2 h3 (* h4 h4) (* 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 632 h1 h2 h3 (* h4 h4) (* h5 h5) (* h6 
h6 h6) (* j2 j2 j2)) (* 56 h1 h2 h3 (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2)) 
(* 124 h1 h2 h3 (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 656
 h1 h2 h3 (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1323 h1 h2 
h3 (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1301 h1 h2 h3 (* h4 h4
) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 663 h1 h2 h3 (* h4 h4) h5 (* h6 h6 
h6 h6) (* j2 j2 j2 j2)) (* 169 h1 h2 h3 (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2
)) (* 16 h1 h2 h3 (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2)) (* 56 h1 h2 h3 h4 (* 
h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 544 h1 h2 h3 h4 (* 
h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2194 h1 h2 h3 h4 (* h5
 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4808 h1 h2 h3 h4 (* h5 h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 6278 h1 h2 h3 h4 (* h5 h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 5023 h1 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* 2433 h1 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2
)) (* 679 h1 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 99 h1 h2 h3 h4 
(* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 6 h1 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6) 
j2) (* 80 h1 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2
)) (* 856 h1 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 3704 h1 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
8622 h1 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 11971 h1
 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 10301 h1 h2 h3 h4 
(* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 5495 h1 h2 h3 h4 (* h5 h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2)) (* 1755 h1 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* 
j2 j2 j2)) (* 306 h1 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 22 h1 h2 
h3 h4 (* h5 h5 h5) (* h6 h6 h6) j2) (* 132 h1 h2 h3 h4 (* h5 h5) (* h6 h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 962 h1 h2 h3 h4 (* h5 h5) (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2910 h1 h2 h3 h4 (* h5 h5) (* h6 h6 h6 h6) (* j2
 j2 j2 j2 j2 j2 j2)) (* 4758 h1 h2 h3 h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 4581 h1 h2 h3 h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
2649 h1 h2 h3 h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 897 h1 h2 h3 h4 
(* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 163 h1 h2 h3 h4 (* h5 h5) (* h6 h6 h6
 h6) (* j2 j2)) (* 12 h1 h2 h3 h4 (* h5 h5) (* h6 h6 h6 h6) j2) (* 24 h1 h2 h3 
(* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 220 h1 h2 h3 
(* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 872 h1 h2 h3 (* 
h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1960 h1 h2 h3 (* h5 h5
 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2747 h1 h2 h3 (* h5 h5 h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2479 h1 h2 h3 (* h5 h5 h5 h5) (* h6 h6 h6
) (* j2 j2 j2 j2 j2)) (* 1430 h1 h2 h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2)) (* 502 h1 h2 h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 95 h1 h2 h3 
(* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 7 h1 h2 h3 (* h5 h5 h5 h5) (* h6 h6 
h6) j2) (* 24 h1 h2 h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 220 h1 h2 h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 872 h1 h2 h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 1960 h1 h2 h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2747 
h1 h2 h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2479 h1 h2 h3 
(* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1430 h1 h2 h3 (* h5 h5 h5) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 502 h1 h2 h3 (* h5 h5 h5) (* h6 h6 h6 h6) 
(* j2 j2 j2)) (* 95 h1 h2 h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 7 h1 h2 
h3 (* h5 h5 h5) (* h6 h6 h6 h6) j2) (* 8 h1 h2 (* h4 h4 h4 h4) (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 36 h1 h2 (* h4 h4 h4 h4) (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 60 h1 h2 (* h4 h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2)) (* 46 h1 h2 (* h4 h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2)) (* 16 h1 h2 (* h4 h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 2 h1 h2 
(* h4 h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 20 h1 h2 (* h4 h4 h4 h4) (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 62 h1 h2 (* h4 h4 h4 h4) (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 66 h1 h2 (* h4 h4 h4 h4) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 28 h1 h2 (* h4 h4 h4 h4) (* h5 h5) (* h6 h6)
 (* j2 j2 j2 j2 j2)) (* 4 h1 h2 (* h4 h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2)) (* 10 h1 h2 (* h4 h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 21
 h1 h2 (* h4 h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 12 h1 h2 (* h4 
h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2 h1 h2 (* h4 h4 h4 h4) h5 (* 
h6 h6 h6) (* j2 j2 j2 j2)) (* 8 h1 h2 (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 44 h1 h2 (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 96 h1 h2 (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 106 h1 h2 (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
62 h1 h2 (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 18 h1 h2 (* h4 
h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 2 h1 h2 (* h4 h4 h4) (* h5 h5 h5 
h5) h6 (* j2 j2 j2)) (* 32 h1 h2 (* h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2
 j2 j2 j2 j2 j2 j2)) (* 190 h1 h2 (* h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 431 h1 h2 (* h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2
 j2 j2 j2 j2)) (* 482 h1 h2 (* h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 279 h1 h2 (* h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
78 h1 h2 (* h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 8 h1 h2 (* h4 
h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 50 h1 h2 (* h4 h4 h4) (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 205 h1 h2 (* h4 h4 h4) (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 316 h1 h2 (* h4 h4 h4) (* h5 h5) (* h6
 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 225 h1 h2 (* h4 h4 h4) (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2)) (* 72 h1 h2 (* h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2)) (* 8 h1 h2 (* h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 10 h1 h2 
(* h4 h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 31 h1 h2 (* h4 h4 
h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 33 h1 h2 (* h4 h4 h4) h5 (* h6 
h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 14 h1 h2 (* h4 h4 h4) h5 (* h6 h6 h6 h6) (* j2 
j2 j2 j2)) (* 2 h1 h2 (* h4 h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 24 h1 h2 
(* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 152 h1 h2
 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 398 h1 h2 
(* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 556 h1 h2 (* h4
 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 444 h1 h2 (* h4 h4) (* 
h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 200 h1 h2 (* h4 h4) (* h5 h5 h5 h5
) (* h6 h6) (* j2 j2 j2 j2)) (* 46 h1 h2 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* 
j2 j2 j2)) (* 4 h1 h2 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 40 h1 h2
 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 264 h1 
h2 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 714 h1 h2
 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1024 h1 h2 (* 
h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 836 h1 h2 (* h4 h4) 
(* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 384 h1 h2 (* h4 h4) (* h5 h5 h5
) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 90 h1 h2 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) 
(* j2 j2 j2)) (* 8 h1 h2 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 30 h1
 h2 (* h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 149 h1 
h2 (* h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 297 h1 h2 
(* h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 301 h1 h2 (* h4 h4
) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 161 h1 h2 (* h4 h4) (* h5 h5)
 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 42 h1 h2 (* h4 h4) (* h5 h5) (* h6 h6 h6 h6
) (* j2 j2 j2)) (* 4 h1 h2 (* h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 16 
h1 h2 h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 112 h1 
h2 h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 336 h1 h2 h4 
(* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 562 h1 h2 h4 (* h5 h5 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 570 h1 h2 h4 (* h5 h5 h5 h5) (* h6
 h6 h6) (* j2 j2 j2 j2 j2)) (* 356 h1 h2 h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2)) (* 132 h1 h2 h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 26 h1 
h2 h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 2 h1 h2 h4 (* h5 h5 h5 h5) (* 
h6 h6 h6) j2) (* 16 h1 h2 h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 112 h1 h2 h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 336 h1 h2 h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
562 h1 h2 h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 570 h1 h2 h4
 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 356 h1 h2 h4 (* h5 h5 h5) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 132 h1 h2 h4 (* h5 h5 h5) (* h6 h6 h6 h6) 
(* j2 j2 j2)) (* 26 h1 h2 h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 2 h1 h2 
h4 (* h5 h5 h5) (* h6 h6 h6 h6) j2) (* 32 h1 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 
h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 192 h1 (* h3 h3 h3 h3) (* h4 h4 h4) 
(* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 464 h1 (* h3 h3 h3 h3) (* h4 h4 h4)
 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 584 h1 (* h3 h3 h3 h3) (* h4 h4 h4) 
(* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 416 h1 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5
 h5) (* j2 j2 j2 j2 j2 j2)) (* 172 h1 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* 
j2 j2 j2 j2 j2)) (* 40 h1 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)
) (* 4 h1 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 112 h1 (* h3 
h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 552 h1 (* h3 h3 
h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1080 h1 (* h3 h3 h3 h3
) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1072 h1 (* h3 h3 h3 h3) (* h4 
h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 568 h1 (* h3 h3 h3 h3) (* h4 h4 h4) h5 h6
 (* j2 j2 j2 j2 j2)) (* 152 h1 (* h3 h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2
)) (* 16 h1 (* h3 h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 32 h1 (* h3 h3 
h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 144 h1 (* h3 h3 h3
 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 256 h1 (* h3 h3 h3 h3) 
(* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 224 h1 (* h3 h3 h3 h3) (* h4 h4
 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 96 h1 (* h3 h3 h3 h3) (* h4 h4 h4) (* h6 
h6) (* j2 j2 j2 j2)) (* 16 h1 (* h3 h3 h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2
)) (* 32 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2
 j2)) (* 224 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 640 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2
 j2)) (* 968 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2))
 (* 848 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 448 
h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 144 h1 (* h3 h3
 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 26 h1 (* h3 h3 h3 h3) (* h4 
h4) (* h5 h5 h5) (* j2 j2 j2)) (* 2 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) 
(* j2 j2)) (* 128 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2
 j2 j2 j2 j2)) (* 1088 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 3680 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 6416 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2)) (* 6232 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 
j2 j2)) (* 3416 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) 
(* 1036 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 168 h1 (* 
h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 12 h1 (* h3 h3 h3 h3) (* h4
 h4) (* h5 h5) h6 (* j2 j2)) (* 272 h1 (* h3 h3 h3 h3) (* h4 h4) h5 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1688 h1 (* h3 h3 h3 h3) (* h4 h4) h5 (* h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4232 h1 (* h3 h3 h3 h3) (* h4 h4) h5 (* h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2)) (* 5488 h1 (* h3 h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 3912 h1 (* h3 h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 
j2 j2 j2)) (* 1504 h1 (* h3 h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) 
(* 288 h1 (* h3 h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 24 h1 (* h3 h3
 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 32 h1 (* h3 h3 h3 h3) (* h4 h4) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 176 h1 (* h3 h3 h3 h3) (* h4 h4) (* h6
 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 400 h1 (* h3 h3 h3 h3) (* h4 h4) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 480 h1 (* h3 h3 h3 h3) (* h4 h4) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2)) (* 320 h1 (* h3 h3 h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2
)) (* 112 h1 (* h3 h3 h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2)) (* 16 h1 (* h3
 h3 h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2)) (* 96 h1 (* h3 h3 h3 h3) h4 (* h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 832 h1 (* h3 h3 h3 h3) h4 (* h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2960 h1 (* h3 h3 h3 h3) h4 (* h5 h5
 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 5576 h1 (* h3 h3 h3 h3) h4 (* h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 5984 h1 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2
 j2 j2 j2 j2 j2)) (* 3680 h1 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2)) (* 1260 h1 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 230 h1 
(* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 18 h1 (* h3 h3 h3 h3) h4 (* 
h5 h5 h5) h6 (* j2 j2)) (* 160 h1 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1456 h1 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 5528 h1 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 11328 h1 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6
) (* j2 j2 j2 j2 j2 j2 j2)) (* 13576 h1 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 9652 h1 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2)) (* 3940 h1 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2))
 (* 840 h1 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 72 h1 (* h3 
h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 160 h1 (* h3 h3 h3 h3) h4 h5 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1136 h1 (* h3 h3 h3 h3) h4 h5 (* h6
 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3360 h1 (* h3 h3 h3 h3) h4 h5 (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 5344 h1 (* h3 h3 h3 h3) h4 h5 (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 4904 h1 (* h3 h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2
 j2)) (* 2568 h1 (* h3 h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 696 h1 
(* h3 h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 72 h1 (* h3 h3 h3 h3) h4 h5 
(* h6 h6 h6) (* j2 j2)) (* 64 h1 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2
 j2 j2 j2 j2 j2 j2 j2 j2)) (* 576 h1 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2176 h1 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4464 h1 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 5360 h1 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 3768 h1 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2)) (* 1456 h1 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) 
(* 264 h1 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 16 h1 (* h3 h3
 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 64 h1 (* h3 h3 h3 h3) (* h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 576 h1 (* h3 h3 h3 h3) (* h5 h5)
 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2208 h1 (* h3 h3 h3 h3) (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4688 h1 (* h3 h3 h3 h3) (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 5984 h1 (* h3 h3 h3 h3) (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4640 h1 (* h3 h3 h3 h3) (* h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2)) (* 2080 h1 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2)) (* 464 h1 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 
32 h1 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 16 h1 (* h3 h3 h3) 
(* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 80 h1 (* h3 h3 
h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 152 h1 (* h3 h3
 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 140 h1 (* h3 h3 
h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 68 h1 (* h3 h3 h3) 
(* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 18 h1 (* h3 h3 h3) (* h4 h4 
h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 2 h1 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 
h5) (* j2 j2 j2 j2)) (* 56 h1 (* h3 h3 h3) (* h4 h4 h4 h4) h5 h6 (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 220 h1 (* h3 h3 h3) (* h4 h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 320 h1 (* h3 h3 h3) (* h4 h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)
) (* 216 h1 (* h3 h3 h3) (* h4 h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 68 h1 
(* h3 h3 h3) (* h4 h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 8 h1 (* h3 h3 h3) (* 
h4 h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 16 h1 (* h3 h3 h3) (* h4 h4 h4 h4) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 56 h1 (* h3 h3 h3) (* h4 h4 h4 h4) (* h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2)) (* 72 h1 (* h3 h3 h3) (* h4 h4 h4 h4) (* h6 h6) (* j2
 j2 j2 j2 j2 j2)) (* 40 h1 (* h3 h3 h3) (* h4 h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2
 j2)) (* 8 h1 (* h3 h3 h3) (* h4 h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 32 h1 
(* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 192
 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
464 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
584 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 416 
h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 172 h1 (* h3
 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 40 h1 (* h3 h3 h3) (* 
h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 4 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 
h5 h5) (* j2 j2 j2)) (* 80 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2
 j2 j2 j2 j2 j2 j2 j2)) (* 688 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 2184 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 3380 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2)) (* 2764 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 
j2 j2 j2 j2 j2)) (* 1210 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 
j2 j2)) (* 278 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 28 
h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 192 h1 (* h3 h3 h3) 
(* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1064 h1 (* h3 h3 h3
) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2292 h1 (* h3 h3 h3)
 (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2436 h1 (* h3 h3 h3) (* 
h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1344 h1 (* h3 h3 h3) (* h4 h4 
h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 376 h1 (* h3 h3 h3) (* h4 h4 h4) h5 (* 
h6 h6) (* j2 j2 j2 j2)) (* 48 h1 (* h3 h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2
 j2)) (* 32 h1 (* h3 h3 h3) (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 144 h1 (* h3 h3 h3) (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 256 h1 (* h3 h3 h3) (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 224 
h1 (* h3 h3 h3) (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 96 h1 (* h3 h3 
h3) (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 16 h1 (* h3 h3 h3) (* h4 h4 h4
) (* h6 h6 h6) (* j2 j2 j2)) (* 16 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 112 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5)
 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 320 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5
) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 484 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 424 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2
 j2 j2 j2 j2 j2)) (* 224 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 
j2 j2)) (* 72 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 13 
h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* h1 (* h3 h3 h3) (* h4
 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 128 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6
 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1080 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3692 h1 (* h3 h3 h3) (* h4 h4) (* h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6580 h1 (* h3 h3 h3) (* h4 h4) (* h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 6556 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 3658 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2)) (* 1109 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 
j2 j2)) (* 179 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 13 h1 
(* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 144 h1 (* h3 h3 h3) (* h4 
h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1440 h1 (* h3 h3 
h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 5536 h1 (* 
h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 10964 h1
 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 12346 
h1 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 8072 h1 
(* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2932 h1 (* h3 
h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 526 h1 (* h3 h3 h3) (* 
h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 42 h1 (* h3 h3 h3) (* h4 h4) (* h5 
h5) (* h6 h6) (* j2 j2)) (* 216 h1 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 1412 h1 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 3724 h1 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 5120 h1 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 3948 h1 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 
j2 j2)) (* 1708 h1 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 
396 h1 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 44 h1 (* h3 h3 h3
) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2)) (* 16 h1 (* h3 h3 h3) (* h4 h4) (* h6 h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 88 h1 (* h3 h3 h3) (* h4 h4) (* h6 h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 200 h1 (* h3 h3 h3) (* h4 h4) (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 240 h1 (* h3 h3 h3) (* h4 h4) (* h6 h6 h6 h6) (* j2 j2
 j2 j2 j2)) (* 160 h1 (* h3 h3 h3) (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) 
(* 56 h1 (* h3 h3 h3) (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 8 h1 (* h3 h3 
h3) (* h4 h4) (* h6 h6 h6 h6) (* j2 j2)) (* 48 h1 (* h3 h3 h3) h4 (* h5 h5 h5 h5
) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 416 h1 (* h3 h3 h3) h4 (* h5 h5 h5 h5
) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1480 h1 (* h3 h3 h3) h4 (* h5 h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2788 h1 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 2992 h1 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2
 j2 j2 j2 j2)) (* 1840 h1 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2))
 (* 630 h1 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 115 h1 (* h3 
h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 9 h1 (* h3 h3 h3) h4 (* h5 h5 h5 
h5) h6 (* j2 j2)) (* 160 h1 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 1456 h1 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 5584 h1 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 11672 h1 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 14374 h1 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 10520 h1 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2)) (* 4382 h1 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 
933 h1 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 81 h1 (* h3 h3 h3
) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 112 h1 (* h3 h3 h3) h4 (* h5 h5) (* h6
 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1120 h1 (* h3 h3 h3) h4 (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4608 h1 (* h3 h3 h3) h4 (* h5 h5
) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 10288 h1 (* h3 h3 h3) h4 (* h5 h5
) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 13732 h1 (* h3 h3 h3) h4 (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 11258 h1 (* h3 h3 h3) h4 (* h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2)) (* 5506 h1 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2)) (* 1436 h1 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) 
(* 144 h1 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 80 h1 (* h3 h3 h3
) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 568 h1 (* h3 h3 h3) 
h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1680 h1 (* h3 h3 h3) h4 h5
 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2672 h1 (* h3 h3 h3) h4 h5 (* h6 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2452 h1 (* h3 h3 h3) h4 h5 (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2)) (* 1284 h1 (* h3 h3 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2
)) (* 348 h1 (* h3 h3 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 36 h1 (* h3 h3 
h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2)) (* 32 h1 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 288 h1 (* h3 h3 h3) (* h5 h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1088 h1 (* h3 h3 h3) (* h5 h5 h5 h5
) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2232 h1 (* h3 h3 h3) (* h5 h5 h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2680 h1 (* h3 h3 h3) (* h5 h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1884 h1 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* 728 h1 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2
 j2)) (* 132 h1 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 8 h1 (* 
h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 64 h1 (* h3 h3 h3) (* h5 h5 h5
) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 576 h1 (* h3 h3 h3) (* h5 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2224 h1 (* h3 h3 h3) (* 
h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4800 h1 (* h3 h3 h3) (* 
h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 6296 h1 (* h3 h3 h3) (* h5 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 5076 h1 (* h3 h3 h3) (* h5 h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2392 h1 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2)) (* 564 h1 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 
j2)) (* 40 h1 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 32 h1 (* h3 
h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 288 h1 
(* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1104 
h1 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2344 
h1 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2992 h1 
(* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2320 h1 (* h3 
h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1040 h1 (* h3 h3 h3) (* 
h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 232 h1 (* h3 h3 h3) (* h5 h5) (* h6 
h6 h6 h6) (* j2 j2 j2)) (* 16 h1 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2
)) (* 8 h1 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 40 h1 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 76 h1 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 70 h1 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
34 h1 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 9 h1 (* 
h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* h1 (* h3 h3) (* h4 h4
 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 56 h1 (* h3 h3) (* h4 h4 h4 h4) (* h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 240 h1 (* h3 h3) (* h4 h4 h4 h4) (* h5
 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 372 h1 (* h3 h3) (* h4 h4 h4 h4) (* h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 253 h1 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2)) (* 75 h1 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* 9 h1 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) 
(* 60 h1 (* h3 h3) (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
190 h1 (* h3 h3) (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 206 
h1 (* h3 h3) (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 94 h1 (* h3 
h3) (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 16 h1 (* h3 h3) (* h4 h4
 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 8 h1 (* h3 h3) (* h4 h4 h4 h4) (* h6 h6
 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 20 h1 (* h3 h3) (* h4 h4 h4 h4) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 16 h1 (* h3 h3) (* h4 h4 h4 h4) (* h6 h6 h6) (* j2 j2 
j2 j2 j2)) (* 4 h1 (* h3 h3) (* h4 h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 8 
h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
48 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
116 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
146 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 104 
h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 43 h1 (* h3 
h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 10 h1 (* h3 h3) (* h4 h4
 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 
h5) (* j2 j2 j2)) (* 40 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2
 j2 j2 j2 j2 j2 j2)) (* 340 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 1086 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 1704 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2)) (* 1414 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2)) (* 623 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2
)) (* 141 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 14 h1 
(* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 192 h1 (* h3 h3) (* h4 
h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1092 h1 (* h3 h3) 
(* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2382 h1 (* h3 
h3) (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2523 h1 (* h3 
h3) (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1352 h1 (* h3 h3)
 (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 348 h1 (* h3 h3) (* h4 
h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 41 h1 (* h3 h3) (* h4 h4 h4) (* 
h5 h5) (* h6 h6) (* j2 j2 j2)) (* 136 h1 (* h3 h3) (* h4 h4 h4) h5 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 580 h1 (* h3 h3) (* h4 h4 h4) h5 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 906 h1 (* h3 h3) (* h4 h4 h4) h5 (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2)) (* 636 h1 (* h3 h3) (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 
j2 j2)) (* 204 h1 (* h3 h3) (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 28 
h1 (* h3 h3) (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 8 h1 (* h3 h3) (* h4 
h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 28 h1 (* h3 h3) (* h4 h4 h4)
 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 36 h1 (* h3 h3) (* h4 h4 h4) (* h6 h6
 h6 h6) (* j2 j2 j2 j2 j2)) (* 20 h1 (* h3 h3) (* h4 h4 h4) (* h6 h6 h6 h6) (* 
j2 j2 j2 j2)) (* 4 h1 (* h3 h3) (* h4 h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 32
 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 264 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (* 896 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 1604 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
1616 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 910 h1 
(* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 274 h1 (* h3 h3) 
(* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 43 h1 (* h3 h3) (* h4 h4) (* h5
 h5 h5 h5) h6 (* j2 j2 j2)) (* 3 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2
 j2)) (* 72 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 712 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 2744 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 5484 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 6251 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 4138 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2)) (* 1514 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2)) (* 268 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 21 h1
 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 216 h1 (* h3 h3) (* h4
 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1436 h1 (* h3 h3)
 (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3828 h1 (* h3 
h3) (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 5272 h1 (* h3 
h3) (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4013 h1 (* h3 h3)
 (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1670 h1 (* h3 h3) (* h4
 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 357 h1 (* h3 h3) (* h4 h4) (* h5
 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 36 h1 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6 
h6) (* j2 j2)) (* 76 h1 (* h3 h3) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 398 h1 (* h3 h3) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 812 h1 (* h3 h3) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 814 h1 (* h3 h3) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 418 h1 
(* h3 h3) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 106 h1 (* h3 h3) (* 
h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 12 h1 (* h3 h3) (* h4 h4) h5 (* h6 h6
 h6 h6) (* j2 j2)) (* 40 h1 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 360 h1 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2
 j2 j2 j2 j2 j2 j2 j2)) (* 1368 h1 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 2838 h1 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 3472 h1 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 2523 h1 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 1040 h1 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 217 
h1 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 18 h1 (* h3 h3) h4 
(* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 56 h1 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 556 h1 (* h3 h3) h4 (* h5 h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2290 h1 (* h3 h3) h4 (* h5 h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 5146 h1 (* h3 h3) h4 (* h5 h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 6930 h1 (* h3 h3) h4 (* h5 h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 5733 h1 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2)) (* 2826 h1 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2)) (* 739 h1 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 72 
h1 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 80 h1 (* h3 h3) h4 (* h5
 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 588 h1 (* h3 h3) h4 (* 
h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1788 h1 (* h3 h3) h4 (* 
h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2900 h1 (* h3 h3) h4 (* h5 
h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2686 h1 (* h3 h3) h4 (* h5 h5) (* 
h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1400 h1 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6 
h6) (* j2 j2 j2 j2)) (* 370 h1 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 
j2)) (* 36 h1 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 16 h1 (* h3 
h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 144 h1 
(* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 552 h1
 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1172 h1 
(* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1496 h1 (* 
h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1160 h1 (* h3 h3) 
(* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 520 h1 (* h3 h3) (* h5 h5 h5
 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 116 h1 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 
h6) (* j2 j2 j2)) (* 8 h1 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 
16 h1 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 144 h1 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (* 552 h1 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 1172 h1 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
1496 h1 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1160 h1
 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 520 h1 (* h3 h3) 
(* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 116 h1 (* h3 h3) (* h5 h5 h5) 
(* h6 h6 h6 h6) (* j2 j2 j2)) (* 8 h1 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* 
j2 j2)) (* 12 h1 h3 (* h4 h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 54 h1 h3 (* h4 h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 88 h1 h3 (* h4 h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 62 h1 
h3 (* h4 h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 18 h1 h3 (* h4 h4 
h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 2 h1 h3 (* h4 h4 h4 h4) (* h5 h5 
h5) h6 (* j2 j2 j2 j2)) (* 28 h1 h3 (* h4 h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2
 j2 j2 j2 j2 j2 j2)) (* 94 h1 h3 (* h4 h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2
 j2 j2 j2 j2)) (* 108 h1 h3 (* h4 h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 50 h1 h3 (* h4 h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 8
 h1 h3 (* h4 h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 14 h1 h3 (* h4 h4
 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 33 h1 h3 (* h4 h4 h4 h4) h5
 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 21 h1 h3 (* h4 h4 h4 h4) h5 (* h6 h6 h6)
 (* j2 j2 j2 j2 j2)) (* 4 h1 h3 (* h4 h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2))
 (* 12 h1 h3 (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
66 h1 h3 (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 142 h1 
h3 (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 150 h1 h3 (* h4 
h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 80 h1 h3 (* h4 h4 h4) (* h5 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 20 h1 h3 (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* 
j2 j2 j2 j2)) (* 2 h1 h3 (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 44 h1 
h3 (* h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 262 h1
 h3 (* h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 593 h1 
h3 (* h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 648 h1 h3 
(* h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 361 h1 h3 (* h4 h4
 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 100 h1 h3 (* h4 h4 h4) (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 12 h1 h3 (* h4 h4 h4) (* h5 h5 h5) (* h6 h6
) (* j2 j2 j2)) (* 66 h1 h3 (* h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 287 h1 h3 (* h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2
 j2 j2)) (* 461 h1 h3 (* h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2))
 (* 333 h1 h3 (* h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 107 h1 
h3 (* h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 14 h1 h3 (* h4 h4 h4)
 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 14 h1 h3 (* h4 h4 h4) h5 (* h6 h6 h6 h6
) (* j2 j2 j2 j2 j2 j2 j2)) (* 47 h1 h3 (* h4 h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2
 j2 j2 j2 j2)) (* 54 h1 h3 (* h4 h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 25 h1 h3 (* h4 h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 4 h1 h3 (* h4 h4
 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 32 h1 h3 (* h4 h4) (* h5 h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 206 h1 h3 (* h4 h4) (* h5 h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 538 h1 h3 (* h4 h4) (* h5 h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 727 h1 h3 (* h4 h4) (* h5 h5 h5 h5) (* h6
 h6) (* j2 j2 j2 j2 j2 j2)) (* 536 h1 h3 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2)) (* 208 h1 h3 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2
)) (* 38 h1 h3 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 3 h1 h3 (* 
h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 52 h1 h3 (* h4 h4) (* h5 h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 350 h1 h3 (* h4 h4) (* h5 h5 h5)
 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 950 h1 h3 (* h4 h4) (* h5 h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1338 h1 h3 (* h4 h4) (* h5 h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1049 h1 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2)) (* 457 h1 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2)) (* 105 h1 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 11 
h1 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 38 h1 h3 (* h4 h4) (* h5
 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 199 h1 h3 (* h4 h4) (* h5 
h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 410 h1 h3 (* h4 h4) (* h5 h5) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 418 h1 h3 (* h4 h4) (* h5 h5) (* h6 h6
 h6 h6) (* j2 j2 j2 j2 j2)) (* 218 h1 h3 (* h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* 
j2 j2 j2 j2)) (* 55 h1 h3 (* h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 6
 h1 h3 (* h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 20 h1 h3 h4 (* h5 h5 h5
 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 144 h1 h3 h4 (* h5 h5 h5 h5
) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 434 h1 h3 h4 (* h5 h5 h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 705 h1 h3 h4 (* h5 h5 h5 h5) (* h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2)) (* 660 h1 h3 h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2
 j2 j2)) (* 350 h1 h3 h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 94 h1 
h3 h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 9 h1 h3 h4 (* h5 h5 h5 h5) 
(* h6 h6 h6) (* j2 j2)) (* 20 h1 h3 h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 144 h1 h3 h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 434 h1 h3 h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 705 h1 h3 h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 660 
h1 h3 h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 350 h1 h3 h4 (* h5 
h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 94 h1 h3 h4 (* h5 h5 h5) (* h6 h6 h6 
h6) (* j2 j2 j2)) (* 9 h1 h3 h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 2 h1 
(* h4 h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 8 h1 (* 
h4 h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 11 h1 (* h4 h4 
h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6 h1 (* h4 h4 h4 h4) (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* h1 (* h4 h4 h4 h4) (* h5 h5 h5) (* h6
 h6) (* j2 j2 j2 j2)) (* 2 h1 (* h4 h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2
 j2 j2 j2 j2)) (* 6 h1 (* h4 h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 5 h1 (* h4 h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* h1 
(* h4 h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 2 h1 (* h4 h4 h4) (* 
h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 10 h1 (* h4 h4 h4) (* h5 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 19 h1 (* h4 h4 h4) (* h5 h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 17 h1 (* h4 h4 h4) (* h5 h5 h5 h5) (* h6
 h6) (* j2 j2 j2 j2 j2)) (* 7 h1 (* h4 h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2
 j2 j2)) (* h1 (* h4 h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 4 h1 (* 
h4 h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 20 h1 (* h4 
h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 38 h1 (* h4 h4 h4)
 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 34 h1 (* h4 h4 h4) (* h5 h5
 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 14 h1 (* h4 h4 h4) (* h5 h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2)) (* 2 h1 (* h4 h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 
j2)) (* 2 h1 (* h4 h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 8 h1 (* h4 h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 11 h1 
(* h4 h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 6 h1 (* h4 h4 h4) 
(* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* h1 (* h4 h4 h4) (* h5 h5) (* h6 h6
 h6 h6) (* j2 j2 j2)) (* 2 h1 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 12 h1 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2
 j2 j2 j2)) (* 29 h1 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2
)) (* 36 h1 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 24 h1 
(* h4 h4) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 8 h1 (* h4 h4) (* h5 
h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* h1 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6 h6
) (* j2 j2)) (* 2 h1 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 12 h1 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2
)) (* 29 h1 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 36 
h1 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 24 h1 (* h4 h4)
 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 8 h1 (* h4 h4) (* h5 h5 h5) 
(* h6 h6 h6 h6) (* j2 j2 j2)) (* h1 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2
 j2)) (* 768 (* h2 h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2))
 (* 1920 (* h2 h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 
1520 (* h2 h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 512 (* h2 
h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 76 (* h2 h2 h2 h2) (* h3
 h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 4 (* h2 h2 h2 h2) (* h3 h3 h3) (* h4 h4) 
h5 (* j2 j2)) (* 1024 (* h2 h2 h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 
j2 j2)) (* 1280 (* h2 h2 h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2)) 
(* 576 (* h2 h2 h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2)) (* 112 (* h2 
h2 h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2)) (* 8 (* h2 h2 h2 h2) (* h3 h3 
h3) (* h4 h4) h6 (* j2 j2)) (* 576 (* h2 h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 2160 (* h2 h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 
j2 j2 j2 j2 j2)) (* 2856 (* h2 h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 
j2 j2)) (* 1620 (* h2 h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 
418 (* h2 h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 48 (* h2 h2 h2 h2
) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2)) (* 2 (* h2 h2 h2 h2) (* h3 h3 h3) h4 (* 
h5 h5) j2) (* 1536 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2
)) (* 5376 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 6880 
(* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 4064 (* h2 h2 h2 h2
) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 1176 (* h2 h2 h2 h2) (* h3 h3 h3) h4
 h5 h6 (* j2 j2 j2)) (* 160 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2)) (* 
8 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 h6 j2) (* 1024 (* h2 h2 h2 h2) (* h3 h3 h3)
 h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2304 (* h2 h2 h2 h2) (* h3 h3 h3) h4 (* 
h6 h6) (* j2 j2 j2 j2 j2)) (* 1856 (* h2 h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* 
j2 j2 j2 j2)) (* 688 (* h2 h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2)) (* 
120 (* h2 h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2)) (* 8 (* h2 h2 h2 h2) 
(* h3 h3 h3) h4 (* h6 h6) j2) (* 576 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 2544 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2)) (* 4296 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 
j2 j2 j2)) (* 3460 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) 
(* 1354 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 236 (* h2 h2 
h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2)) (* 14 (* h2 h2 h2 h2) (* h3 h3 h3) 
(* h5 h5) h6 j2) (* 768 (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2
 j2 j2 j2)) (* 3200 (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 5232 (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
4240 (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 1772 (* h2 h2
 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 360 (* h2 h2 h2 h2) (* h3 h3 
h3) h5 (* h6 h6) (* j2 j2)) (* 28 (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) j2) 
(* 192 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 528 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 
488 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 196 (* 
h2 h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 34 (* h2 h2 h2 h2)
 (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 2 (* h2 h2 h2 h2) (* h3 h3) (* h4
 h4 h4) h5 (* j2 j2 j2)) (* 256 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4 h4) h6 (* j2 
j2 j2 j2 j2 j2 j2)) (* 384 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2
 j2 j2 j2)) (* 208 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2))
 (* 48 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2)) (* 4 (* h2 h2 
h2 h2) (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2)) (* 384 (* h2 h2 h2 h2) (* h3 h3) 
(* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1440 (* h2 h2 h2 h2) (* h3 
h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 2032 (* h2 h2 h2 h2) (* h3 
h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1368 (* h2 h2 h2 h2) (* h3 h3)
 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 460 (* h2 h2 h2 h2) (* h3 h3) (* h4 
h4) (* h5 h5) (* j2 j2 j2 j2)) (* 72 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 
h5) (* j2 j2 j2)) (* 4 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) 
(* 576 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 2608 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
4088 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 3036 
(* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 1158 (* h2 h2 
h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 218 (* h2 h2 h2 h2) (* h3 
h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 16 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 
h6 (* j2 j2)) (* 512 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 1280 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 1184 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 512 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 
104 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 8 (* h2 h2 h2
 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2)) (* 144 (* h2 h2 h2 h2) (* h3 h3) 
h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 720 (* h2 h2 h2 h2) (* h3 h3) h4
 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1416 (* h2 h2 h2 h2) (* h3 h3) h4 (* 
h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1392 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5 
h5) (* j2 j2 j2 j2 j2)) (* 721 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 
j2 j2 j2)) (* 191 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2)) (* 23 
(* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2)) (* (* h2 h2 h2 h2) (* h3 h3
) h4 (* h5 h5 h5) j2) (* 768 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 3696 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2)) (* 7136 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 
j2 j2 j2)) (* 7096 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2))
 (* 3880 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 1151 (* 
h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 168 (* h2 h2 h2 h2) (* 
h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 9 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6
 j2) (* 576 (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 3120 (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 6520 (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6940
 (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 4102 (* h2 h2 
h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 1354 (* h2 h2 h2 h2) (* h3 
h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 232 (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* h6 
h6) (* j2 j2)) (* 16 (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) j2) (* 256 (* h2 
h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 896 (* h2 h2 h2
 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1232 (* h2 h2 h2 h2) 
(* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 848 (* h2 h2 h2 h2) (* h3 h3) 
h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 308 (* h2 h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6
) (* j2 j2 j2)) (* 56 (* h2 h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2)) (* 4 
(* h2 h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6) j2) (* 144 (* h2 h2 h2 h2) (* h3 h3) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 816 (* h2 h2 h2 h2) (* h3 h3) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1896 (* h2 h2 h2 h2) (* h3 h3) (* 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 2320 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2)) (* 1593 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* 
j2 j2 j2 j2)) (* 601 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 
111 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2)) (* 7 (* h2 h2 h2 h2) 
(* h3 h3) (* h5 h5 h5) h6 j2) (* 384 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2128 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4912 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6096 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2)) (* 4372 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2)) (* 1803 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 
j2)) (* 394 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 35 (* h2
 h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) j2) (* 192 (* h2 h2 h2 h2) (* h3 h3) h5
 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1040 (* h2 h2 h2 h2) (* h3 h3) h5 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2344 (* h2 h2 h2 h2) (* h3 h3) h5 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2836 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6 
h6) (* j2 j2 j2 j2 j2)) (* 1978 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 
j2 j2 j2)) (* 790 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 166
 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 14 (* h2 h2 h2 h2) (* 
h3 h3) h5 (* h6 h6 h6) j2) (* 48 (* h2 h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2
 j2 j2 j2 j2 j2 j2 j2 j2)) (* 192 (* h2 h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 296 (* h2 h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2
 j2 j2 j2 j2 j2 j2)) (* 224 (* h2 h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 
j2 j2 j2 j2)) (* 87 (* h2 h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)
) (* 16 (* h2 h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* (* h2 h2 
h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 144 (* h2 h2 h2 h2) h3 (* h4 
h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 400 (* h2 h2 h2 h2) h3 (* h4 h4 h4)
 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 424 (* h2 h2 h2 h2) h3 (* h4 h4 h4) h5 h6 
(* j2 j2 j2 j2 j2 j2)) (* 216 (* h2 h2 h2 h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 
j2 j2)) (* 53 (* h2 h2 h2 h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 5 (* h2 
h2 h2 h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 64 (* h2 h2 h2 h2) h3 (* h4 h4 
h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 112 (* h2 h2 h2 h2) h3 (* h4 h4 h4) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 72 (* h2 h2 h2 h2) h3 (* h4 h4 h4) (* h6 h6)
 (* j2 j2 j2 j2 j2)) (* 20 (* h2 h2 h2 h2) h3 (* h4 h4 h4) (* h6 h6) (* j2 j2 j2
 j2)) (* 2 (* h2 h2 h2 h2) h3 (* h4 h4 h4) (* h6 h6) (* j2 j2 j2)) (* 48 (* h2 
h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 240 (* h2
 h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 488 (* h2 
h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 520 (* h2 h2 h2
 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 311 (* h2 h2 h2 h2) h3 
(* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 103 (* h2 h2 h2 h2) h3 (* h4 h4) 
(* h5 h5 h5) (* j2 j2 j2 j2)) (* 17 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) 
(* j2 j2 j2)) (* (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 144 (* 
h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 832 
(* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1864 
(* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2152 (* 
h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 1401 (* h2 h2 
h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 518 (* h2 h2 h2 h2) h3 
(* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 101 (* h2 h2 h2 h2) h3 (* h4 h4) (* 
h5 h5) h6 (* j2 j2 j2)) (* 8 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2)
) (* 288 (* h2 h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 1072 (* h2 h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
1600 (* h2 h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1224 
(* h2 h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 506 (* h2 h2 h2
 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 107 (* h2 h2 h2 h2) h3 (* h4 
h4) h5 (* h6 h6) (* j2 j2 j2)) (* 9 (* h2 h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6) 
(* j2 j2)) (* 64 (* h2 h2 h2 h2) h3 (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 176 (* h2 h2 h2 h2) h3 (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
184 (* h2 h2 h2 h2) h3 (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 92 (* h2 h2
 h2 h2) h3 (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 22 (* h2 h2 h2 h2) h3 (* 
h4 h4) (* h6 h6 h6) (* j2 j2 j2)) (* 2 (* h2 h2 h2 h2) h3 (* h4 h4) (* h6 h6 h6)
 (* j2 j2)) (* 96 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 576 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 1456 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
2016 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 1662 (* h2 
h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 828 (* h2 h2 h2 h2) h3 h4
 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 240 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) h6 
(* j2 j2 j2)) (* 36 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2)) (* 2 (* h2 
h2 h2 h2) h3 h4 (* h5 h5 h5) h6 j2) (* 144 (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 960 (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2632 (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3912 (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 3465 (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2)) (* 1878 (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2)) (* 609 (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 108 (* h2
 h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 8 (* h2 h2 h2 h2) h3 h4 (* h5
 h5) (* h6 h6) j2) (* 144 (* h2 h2 h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 672 (* h2 h2 h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 1304 (* h2 h2 h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
1360 (* h2 h2 h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 821 (* h2 h2 
h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 286 (* h2 h2 h2 h2) h3 h4 h5 
(* h6 h6 h6) (* j2 j2 j2)) (* 53 (* h2 h2 h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2)
) (* 4 (* h2 h2 h2 h2) h3 h4 h5 (* h6 h6 h6) j2) (* 48 (* h2 h2 h2 h2) h3 (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 320 (* h2 h2 h2 h2) h3 (* h5
 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 920 (* h2 h2 h2 h2) h3 (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1488 (* h2 h2 h2 h2) h3 (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1479 (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2)) (* 924 (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2)) (* 354 (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 
76 (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 7 (* h2 h2 h2 h2) h3 
(* h5 h5 h5) (* h6 h6) j2) (* 48 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2 j2)) (* 320 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 920 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2 j2)) (* 1488 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 1479 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2)) (* 924 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 354 
(* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 76 (* h2 h2 h2 h2) h3
 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 7 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6
) j2) (* 16 (* h2 h2 h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2
 j2)) (* 64 (* h2 h2 h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 104 (* h2 h2 h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 88 (* h2 h2 h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 41 (* 
h2 h2 h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 10 (* h2 h2 h2 h2)
 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* (* h2 h2 h2 h2) (* h4 h4 h4) (* 
h5 h5) h6 (* j2 j2 j2)) (* 16 (* h2 h2 h2 h2) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2
 j2 j2 j2 j2 j2 j2)) (* 48 (* h2 h2 h2 h2) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2
 j2 j2 j2 j2)) (* 56 (* h2 h2 h2 h2) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2
 j2)) (* 32 (* h2 h2 h2 h2) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 9 
(* h2 h2 h2 h2) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* (* h2 h2 h2 h2) 
(* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 16 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5
 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 80 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5
 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 168 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 192 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2)) (* 129 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2
 j2 j2 j2 j2)) (* 51 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) 
(* 11 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* (* h2 h2 h2 h2)
 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 32 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 160 (* h2 h2 h2 h2) (* h4 h4) (* h5
 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 336 (* h2 h2 h2 h2) (* h4 h4) (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 384 (* h2 h2 h2 h2) (* h4 h4) (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 258 (* h2 h2 h2 h2) (* h4 h4) (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 102 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2)) (* 22 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* 
j2 j2 j2)) (* 2 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 16 
(* h2 h2 h2 h2) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 64 (* 
h2 h2 h2 h2) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 104 (* h2 h2
 h2 h2) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 88 (* h2 h2 h2 h2) 
(* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 41 (* h2 h2 h2 h2) (* h4 h4) h5
 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 10 (* h2 h2 h2 h2) (* h4 h4) h5 (* h6 h6 h6) 
(* j2 j2 j2)) (* (* h2 h2 h2 h2) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2)) (* 16 (* 
h2 h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 96 (* 
h2 h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 248 (* h2
 h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 360 (* h2 h2 
h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 321 (* h2 h2 h2 h2) 
h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 180 (* h2 h2 h2 h2) h4 (* h5 h5
 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 62 (* h2 h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2)) (* 12 (* h2 h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* (* 
h2 h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6) j2) (* 16 (* h2 h2 h2 h2) h4 (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 96 (* h2 h2 h2 h2) h4 (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 248 (* h2 h2 h2 h2) h4 (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 360 (* h2 h2 h2 h2) h4 (* h5 h5) (* h6
 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 321 (* h2 h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2)) (* 180 (* h2 h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2
 j2)) (* 62 (* h2 h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 12 (* h2 
h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* (* h2 h2 h2 h2) h4 (* h5 h5) 
(* h6 h6 h6) j2) (* 768 (* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2
 j2 j2 j2)) (* 2304 (* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 
j2)) (* 2288 (* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 
888 (* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 144 (* h2 h2 
h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 8 (* h2 h2 h2) (* h3 h3 h3 h3)
 (* h4 h4) h5 (* j2 j2)) (* 1024 (* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4) h6 (* j2
 j2 j2 j2 j2 j2)) (* 1792 (* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 
j2 j2)) (* 960 (* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2)) (* 208
 (* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2)) (* 16 (* h2 h2 h2) (* 
h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2)) (* 576 (* h2 h2 h2) (* h3 h3 h3 h3) h4 (* 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 2448 (* h2 h2 h2) (* h3 h3 h3 h3) h4 (* h5 
h5) (* j2 j2 j2 j2 j2 j2)) (* 3792 (* h2 h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* 
j2 j2 j2 j2 j2)) (* 2580 (* h2 h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 
j2)) (* 748 (* h2 h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 92 (* h2 
h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2)) (* 4 (* h2 h2 h2) (* h3 h3 h3 h3)
 h4 (* h5 h5) j2) (* 1536 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 
j2 j2 j2)) (* 6144 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) 
(* 9184 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 6352 (* h2 
h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 2064 (* h2 h2 h2) (* h3 h3 
h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 304 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2
 j2)) (* 16 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 h6 j2) (* 1024 (* h2 h2 h2) (* h3
 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2816 (* h2 h2 h2) (* h3 h3 h3 
h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2752 (* h2 h2 h2) (* h3 h3 h3 h3) h4 (* 
h6 h6) (* j2 j2 j2 j2)) (* 1168 (* h2 h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 
j2 j2)) (* 224 (* h2 h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2)) (* 16 (* h2 
h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6) j2) (* 576 (* h2 h2 h2) (* h3 h3 h3 h3) (* 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2832 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 
h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 5424 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 
(* j2 j2 j2 j2 j2)) (* 5044 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 
j2 j2)) (* 2292 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 444 
(* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2)) (* 28 (* h2 h2 h2) (* h3 h3
 h3 h3) (* h5 h5) h6 j2) (* 768 (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 3584 (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 6640 (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 6152 (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 2936 
(* h2 h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 664 (* h2 h2 h2) (* 
h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2)) (* 56 (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* h6
 h6) j2) (* 384 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 1248 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 
j2)) (* 1408 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) 
(* 664 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 128 (* 
h2 h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 8 (* h2 h2 h2) (* h3 
h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 512 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4 
h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1024 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4 h4) 
h6 (* j2 j2 j2 j2 j2 j2)) (* 672 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4 h4) h6 (* j2
 j2 j2 j2 j2)) (* 176 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2))
 (* 16 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2)) (* 768 (* h2 h2 
h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3360 (* h2 
h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 5336 (* h2 
h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 3896 (* h2 h2 
h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 1426 (* h2 h2 h2) 
(* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 240 (* h2 h2 h2) (* h3 h3 
h3) (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 14 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) 
(* h5 h5) (* j2 j2)) (* 1152 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 5792 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 
j2 j2 j2 j2 j2)) (* 10496 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 
j2 j2 j2)) (* 8488 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2))
 (* 3440 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 680 (* h2
 h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 52 (* h2 h2 h2) (* h3 h3 
h3) (* h4 h4) h5 h6 (* j2 j2)) (* 1024 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) (* h6
 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3072 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) (* h6
 h6) (* j2 j2 j2 j2 j2 j2)) (* 3392 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6
) (* j2 j2 j2 j2 j2)) (* 1696 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* 
j2 j2 j2 j2)) (* 384 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2))
 (* 32 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2)) (* 288 (* h2 h2 
h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1656 (* h2 h2 
h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 3660 (* h2 h2 h2) 
(* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 3954 (* h2 h2 h2) (* h3 
h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 2231 (* h2 h2 h2) (* h3 h3 h3) h4 
(* h5 h5 h5) (* j2 j2 j2 j2)) (* 664 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) 
(* j2 j2 j2)) (* 87 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2)) (* 4 
(* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) j2) (* 1536 (* h2 h2 h2) (* h3 h3 h3) 
h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 8352 (* h2 h2 h2) (* h3 h3 h3) 
h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 17632 (* h2 h2 h2) (* h3 h3 h3) h4 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 18600 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 
h5) h6 (* j2 j2 j2 j2 j2)) (* 10600 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 
(* j2 j2 j2 j2)) (* 3292 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2))
 (* 504 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 28 (* h2 h2 h2) 
(* h3 h3 h3) h4 (* h5 h5) h6 j2) (* 1152 (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6816 (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 15872 (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6)
 (* j2 j2 j2 j2 j2 j2)) (* 18344 (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2
 j2 j2 j2 j2)) (* 11376 (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2
)) (* 3872 (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 680 (* h2 
h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 48 (* h2 h2 h2) (* h3 h3 h3) 
h4 h5 (* h6 h6) j2) (* 512 (* h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2
 j2 j2 j2 j2)) (* 2048 (* h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 3232 (* h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 2544 (* h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1040 (* h2
 h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2)) (* 208 (* h2 h2 h2) (* h3 h3 
h3) h4 (* h6 h6 h6) (* j2 j2)) (* 16 (* h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6) 
j2) (* 288 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 1848 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 4764 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 6362
 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 4731 (* h2 h2 
h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 1954 (* h2 h2 h2) (* h3 h3 
h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 409 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) 
h6 (* j2 j2)) (* 28 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 j2) (* 768 (* h2 
h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4736 (* 
h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 11848 
(* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 15616 
(* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 11742 (* h2
 h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 5068 (* h2 h2 h2) 
(* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 1174 (* h2 h2 h2) (* h3 h3 h3)
 (* h5 h5) (* h6 h6) (* j2 j2)) (* 112 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* h6
 h6) j2) (* 384 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 2272 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 5632 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 7544 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 5856 
(* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 2608 (* h2 h2 h2) 
(* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 608 (* h2 h2 h2) (* h3 h3 h3) h5 
(* h6 h6 h6) (* j2 j2)) (* 56 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) j2) (* 
96 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 216
 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 136 (* 
h2 h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 30 (* h2 h2 h2)
 (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 2 (* h2 h2 h2) (* h3 h3) 
(* h4 h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 128 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4 h4
) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 128 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4 h4) h6 
(* j2 j2 j2 j2 j2 j2)) (* 40 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4 h4) h6 (* j2 j2 
j2 j2 j2)) (* 4 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4 h4) h6 (* j2 j2 j2 j2)) (* 
144 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 768 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 1488 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 
j2)) (* 1340 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)
) (* 595 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 
121 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 8 (* h2 h2
 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 816 (* h2 h2 h2) (* h3 h3
) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2504 (* h2 h2 h2) (* h3 h3)
 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2684 (* h2 h2 h2) (* h3 h3) (* 
h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 1358 (* h2 h2 h2) (* h3 h3) (* h4 h4 
h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 334 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 
(* j2 j2 j2 j2)) (* 32 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2)) 
(* 576 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 944 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
584 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 160 (* 
h2 h2 h2) (* h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 16 (* h2 h2 h2) 
(* h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2)) (* 144 (* h2 h2 h2) (* h3 h3) (* 
h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 912 (* h2 h2 h2) (* h3 h3
) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2232 (* h2 h2 h2) (* h3
 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 2744 (* h2 h2 h2) (* h3
 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1829 (* h2 h2 h2) (* h3 h3
) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 657 (* h2 h2 h2) (* h3 h3) (* h4
 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 115 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5
 h5 h5) (* j2 j2 j2)) (* 7 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 
j2)) (* 432 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 3072 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 8088 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2)) (* 10408 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2
 j2 j2 j2)) (* 7255 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2
 j2)) (* 2798 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 
560 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 45 (* h2 h2 
h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 1440 (* h2 h2 h2) (* h3 h3) 
(* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 5744 (* h2 h2 h2) (* h3 
h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 8872 (* h2 h2 h2) (* h3 
h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6908 (* h2 h2 h2) (* h3 h3)
 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2932 (* h2 h2 h2) (* h3 h3) (* h4
 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 650 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 
(* h6 h6) (* j2 j2 j2)) (* 58 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* 
j2 j2)) (* 576 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 1520 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 1528 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 744 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 176 (* 
h2 h2 h2) (* h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2)) (* 16 (* h2 h2 h2) (* 
h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2)) (* 72 (* h2 h2 h2) (* h3 h3) h4 (* h5 
h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 396 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5
 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 870 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5 
h5) (* j2 j2 j2 j2 j2 j2)) (* 969 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* 
j2 j2 j2 j2 j2)) (* 572 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2
)) (* 170 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2)) (* 22 (* h2 h2
 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2)) (* (* h2 h2 h2) (* h3 h3) h4 (* h5 
h5 h5 h5) j2) (* 288 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2
 j2 j2 j2 j2)) (* 2112 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 6288 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2)) (* 9952 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2)) (* 9146 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
4972 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 1544 (* h2 h2
 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 244 (* h2 h2 h2) (* h3 h3) h4
 (* h5 h5 h5) h6 (* j2 j2)) (* 14 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 j2) 
(* 432 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 3456 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 10928 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2)) (* 18020 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 17109 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2
)) (* 9655 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 
3185 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 564 (* h2 h2
 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 41 (* h2 h2 h2) (* h3 h3) h4
 (* h5 h5) (* h6 h6) j2) (* 816 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 4024 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 8116 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 8682 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 
j2)) (* 5336 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1894 
(* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 360 (* h2 h2 h2) (* 
h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2)) (* 28 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6
 h6) j2) (* 128 (* h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 512 (* h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
808 (* h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 636 (* h2 
h2 h2) (* h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 260 (* h2 h2 h2) (* h3 
h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 52 (* h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6
 h6) (* j2 j2)) (* 4 (* h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6 h6) j2) (* 72 (* h2 
h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 444 (* h2 h2
 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1134 (* h2 h2 h2)
 (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 1541 (* h2 h2 h2) (* h3 
h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 1186 (* h2 h2 h2) (* h3 h3) (* h5 
h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 504 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 
(* j2 j2 j2)) (* 104 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 7 
(* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 j2) (* 144 (* h2 h2 h2) (* h3 h3) (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1152 (* h2 h2 h2) (* h3 
h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3872 (* h2 h2 h2) (* 
h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 7180 (* h2 h2 h2) (* 
h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 8059 (* h2 h2 h2) (* h3 
h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 5617 (* h2 h2 h2) (* h3 h3) 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 2377 (* h2 h2 h2) (* h3 h3) (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2)) (* 559 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6)
 (* j2 j2)) (* 56 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) j2) (* 144 (* h2
 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1152
 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
3896 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
7304 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
8321 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 5906 
(* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 2552 (* h2 h2 
h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 614 (* h2 h2 h2) (* h3 h3)
 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 63 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 
h6 h6) j2) (* 96 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 568 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2
)) (* 1408 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
1886 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1464 (* h2
 h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 652 (* h2 h2 h2) (* h3 
h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 152 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 
h6 h6) (* j2 j2)) (* 14 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) j2) (* 24 (* 
h2 h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 84 (* 
h2 h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 106 (* h2
 h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 59 (* h2 h2 h2
) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 14 (* h2 h2 h2) h3 (* 
h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* (* h2 h2 h2) h3 (* h4 h4 h4 h4) 
(* h5 h5) (* j2 j2 j2 j2)) (* 72 (* h2 h2 h2) h3 (* h4 h4 h4 h4) h5 h6 (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 164 (* h2 h2 h2) h3 (* h4 h4 h4 h4) h5 h6 (* j2 j2 j2 j2 
j2 j2 j2)) (* 130 (* h2 h2 h2) h3 (* h4 h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) 
(* 43 (* h2 h2 h2) h3 (* h4 h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 5 (* h2 h2 h2
) h3 (* h4 h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 32 (* h2 h2 h2) h3 (* h4 h4 h4 h4
) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 40 (* h2 h2 h2) h3 (* h4 h4 h4 h4) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 16 (* h2 h2 h2) h3 (* h4 h4 h4 h4) (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* 2 (* h2 h2 h2) h3 (* h4 h4 h4 h4) (* h6 h6) (* j2 j2 j2 
j2)) (* 48 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 216 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 380 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 330 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 146 
(* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 30 (* h2 h2 h2)
 h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 2 (* h2 h2 h2) h3 (* h4 h4 h4)
 (* h5 h5 h5) (* j2 j2 j2)) (* 160 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 768 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1408 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 1288 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2)) (* 630 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2
 j2 j2)) (* 158 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 16
 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 280 (* h2 h2 h2) h3 
(* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 868 (* h2 h2 h2) h3 
(* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1026 (* h2 h2 h2) h3 (* 
h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 587 (* h2 h2 h2) h3 (* h4 h4 h4
) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 164 (* h2 h2 h2) h3 (* h4 h4 h4) h5 (* h6 
h6) (* j2 j2 j2 j2)) (* 18 (* h2 h2 h2) h3 (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2
)) (* 64 (* h2 h2 h2) h3 (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
144 (* h2 h2 h2) h3 (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 112 (* 
h2 h2 h2) h3 (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 36 (* h2 h2 h2) h3
 (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 4 (* h2 h2 h2) h3 (* h4 h4 h4) 
(* h6 h6 h6) (* j2 j2 j2)) (* 24 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2
 j2 j2 j2 j2 j2 j2 j2 j2)) (* 132 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 298 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2
 j2 j2 j2 j2 j2 j2)) (* 355 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 
j2 j2 j2 j2)) (* 238 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2
)) (* 88 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 16 (* h2 
h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* (* h2 h2 h2) h3 (* h4 h4) 
(* h5 h5 h5 h5) (* j2 j2)) (* 208 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1128 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2484 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 2890 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2)) (* 1926 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2)) (* 739 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 
152 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 13 (* h2 h2 h2) 
h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 272 (* h2 h2 h2) h3 (* h4 h4) (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1584 (* h2 h2 h2) h3 (* h4 h4) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3720 (* h2 h2 h2) h3 (* h4 
h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4616 (* h2 h2 h2) h3 (* h4 
h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3297 (* h2 h2 h2) h3 (* h4 h4)
 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1367 (* h2 h2 h2) h3 (* h4 h4) (* h5
 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 307 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* h6
 h6) (* j2 j2 j2)) (* 29 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)
) (* 280 (* h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 1140 (* h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
1866 (* h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1575 
(* h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 726 (* h2 h2 h2
) h3 (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 174 (* h2 h2 h2) h3 (* h4 h4)
 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 17 (* h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6 h6) 
(* j2 j2)) (* 32 (* h2 h2 h2) h3 (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 104 (* h2 h2 h2) h3 (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
128 (* h2 h2 h2) h3 (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 74 (* h2 h2
 h2) h3 (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 20 (* h2 h2 h2) h3 (* h4 
h4) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 2 (* h2 h2 h2) h3 (* h4 h4) (* h6 h6 h6 h6)
 (* j2 j2)) (* 48 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 312 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 860 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1306
 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 1186 (* h2 h2 
h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 652 (* h2 h2 h2) h3 h4 (* h5
 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 208 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* 
j2 j2 j2)) (* 34 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 2 (* h2 h2 
h2) h3 h4 (* h5 h5 h5 h5) h6 j2) (* 208 (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1320 (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3532 (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 5206 (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 4624 (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2)) (* 2536 (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2))
 (* 840 (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 154 (* h2 h2 
h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 12 (* h2 h2 h2) h3 h4 (* h5 h5 h5
) (* h6 h6) j2) (* 160 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 1072 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 3016 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 4668 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 4356 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 2514 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 878 (* h2 
h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 170 (* h2 h2 h2) h3 h4 (* 
h5 h5) (* h6 h6 h6) (* j2 j2)) (* 14 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) 
j2) (* 72 (* h2 h2 h2) h3 h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
372 (* h2 h2 h2) h3 h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 802 (* h2
 h2 h2) h3 h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 931 (* h2 h2 h2) h3 
h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 625 (* h2 h2 h2) h3 h4 h5 (* h6 h6 
h6 h6) (* j2 j2 j2 j2)) (* 241 (* h2 h2 h2) h3 h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2
)) (* 49 (* h2 h2 h2) h3 h4 h5 (* h6 h6 h6 h6) (* j2 j2)) (* 4 (* h2 h2 h2) h3 
h4 h5 (* h6 h6 h6 h6) j2) (* 24 (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 172 (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 534 (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 937 (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2
 j2 j2 j2)) (* 1015 (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)
) (* 694 (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 292 (* h2
 h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 69 (* h2 h2 h2) h3 (* h5 
h5 h5 h5) (* h6 h6) (* j2 j2)) (* 7 (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) j2
) (* 48 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 344 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 1068 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
1874 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2030 
(* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1388 (* h2 h2 
h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 584 (* h2 h2 h2) h3 (* h5 
h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 138 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6 
h6) (* j2 j2)) (* 14 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) j2) (* 24 (* h2 
h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 172 (* h2
 h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 534 (* h2 
h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 937 (* h2 h2 h2
) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1015 (* h2 h2 h2) h3 
(* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 694 (* h2 h2 h2) h3 (* h5 h5) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 292 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6
) (* j2 j2 j2)) (* 69 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 7 
(* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) j2) (* 8 (* h2 h2 h2) (* h4 h4 h4 h4) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 28 (* h2 h2 h2) (* h4 h4 h4 h4) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 38 (* h2 h2 h2) (* h4 h4 h4 h4) (* 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 25 (* h2 h2 h2) (* h4 h4 h4 h4) (* h5 h5)
 h6 (* j2 j2 j2 j2 j2 j2)) (* 8 (* h2 h2 h2) (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* (* h2 h2 h2) (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 8
 (* h2 h2 h2) (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 20 
(* h2 h2 h2) (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 18 (* h2 
h2 h2) (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 7 (* h2 h2 h2) (* 
h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* (* h2 h2 h2) (* h4 h4 h4 h4) h5
 (* h6 h6) (* j2 j2 j2 j2)) (* 16 (* h2 h2 h2) (* h4 h4 h4) (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 72 (* h2 h2 h2) (* h4 h4 h4) (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 132 (* h2 h2 h2) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2
 j2 j2 j2 j2 j2 j2)) (* 126 (* h2 h2 h2) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2)) (* 66 (* h2 h2 h2) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)
) (* 18 (* h2 h2 h2) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 2 (* h2 h2
 h2) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 24 (* h2 h2 h2) (* h4 h4 h4) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 116 (* h2 h2 h2) (* h4 h4
 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 226 (* h2 h2 h2) (* h4 
h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 227 (* h2 h2 h2) (* h4 
h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 124 (* h2 h2 h2) (* h4 h4 
h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 35 (* h2 h2 h2) (* h4 h4 h4) (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 4 (* h2 h2 h2) (* h4 h4 h4) (* h5 h5) (* h6
 h6) (* j2 j2 j2)) (* 16 (* h2 h2 h2) (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 56 (* h2 h2 h2) (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 76 (* h2 h2 h2) (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)
) (* 50 (* h2 h2 h2) (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 16 (* 
h2 h2 h2) (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 2 (* h2 h2 h2) (* h4 
h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 8 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5 h5)
 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 44 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5 h5)
 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 102 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 129 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 96 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 
j2 j2 j2)) (* 42 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 
10 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* (* h2 h2 h2) (* h4
 h4) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 32 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 176 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5
) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 408 (* h2 h2 h2) (* h4 h4) (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 516 (* h2 h2 h2) (* h4 h4) (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 384 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 168 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2)) (* 40 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 
j2 j2)) (* 4 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 24 (* 
h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
140 (* h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 342 (* h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 453 (* h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
351 (* h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 159 (* 
h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 39 (* h2 h2 h2) 
(* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 4 (* h2 h2 h2) (* h4 h4) (* h5
 h5) (* h6 h6 h6) (* j2 j2)) (* 8 (* h2 h2 h2) (* h4 h4) h5 (* h6 h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 36 (* h2 h2 h2) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 66 (* h2 h2 h2) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 63 (* h2 h2 h2) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 33 (* h2 h2 h2) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 9 (* h2 h2 
h2) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* (* h2 h2 h2) (* h4 h4) h5 (* 
h6 h6 h6 h6) (* j2 j2)) (* 8 (* h2 h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 52 (* h2 h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 146 (* h2 h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2
 j2 j2 j2 j2)) (* 231 (* h2 h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 225 (* h2 h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
138 (* h2 h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 52 (* h2 h2 h2
) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 11 (* h2 h2 h2) h4 (* h5 h5 h5 
h5) (* h6 h6) (* j2 j2)) (* (* h2 h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6) j2) (* 16 
(* h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 104
 (* h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 292 
(* h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 462 (* h2
 h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 450 (* h2 h2 h2) 
h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 276 (* h2 h2 h2) h4 (* h5 h5
 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 104 (* h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6 
h6) (* j2 j2 j2)) (* 22 (* h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 
2 (* h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6) j2) (* 8 (* h2 h2 h2) h4 (* h5 h5) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 52 (* h2 h2 h2) h4 (* h5 h5) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 146 (* h2 h2 h2) h4 (* h5 h5) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 231 (* h2 h2 h2) h4 (* h5 h5) (* h6
 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 225 (* h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6 
h6) (* j2 j2 j2 j2 j2)) (* 138 (* h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 
j2 j2 j2)) (* 52 (* h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 11 
(* h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* (* h2 h2 h2) h4 (* h5 h5
) (* h6 h6 h6 h6) j2) (* 192 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 720 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2
 j2 j2 j2 j2)) (* 968 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 
j2 j2)) (* 552 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 
120 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 8 (* h2 h2) 
(* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 256 (* h2 h2) (* h3 h3 h3 h3) 
(* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 640 (* h2 h2) (* h3 h3 h3 h3) (* h4
 h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 528 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4 h4) 
h6 (* j2 j2 j2 j2 j2)) (* 160 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2
 j2 j2)) (* 16 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2)) (* 384 
(* h2 h2) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
1824 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
3184 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 
2512 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 904 
(* h2 h2) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 144 (* h2 h2) 
(* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 8 (* h2 h2) (* h3 h3 h3 h3)
 (* h4 h4) (* h5 h5) (* j2 j2)) (* 576 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 h6
 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3184 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 6424 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* 
j2 j2 j2 j2 j2 j2)) (* 5768 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 
j2 j2 j2)) (* 2368 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) 
(* 448 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 32 (* h2 h2) 
(* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 512 (* h2 h2) (* h3 h3 h3 h3) (* 
h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1792 (* h2 h2) (* h3 h3 h3 h3) (* 
h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2336 (* h2 h2) (* h3 h3 h3 h3) (* h4 
h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1376 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) 
(* h6 h6) (* j2 j2 j2 j2)) (* 352 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) (* h6 h6) 
(* j2 j2 j2)) (* 32 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2)) (* 
144 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
864 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 2028 
(* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2340 (* h2 
h2) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 1366 (* h2 h2) (* h3 
h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 378 (* h2 h2) (* h3 h3 h3 h3) h4 
(* h5 h5 h5) (* j2 j2 j2)) (* 46 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2
 j2)) (* 2 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5 h5) j2) (* 768 (* h2 h2) (* h3 
h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4464 (* h2 h2) (* h3 
h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 10064 (* h2 h2) (* h3 h3 
h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 11148 (* h2 h2) (* h3 h3 h3 h3)
 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 6336 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 
h5) h6 (* j2 j2 j2 j2)) (* 1784 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 
j2 j2)) (* 240 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 12 (* h2 
h2) (* h3 h3 h3 h3) h4 (* h5 h5) h6 j2) (* 576 (* h2 h2) (* h3 h3 h3 h3) h4 h5 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3696 (* h2 h2) (* h3 h3 h3 h3) h4 h5 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 9368 (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 11720 (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* h6 h6)
 (* j2 j2 j2 j2 j2)) (* 7584 (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 
j2 j2)) (* 2480 (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 392 
(* h2 h2) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 24 (* h2 h2) (* h3 h3 h3
 h3) h4 h5 (* h6 h6) j2) (* 256 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 1152 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 2064 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 
j2)) (* 1856 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 864 
(* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2)) (* 192 (* h2 h2) (* h3 
h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2)) (* 16 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6
 h6) j2) (* 144 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 960 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2
)) (* 2604 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
3676 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 2854 (* h2
 h2) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 1174 (* h2 h2) (* h3 h3
 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 222 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 
h5) h6 (* j2 j2)) (* 14 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) h6 j2) (* 384 (* 
h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2512 
(* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 6656 
(* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 9204 (* 
h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 7092 (* h2 h2)
 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 2996 (* h2 h2) (* h3 h3
 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 636 (* h2 h2) (* h3 h3 h3 h3) (* h5
 h5) (* h6 h6) (* j2 j2)) (* 56 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) j2
) (* 192 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 1232 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
3336 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4920 
(* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 4240 (* h2 h2) 
(* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 2112 (* h2 h2) (* h3 h3 h3 
h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 552 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6 
h6) (* j2 j2)) (* 56 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6 h6) j2) (* 96 (* h2 
h2) (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 264 (* h2 h2
) (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 220 (* h2 h2) (* 
h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 56 (* h2 h2) (* h3 h3 h3)
 (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 4 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4 
h4) h5 (* j2 j2 j2 j2)) (* 128 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4 h4) h6 (* j2 
j2 j2 j2 j2 j2 j2)) (* 192 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4 h4) h6 (* j2 j2 j2
 j2 j2 j2)) (* 72 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4 h4) h6 (* j2 j2 j2 j2 j2)) 
(* 8 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4 h4) h6 (* j2 j2 j2 j2)) (* 144 (* h2 h2)
 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 840 (* 
h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1812 
(* h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1838 
(* h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 910 (* 
h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 202 (* h2 h2) 
(* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 14 (* h2 h2) (* h3 h3 h3
) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 816 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4
) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2880 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4)
 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 3580 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 
h6 (* j2 j2 j2 j2 j2 j2)) (* 1980 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* 
j2 j2 j2 j2 j2)) (* 516 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2
)) (* 52 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 576 (* h2 h2
) (* h3 h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1232 (* h2 h2
) (* h3 h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 912 (* h2 h2) 
(* h3 h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 288 (* h2 h2) (* h3 
h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 32 (* h2 h2) (* h3 h3 h3) (* 
h4 h4 h4) (* h6 h6) (* j2 j2 j2)) (* 144 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 984 (* h2 h2) (* h3 h3 h3) (* h4 h4) 
(* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2604 (* h2 h2) (* h3 h3 h3) (* h4 
h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 3398 (* h2 h2) (* h3 h3 h3) (* h4 
h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2320 (* h2 h2) (* h3 h3 h3) (* h4 h4)
 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 821 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 
h5 h5) (* j2 j2 j2 j2)) (* 137 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* 
j2 j2 j2)) (* 8 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 432 
(* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 3288 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 9380 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2
)) (* 13090 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2))
 (* 9656 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
3824 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 748 (* h2
 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 56 (* h2 h2) (* h3 h3 
h3) (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 1440 (* h2 h2) (* h3 h3 h3) (* h4 h4) 
h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6400 (* h2 h2) (* h3 h3 h3) (* h4 
h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 11016 (* h2 h2) (* h3 h3 h3) (* h4
 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 9456 (* h2 h2) (* h3 h3 h3) (* h4 h4
) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 4324 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 
(* h6 h6) (* j2 j2 j2 j2)) (* 1020 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6)
 (* j2 j2 j2)) (* 96 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2)) 
(* 576 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 1808 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
2144 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1200 
(* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 320 (* h2 h2) 
(* h3 h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2)) (* 32 (* h2 h2) (* h3 h3 h3) 
(* h4 h4) (* h6 h6 h6) (* j2 j2)) (* 72 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5 h5
) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 432 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 1014 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* 
j2 j2 j2 j2 j2 j2)) (* 1170 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 
j2 j2 j2)) (* 683 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 
189 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2)) (* 23 (* h2 h2) (* 
h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2)) (* (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5
 h5) j2) (* 288 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 2256 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 7128 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 11776 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)
) (* 11056 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 6001
 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 1803 (* h2 h2) 
(* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 255 (* h2 h2) (* h3 h3 h3) h4 
(* h5 h5 h5) h6 (* j2 j2)) (* 13 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) h6 j2) 
(* 432 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 3672 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 12388 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2)) (* 21754 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 21700 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2
)) (* 12584 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 
4128 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 680 (* h2 h2
) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 42 (* h2 h2) (* h3 h3 h3) h4
 (* h5 h5) (* h6 h6) j2) (* 816 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 4400 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 9676 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 11248 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 
j2)) (* 7456 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 2812 
(* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 556 (* h2 h2) (* h3 
h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2)) (* 44 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6
 h6) j2) (* 128 (* h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 576 (* h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
1032 (* h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 928 (* h2 
h2) (* h3 h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 432 (* h2 h2) (* h3 h3 
h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 96 (* h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6
 h6) (* j2 j2)) (* 8 (* h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6 h6) j2) (* 72 (* h2 
h2) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 480 (* h2 h2
) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1302 (* h2 h2) 
(* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 1838 (* h2 h2) (* h3 
h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 1427 (* h2 h2) (* h3 h3 h3) (* 
h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 587 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) 
h6 (* j2 j2 j2)) (* 111 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 
7 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) h6 j2) (* 144 (* h2 h2) (* h3 h3 h3) 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1224 (* h2 h2) (* h3 
h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4340 (* h2 h2) (* 
h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 8402 (* h2 h2) (* 
h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 9754 (* h2 h2) (* h3 
h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 6985 (* h2 h2) (* h3 h3 h3)
 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 3015 (* h2 h2) (* h3 h3 h3) (* h5 h5
 h5) (* h6 h6) (* j2 j2 j2)) (* 705 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6
) (* j2 j2)) (* 63 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) j2) (* 144 (* 
h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
1224 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 4388 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 8758 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
10710 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 8238 
(* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 3886 (* h2 h2)
 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 1020 (* h2 h2) (* h3 h3 h3
) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 112 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* 
h6 h6 h6) j2) (* 96 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 616 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2
 j2)) (* 1668 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 2460 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2120 
(* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 1056 (* h2 h2) (* 
h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 276 (* h2 h2) (* h3 h3 h3) h5 (* 
h6 h6 h6 h6) (* j2 j2)) (* 28 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6 h6) j2) (* 
48 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (* 204 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 296 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)
) (* 181 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) 
(* 51 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 4 (* 
h2 h2) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 144 (* h2 h2) (* 
h3 h3) (* h4 h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 400 (* h2 h2) (* h3
 h3) (* h4 h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 340 (* h2 h2) (* h3 h3) 
(* h4 h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 124 (* h2 h2) (* h3 h3) (* h4 h4
 h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 16 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 
h6 (* j2 j2 j2 j2)) (* 64 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) (* h6 h6) (* j2 j2
 j2 j2 j2 j2 j2)) (* 112 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) (* h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 56 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2
 j2)) (* 8 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 96 
(* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 492 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 964 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2))
 (* 913 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 
437 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 99 (* 
h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 7 (* h2 h2) (* h3
 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 288 (* h2 h2) (* h3 h3) (* h4 h4
 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1576 (* h2 h2) (* h3 h3) 
(* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3196 (* h2 h2) (* h3 
h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 3138 (* h2 h2) (* h3 
h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 1639 (* h2 h2) (* h3 h3)
 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 433 (* h2 h2) (* h3 h3) (* h4 
h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 45 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* 
h5 h5) h6 (* j2 j2 j2)) (* 528 (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 1880 (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 2420 (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 1538 (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* 
j2 j2 j2 j2 j2)) (* 480 (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 
j2 j2)) (* 58 (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 128
 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 352 
(* h2 h2) (* h3 h3) (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 336 (* 
h2 h2) (* h3 h3) (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 128 (* h2 h2) 
(* h3 h3) (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 16 (* h2 h2) (* h3 h3) 
(* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2)) (* 48 (* h2 h2) (* h3 h3) (* h4 h4) (* 
h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 288 (* h2 h2) (* h3 h3) (* h4 h4
) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 692 (* h2 h2) (* h3 h3) (* h4 
h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 852 (* h2 h2) (* h3 h3) (* h4 
h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 570 (* h2 h2) (* h3 h3) (* h4 h4) 
(* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 202 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 
h5 h5 h5) (* j2 j2 j2 j2)) (* 34 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) 
(* j2 j2 j2)) (* 2 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 
384 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 2300 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 5496 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2)) (* 6777 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)
) (* 4674 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
1810 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 361 (* h2
 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 28 (* h2 h2) (* h3 h3)
 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 480 (* h2 h2) (* h3 h3) (* h4 h4) (* h5
 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3112 (* h2 h2) (* h3 h3) (* h4
 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 7956 (* h2 h2) (* h3 h3
) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 10586 (* h2 h2) (* 
h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 8057 (* h2 h2) 
(* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 3549 (* h2 h2) 
(* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 836 (* h2 h2) (* h3 
h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 82 (* h2 h2) (* h3 h3) (* h4 
h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 528 (* h2 h2) (* h3 h3) (* h4 h4) h5 (* h6
 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2392 (* h2 h2) (* h3 h3) (* h4 h4) h5 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4236 (* h2 h2) (* h3 h3) (* h4 h4) h5 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3874 (* h2 h2) (* h3 h3) (* h4 h4) h5 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1970 (* h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6 
h6) (* j2 j2 j2 j2)) (* 524 (* h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 
j2 j2)) (* 56 (* h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2)) (* 64 (* 
h2 h2) (* h3 h3) (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 240 (* 
h2 h2) (* h3 h3) (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 344 (* h2 
h2) (* h3 h3) (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 232 (* h2 h2) (* 
h3 h3) (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 72 (* h2 h2) (* h3 h3) (* 
h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 8 (* h2 h2) (* h3 h3) (* h4 h4) (* h6 h6
 h6 h6) (* j2 j2)) (* 96 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 672 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 1948 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2)) (* 3028 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2)) (* 2725 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) 
(* 1426 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 412 (* h2 
h2) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 58 (* h2 h2) (* h3 h3) h4 
(* h5 h5 h5 h5) h6 (* j2 j2)) (* 3 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) h6 j2)
 (* 384 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
 j2)) (* 2652 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 7620 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2)) (* 11857 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 10901 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2
)) (* 6043 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 
1956 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 330 (* h2 h2
) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 21 (* h2 h2) (* h3 h3) h4 
(* h5 h5 h5) (* h6 h6) j2) (* 288 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2120 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6428 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 10582 (* h2 h2) (* h3 h3) h4 (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 10407 (* h2 h2) (* h3 h3) h4 (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 6282 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2)) (* 2271 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2)) (* 446 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2)) 
(* 36 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) j2) (* 144 (* h2 h2) (* h3 
h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 816 (* h2 h2) (* h3 h3
) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1892 (* h2 h2) (* h3 h3) h4
 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2324 (* h2 h2) (* h3 h3) h4 h5 (* 
h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1632 (* h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6 
h6) (* j2 j2 j2 j2)) (* 656 (* h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2 
j2)) (* 140 (* h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2)) (* 12 (* h2 h2)
 (* h3 h3) h4 h5 (* h6 h6 h6 h6) j2) (* 48 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 368 (* h2 h2) (* h3 h3) (* h5 h5 h5
 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1204 (* h2 h2) (* h3 h3) (* h5 h5
 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2192 (* h2 h2) (* h3 h3) (* h5 h5
 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2422 (* h2 h2) (* h3 h3) (* h5 h5 h5
 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1656 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2)) (* 680 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) 
(* j2 j2 j2)) (* 152 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) 
(* 14 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) j2) (* 96 (* h2 h2) (* h3 h3
) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 748 (* h2 h2) (* 
h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2512 (* h2 h2) 
(* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4753 (* h2 h2) 
(* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 5548 (* h2 h2) (* 
h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 4098 (* h2 h2) (* h3 h3)
 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1876 (* h2 h2) (* h3 h3) (* h5 h5
 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 489 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6
 h6) (* j2 j2)) (* 56 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) j2) (* 48 
(* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 380 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 1284 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 2425 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 2808 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
2050 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 928 (* h2
 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 241 (* h2 h2) (* h3 h3
) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 28 (* h2 h2) (* h3 h3) (* h5 h5) (* h6
 h6 h6 h6) j2) (* 12 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2
 j2 j2 j2 j2)) (* 48 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 71 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2
 j2)) (* 47 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 
13 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* (* h2 h2) h3
 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 24 (* h2 h2) h3 (* h4 h4 h4 h4
) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 120 (* h2 h2) h3 (* h4 h4 h4 
h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 206 (* h2 h2) h3 (* h4 h4 h4 h4
) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 160 (* h2 h2) h3 (* h4 h4 h4 h4) (* 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 58 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) h6
 (* j2 j2 j2 j2 j2)) (* 8 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 
j2)) (* 24 (* h2 h2) h3 (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 96 (* h2 h2) h3 (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
114 (* h2 h2) h3 (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 54 (* h2
 h2) h3 (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 9 (* h2 h2) h3 (* h4
 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 16 (* h2 h2) h3 (* h4 h4 h4 h4) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 12 (* h2 h2) h3 (* h4 h4 h4 h4) (* h6 h6 h6)
 (* j2 j2 j2 j2 j2)) (* 2 (* h2 h2) h3 (* h4 h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 
j2)) (* 12 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 60 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 119 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
118 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 60 (* h2
 h2) h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 14 (* h2 h2) h3 (* 
h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* (* h2 h2) h3 (* h4 h4 h4) (* h5 h5
 h5 h5) (* j2 j2 j2)) (* 96 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 468 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2
 j2 j2 j2 j2 j2 j2)) (* 896 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2)) (* 865 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2
 j2 j2)) (* 447 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) 
(* 119 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 13 (* h2 h2
) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 72 (* h2 h2) h3 (* h4 h4 h4) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 456 (* h2 h2) h3 (* h4 h4
 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1058 (* h2 h2) h3 (* h4
 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1208 (* h2 h2) h3 (* h4
 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 734 (* h2 h2) h3 (* h4 h4 
h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 229 (* h2 h2) h3 (* h4 h4 h4) (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 29 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* 
h6 h6) (* j2 j2 j2)) (* 48 (* h2 h2) h3 (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 240 (* h2 h2) h3 (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 416 (* h2 h2) h3 (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2
 j2)) (* 328 (* h2 h2) h3 (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
121 (* h2 h2) h3 (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 17 (* h2 h2) 
h3 (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 16 (* h2 h2) h3 (* h4 h4 h4) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 28 (* h2 h2) h3 (* h4 h4 h4) (* h6 h6 
h6 h6) (* j2 j2 j2 j2 j2)) (* 14 (* h2 h2) h3 (* h4 h4 h4) (* h6 h6 h6 h6) (* j2
 j2 j2 j2)) (* 2 (* h2 h2) h3 (* h4 h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 60 
(* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 336
 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 771 
(* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 935 (* h2
 h2) h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 643 (* h2 h2) h3 
(* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 249 (* h2 h2) h3 (* h4 h4) 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 50 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5)
 h6 (* j2 j2 j2)) (* 4 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 
168 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 980 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 2354 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 3023 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)
) (* 2249 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
977 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 233 (* h2 
h2) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 24 (* h2 h2) h3 (* h4 
h4) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 72 (* h2 h2) h3 (* h4 h4) (* h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 528 (* h2 h2) h3 (* h4 h4) (* h5 h5
) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1506 (* h2 h2) h3 (* h4 h4) (* h5
 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2238 (* h2 h2) h3 (* h4 h4) (* h5
 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1904 (* h2 h2) h3 (* h4 h4) (* h5 h5
) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 938 (* h2 h2) h3 (* h4 h4) (* h5 h5) (* h6
 h6 h6) (* j2 j2 j2 j2)) (* 250 (* h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2)) (* 28 (* h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 
24 (* h2 h2) h3 (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 144
 (* h2 h2) h3 (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 326 (* 
h2 h2) h3 (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 366 (* h2 h2) 
h3 (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 218 (* h2 h2) h3 (* h4 h4
) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 66 (* h2 h2) h3 (* h4 h4) h5 (* h6 h6 
h6 h6) (* j2 j2 j2)) (* 8 (* h2 h2) h3 (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2)) 
(* 60 (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 392 (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 1083 (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
1645 (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1493 
(* h2 h2) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 822 (* h2 h2) 
h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 265 (* h2 h2) h3 h4 (* h5 h5
 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 45 (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* h6 h6) 
(* j2 j2)) (* 3 (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* h6 h6) j2) (* 96 (* h2 h2) h3
 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 652 (* h2 h2) 
h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1880 (* h2 h2) 
h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3003 (* h2 h2) h3 
h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2903 (* h2 h2) h3 h4 (* 
h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1738 (* h2 h2) h3 h4 (* h5 h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2)) (* 630 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6 h6) 
(* j2 j2 j2)) (* 127 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 11 
(* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6 h6) j2) (* 24 (* h2 h2) h3 h4 (* h5 h5) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 192 (* h2 h2) h3 h4 (* h5 h5)
 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 630 (* h2 h2) h3 h4 (* h5 h5) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1122 (* h2 h2) h3 h4 (* h5 h5) (* 
h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1194 (* h2 h2) h3 h4 (* h5 h5) (* h6 h6 
h6 h6) (* j2 j2 j2 j2 j2)) (* 780 (* h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6 h6) (* 
j2 j2 j2 j2)) (* 306 (* h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 
66 (* h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 6 (* h2 h2) h3 h4 (* 
h5 h5) (* h6 h6 h6 h6) j2) (* 12 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2 j2)) (* 92 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 307 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 582 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2
 j2 j2 j2)) (* 685 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2))
 (* 512 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 237 (* h2 
h2) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 62 (* h2 h2) h3 (* h5 h5 h5
 h5) (* h6 h6 h6) (* j2 j2)) (* 7 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6 h6) j2) 
(* 12 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 92 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
307 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 582 
(* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 685 (* h2 h2
) h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 512 (* h2 h2) h3 (* h5 
h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 237 (* h2 h2) h3 (* h5 h5 h5) (* h6 
h6 h6 h6) (* j2 j2 j2)) (* 62 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2
)) (* 7 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6 h6) j2) (* 4 (* h2 h2) (* h4 h4 h4
 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 16 (* h2 h2) (* h4 h4 h4
 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 25 (* h2 h2) (* h4 h4 h4 h4
) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 19 (* h2 h2) (* h4 h4 h4 h4) (* 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 7 (* h2 h2) (* h4 h4 h4 h4) (* h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2)) (* (* h2 h2) (* h4 h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 
j2)) (* 8 (* h2 h2) (* h4 h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 24 (* h2 h2) (* h4 h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2
)) (* 26 (* h2 h2) (* h4 h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 12 (* h2 h2) (* h4 h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2 (* 
h2 h2) (* h4 h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 4 (* h2 h2) (* h4
 h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 8 (* h2 h2) (* h4 h4 h4 
h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 5 (* h2 h2) (* h4 h4 h4 h4) h5 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2)) (* (* h2 h2) (* h4 h4 h4 h4) h5 (* h6 h6 h6) (* j2
 j2 j2 j2)) (* 4 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 20 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 41 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)
) (* 44 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 26 
(* h2 h2) (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 8 (* h2 h2) (* 
h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* (* h2 h2) (* h4 h4 h4) (* h5 h5
 h5 h5) h6 (* j2 j2 j2)) (* 12 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 64 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5) (* h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 139 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 157 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 97 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* 31 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2
 j2 j2)) (* 4 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 16 
(* h2 h2) (* h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 64
 (* h2 h2) (* h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 100 
(* h2 h2) (* h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 76 (* h2
 h2) (* h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 28 (* h2 h2) (* 
h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 4 (* h2 h2) (* h4 h4 h4) 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 4 (* h2 h2) (* h4 h4 h4) h5 (* h6 h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 12 (* h2 h2) (* h4 h4 h4) h5 (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 13 (* h2 h2) (* h4 h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 
j2 j2 j2)) (* 6 (* h2 h2) (* h4 h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 
(* h2 h2) (* h4 h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 8 (* h2 h2) (* h4 h4)
 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 48 (* h2 h2) (* h4
 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 122 (* h2 h2) (* 
h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 170 (* h2 h2) (* 
h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 140 (* h2 h2) (* h4 
h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 68 (* h2 h2) (* h4 h4) (* 
h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 18 (* h2 h2) (* h4 h4) (* h5 h5 h5 h5
) (* h6 h6) (* j2 j2 j2)) (* 2 (* h2 h2) (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* 
j2 j2)) (* 12 (* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2 j2)) (* 76 (* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 203 (* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 296 (* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 254 (* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2)) (* 128 (* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 35
 (* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 4 (* h2 h2) (* 
h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 8 (* h2 h2) (* h4 h4) (* h5 h5) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 40 (* h2 h2) (* h4 h4) (* h5 h5)
 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 82 (* h2 h2) (* h4 h4) (* h5 h5) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 88 (* h2 h2) (* h4 h4) (* h5 h5) (* h6
 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 52 (* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6 h6 
h6) (* j2 j2 j2 j2)) (* 16 (* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 
j2 j2)) (* 2 (* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 4 (* h2
 h2) h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 28 (* h2
 h2) h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 85 (* h2 h2
) h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 146 (* h2 h2) h4 
(* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 155 (* h2 h2) h4 (* h5 h5
 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 104 (* h2 h2) h4 (* h5 h5 h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2)) (* 43 (* h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2
 j2 j2)) (* 10 (* h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* (* h2 h2)
 h4 (* h5 h5 h5 h5) (* h6 h6 h6) j2) (* 4 (* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 28 (* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 85 (* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2)) (* 146 (* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 155 (* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2
 j2 j2)) (* 104 (* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 43
 (* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 10 (* h2 h2) h4 (* 
h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* (* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6 h6
) j2) (* 48 h2 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2
 j2)) (* 264 h2 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 560 h2 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 572 h2 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 284 
h2 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 60 h2 (* h3 h3 
h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 4 h2 (* h3 h3 h3 h3) (* h4 h4 
h4) (* h5 h5) (* j2 j2 j2)) (* 144 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 584 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 
j2 j2 j2 j2)) (* 856 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)
) (* 552 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 152 h2 (* 
h3 h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 16 h2 (* h3 h3 h3 h3) (* h4 
h4 h4) h5 h6 (* j2 j2 j2)) (* 64 h2 (* h3 h3 h3 h3) (* h4 h4 h4) (* h6 h6) (* j2
 j2 j2 j2 j2 j2 j2)) (* 208 h2 (* h3 h3 h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 240 h2 (* h3 h3 h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2
)) (* 112 h2 (* h3 h3 h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 16 h2 
(* h3 h3 h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2)) (* 48 h2 (* h3 h3 h3 h3) 
(* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 312 h2 (* h3 h3 h3 h3)
 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 800 h2 (* h3 h3 h3 h3) 
(* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1024 h2 (* h3 h3 h3 h3) (* 
h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 684 h2 (* h3 h3 h3 h3) (* h4 h4) 
(* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 230 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5
) (* j2 j2 j2 j2)) (* 36 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2))
 (* 2 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 144 h2 (* h3 h3 h3
 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1048 h2 (* h3 h3 
h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2976 h2 (* h3 h3 
h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 4164 h2 (* h3 h3 h3 
h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 2996 h2 (* h3 h3 h3 h3) (* 
h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 1076 h2 (* h3 h3 h3 h3) (* h4 h4) (* 
h5 h5) h6 (* j2 j2 j2 j2)) (* 184 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* 
j2 j2 j2)) (* 12 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 288 h2 
(* h3 h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1440 h2 
(* h3 h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2808 h2 (* 
h3 h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2688 h2 (* h3 h3 
h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1296 h2 (* h3 h3 h3 h3) (* 
h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 288 h2 (* h3 h3 h3 h3) (* h4 h4) h5 (* 
h6 h6) (* j2 j2 j2)) (* 24 h2 (* h3 h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2)) 
(* 64 h2 (* h3 h3 h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 272
 h2 (* h3 h3 h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 448 h2 (* 
h3 h3 h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 352 h2 (* h3 h3 h3 h3
) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 128 h2 (* h3 h3 h3 h3) (* h4 h4) 
(* h6 h6 h6) (* j2 j2 j2)) (* 16 h2 (* h3 h3 h3 h3) (* h4 h4) (* h6 h6 h6) (* j2
 j2)) (* 96 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 720 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
2176 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 3384 h2 
(* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 2856 h2 (* h3 h3 h3
 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 1256 h2 (* h3 h3 h3 h3) h4 (* h5 
h5 h5) h6 (* j2 j2 j2 j2)) (* 248 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2
 j2)) (* 16 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2)) (* 144 h2 (* h3 h3 
h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1176 h2 (* h3 
h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3912 h2 (* h3 
h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 6744 h2 (* h3 h3 
h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6364 h2 (* h3 h3 h3 h3) 
h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 3192 h2 (* h3 h3 h3 h3) h4 (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2)) (* 756 h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) 
(* j2 j2 j2)) (* 64 h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 144 
h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 856 h2 (* 
h3 h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2048 h2 (* h3 h3 h3
 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2512 h2 (* h3 h3 h3 h3) h4 h5 
(* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1648 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6 h6) 
(* j2 j2 j2 j2)) (* 536 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 
64 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2)) (* 48 h2 (* h3 h3 h3 h3) (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 392 h2 (* h3 h3 h3 h3) 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1328 h2 (* h3 h3 h3 h3) 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2412 h2 (* h3 h3 h3 h3) (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2524 h2 (* h3 h3 h3 h3) (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1508 h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2)) (* 468 h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 
j2)) (* 56 h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 48 h2 (* h3 
h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 392 h2 (* h3
 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1352 h2 (* h3 
h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2560 h2 (* h3 h3 
h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2880 h2 (* h3 h3 h3 h3) 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1928 h2 (* h3 h3 h3 h3) (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2)) (* 712 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2)) (* 112 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 24 
h2 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 108
 h2 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 172 
h2 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 114 h2 
(* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 28 h2 (* h3 h3 
h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 2 h2 (* h3 h3 h3) (* h4 h4 
h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 72 h2 (* h3 h3 h3) (* h4 h4 h4 h4) h5 h6 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 220 h2 (* h3 h3 h3) (* h4 h4 h4 h4) h5 h6 (* j2 
j2 j2 j2 j2 j2 j2)) (* 208 h2 (* h3 h3 h3) (* h4 h4 h4 h4) h5 h6 (* j2 j2 j2 j2 
j2 j2)) (* 68 h2 (* h3 h3 h3) (* h4 h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 8 h2 
(* h3 h3 h3) (* h4 h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 32 h2 (* h3 h3 h3) (* h4 
h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 72 h2 (* h3 h3 h3) (* h4 h4 h4 
h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 48 h2 (* h3 h3 h3) (* h4 h4 h4 h4) (* h6
 h6) (* j2 j2 j2 j2 j2)) (* 8 h2 (* h3 h3 h3) (* h4 h4 h4 h4) (* h6 h6) (* j2 j2
 j2 j2)) (* 48 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2
 j2 j2)) (* 264 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 560 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2
)) (* 572 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 
284 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 60 h2 (* h3
 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 4 h2 (* h3 h3 h3) (* h4 h4
 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 160 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6
 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 912 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1976 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2068 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 1104 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* 288 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) 
(* 28 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 280 h2 (* h3 h3
 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1084 h2 (* h3 h3 
h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1548 h2 (* h3 h3 h3) 
(* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1060 h2 (* h3 h3 h3) (* h4 
h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 364 h2 (* h3 h3 h3) (* h4 h4 h4) h5 
(* h6 h6) (* j2 j2 j2 j2)) (* 48 h2 (* h3 h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2
 j2 j2)) (* 64 h2 (* h3 h3 h3) (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2
)) (* 208 h2 (* h3 h3 h3) (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
240 h2 (* h3 h3 h3) (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 112 h2 (* 
h3 h3 h3) (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 16 h2 (* h3 h3 h3) (* h4
 h4 h4) (* h6 h6 h6) (* j2 j2 j2)) (* 24 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 
h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 156 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5
 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 400 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 
h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 512 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2)) (* 342 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2
 j2 j2 j2)) (* 115 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) 
(* 18 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* h2 (* h3 h3 h3)
 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 208 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1320 h2 (* h3 h3 h3) (* h4 h4) (* h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3344 h2 (* h3 h3 h3) (* h4 h4) (* h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 4308 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 2988 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2)) (* 1098 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 
j2 j2)) (* 196 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 13 h2 
(* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 272 h2 (* h3 h3 h3) (* h4 
h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1824 h2 (* h3 h3 h3) 
(* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4896 h2 (* h3 h3 
h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 6826 h2 (* h3 h3 
h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 5332 h2 (* h3 h3 h3)
 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2312 h2 (* h3 h3 h3) (* h4
 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 504 h2 (* h3 h3 h3) (* h4 h4) (* h5
 h5) (* h6 h6) (* j2 j2 j2)) (* 42 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6)
 (* j2 j2)) (* 280 h2 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 1356 h2 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 2580 h2 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2))
 (* 2508 h2 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1344 
h2 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 384 h2 (* h3 h3 h3
) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 44 h2 (* h3 h3 h3) (* h4 h4) h5 (* 
h6 h6 h6) (* j2 j2)) (* 32 h2 (* h3 h3 h3) (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2
 j2 j2 j2 j2)) (* 136 h2 (* h3 h3 h3) (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 224 h2 (* h3 h3 h3) (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
176 h2 (* h3 h3 h3) (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 64 h2 (* h3 h3
 h3) (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 8 h2 (* h3 h3 h3) (* h4 h4) (* 
h6 h6 h6 h6) (* j2 j2)) (* 48 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 360 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 1088 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2
 j2)) (* 1692 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
1428 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 628 h2 (* h3 
h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 124 h2 (* h3 h3 h3) h4 (* h5 h5
 h5 h5) h6 (* j2 j2 j2)) (* 8 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2)) 
(* 208 h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (* 1512 h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 4540 h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
7242 h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6556 h2
 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 3312 h2 (* h3 h3 
h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 834 h2 (* h3 h3 h3) h4 (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2)) (* 72 h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) 
(* j2 j2)) (* 160 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2 j2)) (* 1216 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 3816 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 6436 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2))
 (* 6318 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 3600 
h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1086 h2 (* h3 h3 
h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 128 h2 (* h3 h3 h3) h4 (* h5 h5) 
(* h6 h6 h6) (* j2 j2)) (* 72 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 428 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 1024 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
1256 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 824 h2 (* h3 
h3 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 268 h2 (* h3 h3 h3) h4 h5 (* h6
 h6 h6 h6) (* j2 j2 j2)) (* 32 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2)) 
(* 24 h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 196 h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 664 h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
1206 h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1262 h2
 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 754 h2 (* h3 h3 
h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 234 h2 (* h3 h3 h3) (* h5 h5 
h5 h5) (* h6 h6) (* j2 j2 j2)) (* 28 h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) 
(* j2 j2)) (* 48 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 392 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 1364 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 2634 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 3058 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2138 h2
 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 834 h2 (* h3 h3 h3) 
(* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 140 h2 (* h3 h3 h3) (* h5 h5 h5) (* 
h6 h6 h6) (* j2 j2)) (* 24 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2
 j2 j2 j2 j2 j2 j2)) (* 196 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 676 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2
 j2 j2 j2 j2)) (* 1280 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 1440 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 964 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 356 h2 (* 
h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 56 h2 (* h3 h3 h3) (* h5 h5
) (* h6 h6 h6 h6) (* j2 j2)) (* 12 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 54 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 86 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 
j2 j2 j2 j2 j2 j2)) (* 57 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 
j2 j2 j2)) (* 14 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) 
(* h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 24 h2 (* h3 h3)
 (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 128 h2 (* h3 h3
) (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 242 h2 (* h3 h3) 
(* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 202 h2 (* h3 h3) (* h4
 h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 76 h2 (* h3 h3) (* h4 h4 h4 h4
) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 9 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) 
h6 (* j2 j2 j2 j2)) (* 24 h2 (* h3 h3) (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 104 h2 (* h3 h3) (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2
 j2 j2 j2)) (* 150 h2 (* h3 h3) (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 86 h2 (* h3 h3) (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 16 
h2 (* h3 h3) (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 16 h2 (* h3 h3) 
(* h4 h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 20 h2 (* h3 h3) (* h4 h4 
h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 4 h2 (* h3 h3) (* h4 h4 h4 h4) (* h6 
h6 h6) (* j2 j2 j2 j2)) (* 12 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2
 j2 j2 j2 j2 j2 j2 j2)) (* 66 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2
 j2 j2 j2 j2 j2 j2)) (* 140 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 
j2 j2 j2 j2 j2)) (* 143 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2
 j2 j2)) (* 71 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 
15 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* h2 (* h3 h3) 
(* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 96 h2 (* h3 h3) (* h4 h4 h4) (* h5
 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 508 h2 (* h3 h3) (* h4 h4 h4) (* 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1034 h2 (* h3 h3) (* h4 h4 h4) (* 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1032 h2 (* h3 h3) (* h4 h4 h4) (* h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 538 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2)) (* 142 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2
 j2 j2)) (* 14 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 72 h2 
(* h3 h3) (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
480 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 1202 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 1478 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
965 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 316 h2 
(* h3 h3) (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 41 h2 (* h3 h3) 
(* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 48 h2 (* h3 h3) (* h4 h4 h4) 
h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 256 h2 (* h3 h3) (* h4 h4 h4) h5
 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 504 h2 (* h3 h3) (* h4 h4 h4) h5 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 454 h2 (* h3 h3) (* h4 h4 h4) h5 (* h6 h6 h6
) (* j2 j2 j2 j2 j2)) (* 186 h2 (* h3 h3) (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 
j2 j2)) (* 28 h2 (* h3 h3) (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 16 h2 
(* h3 h3) (* h4 h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 36 h2 (* h3 h3)
 (* h4 h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 24 h2 (* h3 h3) (* h4 h4 h4
) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 4 h2 (* h3 h3) (* h4 h4 h4) (* h6 h6 h6 h6
) (* j2 j2 j2)) (* 60 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 362 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2
 j2 j2 j2 j2)) (* 872 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2)) (* 1073 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2)) (* 717 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 256
 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 45 h2 (* h3 h3) 
(* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 3 h2 (* h3 h3) (* h4 h4) (* h5 h5 
h5 h5) h6 (* j2 j2)) (* 168 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 1048 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2652 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3519 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 2639 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6)
 (* j2 j2 j2 j2 j2)) (* 1118 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2
 j2 j2 j2)) (* 247 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) 
(* 21 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 72 h2 (* h3 h3
) (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 552 h2 (* 
h3 h3) (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1670 h2 
(* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2618 h2 
(* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2325 h2 (* 
h3 h3) (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1175 h2 (* h3 h3)
 (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 314 h2 (* h3 h3) (* h4 h4)
 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 36 h2 (* h3 h3) (* h4 h4) (* h5 h5) (* 
h6 h6 h6) (* j2 j2)) (* 24 h2 (* h3 h3) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 152 h2 (* h3 h3) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 378 h2 (* h3 h3) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2
 j2)) (* 468 h2 (* h3 h3) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
302 h2 (* h3 h3) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 96 h2 (* h3 h3
) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 12 h2 (* h3 h3) (* h4 h4) h5 (* 
h6 h6 h6 h6) (* j2 j2)) (* 60 h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2
 j2 j2 j2 j2 j2 j2 j2)) (* 418 h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 1198 h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 1820 h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 1568 h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 754 h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 182 h2
 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 16 h2 (* h3 h3) h4 (* 
h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 96 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 692 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2078 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3372 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 3192 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2)) (* 1760 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2))
 (* 522 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 64 h2 (* h3 
h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 24 h2 (* h3 h3) h4 (* h5 h5) (* 
h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 200 h2 (* h3 h3) h4 (* h5 h5) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 686 h2 (* h3 h3) h4 (* h5 h5) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1254 h2 (* h3 h3) h4 (* h5 h5) (* 
h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1318 h2 (* h3 h3) h4 (* h5 h5) (* h6 h6 
h6 h6) (* j2 j2 j2 j2 j2)) (* 794 h2 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6 h6) (* 
j2 j2 j2 j2)) (* 252 h2 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 
32 h2 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 12 h2 (* h3 h3) (* h5
 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 98 h2 (* h3 h3) (* h5
 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 338 h2 (* h3 h3) (* h5 
h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 640 h2 (* h3 h3) (* h5 h5 h5
 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 720 h2 (* h3 h3) (* h5 h5 h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 482 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2)) (* 178 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) 
(* 28 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 12 h2 (* h3 h3) 
(* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 98 h2 (* h3 h3) 
(* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 338 h2 (* h3 h3) 
(* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 640 h2 (* h3 h3) (* h5
 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 720 h2 (* h3 h3) (* h5 h5 h5) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 482 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6
 h6) (* j2 j2 j2 j2)) (* 178 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 
j2)) (* 28 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 8 h2 h3 (* h4
 h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 36 h2 h3 (* h4 h4 
h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 60 h2 h3 (* h4 h4 h4 h4) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 46 h2 h3 (* h4 h4 h4 h4) (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 16 h2 h3 (* h4 h4 h4 h4) (* h5 h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* 2 h2 h3 (* h4 h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 16 
h2 h3 (* h4 h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 60 h2 
h3 (* h4 h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 76 h2 h3 (* 
h4 h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 40 h2 h3 (* h4 h4 h4 
h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 8 h2 h3 (* h4 h4 h4 h4) (* h5 h5)
 (* h6 h6) (* j2 j2 j2 j2)) (* 8 h2 h3 (* h4 h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 22 h2 h3 (* h4 h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 15 h2 h3 (* h4 h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 4 h2 h3 
(* h4 h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 8 h2 h3 (* h4 h4 h4) (* h5 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 44 h2 h3 (* h4 h4 h4) (* h5 h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 96 h2 h3 (* h4 h4 h4) (* h5 h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 106 h2 h3 (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2)) (* 62 h2 h3 (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2))
 (* 18 h2 h3 (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 2 h2 h3 (* h4 
h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 24 h2 h3 (* h4 h4 h4) (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 140 h2 h3 (* h4 h4 h4) (* h5 h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 326 h2 h3 (* h4 h4 h4) (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 389 h2 h3 (* h4 h4 h4) (* h5 h5 h5) (* h6
 h6) (* j2 j2 j2 j2 j2 j2)) (* 252 h2 h3 (* h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2)) (* 85 h2 h3 (* h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)
) (* 12 h2 h3 (* h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 32 h2 h3 (* 
h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 152 h2 h3 (* h4
 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 268 h2 h3 (* h4 h4 
h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 222 h2 h3 (* h4 h4 h4) (* 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 88 h2 h3 (* h4 h4 h4) (* h5 h5) (* h6
 h6 h6) (* j2 j2 j2 j2)) (* 14 h2 h3 (* h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 
j2 j2)) (* 8 h2 h3 (* h4 h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
30 h2 h3 (* h4 h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 37 h2 h3 (* 
h4 h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 19 h2 h3 (* h4 h4 h4) h5 (* 
h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 4 h2 h3 (* h4 h4 h4) h5 (* h6 h6 h6 h6) (* j2 
j2 j2)) (* 16 h2 h3 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 104 h2 h3 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2
 j2)) (* 278 h2 h3 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2))
 (* 395 h2 h3 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 320 
h2 h3 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 146 h2 h3 (* h4
 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 34 h2 h3 (* h4 h4) (* h5 h5 
h5 h5) (* h6 h6) (* j2 j2 j2)) (* 3 h2 h3 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) 
(* j2 j2)) (* 24 h2 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 164 h2 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 462 h2 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 699 h2 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
616 h2 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 318 h2 h3 
(* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 90 h2 h3 (* h4 h4) (* h5
 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 11 h2 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6 
h6) (* j2 j2)) (* 16 h2 h3 (* h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 92 h2 h3 (* h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2
 j2)) (* 208 h2 h3 (* h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 238 h2 h3 (* h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 146 h2 
h3 (* h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 46 h2 h3 (* h4 h4) 
(* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 6 h2 h3 (* h4 h4) (* h5 h5) (* h6 h6 
h6 h6) (* j2 j2)) (* 8 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 60 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 188 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 320 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 320 h2 h3
 h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 188 h2 h3 h4 (* h5 h5 h5
 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 60 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6 h6) 
(* j2 j2 j2)) (* 8 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 8 h2 h3 
h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 60 h2 h3 h4 
(* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 188 h2 h3 h4 (* h5 
h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 320 h2 h3 h4 (* h5 h5 h5) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 320 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6 
h6) (* j2 j2 j2 j2 j2)) (* 188 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2
 j2)) (* 60 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 8 h2 h3 h4 
(* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 2 h2 (* h4 h4 h4 h4) (* h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 7 h2 (* h4 h4 h4 h4) (* h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 9 h2 (* h4 h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 5 h2 (* h4 h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2)) (* h2 (* h4 h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 2 h2 
(* h4 h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 5 h2 (* h4 
h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4 h2 (* h4 h4 h4 h4) 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* h2 (* h4 h4 h4 h4) (* h5 h5) (* h6
 h6 h6) (* j2 j2 j2 j2)) (* 2 h2 (* h4 h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2
 j2 j2 j2 j2 j2 j2)) (* 9 h2 (* h4 h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 16 h2 (* h4 h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 14 h2 (* h4 h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 6 h2
 (* h4 h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* h2 (* h4 h4 h4) (* 
h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 4 h2 (* h4 h4 h4) (* h5 h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 18 h2 (* h4 h4 h4) (* h5 h5 h5) (* h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2)) (* 32 h2 (* h4 h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2)) (* 28 h2 (* h4 h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2
 j2)) (* 12 h2 (* h4 h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 2 h2 
(* h4 h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 2 h2 (* h4 h4 h4) (* h5 
h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 7 h2 (* h4 h4 h4) (* h5 h5) (* 
h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 9 h2 (* h4 h4 h4) (* h5 h5) (* h6 h6 h6 
h6) (* j2 j2 j2 j2 j2)) (* 5 h2 (* h4 h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 
j2 j2)) (* h2 (* h4 h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 2 h2 (* h4
 h4) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 11 h2 (* h4 h4
) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 25 h2 (* h4 h4) (* 
h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 30 h2 (* h4 h4) (* h5 h5 h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 20 h2 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6
 h6) (* j2 j2 j2 j2)) (* 7 h2 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2
)) (* h2 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 2 h2 (* h4 h4) (* 
h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 11 h2 (* h4 h4) (* h5 
h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 25 h2 (* h4 h4) (* h5 h5 h5)
 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 30 h2 (* h4 h4) (* h5 h5 h5) (* h6 h6
 h6 h6) (* j2 j2 j2 j2 j2)) (* 20 h2 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6 h6) (* 
j2 j2 j2 j2)) (* 7 h2 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* h2
 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 16 (* h3 h3 h3 h3) (* h4 
h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 88 (* h3 h3 h3 h3) (* h4 
h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 184 (* h3 h3 h3 h3) (* h4 h4
 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 180 (* h3 h3 h3 h3) (* h4 h4 h4) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 80 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5)
 h6 (* j2 j2 j2 j2 j2)) (* 12 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2
 j2 j2)) (* 16 (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2
 j2)) (* 72 (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 120 (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 88 
(* h3 h3 h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 24 (* h3 h3 h3 
h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 16 (* h3 h3 h3 h3) (* h4 h4) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 104 (* h3 h3 h3 h3) (* h4 h4)
 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 264 (* h3 h3 h3 h3) (* h4 h4) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 328 (* h3 h3 h3 h3) (* h4 h4) (* h5
 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 204 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2)) (* 58 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 
j2 j2)) (* 6 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 32 (* h3
 h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 208 
(* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
544 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
728 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 520 
(* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 184 (* h3 
h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 24 (* h3 h3 h3 h3) 
(* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 16 (* h3 h3 h3 h3) (* h4 h4) h5 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 88 (* h3 h3 h3 h3) (* h4 h4) h5 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 192 (* h3 h3 h3 h3) (* h4 h4) h5 (* h6 h6
 h6) (* j2 j2 j2 j2 j2 j2)) (* 208 (* h3 h3 h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* 
j2 j2 j2 j2 j2)) (* 112 (* h3 h3 h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2
)) (* 24 (* h3 h3 h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 16 (* h3 h3 
h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 120 (* h3 h3
 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 360 (* h3 h3 
h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 548 (* h3 h3 h3 h3
) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 440 (* h3 h3 h3 h3) h4 (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 172 (* h3 h3 h3 h3) h4 (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2)) (* 24 (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2
 j2 j2)) (* 16 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2
 j2 j2)) (* 120 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 368 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2
)) (* 592 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
528 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 248 (* h3 
h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 48 (* h3 h3 h3 h3) h4 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 8 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5)
 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 36 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5)
 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 56 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) h6
 (* j2 j2 j2 j2 j2 j2 j2)) (* 34 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) h6 (* j2
 j2 j2 j2 j2 j2)) (* 6 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 
j2)) (* 8 (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2))
 (* 28 (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 32
 (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 12 (* h3 h3
 h3) (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 16 (* h3 h3 h3) (* h4 
h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 88 (* h3 h3 h3) (* h4 
h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 184 (* h3 h3 h3) (* h4 h4
 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 180 (* h3 h3 h3) (* h4 h4 h4) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 80 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2)) (* 12 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2
 j2 j2 j2)) (* 24 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 140 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 316 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 352 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 200 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2)) (* 48 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) 
(* 16 (* h3 h3 h3) (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
72 (* h3 h3 h3) (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 120 
(* h3 h3 h3) (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 88 (* h3 h3 
h3) (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 24 (* h3 h3 h3) (* h4 h4
 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 8 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5
) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 52 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5
) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 132 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 164 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 102 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2
 j2 j2 j2)) (* 29 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 
3 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 32 (* h3 h3 h3) (* 
h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 208 (* h3 h3 h3
) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 548 (* h3 h3 
h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 746 (* h3 h3 
h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 548 (* h3 h3 h3) 
(* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 201 (* h3 h3 h3) (* h4 
h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 27 (* h3 h3 h3) (* h4 h4) (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2)) (* 24 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 164 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 452 (* h3 h3 h3) (* h4 h4) (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 654 (* h3 h3 h3) (* h4 h4) (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 536 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 242 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2)) (* 48 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 
j2 j2)) (* 8 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 44 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 96 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 104 
(* h3 h3 h3) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 56 (* h3 h3 h3)
 (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 12 (* h3 h3 h3) (* h4 h4) h5 
(* h6 h6 h6 h6) (* j2 j2 j2)) (* 8 (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 60 (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 180 (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2
 j2 j2 j2 j2 j2 j2)) (* 274 (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 220 (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2
)) (* 86 (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 12 (* h3 
h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 16 (* h3 h3 h3) h4 (* h5 h5
 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 120 (* h3 h3 h3) h4 (* h5 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 372 (* h3 h3 h3) h4 (* h5 h5
 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 614 (* h3 h3 h3) h4 (* h5 h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 572 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6
 h6) (* j2 j2 j2 j2 j2)) (* 286 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2)) (* 60 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 8 
(* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 60 
(* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 184 
(* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 296 (* h3
 h3 h3) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 264 (* h3 h3 h3) 
h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 124 (* h3 h3 h3) h4 (* h5 h5
) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 24 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6 
h6) (* j2 j2 j2)) (* 4 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 18 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 28 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 17 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 3 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 8 (* h3 h3
) (* h4 h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 30 (* h3 
h3) (* h4 h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 37 (* h3 h3
) (* h4 h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 15 (* h3 h3) (* 
h4 h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 4 (* h3 h3) (* h4 h4 h4 
h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 10 (* h3 h3) (* h4 h4 h4 h4) h5
 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6 (* h3 h3) (* h4 h4 h4 h4) h5 (* h6 h6 
h6) (* j2 j2 j2 j2 j2)) (* 4 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 22 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 46 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2)) (* 45 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2)) (* 20 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 3 
(* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 12 (* h3 h3) (* h4
 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 70 (* h3 h3) 
(* h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 158 (* h3 h3
) (* h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 176 (* h3 h3)
 (* h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 100 (* h3 h3) (* 
h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 24 (* h3 h3) (* h4 h4 h4
) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 16 (* h3 h3) (* h4 h4 h4) (* h5 h5)
 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 76 (* h3 h3) (* h4 h4 h4) (* h5 h5
) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 132 (* h3 h3) (* h4 h4 h4) (* h5 h5)
 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 99 (* h3 h3) (* h4 h4 h4) (* h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 27 (* h3 h3) (* h4 h4 h4) (* h5 h5) (* h6 h6 h6
) (* j2 j2 j2 j2)) (* 4 (* h3 h3) (* h4 h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2
 j2 j2 j2)) (* 14 (* h3 h3) (* h4 h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2
)) (* 16 (* h3 h3) (* h4 h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 6 (* 
h3 h3) (* h4 h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 8 (* h3 h3) (* h4 h4)
 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 52 (* h3 h3) (* h4
 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 136 (* h3 h3) (* 
h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 182 (* h3 h3) (* 
h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 130 (* h3 h3) (* h4 
h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 46 (* h3 h3) (* h4 h4) (* 
h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 6 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5)
 (* h6 h6) (* j2 j2 j2)) (* 12 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 82 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 226 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 327 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 268 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2)) (* 121 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2)) (* 24 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 
8 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
46 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
103 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 112 
(* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 59 (* h3 h3
) (* h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 12 (* h3 h3) (* h4 h4)
 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 4 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6
 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 30 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6
 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 92 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6
 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 148 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 132 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2
 j2 j2 j2)) (* 62 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 
12 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 4 (* h3 h3) h4 (* 
h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 30 (* h3 h3) h4 (* 
h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 92 (* h3 h3) h4 (* h5 
h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 148 (* h3 h3) h4 (* h5 h5 h5
) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 132 (* h3 h3) h4 (* h5 h5 h5) (* h6 
h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 62 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6 h6) 
(* j2 j2 j2 j2)) (* 12 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) 
(* 2 h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 7
 h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 8 h3 (* 
h4 h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3 h3 (* h4 h4 h4 
h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2 h3 (* h4 h4 h4 h4) (* h5 h5)
 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 5 h3 (* h4 h4 h4 h4) (* h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3 h3 (* h4 h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2)) (* 2 h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 9 h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 15 h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 11 h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 3 h3 (* 
h4 h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 4 h3 (* h4 h4 h4) (* h5 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 18 h3 (* h4 h4 h4) (* h5 h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 30 h3 (* h4 h4 h4) (* h5 h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 22 h3 (* h4 h4 h4) (* h5 h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2)) (* 6 h3 (* h4 h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2)) (* 2 h3 (* h4 h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2))
 (* 7 h3 (* h4 h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 8 h3 
(* h4 h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 3 h3 (* h4 h4 h4) 
(* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 2 h3 (* h4 h4) (* h5 h5 h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 11 h3 (* h4 h4) (* h5 h5 h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 24 h3 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2)) (* 26 h3 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2
 j2 j2 j2)) (* 14 h3 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 
3 h3 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 2 h3 (* h4 h4) (* 
h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 11 h3 (* h4 h4) (* h5 
h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 24 h3 (* h4 h4) (* h5 h5 h5)
 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 26 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6
 h6 h6) (* j2 j2 j2 j2 j2)) (* 14 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6 h6) (* 
j2 j2 j2 j2)) (* 3 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2))) 0)))
(check-sat)
(exit)

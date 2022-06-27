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
(set-info :instance |E8E25|)
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
(+ (* 40 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2 j2 j2)) (* 536
 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2 j2)) (* 2568 (* h1 h1 
h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2)) (* 5384 (* h1 h1 h1 h1) (* h2 
h2 h2) (* h3 h3) h5 (* j2 j2 j2)) (* 5136 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3)
 h5 (* j2 j2)) (* 2144 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 j2) (* 320 (* 
h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5) (* 16 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3
 h3) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 232 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) 
h6 (* j2 j2 j2 j2 j2 j2)) (* 1264 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h6 (* 
j2 j2 j2 j2 j2)) (* 3296 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h6 (* j2 j2 j2 
j2)) (* 4480 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h6 (* j2 j2 j2)) (* 3224 (* 
h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h6 (* j2 j2)) (* 1152 (* h1 h1 h1 h1) (* h2 
h2 h2) (* h3 h3) h6 j2) (* 160 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h6) (* 40 
(* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 456 (* h1 h1
 h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 1896 (* h1 h1 h1 h1) 
(* h2 h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2)) (* 3768 (* h1 h1 h1 h1) (* h2 h2 h2) 
h3 (* h5 h5) (* j2 j2 j2)) (* 3792 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* 
j2 j2)) (* 1824 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) j2) (* 320 (* h1 h1 h1
 h1) (* h2 h2 h2) h3 (* h5 h5)) (* 24 (* h1 h1 h1 h1) (* h2 h2 h2) h3 h5 h6 (* 
j2 j2 j2 j2 j2 j2 j2)) (* 328 (* h1 h1 h1 h1) (* h2 h2 h2) h3 h5 h6 (* j2 j2 j2 
j2 j2 j2)) (* 1720 (* h1 h1 h1 h1) (* h2 h2 h2) h3 h5 h6 (* j2 j2 j2 j2 j2)) (* 
4488 (* h1 h1 h1 h1) (* h2 h2 h2) h3 h5 h6 (* j2 j2 j2 j2)) (* 6352 (* h1 h1 h1 
h1) (* h2 h2 h2) h3 h5 h6 (* j2 j2 j2)) (* 4944 (* h1 h1 h1 h1) (* h2 h2 h2) h3 
h5 h6 (* j2 j2)) (* 1984 (* h1 h1 h1 h1) (* h2 h2 h2) h3 h5 h6 j2) (* 320 (* h1 
h1 h1 h1) (* h2 h2 h2) h3 h5 h6) (* 16 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2)) (* 184 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 792 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6) (* j2 j2 j2
 j2 j2)) (* 1728 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6) (* j2 j2 j2 j2)) (* 
2112 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6) (* j2 j2 j2)) (* 1464 (* h1 h1 h1
 h1) (* h2 h2 h2) h3 (* h6 h6) (* j2 j2)) (* 536 (* h1 h1 h1 h1) (* h2 h2 h2) h3
 (* h6 h6) j2) (* 80 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6)) (* 8 (* h1 h1 h1
 h1) (* h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 112 (* h1 h1 h1 h1) 
(* h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 624 (* h1 h1 h1 h1) (* h2 h2
 h2) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 1824 (* h1 h1 h1 h1) (* h2 h2 h2) (* h5
 h5) h6 (* j2 j2 j2 j2)) (* 3048 (* h1 h1 h1 h1) (* h2 h2 h2) (* h5 h5) h6 (* j2
 j2 j2)) (* 2928 (* h1 h1 h1 h1) (* h2 h2 h2) (* h5 h5) h6 (* j2 j2)) (* 1504 
(* h1 h1 h1 h1) (* h2 h2 h2) (* h5 h5) h6 j2) (* 320 (* h1 h1 h1 h1) (* h2 h2 h2
) (* h5 h5) h6) (* 8 (* h1 h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2)) (* 104 (* h1 h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2))
 (* 528 (* h1 h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1392 
(* h1 h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 2088 (* h1 h1 h1 
h1) (* h2 h2 h2) h5 (* h6 h6) (* j2 j2 j2)) (* 1800 (* h1 h1 h1 h1) (* h2 h2 h2)
 h5 (* h6 h6) (* j2 j2)) (* 832 (* h1 h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6) j2) 
(* 160 (* h1 h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6)) (* 20 (* h1 h1 h1 h1) (* h2 h2
) (* h3 h3 h3) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 468 (* h1 h1 h1 h1) (* h2 h2) (* 
h3 h3 h3) h5 (* j2 j2 j2 j2 j2 j2)) (* 3664 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 
h3) h5 (* j2 j2 j2 j2 j2)) (* 12112 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 
(* j2 j2 j2 j2)) (* 17068 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2)
) (* 11212 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* j2 j2)) (* 3440 (* h1 h1
 h1 h1) (* h2 h2) (* h3 h3 h3) h5 j2) (* 400 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 
h3) h5) (* 8 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 196 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 1672 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2 j2 j2 j2)) (* 6468
 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2 j2 j2)) (* 12240 (* h1 h1
 h1 h1) (* h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2 j2)) (* 12252 (* h1 h1 h1 h1) (* 
h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2)) (* 6616 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 
h3) h6 (* j2 j2)) (* 1820 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h6 j2) (* 200 
(* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h6) (* 20 (* h1 h1 h1 h1) (* h2 h2) (* h3
 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 488 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) 
h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 3672 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 
(* j2 j2 j2 j2 j2)) (* 11712 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* j2 j2 
j2 j2)) (* 17748 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2)) (* 
13368 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* j2 j2)) (* 4768 (* h1 h1 h1 
h1) (* h2 h2) (* h3 h3) h4 h5 j2) (* 640 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 
h5) (* 80 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 936 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2)) (* 4032 
(* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 8448 (* h1 h1 
h1 h1) (* h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 9552 (* h1 h1 h1 h1) (* h2 
h2) (* h3 h3) h4 h6 (* j2 j2 j2)) (* 5928 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4
 h6 (* j2 j2)) (* 1888 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h6 j2) (* 240 (* 
h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h6) (* 40 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3
) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 876 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3)
 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 5884 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) 
(* h5 h5) (* j2 j2 j2 j2 j2)) (* 16356 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h5
 h5) (* j2 j2 j2 j2)) (* 21996 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* 
j2 j2 j2)) (* 15056 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* j2 j2)) (* 
5008 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) j2) (* 640 (* h1 h1 h1 h1) 
(* h2 h2) (* h3 h3) (* h5 h5)) (* 20 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h5 h6 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 512 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h5 h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 4196 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h5 h6 (* 
j2 j2 j2 j2 j2 j2)) (* 15712 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h5 h6 (* j2 j2 
j2 j2 j2)) (* 31372 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2)) 
(* 35168 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2)) (* 21900 (* h1 
h1 h1 h1) (* h2 h2) (* h3 h3) h5 h6 (* j2 j2)) (* 6976 (* h1 h1 h1 h1) (* h2 h2)
 (* h3 h3) h5 h6 j2) (* 880 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h5 h6) (* 16 (* 
h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 320 
(* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2292 
(* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 7772 (* 
h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 14168 (* h1 h1
 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 14648 (* h1 h1 h1 h1) 
(* h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2)) (* 8548 (* h1 h1 h1 h1) (* h2 h2) 
(* h3 h3) (* h6 h6) (* j2 j2)) (* 2604 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h6
 h6) j2) (* 320 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6)) (* 20 (* h1 h1 h1
 h1) (* h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 368 (* h1 h1 h1 h1) 
(* h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2404 (* h1 h1 h1 h1) (* h2 
h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 7204 (* h1 h1 h1 h1) (* h2 h2) h3 h4 
(* h5 h5) (* j2 j2 j2 j2)) (* 11080 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) 
(* j2 j2 j2)) (* 9004 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* j2 j2)) (* 
3632 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) j2) (* 560 (* h1 h1 h1 h1) (* h2 
h2) h3 h4 (* h5 h5)) (* 108 (* h1 h1 h1 h1) (* h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2
 j2 j2 j2)) (* 1240 (* h1 h1 h1 h1) (* h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2 j2 j2))
 (* 5264 (* h1 h1 h1 h1) (* h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 11072 (* 
h1 h1 h1 h1) (* h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2)) (* 12812 (* h1 h1 h1 h1) (* 
h2 h2) h3 h4 h5 h6 (* j2 j2 j2)) (* 8312 (* h1 h1 h1 h1) (* h2 h2) h3 h4 h5 h6 
(* j2 j2)) (* 2840 (* h1 h1 h1 h1) (* h2 h2) h3 h4 h5 h6 j2) (* 400 (* h1 h1 h1 
h1) (* h2 h2) h3 h4 h5 h6) (* 24 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6) (* j2
 j2 j2 j2 j2 j2 j2)) (* 252 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 960 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2 j2 j2
)) (* 1860 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2 j2)) (* 2040 
(* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2)) (* 1284 (* h1 h1 h1 h1) 
(* h2 h2) h3 h4 (* h6 h6) (* j2 j2)) (* 432 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* 
h6 h6) j2) (* 60 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6)) (* 20 (* h1 h1 h1 h1
) (* h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 308 (* h1 h1 h1 h1) (* 
h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1780 (* h1 h1 h1 h1) (* h2 h2) 
h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 4924 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 
h5 h5) (* j2 j2 j2 j2)) (* 7144 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* j2 
j2 j2)) (* 5536 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* j2 j2)) (* 2144 (* 
h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) j2) (* 320 (* h1 h1 h1 h1) (* h2 h2) h3 
(* h5 h5 h5)) (* 16 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 368 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2
 j2)) (* 2944 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 11132 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 22692 
(* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 26436 (* h1 h1 h1 
h1) (* h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2)) (* 17580 (* h1 h1 h1 h1) (* h2 h2) 
h3 (* h5 h5) h6 (* j2 j2)) (* 6176 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5) h6 j2)
 (* 880 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5) h6) (* 24 (* h1 h1 h1 h1) (* h2 
h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 440 (* h1 h1 h1 h1) (* h2 h2
) h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3016 (* h1 h1 h1 h1) (* h2 h2) h3
 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 10092 (* h1 h1 h1 h1) (* h2 h2) h3 h5 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 18544 (* h1 h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6)
 (* j2 j2 j2 j2)) (* 19664 (* h1 h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2
)) (* 11976 (* h1 h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6) (* j2 j2)) (* 3884 (* h1 
h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6) j2) (* 520 (* h1 h1 h1 h1) (* h2 h2) h3 h5 
(* h6 h6)) (* 8 (* h1 h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 116 (* h1 h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2
)) (* 656 (* h1 h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
1900 (* h1 h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 3160 (* h1
 h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 3148 (* h1 h1 h1 h1) 
(* h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2)) (* 1856 (* h1 h1 h1 h1) (* h2 h2) h3 (* 
h6 h6 h6) (* j2 j2)) (* 596 (* h1 h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6) j2) (* 80 
(* h1 h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6)) (* 24 (* h1 h1 h1 h1) (* h2 h2) h4 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 308 (* h1 h1 h1 h1) (* h2 h2) h4 (* h5
 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 1536 (* h1 h1 h1 h1) (* h2 h2) h4 (* h5 h5) h6
 (* j2 j2 j2 j2 j2)) (* 3960 (* h1 h1 h1 h1) (* h2 h2) h4 (* h5 h5) h6 (* j2 j2 
j2 j2)) (* 5784 (* h1 h1 h1 h1) (* h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 4836 
(* h1 h1 h1 h1) (* h2 h2) h4 (* h5 h5) h6 (* j2 j2)) (* 2160 (* h1 h1 h1 h1) (* 
h2 h2) h4 (* h5 h5) h6 j2) (* 400 (* h1 h1 h1 h1) (* h2 h2) h4 (* h5 h5) h6) (* 
12 (* h1 h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 144 
(* h1 h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 660 (* h1 h1
 h1 h1) (* h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1560 (* h1 h1 h1 h1) 
(* h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 2100 (* h1 h1 h1 h1) (* h2 h2) h4 
h5 (* h6 h6) (* j2 j2 j2)) (* 1632 (* h1 h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6) (* 
j2 j2)) (* 684 (* h1 h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6) j2) (* 120 (* h1 h1 h1 
h1) (* h2 h2) h4 h5 (* h6 h6)) (* 4 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 72 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2)) (* 520 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5 h5) h6 (* j2 j2
 j2 j2 j2 j2)) (* 1968 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2)) (* 4308 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 5640 
(* h1 h1 h1 h1) (* h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 4352 (* h1 h1 h1 h1) 
(* h2 h2) (* h5 h5 h5) h6 (* j2 j2)) (* 1824 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5 
h5) h6 j2) (* 320 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5 h5) h6) (* 8 (* h1 h1 h1 h1
) (* h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 136 (* h1 h1 h1 
h1) (* h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 924 (* h1 h1 h1 
h1) (* h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3280 (* h1 h1 h1 h1)
 (* h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 6736 (* h1 h1 h1 h1) (* h2
 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 8296 (* h1 h1 h1 h1) (* h2 h2) (* 
h5 h5) (* h6 h6) (* j2 j2 j2)) (* 6044 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5) (* h6
 h6) (* j2 j2)) (* 2400 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6) j2) (* 400
 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6)) (* 4 (* h1 h1 h1 h1) (* h2 h2) 
h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 64 (* h1 h1 h1 h1) (* h2 h2) h5 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 412 (* h1 h1 h1 h1) (* h2 h2) h5 (* h6
 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1400 (* h1 h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6)
 (* j2 j2 j2 j2 j2)) (* 2780 (* h1 h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6) (* j2 j2 
j2 j2)) (* 3344 (* h1 h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 2404 
(* h1 h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6) (* j2 j2)) (* 952 (* h1 h1 h1 h1) (* 
h2 h2) h5 (* h6 h6 h6) j2) (* 160 (* h1 h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6)) (* 
10 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 314 (* 
h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 3454 (* h1 h1 h1
 h1) h2 (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 16002 (* h1 h1 h1 h1) h2 
(* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 32658 (* h1 h1 h1 h1) h2 (* h3 h3 h3) 
h4 h5 (* j2 j2 j2 j2)) (* 33366 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h5 (* j2 j2 
j2)) (* 17810 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h5 (* j2 j2)) (* 4750 (* h1 h1 
h1 h1) h2 (* h3 h3 h3) h4 h5 j2) (* 500 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h5) 
(* 28 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 586 
(* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 3858 (* h1 h1
 h1 h1) h2 (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2)) (* 10830 (* h1 h1 h1 h1) h2
 (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 15822 (* h1 h1 h1 h1) h2 (* h3 h3 h3)
 h4 h6 (* j2 j2 j2 j2)) (* 13014 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h6 (* j2 j2 
j2)) (* 6062 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h6 (* j2 j2)) (* 1490 (* h1 h1 
h1 h1) h2 (* h3 h3 h3) h4 h6 j2) (* 150 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h6) 
(* 100 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
1980 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 11536 
(* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 25504 (* h1 h1 
h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 26860 (* h1 h1 h1 h1) h2 
(* h3 h3 h3) (* h5 h5) (* j2 j2 j2)) (* 14452 (* h1 h1 h1 h1) h2 (* h3 h3 h3) 
(* h5 h5) (* j2 j2)) (* 3840 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) j2) (* 
400 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5)) (* 70 (* h1 h1 h1 h1) h2 (* h3 h3
 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1498 (* h1 h1 h1 h1) h2 (* h3 h3 h3) 
h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 10298 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h5 h6 
(* j2 j2 j2 j2 j2 j2)) (* 30874 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h5 h6 (* j2 j2 
j2 j2 j2)) (* 47926 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 
41302 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h5 h6 (* j2 j2 j2)) (* 19830 (* h1 h1 h1 
h1) h2 (* h3 h3 h3) h5 h6 (* j2 j2)) (* 4950 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h5 
h6 j2) (* 500 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h5 h6) (* 8 (* h1 h1 h1 h1) h2 (* 
h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 204 (* h1 h1 h1 h1) h2 
(* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1868 (* h1 h1 h1 h1) h2 
(* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 8140 (* h1 h1 h1 h1) h2 (* 
h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 18708 (* h1 h1 h1 h1) h2 (* h3 h3 
h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 24492 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h6
 h6) (* j2 j2 j2 j2)) (* 18868 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6) (* j2 
j2 j2)) (* 8436 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6) (* j2 j2)) (* 2020 (* 
h1 h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6) j2) (* 200 (* h1 h1 h1 h1) h2 (* h3 h3 h3
) (* h6 h6)) (* 100 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 
j2 j2)) (* 1370 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2))
 (* 6782 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 15320 
(* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 17888 (* h1 h1 h1 
h1) h2 (* h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 11114 (* h1 h1 h1 h1) h2 (* h3 h3
) (* h4 h4) h5 (* j2 j2)) (* 3454 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 j2) 
(* 420 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5) (* 84 (* h1 h1 h1 h1) h2 (* h3
 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 834 (* h1 h1 h1 h1) h2 (* h3 h3) 
(* h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 2904 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 
h4) h6 (* j2 j2 j2 j2 j2)) (* 5046 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h6 (* 
j2 j2 j2 j2)) (* 4884 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h6 (* j2 j2 j2)) 
(* 2670 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h6 (* j2 j2)) (* 768 (* h1 h1 h1 
h1) h2 (* h3 h3) (* h4 h4) h6 j2) (* 90 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) 
h6) (* 20 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2))
 (* 508 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
4560 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 18704 
(* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 37724 (* h1 h1 
h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 40436 (* h1 h1 h1 h1) h2 
(* h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 23424 (* h1 h1 h1 h1) h2 (* h3 h3) h4 
(* h5 h5) (* j2 j2)) (* 6880 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) j2) (* 
800 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5)) (* 54 (* h1 h1 h1 h1) h2 (* h3 h3
) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1476 (* h1 h1 h1 h1) h2 (* h3 h3) h4 
h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 11536 (* h1 h1 h1 h1) h2 (* h3 h3) h4 h5 h6 
(* j2 j2 j2 j2 j2 j2)) (* 38682 (* h1 h1 h1 h1) h2 (* h3 h3) h4 h5 h6 (* j2 j2 
j2 j2 j2)) (* 67674 (* h1 h1 h1 h1) h2 (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 
66504 (* h1 h1 h1 h1) h2 (* h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 36732 (* h1 h1 h1 
h1) h2 (* h3 h3) h4 h5 h6 (* j2 j2)) (* 10554 (* h1 h1 h1 h1) h2 (* h3 h3) h4 h5
 h6 j2) (* 1220 (* h1 h1 h1 h1) h2 (* h3 h3) h4 h5 h6) (* 52 (* h1 h1 h1 h1) h2 
(* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 738 (* h1 h1 h1 h1) h2 
(* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4000 (* h1 h1 h1 h1) h2 (* 
h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 10798 (* h1 h1 h1 h1) h2 (* h3 h3)
 h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 16372 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h6
 h6) (* j2 j2 j2 j2)) (* 14590 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6) (* j2 
j2 j2)) (* 7560 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6) (* j2 j2)) (* 2098 (* 
h1 h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6) j2) (* 240 (* h1 h1 h1 h1) h2 (* h3 h3) 
h4 (* h6 h6)) (* 100 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2
 j2 j2)) (* 1380 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)
) (* 6756 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 14668
 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 16232 (* h1 h1 h1
 h1) h2 (* h3 h3) (* h5 h5 h5) (* j2 j2 j2)) (* 9504 (* h1 h1 h1 h1) h2 (* h3 h3
) (* h5 h5 h5) (* j2 j2)) (* 2784 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) j2) 
(* 320 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5)) (* 110 (* h1 h1 h1 h1) h2 (* 
h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2074 (* h1 h1 h1 h1) h2 (* 
h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 13672 (* h1 h1 h1 h1) h2 (* h3 
h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 41544 (* h1 h1 h1 h1) h2 (* h3 h3) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 67770 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5)
 h6 (* j2 j2 j2 j2)) (* 63054 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5) h6 (* j2 j2
 j2)) (* 33328 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5) h6 (* j2 j2)) (* 9248 (* 
h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5) h6 j2) (* 1040 (* h1 h1 h1 h1) h2 (* h3 h3) 
(* h5 h5) h6) (* 16 (* h1 h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 410 (* h1 h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 3936 (* h1 h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 18446 (* h1 h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)
) (* 46496 (* h1 h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
67654 (* h1 h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 58448 (* h1 
h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 29442 (* h1 h1 h1 h1) h2 
(* h3 h3) h5 (* h6 h6) (* j2 j2)) (* 7936 (* h1 h1 h1 h1) h2 (* h3 h3) h5 (* h6 
h6) j2) (* 880 (* h1 h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6)) (* 8 (* h1 h1 h1 h1) 
h2 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 148 (* h1 h1 h1 h1)
 h2 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1104 (* h1 h1 h1 h1) 
h2 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4308 (* h1 h1 h1 h1) h2 
(* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 9664 (* h1 h1 h1 h1) h2 (* h3 
h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 13084 (* h1 h1 h1 h1) h2 (* h3 h3) (* h6
 h6 h6) (* j2 j2 j2 j2)) (* 10832 (* h1 h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6) (* 
j2 j2 j2)) (* 5340 (* h1 h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6) (* j2 j2)) (* 1432 
(* h1 h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6) j2) (* 160 (* h1 h1 h1 h1) h2 (* h3 h3
) (* h6 h6 h6)) (* 60 (* h1 h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 
j2 j2 j2)) (* 764 (* h1 h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2
)) (* 3616 (* h1 h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 8248
 (* h1 h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 10108 (* h1 h1 h1
 h1) h2 h3 (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 6796 (* h1 h1 h1 h1) h2 h3 (* h4
 h4) (* h5 h5) (* j2 j2)) (* 2344 (* h1 h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) j2) 
(* 320 (* h1 h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5)) (* 108 (* h1 h1 h1 h1) h2 h3 
(* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1068 (* h1 h1 h1 h1) h2 h3 (* h4 h4
) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 3696 (* h1 h1 h1 h1) h2 h3 (* h4 h4) h5 h6 (* 
j2 j2 j2 j2 j2)) (* 6384 (* h1 h1 h1 h1) h2 h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2)) 
(* 6156 (* h1 h1 h1 h1) h2 h3 (* h4 h4) h5 h6 (* j2 j2 j2)) (* 3372 (* h1 h1 h1 
h1) h2 h3 (* h4 h4) h5 h6 (* j2 j2)) (* 984 (* h1 h1 h1 h1) h2 h3 (* h4 h4) h5 
h6 j2) (* 120 (* h1 h1 h1 h1) h2 h3 (* h4 h4) h5 h6) (* 10 (* h1 h1 h1 h1) h2 h3
 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 194 (* h1 h1 h1 h1) h2 h3 h4 
(* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1466 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5
 h5) (* j2 j2 j2 j2 j2 j2)) (* 5486 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5 h5) (* j2 
j2 j2 j2 j2)) (* 10932 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2)) 
(* 12184 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5 h5) (* j2 j2 j2)) (* 7600 (* h1 h1 h1
 h1) h2 h3 h4 (* h5 h5 h5) (* j2 j2)) (* 2464 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5 
h5) j2) (* 320 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5 h5)) (* 42 (* h1 h1 h1 h1) h2 
h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 872 (* h1 h1 h1 h1) h2 h3 h4 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 6318 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5
) h6 (* j2 j2 j2 j2 j2 j2)) (* 21472 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5) h6 (* j2
 j2 j2 j2 j2)) (* 39614 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2)) 
(* 42072 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5) h6 (* j2 j2 j2)) (* 25618 (* h1 h1 
h1 h1) h2 h3 h4 (* h5 h5) h6 (* j2 j2)) (* 8256 (* h1 h1 h1 h1) h2 h3 h4 (* h5 
h5) h6 j2) (* 1080 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5) h6) (* 60 (* h1 h1 h1 h1) 
h2 h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 908 (* h1 h1 h1 h1) h2 h3 
h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 5188 (* h1 h1 h1 h1) h2 h3 h4 h5 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 14532 (* h1 h1 h1 h1) h2 h3 h4 h5 (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* 22708 (* h1 h1 h1 h1) h2 h3 h4 h5 (* h6 h6) (* j2 j2 j2 
j2)) (* 20852 (* h1 h1 h1 h1) h2 h3 h4 h5 (* h6 h6) (* j2 j2 j2)) (* 11196 (* h1
 h1 h1 h1) h2 h3 h4 h5 (* h6 h6) (* j2 j2)) (* 3260 (* h1 h1 h1 h1) h2 h3 h4 h5 
(* h6 h6) j2) (* 400 (* h1 h1 h1 h1) h2 h3 h4 h5 (* h6 h6)) (* 40 (* h1 h1 h1 h1
) h2 h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 656 (* h1 h1 h1 h1) h2 
h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 4176 (* h1 h1 h1 h1) h2 h3 (* h5
 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 13408 (* h1 h1 h1 h1) h2 h3 (* h5 h5 h5) h6
 (* j2 j2 j2 j2 j2)) (* 24136 (* h1 h1 h1 h1) h2 h3 (* h5 h5 h5) h6 (* j2 j2 j2 
j2)) (* 25360 (* h1 h1 h1 h1) h2 h3 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 15360 (* h1
 h1 h1 h1) h2 h3 (* h5 h5 h5) h6 (* j2 j2)) (* 4928 (* h1 h1 h1 h1) h2 h3 (* h5 
h5 h5) h6 j2) (* 640 (* h1 h1 h1 h1) h2 h3 (* h5 h5 h5) h6) (* 10 (* h1 h1 h1 h1
) h2 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 252 (* h1 h1 h1 
h1) h2 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2394 (* h1 h1 h1 
h1) h2 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 11320 (* h1 h1 h1 h1)
 h2 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 29614 (* h1 h1 h1 h1) h2 h3
 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 45708 (* h1 h1 h1 h1) h2 h3 (* h5 h5
) (* h6 h6) (* j2 j2 j2 j2)) (* 42622 (* h1 h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6) 
(* j2 j2 j2)) (* 23536 (* h1 h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6) (* j2 j2)) (* 
7056 (* h1 h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6) j2) (* 880 (* h1 h1 h1 h1) h2 h3 
(* h5 h5) (* h6 h6)) (* 8 (* h1 h1 h1 h1) h2 h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 168 (* h1 h1 h1 h1) h2 h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 1388 (* h1 h1 h1 h1) h2 h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2
)) (* 5868 (* h1 h1 h1 h1) h2 h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 14016
 (* h1 h1 h1 h1) h2 h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 20032 (* h1 h1 h1 
h1) h2 h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 17484 (* h1 h1 h1 h1) h2 h3 h5 (* 
h6 h6 h6) (* j2 j2 j2)) (* 9132 (* h1 h1 h1 h1) h2 h3 h5 (* h6 h6 h6) (* j2 j2))
 (* 2624 (* h1 h1 h1 h1) h2 h3 h5 (* h6 h6 h6) j2) (* 320 (* h1 h1 h1 h1) h2 h3 
h5 (* h6 h6 h6)) (* 18 (* h1 h1 h1 h1) h2 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2)) (* 210 (* h1 h1 h1 h1) h2 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2
)) (* 924 (* h1 h1 h1 h1) h2 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 2076 
(* h1 h1 h1 h1) h2 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 2634 (* h1 h1 h1 
h1) h2 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 1914 (* h1 h1 h1 h1) h2 (* h4 h4)
 (* h5 h5) h6 (* j2 j2)) (* 744 (* h1 h1 h1 h1) h2 (* h4 h4) (* h5 h5) h6 j2) 
(* 120 (* h1 h1 h1 h1) h2 (* h4 h4) (* h5 h5) h6) (* 6 (* h1 h1 h1 h1) h2 h4 (* 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 100 (* h1 h1 h1 h1) h2 h4 (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 652 (* h1 h1 h1 h1) h2 h4 (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 2168 (* h1 h1 h1 h1) h2 h4 (* h5 h5 h5) h6 (* j2 j2 j2
 j2 j2)) (* 4094 (* h1 h1 h1 h1) h2 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 4580 
(* h1 h1 h1 h1) h2 h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 3008 (* h1 h1 h1 h1) h2 
h4 (* h5 h5 h5) h6 (* j2 j2)) (* 1072 (* h1 h1 h1 h1) h2 h4 (* h5 h5 h5) h6 j2) 
(* 160 (* h1 h1 h1 h1) h2 h4 (* h5 h5 h5) h6) (* 12 (* h1 h1 h1 h1) h2 h4 (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 196 (* h1 h1 h1 h1) h2 h4 (* h5 h5
) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1272 (* h1 h1 h1 h1) h2 h4 (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4288 (* h1 h1 h1 h1) h2 h4 (* h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2)) (* 8332 (* h1 h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6) (* j2 
j2 j2 j2)) (* 9700 (* h1 h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 
6688 (* h1 h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 2520 (* h1 h1 h1 h1
) h2 h4 (* h5 h5) (* h6 h6) j2) (* 400 (* h1 h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6)
) (* 2 (* h1 h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (* 44 (* h1 h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 396 (* h1 h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
1896 (* h1 h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 5306 
(* h1 h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 9068 (* h1 h1 
h1 h1) h2 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 9576 (* h1 h1 h1 h1) h2 (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 6096 (* h1 h1 h1 h1) h2 (* h5 h5 h5) (* h6 
h6) (* j2 j2)) (* 2144 (* h1 h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6) j2) (* 320 (* 
h1 h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6)) (* 2 (* h1 h1 h1 h1) h2 (* h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 42 (* h1 h1 h1 h1) h2 (* h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 364 (* h1 h1 h1 h1) h2 (* h5 h5) (* h6 h6
 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1700 (* h1 h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2)) (* 4714 (* h1 h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2)) (* 8098 (* h1 h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2))
 (* 8696 (* h1 h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 5680 (* h1 
h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 2064 (* h1 h1 h1 h1) h2 (* h5 
h5) (* h6 h6 h6) j2) (* 320 (* h1 h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6)) (* 35 (* 
h1 h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 729 (* h1
 h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 4751 (* h1 h1 
h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 13091 (* h1 h1 h1 h1)
 (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 18647 (* h1 h1 h1 h1) (* h3 h3
 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 14855 (* h1 h1 h1 h1) (* h3 h3 h3) (* h4 
h4) h5 (* j2 j2 j2)) (* 6657 (* h1 h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2)
) (* 1565 (* h1 h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 j2) (* 150 (* h1 h1 h1 h1) 
(* h3 h3 h3) (* h4 h4) h5) (* 50 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 1040 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* j2 
j2 j2 j2 j2 j2 j2)) (* 6758 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 
j2 j2 j2 j2)) (* 18520 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 
j2)) (* 26182 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 
20656 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 9146 (* h1 h1 
h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2)) (* 2120 (* h1 h1 h1 h1) (* h3 h3 h3)
 h4 (* h5 h5) j2) (* 200 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5)) (* 10 (* h1 
h1 h1 h1) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 324 (* h1 h1 
h1 h1) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3768 (* h1 h1 h1 h1
) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 19456 (* h1 h1 h1 h1) (* h3
 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 48660 (* h1 h1 h1 h1) (* h3 h3 h3) h4
 h5 h6 (* j2 j2 j2 j2 j2)) (* 66024 (* h1 h1 h1 h1) (* h3 h3 h3) h4 h5 h6 (* j2 
j2 j2 j2)) (* 51176 (* h1 h1 h1 h1) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 22560
 (* h1 h1 h1 h1) (* h3 h3 h3) h4 h5 h6 (* j2 j2)) (* 5250 (* h1 h1 h1 h1) (* h3 
h3 h3) h4 h5 h6 j2) (* 500 (* h1 h1 h1 h1) (* h3 h3 h3) h4 h5 h6) (* 100 (* h1 
h1 h1 h1) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2080 (* h1 
h1 h1 h1) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 13516 (* h1 h1 
h1 h1) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 37040 (* h1 h1 h1 h1)
 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 52364 (* h1 h1 h1 h1) (* h3 h3
 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 41312 (* h1 h1 h1 h1) (* h3 h3 h3) (* h5 
h5) h6 (* j2 j2 j2)) (* 18292 (* h1 h1 h1 h1) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2
)) (* 4240 (* h1 h1 h1 h1) (* h3 h3 h3) (* h5 h5) h6 j2) (* 400 (* h1 h1 h1 h1) 
(* h3 h3 h3) (* h5 h5) h6) (* 20 (* h1 h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2 j2)) (* 508 (* h1 h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 4620 (* h1 h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 19908 (* h1 h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 44956 (* h1 h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 
j2 j2)) (* 57460 (* h1 h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 
42932 (* h1 h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 18492 (* h1 h1 
h1 h1) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2)) (* 4240 (* h1 h1 h1 h1) (* h3 h3 h3)
 h5 (* h6 h6) j2) (* 400 (* h1 h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6)) (* 105 (* h1
 h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 1032 (* h1 h1 
h1 h1) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 3531 (* h1 h1 h1 h1) 
(* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 5994 (* h1 h1 h1 h1) (* h3 h3) 
(* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 5631 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4 h4) 
h5 (* j2 j2 j2)) (* 2964 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2)) 
(* 813 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 j2) (* 90 (* h1 h1 h1 h1) (* h3
 h3) (* h4 h4 h4) h5) (* 25 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 615 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 4382 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* 
j2 j2 j2 j2 j2 j2)) (* 13066 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* j2
 j2 j2 j2 j2)) (* 20229 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 
j2 j2)) (* 17651 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 
8724 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 2268 (* h1 h1 
h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) j2) (* 240 (* h1 h1 h1 h1) (* h3 h3) (* h4 
h4) (* h5 h5)) (* 65 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 1126 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 6975 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2))
 (* 20104 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 31331
 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 28014 (* h1 h1 h1
 h1) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 14297 (* h1 h1 h1 h1) (* h3 h3) 
(* h4 h4) h5 h6 (* j2 j2)) (* 3844 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) h5 h6 j2)
 (* 420 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) h5 h6) (* 50 (* h1 h1 h1 h1) (* h3 
h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 740 (* h1 h1 h1 h1) (* h3 h3
) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 4068 (* h1 h1 h1 h1) (* h3 h3) h4
 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 10712 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5
 h5 h5) (* j2 j2 j2 j2 j2)) (* 15450 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) 
(* j2 j2 j2 j2)) (* 12868 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2)
) (* 6144 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2)) (* 1552 (* h1 h1 
h1 h1) (* h3 h3) h4 (* h5 h5 h5) j2) (* 160 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 
h5 h5)) (* 15 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 376 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2
 j2)) (* 3943 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)
) (* 19998 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
51637 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 74268 (* 
h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 62093 (* h1 h1 h1 h1)
 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 29886 (* h1 h1 h1 h1) (* h3 h3) h4 
(* h5 h5) h6 (* j2 j2)) (* 7640 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5) h6 j2) 
(* 800 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5) h6) (* 10 (* h1 h1 h1 h1) (* h3 h3
) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 314 (* h1 h1 h1 h1) (* h3 
h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3194 (* h1 h1 h1 h1) (* h3 
h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 15078 (* h1 h1 h1 h1) (* h3 h3)
 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 37690 (* h1 h1 h1 h1) (* h3 h3) h4 h5
 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 54070 (* h1 h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6
) (* j2 j2 j2 j2)) (* 45894 (* h1 h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 
j2)) (* 22634 (* h1 h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 5948 (* h1
 h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6) j2) (* 640 (* h1 h1 h1 h1) (* h3 h3) h4 h5 
(* h6 h6)) (* 100 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 1480 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2)) (* 8136 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 21424 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 30900 
(* h1 h1 h1 h1) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 25736 (* h1 h1 h1 
h1) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 12288 (* h1 h1 h1 h1) (* h3 h3) 
(* h5 h5 h5) h6 (* j2 j2)) (* 3104 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5 h5) h6 j2)
 (* 320 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5 h5) h6) (* 30 (* h1 h1 h1 h1) (* h3 
h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 652 (* h1 h1 h1 h1) 
(* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 5426 (* h1 h1 h1 
h1) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 22468 (* h1 h1 h1
 h1) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 51010 (* h1 h1 h1 
h1) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 67620 (* h1 h1 h1 h1) 
(* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 53582 (* h1 h1 h1 h1) (* h3 h3
) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 24876 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5)
 (* h6 h6) (* j2 j2)) (* 6208 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6) j2) 
(* 640 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6)) (* 20 (* h1 h1 h1 h1) (* 
h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 368 (* h1 h1 h1 h1) 
(* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2724 (* h1 h1 h1 h1) 
(* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 10512 (* h1 h1 h1 h1) (* 
h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 23212 (* h1 h1 h1 h1) (* h3 h3)
 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 30768 (* h1 h1 h1 h1) (* h3 h3) h5 (* h6
 h6 h6) (* j2 j2 j2 j2)) (* 24780 (* h1 h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6) (* 
j2 j2 j2)) (* 11792 (* h1 h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 3024
 (* h1 h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6) j2) (* 320 (* h1 h1 h1 h1) (* h3 h3) 
h5 (* h6 h6 h6)) (* 45 (* h1 h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 
j2 j2 j2)) (* 453 (* h1 h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2
)) (* 1614 (* h1 h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 2886
 (* h1 h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 2889 (* h1 h1 h1 
h1) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 1641 (* h1 h1 h1 h1) h3 (* h4 h4 
h4) (* h5 h5) (* j2 j2)) (* 492 (* h1 h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) j2) 
(* 60 (* h1 h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5)) (* 15 (* h1 h1 h1 h1) h3 (* h4 
h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 226 (* h1 h1 h1 h1) h3 (* h4 h4
) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1278 (* h1 h1 h1 h1) h3 (* h4 h4) 
(* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 3516 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 
h5 h5) (* j2 j2 j2 j2 j2)) (* 5371 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* 
j2 j2 j2 j2)) (* 4802 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) 
(* 2496 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 696 (* h1 h1 h1 
h1) h3 (* h4 h4) (* h5 h5 h5) j2) (* 80 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5
)) (* 30 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 532 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
3398 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 10236 
(* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 16874 (* h1 h1 
h1 h1) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 16156 (* h1 h1 h1 h1) h3 
(* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 8946 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 
h5) h6 (* j2 j2)) (* 2644 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5) h6 j2) (* 320 
(* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5) h6) (* 5 (* h1 h1 h1 h1) h3 h4 (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 132 (* h1 h1 h1 h1) h3 h4 (* h5 h5 h5)
 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1282 (* h1 h1 h1 h1) h3 h4 (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 6032 (* h1 h1 h1 h1) h3 h4 (* h5 h5 h5) h6 (* j2 j2
 j2 j2 j2 j2)) (* 15241 (* h1 h1 h1 h1) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)
) (* 22300 (* h1 h1 h1 h1) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 19496 (* h1
 h1 h1 h1) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 10024 (* h1 h1 h1 h1) h3 h4 
(* h5 h5 h5) h6 (* j2 j2)) (* 2784 (* h1 h1 h1 h1) h3 h4 (* h5 h5 h5) h6 j2) (* 
320 (* h1 h1 h1 h1) h3 h4 (* h5 h5 h5) h6) (* 5 (* h1 h1 h1 h1) h3 h4 (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 157 (* h1 h1 h1 h1) h3 h4 (* h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1642 (* h1 h1 h1 h1) h3 h4 (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 8082 (* h1 h1 h1 h1) h3 h4 (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 21305 (* h1 h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6)
 (* j2 j2 j2 j2 j2)) (* 32585 (* h1 h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2
 j2 j2)) (* 29832 (* h1 h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 
16072 (* h1 h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 4672 (* h1 h1 h1 
h1) h3 h4 (* h5 h5) (* h6 h6) j2) (* 560 (* h1 h1 h1 h1) h3 h4 (* h5 h5) (* h6 
h6)) (* 10 (* h1 h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 204 (* h1 h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 1660 (* h1 h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 6952 (* h1 h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
16418 (* h1 h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 23116 (* 
h1 h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 19784 (* h1 h1 h1 h1)
 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 10064 (* h1 h1 h1 h1) h3 (* h5 h5 h5
) (* h6 h6) (* j2 j2)) (* 2784 (* h1 h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6) j2) (* 
320 (* h1 h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6)) (* 10 (* h1 h1 h1 h1) h3 (* h5 h5
) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 194 (* h1 h1 h1 h1) h3 (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1516 (* h1 h1 h1 h1) h3 (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 6196 (* h1 h1 h1 h1) h3 (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 14578 (* h1 h1 h1 h1) h3 (* h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2)) (* 20762 (* h1 h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2)) (* 18152 (* h1 h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)
) (* 9488 (* h1 h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 2704 (* h1 h1 
h1 h1) h3 (* h5 h5) (* h6 h6 h6) j2) (* 320 (* h1 h1 h1 h1) h3 (* h5 h5) (* h6 
h6 h6)) (* 80 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2 j2)) (* 
672 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2)) (* 1776 (* h1 h1 
h1) (* h2 h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2)) (* 1888 (* h1 h1 h1) (* h2 h2 h2 
h2) (* h3 h3) h5 (* j2 j2)) (* 832 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 j2)
 (* 128 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5) (* 32 (* h1 h1 h1) (* h2 h2 
h2 h2) (* h3 h3) h6 (* j2 j2 j2 j2 j2 j2)) (* 304 (* h1 h1 h1) (* h2 h2 h2 h2) 
(* h3 h3) h6 (* j2 j2 j2 j2 j2)) (* 1008 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) 
h6 (* j2 j2 j2 j2)) (* 1552 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h6 (* j2 j2 
j2)) (* 1200 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h6 (* j2 j2)) (* 448 (* h1 
h1 h1) (* h2 h2 h2 h2) (* h3 h3) h6 j2) (* 64 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3
 h3) h6) (* 80 (* h1 h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 
512 (* h1 h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2)) (* 1232 (* h1 h1 
h1) (* h2 h2 h2 h2) h3 (* h5 h5) (* j2 j2 j2)) (* 1376 (* h1 h1 h1) (* h2 h2 h2 
h2) h3 (* h5 h5) (* j2 j2)) (* 704 (* h1 h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) j2)
 (* 128 (* h1 h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5)) (* 48 (* h1 h1 h1) (* h2 h2 
h2 h2) h3 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 416 (* h1 h1 h1) (* h2 h2 h2 h2) h3 h5
 h6 (* j2 j2 j2 j2 j2)) (* 1360 (* h1 h1 h1) (* h2 h2 h2 h2) h3 h5 h6 (* j2 j2 
j2 j2)) (* 2176 (* h1 h1 h1) (* h2 h2 h2 h2) h3 h5 h6 (* j2 j2 j2)) (* 1824 (* 
h1 h1 h1) (* h2 h2 h2 h2) h3 h5 h6 (* j2 j2)) (* 768 (* h1 h1 h1) (* h2 h2 h2 h2
) h3 h5 h6 j2) (* 128 (* h1 h1 h1) (* h2 h2 h2 h2) h3 h5 h6) (* 32 (* h1 h1 h1) 
(* h2 h2 h2 h2) h3 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 208 (* h1 h1 h1) (* h2 h2
 h2 h2) h3 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 544 (* h1 h1 h1) (* h2 h2 h2 h2) h3 
(* h6 h6) (* j2 j2 j2 j2)) (* 736 (* h1 h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6) (* 
j2 j2 j2)) (* 544 (* h1 h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6) (* j2 j2)) (* 208 
(* h1 h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6) j2) (* 32 (* h1 h1 h1) (* h2 h2 h2 h2)
 h3 (* h6 h6)) (* 16 (* h1 h1 h1) (* h2 h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2 j2 j2
 j2)) (* 144 (* h1 h1 h1) (* h2 h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
528 (* h1 h1 h1) (* h2 h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 1008 (* h1 h1 
h1) (* h2 h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2)) (* 1056 (* h1 h1 h1) (* h2 h2 h2 
h2) (* h5 h5) h6 (* j2 j2)) (* 576 (* h1 h1 h1) (* h2 h2 h2 h2) (* h5 h5) h6 j2)
 (* 128 (* h1 h1 h1) (* h2 h2 h2 h2) (* h5 h5) h6) (* 16 (* h1 h1 h1) (* h2 h2 
h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 128 (* h1 h1 h1) (* h2 h2 h2 h2) 
h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 416 (* h1 h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6
) (* j2 j2 j2 j2)) (* 704 (* h1 h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6) (* j2 j2 j2)
) (* 656 (* h1 h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6) (* j2 j2)) (* 320 (* h1 h1 h1
) (* h2 h2 h2 h2) h5 (* h6 h6) j2) (* 64 (* h1 h1 h1) (* h2 h2 h2 h2) h5 (* h6 
h6)) (* 160 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2 j2 j2)) (* 
1944 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2 j2)) (* 7792 (* h1
 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2)) (* 11976 (* h1 h1 h1) (* 
h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2)) (* 8304 (* h1 h1 h1) (* h2 h2 h2) (* h3 
h3 h3) h5 (* j2 j2)) (* 2656 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 j2) (* 
320 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5) (* 64 (* h1 h1 h1) (* h2 h2 h2) 
(* h3 h3 h3) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 848 (* h1 h1 h1) (* h2 h2 h2) (* h3
 h3 h3) h6 (* j2 j2 j2 j2 j2 j2)) (* 3976 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3)
 h6 (* j2 j2 j2 j2 j2)) (* 8264 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h6 (* j2 
j2 j2 j2)) (* 8760 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2)) (* 
4936 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2)) (* 1408 (* h1 h1 h1) 
(* h2 h2 h2) (* h3 h3 h3) h6 j2) (* 160 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) 
h6) (* 8 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 
328 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 3232 (* 
h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 11872 (* h1 h1 h1)
 (* h2 h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2)) (* 19576 (* h1 h1 h1) (* h2 h2 h2
) (* h3 h3) h4 h5 (* j2 j2 j2)) (* 15608 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 
h5 (* j2 j2)) (* 5792 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 j2) (* 800 (* h1
 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5) (* 64 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) 
h4 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 896 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h6
 (* j2 j2 j2 j2 j2 j2)) (* 4208 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h6 (* j2 
j2 j2 j2 j2)) (* 9248 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2))
 (* 10784 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2)) (* 6848 (* h1 
h1 h1) (* h2 h2 h2) (* h3 h3) h4 h6 (* j2 j2)) (* 2224 (* h1 h1 h1) (* h2 h2 h2)
 (* h3 h3) h4 h6 j2) (* 288 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h6) (* 280 
(* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 3072 (* 
h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 10344 (* h1 h1
 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 15744 (* h1 h1 h1) (* 
h2 h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2)) (* 11872 (* h1 h1 h1) (* h2 h2 h2) 
(* h3 h3) (* h5 h5) (* j2 j2)) (* 4256 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h5
 h5) j2) (* 576 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5)) (* 152 (* h1 h1 
h1) (* h2 h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1992 (* h1 h1 h1) 
(* h2 h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 9144 (* h1 h1 h1) (* h2 
h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 21312 (* h1 h1 h1) (* h2 h2 h2) 
(* h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 27216 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5
 h6 (* j2 j2 j2)) (* 18824 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 h6 (* j2 j2)) 
(* 6480 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 h6 j2) (* 864 (* h1 h1 h1) (* h2 
h2 h2) (* h3 h3) h5 h6) (* 96 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 1136 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 4928 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 
j2 j2 j2 j2)) (* 10384 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2
 j2)) (* 11808 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2)) (* 
7376 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2)) (* 2368 (* h1 h1 
h1) (* h2 h2 h2) (* h3 h3) (* h6 h6) j2) (* 304 (* h1 h1 h1) (* h2 h2 h2) (* h3 
h3) (* h6 h6)) (* 8 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2 
j2 j2)) (* 272 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) 
(* 2280 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 7776 
(* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2)) (* 13024 (* h1 h1 h1)
 (* h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2)) (* 11296 (* h1 h1 h1) (* h2 h2 h2) 
h3 h4 (* h5 h5) (* j2 j2)) (* 4800 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) j2)
 (* 768 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5)) (* 88 (* h1 h1 h1) (* h2 h2 
h2) h3 h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1200 (* h1 h1 h1) (* h2 h2 h2) h3 
h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 5584 (* h1 h1 h1) (* h2 h2 h2) h3 h4 h5 h6 
(* j2 j2 j2 j2 j2)) (* 12496 (* h1 h1 h1) (* h2 h2 h2) h3 h4 h5 h6 (* j2 j2 j2 
j2)) (* 15208 (* h1 h1 h1) (* h2 h2 h2) h3 h4 h5 h6 (* j2 j2 j2)) (* 10336 (* h1
 h1 h1) (* h2 h2 h2) h3 h4 h5 h6 (* j2 j2)) (* 3696 (* h1 h1 h1) (* h2 h2 h2) h3
 h4 h5 h6 j2) (* 544 (* h1 h1 h1) (* h2 h2 h2) h3 h4 h5 h6) (* 32 (* h1 h1 h1) 
(* h2 h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 336 (* h1 h1 h1) (* h2
 h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1280 (* h1 h1 h1) (* h2 h2 h2)
 h3 h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2480 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* 
h6 h6) (* j2 j2 j2 j2)) (* 2720 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6) (* j2 
j2 j2)) (* 1712 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6) (* j2 j2)) (* 576 (* 
h1 h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6) j2) (* 80 (* h1 h1 h1) (* h2 h2 h2) h3 h4
 (* h6 h6)) (* 80 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2
)) (* 832 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 3000 
(* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 5072 (* h1 h1 h1) 
(* h2 h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2)) (* 4360 (* h1 h1 h1) (* h2 h2 h2) h3 
(* h5 h5 h5) (* j2 j2)) (* 1824 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) j2) 
(* 288 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5)) (* 96 (* h1 h1 h1) (* h2 h2 h2
) h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1320 (* h1 h1 h1) (* h2 h2 h2) h3
 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 6416 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 
h5) h6 (* j2 j2 j2 j2 j2)) (* 15272 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) h6 
(* j2 j2 j2 j2)) (* 20016 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2)
) (* 14720 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) h6 (* j2 j2)) (* 5648 (* h1 h1
 h1) (* h2 h2 h2) h3 (* h5 h5) h6 j2) (* 864 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 
h5) h6) (* 120 (* h1 h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2
)) (* 1448 (* h1 h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
6272 (* h1 h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 13384 (* 
h1 h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 15720 (* h1 h1 h1) 
(* h2 h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2)) (* 10376 (* h1 h1 h1) (* h2 h2 h2) h3
 h5 (* h6 h6) (* j2 j2)) (* 3616 (* h1 h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6) j2) 
(* 520 (* h1 h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6)) (* 32 (* h1 h1 h1) (* h2 h2 h2
) h3 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 336 (* h1 h1 h1) (* h2 h2 h2) h3 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1280 (* h1 h1 h1) (* h2 h2 h2) h3 (* h6 
h6 h6) (* j2 j2 j2 j2 j2)) (* 2480 (* h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6) (* 
j2 j2 j2 j2)) (* 2720 (* h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2)) 
(* 1712 (* h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6) (* j2 j2)) (* 576 (* h1 h1 h1)
 (* h2 h2 h2) h3 (* h6 h6 h6) j2) (* 80 (* h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6
)) (* 24 (* h1 h1 h1) (* h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
336 (* h1 h1 h1) (* h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 1768 (* 
h1 h1 h1) (* h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 4744 (* h1 h1 h1) 
(* h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 7168 (* h1 h1 h1) (* h2 h2 h2) 
h4 (* h5 h5) h6 (* j2 j2 j2)) (* 6184 (* h1 h1 h1) (* h2 h2 h2) h4 (* h5 h5) h6 
(* j2 j2)) (* 2848 (* h1 h1 h1) (* h2 h2 h2) h4 (* h5 h5) h6 j2) (* 544 (* h1 h1
 h1) (* h2 h2 h2) h4 (* h5 h5) h6) (* 16 (* h1 h1 h1) (* h2 h2 h2) h4 h5 (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 192 (* h1 h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 880 (* h1 h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6) (* j2 j2
 j2 j2 j2)) (* 2080 (* h1 h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) 
(* 2800 (* h1 h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 2176 (* h1 h1
 h1) (* h2 h2 h2) h4 h5 (* h6 h6) (* j2 j2)) (* 912 (* h1 h1 h1) (* h2 h2 h2) h4
 h5 (* h6 h6) j2) (* 160 (* h1 h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6)) (* 16 (* h1 
h1 h1) (* h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 208 (* h1 h1 h1
) (* h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 1048 (* h1 h1 h1) (* h2
 h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 2728 (* h1 h1 h1) (* h2 h2 h2) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 4024 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5 h5) 
h6 (* j2 j2 j2)) (* 3400 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2)) 
(* 1536 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5 h5) h6 j2) (* 288 (* h1 h1 h1) (* h2 
h2 h2) (* h5 h5 h5) h6) (* 32 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 400 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 1920 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2)) (* 4760 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2)) (* 6712 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 5448
 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 j2)) (* 2376 (* h1 h1 h1) 
(* h2 h2 h2) (* h5 h5) (* h6 h6) j2) (* 432 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5) 
(* h6 h6)) (* 16 (* h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 192 (* h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
880 (* h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2080 (* h1 
h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 2800 (* h1 h1 h1) (* h2 
h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 2176 (* h1 h1 h1) (* h2 h2 h2) h5 (* h6 
h6 h6) (* j2 j2)) (* 912 (* h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6) j2) (* 160 
(* h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6)) (* 40 (* h1 h1 h1) (* h2 h2) (* h3 h3
 h3 h3) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 756 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 
h3) h5 (* j2 j2 j2 j2 j2 j2)) (* 4016 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 
(* j2 j2 j2 j2 j2)) (* 7808 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2 
j2 j2)) (* 7208 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2 j2)) (* 3452 
(* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2)) (* 832 (* h1 h1 h1) (* h2 
h2) (* h3 h3 h3 h3) h5 j2) (* 80 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5) (* 
16 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 320
 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1940 (* 
h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2 j2 j2 j2 j2)) (* 4908 (* h1 h1 
h1) (* h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2 j2 j2 j2)) (* 6408 (* h1 h1 h1) (* h2 
h2) (* h3 h3 h3 h3) h6 (* j2 j2 j2 j2)) (* 4704 (* h1 h1 h1) (* h2 h2) (* h3 h3 
h3 h3) h6 (* j2 j2 j2)) (* 1964 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h6 (* j2 
j2)) (* 436 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h6 j2) (* 40 (* h1 h1 h1) (* 
h2 h2) (* h3 h3 h3 h3) h6) (* 4 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 284 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2
 j2 j2 j2 j2 j2)) (* 4268 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 
j2 j2 j2)) (* 23092 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2)
) (* 51576 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2)) (* 56232 
(* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2)) (* 31592 (* h1 h1 h1) 
(* h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2)) (* 8792 (* h1 h1 h1) (* h2 h2) (* h3 h3 
h3) h4 h5 j2) (* 960 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5) (* 40 (* h1 h1 
h1) (* h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 940 (* h1 h1 h1
) (* h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 6548 (* h1 h1 h1) 
(* h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2)) (* 18972 (* h1 h1 h1) (* h2 
h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 28420 (* h1 h1 h1) (* h2 h2) (* h3
 h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 23948 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 
h6 (* j2 j2 j2)) (* 11444 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2)) 
(* 2892 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h6 j2) (* 300 (* h1 h1 h1) (* h2 
h2) (* h3 h3 h3) h4 h6) (* 140 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 2496 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) (* 
j2 j2 j2 j2 j2 j2)) (* 13816 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) (* j2
 j2 j2 j2 j2)) (* 31816 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 
j2 j2)) (* 35472 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2)) (* 
20080 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2)) (* 5564 (* h1 h1 
h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) j2) (* 600 (* h1 h1 h1) (* h2 h2) (* h3 h3 
h3) (* h5 h5)) (* 68 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 1476 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 10744 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2)
) (* 35812 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 
62088 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 58948 (* h1 
h1 h1) (* h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2)) (* 30592 (* h1 h1 h1) (* h2 h2
) (* h3 h3 h3) h5 h6 (* j2 j2)) (* 8116 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 
h6 j2) (* 860 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 h6) (* 56 (* h1 h1 h1) (* 
h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1228 (* h1 h1 h1) 
(* h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 7832 (* h1 h1 h1) 
(* h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 21680 (* h1 h1 h1) 
(* h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 31632 (* h1 h1 h1) (* h2
 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 26212 (* h1 h1 h1) (* h2 h2) (* 
h3 h3 h3) (* h6 h6) (* j2 j2 j2)) (* 12384 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) 
(* h6 h6) (* j2 j2)) (* 3104 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6) j2) 
(* 320 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6)) (* 120 (* h1 h1 h1) (* h2 
h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 2100 (* h1 h1 h1) (* h2 
h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 11844 (* h1 h1 h1) (* h2 h2
) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 28976 (* h1 h1 h1) (* h2 h2) (* 
h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 35840 (* h1 h1 h1) (* h2 h2) (* h3 h3) 
(* h4 h4) h5 (* j2 j2 j2)) (* 23284 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) 
h5 (* j2 j2)) (* 7492 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 j2) (* 936 
(* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5) (* 184 (* h1 h1 h1) (* h2 h2) (* 
h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1820 (* h1 h1 h1) (* h2 h2) (* 
h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 6344 (* h1 h1 h1) (* h2 h2) (* h3 
h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 11060 (* h1 h1 h1) (* h2 h2) (* h3 h3) 
(* h4 h4) h6 (* j2 j2 j2 j2)) (* 10760 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4
) h6 (* j2 j2 j2)) (* 5924 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 
j2)) (* 1720 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h6 j2) (* 204 (* h1 h1 
h1) (* h2 h2) (* h3 h3) (* h4 h4) h6) (* 8 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 
(* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 496 (* h1 h1 h1) (* h2 h2) (* h3 h3) 
h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 6092 (* h1 h1 h1) (* h2 h2) (* h3 h3) 
h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 28760 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4
 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 63260 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* 
h5 h5) (* j2 j2 j2 j2)) (* 72544 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) 
(* j2 j2 j2)) (* 44504 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2)) 
(* 13728 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) j2) (* 1664 (* h1 h1 h1) 
(* h2 h2) (* h3 h3) h4 (* h5 h5)) (* 92 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2136 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 16440 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6 
(* j2 j2 j2 j2 j2 j2)) (* 57132 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6 (* j2 
j2 j2 j2 j2)) (* 105352 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2
)) (* 109556 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 63876 
(* h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2)) (* 19256 (* h1 h1 h1) (* h2
 h2) (* h3 h3) h4 h5 h6 j2) (* 2320 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6) 
(* 48 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2))
 (* 936 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 6048 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
17956 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 28860
 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 26768 (* h1 
h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2)) (* 14296 (* h1 h1 h1) (* 
h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2)) (* 4068 (* h1 h1 h1) (* h2 h2) (* h3 h3
) h4 (* h6 h6) j2) (* 476 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6)) (* 120 
(* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1608 
(* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 8104 (* 
h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 18752 (* h1 h1
 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 22224 (* h1 h1 h1) (* 
h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2)) (* 13848 (* h1 h1 h1) (* h2 h2) (* 
h3 h3) (* h5 h5 h5) (* j2 j2)) (* 4272 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5
 h5) j2) (* 512 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5)) (* 84 (* h1 h1 h1
) (* h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1724 (* h1 h1
 h1) (* h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 12796 (* h1 
h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 43572 (* h1 h1
 h1) (* h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 78992 (* h1 h1 h1) 
(* h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 80772 (* h1 h1 h1) (* h2 h2
) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 46288 (* h1 h1 h1) (* h2 h2) (* h3 h3)
 (* h5 h5) h6 (* j2 j2)) (* 13716 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) h6 
j2) (* 1624 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) h6) (* 140 (* h1 h1 h1) 
(* h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2528 (* h1 h1 
h1) (* h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 16104 (* h1 h1
 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 48176 (* h1 h1 
h1) (* h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 78832 (* h1 h1 h1) 
(* h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 74708 (* h1 h1 h1) (* h2 h2
) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 40660 (* h1 h1 h1) (* h2 h2) (* h3 h3)
 h5 (* h6 h6) (* j2 j2)) (* 11692 (* h1 h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6) 
j2) (* 1368 (* h1 h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6)) (* 48 (* h1 h1 h1) 
(* h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 752 (* h1 h1 h1
) (* h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4228 (* h1 h1 h1
) (* h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 11612 (* h1 h1 h1) 
(* h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 17800 (* h1 h1 h1) (* h2
 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 16008 (* h1 h1 h1) (* h2 h2) (* 
h3 h3) (* h6 h6 h6) (* j2 j2 j2)) (* 8372 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h6
 h6 h6) (* j2 j2)) (* 2348 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6) j2) (* 
272 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6)) (* 84 (* h1 h1 h1) (* h2 h2) 
h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1292 (* h1 h1 h1) (* h2 h2) 
h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 6816 (* h1 h1 h1) (* h2 h2) h3 
(* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 16792 (* h1 h1 h1) (* h2 h2) h3 (* h4
 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 21924 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* 
h5 h5) (* j2 j2 j2)) (* 15580 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) (* 
j2 j2)) (* 5640 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) j2) (* 800 (* h1 
h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5)) (* 240 (* h1 h1 h1) (* h2 h2) h3 (* h4 
h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2348 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) 
h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 8216 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) h5 h6 
(* j2 j2 j2 j2 j2)) (* 14512 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 
j2 j2)) (* 14448 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2)) (* 8252
 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2)) (* 2536 (* h1 h1 h1) (* h2
 h2) h3 (* h4 h4) h5 h6 j2) (* 328 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) h5 h6) 
(* 24 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 156 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
432 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 660 (* 
h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 600 (* h1 h1 h1) 
(* h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 324 (* h1 h1 h1) (* h2 h2) h3 
(* h4 h4) (* h6 h6) (* j2 j2)) (* 96 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h6 
h6) j2) (* 12 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h6 h6)) (* 4 (* h1 h1 h1) 
(* h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 172 (* h1 h1 h1) 
(* h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1836 (* h1 h1 h1) (* 
h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 8360 (* h1 h1 h1) (* h2 h2) 
h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 18992 (* h1 h1 h1) (* h2 h2) h3 h4 (* 
h5 h5 h5) (* j2 j2 j2 j2)) (* 23444 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) 
(* j2 j2 j2)) (* 15944 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2)) (* 
5568 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) j2) (* 768 (* h1 h1 h1) (* h2 h2)
 h3 h4 (* h5 h5 h5)) (* 64 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 1332 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2)) (* 9928 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 
j2 j2)) (* 34988 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) 
(* 67232 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 74564 (* 
h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2)) (* 47472 (* h1 h1 h1) (* h2
 h2) h3 h4 (* h5 h5) h6 (* j2 j2)) (* 15996 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 
h5) h6 j2) (* 2184 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6) (* 60 (* h1 h1 h1)
 (* h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1176 (* h1 h1 h1) 
(* h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 7804 (* h1 h1 h1) (* 
h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 23808 (* h1 h1 h1) (* h2 h2)
 h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 39444 (* h1 h1 h1) (* h2 h2) h3 h4 h5
 (* h6 h6) (* j2 j2 j2 j2)) (* 37976 (* h1 h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6) 
(* j2 j2 j2)) (* 21300 (* h1 h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2)) (* 
6480 (* h1 h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6) j2) (* 832 (* h1 h1 h1) (* h2 h2)
 h3 h4 h5 (* h6 h6)) (* 8 (* h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 108 (* h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2 j2 j2
 j2 j2 j2)) (* 508 (* h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 1228 (* h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
1740 (* h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1508 (* h1 h1
 h1) (* h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2 j2)) (* 788 (* h1 h1 h1) (* h2 h2) h3
 h4 (* h6 h6 h6) (* j2 j2)) (* 228 (* h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6 h6) j2)
 (* 28 (* h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6 h6)) (* 20 (* h1 h1 h1) (* h2 h2) 
h3 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 228 (* h1 h1 h1) (* h2 h2) h3 
(* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 948 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5
 h5 h5) (* j2 j2 j2 j2 j2)) (* 1964 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) 
(* j2 j2 j2 j2)) (* 2248 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) (* j2 j2 j2))
 (* 1440 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) (* j2 j2)) (* 480 (* h1 h1 h1
) (* h2 h2) h3 (* h5 h5 h5 h5) j2) (* 64 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5 
h5)) (* 36 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 636 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
4348 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 14896 
(* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 28564 (* h1 h1 
h1) (* h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 31924 (* h1 h1 h1) (* h2 h2
) h3 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 20508 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 
h5) h6 (* j2 j2)) (* 6944 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) h6 j2) (* 944 
(* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) h6) (* 92 (* h1 h1 h1) (* h2 h2) h3 (* h5
 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1540 (* h1 h1 h1) (* h2 h2) h3 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 9692 (* h1 h1 h1) (* h2 h2) h3 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 29932 (* h1 h1 h1) (* h2 h2) h3 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 51716 (* h1 h1 h1) (* h2 h2) h3 (* h5
 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 52612 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5) (* 
h6 h6) (* j2 j2 j2)) (* 31260 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6) (* 
j2 j2)) (* 9996 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6) j2) (* 1320 (* h1 
h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6)) (* 60 (* h1 h1 h1) (* h2 h2) h3 h5 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 928 (* h1 h1 h1) (* h2 h2) h3 h5 (* h6
 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 5404 (* h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 15448 (* h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2)) (* 24712 (* h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 
j2 j2)) (* 23328 (* h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 
12940 (* h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2)) (* 3912 (* h1 h1 h1) 
(* h2 h2) h3 h5 (* h6 h6 h6) j2) (* 500 (* h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6
)) (* 8 (* h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 84 (* h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 352
 (* h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 796 (* h1 
h1 h1) (* h2 h2) h3 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1080 (* h1 h1 h1) (* 
h2 h2) h3 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 908 (* h1 h1 h1) (* h2 h2) h3 (* 
h6 h6 h6 h6) (* j2 j2 j2)) (* 464 (* h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6 h6) (* 
j2 j2)) (* 132 (* h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6 h6) j2) (* 16 (* h1 h1 h1) 
(* h2 h2) h3 (* h6 h6 h6 h6)) (* 48 (* h1 h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 532 (* h1 h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2)) (* 2300 (* h1 h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) h6 
(* j2 j2 j2 j2 j2)) (* 5168 (* h1 h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 
j2 j2 j2)) (* 6632 (* h1 h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) 
(* 4916 (* h1 h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 1964 (* h1 
h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) h6 j2) (* 328 (* h1 h1 h1) (* h2 h2) (* h4 
h4) (* h5 h5) h6) (* 12 (* h1 h1 h1) (* h2 h2) (* h4 h4) h5 (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 96 (* h1 h1 h1) (* h2 h2) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2
 j2 j2 j2)) (* 324 (* h1 h1 h1) (* h2 h2) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 600 (* h1 h1 h1) (* h2 h2) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 
660 (* h1 h1 h1) (* h2 h2) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 432 (* h1 h1 
h1) (* h2 h2) (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 156 (* h1 h1 h1) (* h2 h2) 
(* h4 h4) h5 (* h6 h6) j2) (* 24 (* h1 h1 h1) (* h2 h2) (* h4 h4) h5 (* h6 h6)) 
(* 12 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
204 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1368 
(* h1 h1 h1) (* h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 4716 (* h1 
h1 h1) (* h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 9304 (* h1 h1 h1) (* 
h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 10952 (* h1 h1 h1) (* h2 h2) h4 
(* h5 h5 h5) h6 (* j2 j2 j2)) (* 7620 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5 h5) h6 
(* j2 j2)) (* 2896 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5 h5) h6 j2) (* 464 (* h1 h1
 h1) (* h2 h2) h4 (* h5 h5 h5) h6) (* 16 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 292 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2040 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 7236 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2)) (* 14616 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6
) (* j2 j2 j2 j2)) (* 17580 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 
j2 j2)) (* 12488 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 
4844 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6) j2) (* 792 (* h1 h1 h1) (* h2
 h2) h4 (* h5 h5) (* h6 h6)) (* 4 (* h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 60 (* h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 332 (* h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2
 j2 j2 j2)) (* 956 (* h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2))
 (* 1620 (* h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1684 (* 
h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 1060 (* h1 h1 h1) (* h2 
h2) h4 h5 (* h6 h6 h6) (* j2 j2)) (* 372 (* h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6 
h6) j2) (* 56 (* h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6 h6)) (* 4 (* h1 h1 h1) (* h2
 h2) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 56 (* h1 h1 h1) (* h2 h2
) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 312 (* h1 h1 h1) (* h2 h2) (* 
h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 928 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5
 h5) h6 (* j2 j2 j2 j2 j2)) (* 1636 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5 h5) h6 
(* j2 j2 j2 j2)) (* 1768 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5 h5) h6 (* j2 j2 j2))
 (* 1152 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 416 (* h1 h1 h1
) (* h2 h2) (* h5 h5 h5 h5) h6 j2) (* 64 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5 h5) 
h6) (* 16 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 252 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 1592 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)
) (* 5260 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
10060 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 11560 
(* h1 h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 7884 (* h1 h1 h1)
 (* h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 2944 (* h1 h1 h1) (* h2 h2) (* 
h5 h5 h5) (* h6 h6) j2) (* 464 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6)) 
(* 16 (* h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2))
 (* 240 (* h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 1476 (* h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
4828 (* h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 9248 
(* h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 10728 (* h1 h1
 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 7428 (* h1 h1 h1) (* h2 
h2) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 2828 (* h1 h1 h1) (* h2 h2) (* h5 h5) 
(* h6 h6 h6) j2) (* 456 (* h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6)) (* 4 (* 
h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 48 (* h1 
h1 h1) (* h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 236 (* h1 h1 h1
) (* h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 632 (* h1 h1 h1) (* h2 
h2) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1020 (* h1 h1 h1) (* h2 h2) h5 (* 
h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 1024 (* h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6 h6) 
(* j2 j2 j2)) (* 628 (* h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2)) (* 216
 (* h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6 h6) j2) (* 32 (* h1 h1 h1) (* h2 h2) h5 
(* h6 h6 h6 h6)) (* 20 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 538 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2)
) (* 4532 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 12798 
(* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 17328 (* h1 h1 h1) 
h2 (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2)) (* 12750 (* h1 h1 h1) h2 (* h3 h3 h3 
h3) h4 h5 (* j2 j2 j2)) (* 5236 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h5 (* j2 j2))
 (* 1130 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h5 j2) (* 100 (* h1 h1 h1) h2 (* h3 
h3 h3 h3) h4 h5) (* 56 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 920 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2)
) (* 3702 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2)) (* 7008 
(* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 7434 (* h1 h1 h1) 
h2 (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 4680 (* h1 h1 h1) h2 (* h3 h3 h3 h3
) h4 h6 (* j2 j2 j2)) (* 1738 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h6 (* j2 j2)) 
(* 352 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h6 j2) (* 30 (* h1 h1 h1) h2 (* h3 h3 
h3 h3) h4 h6) (* 200 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2
 j2 j2)) (* 3060 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2)
) (* 9752 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 13784
 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 10304 (* h1 h1 h1
) h2 (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2)) (* 4244 (* h1 h1 h1) h2 (* h3 h3 h3
 h3) (* h5 h5) (* j2 j2)) (* 912 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) j2) 
(* 80 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5)) (* 140 (* h1 h1 h1) h2 (* h3 h3
 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2366 (* h1 h1 h1) h2 (* h3 h3 h3 
h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 10264 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h5 
h6 (* j2 j2 j2 j2 j2 j2)) (* 20726 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h5 h6 (* j2 
j2 j2 j2 j2)) (* 23096 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2)) 
(* 15050 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2)) (* 5712 (* h1 h1 h1
) h2 (* h3 h3 h3 h3) h5 h6 (* j2 j2)) (* 1170 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h5
 h6 j2) (* 100 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h5 h6) (* 16 (* h1 h1 h1) h2 (* 
h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 336 (* h1 h1 h1) h2 
(* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2260 (* h1 h1 h1) h2 
(* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 6848 (* h1 h1 h1) h2 (* 
h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 11316 (* h1 h1 h1) h2 (* h3 h3 
h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 11112 (* h1 h1 h1) h2 (* h3 h3 h3 h3) 
(* h6 h6) (* j2 j2 j2 j2)) (* 6668 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6) (* 
j2 j2 j2)) (* 2400 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6) (* j2 j2)) (* 476 
(* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6) j2) (* 40 (* h1 h1 h1) h2 (* h3 h3 h3 
h3) (* h6 h6)) (* 64 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 1694 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 
j2 j2)) (* 12758 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)
) (* 38560 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 
58946 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 49754 (* h1 
h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 23406 (* h1 h1 h1) h2 (* h3
 h3 h3) (* h4 h4) h5 (* j2 j2)) (* 5736 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) 
h5 j2) (* 570 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5) (* 84 (* h1 h1 h1) h2 
(* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1030 (* h1 h1 h1) h2 
(* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 4150 (* h1 h1 h1) h2 (* 
h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 8372 (* h1 h1 h1) h2 (* h3 h3 
h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 9708 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 
h4) h6 (* j2 j2 j2 j2)) (* 6766 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h6 (* j2 
j2 j2)) (* 2798 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h6 (* j2 j2)) (* 632 (* 
h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h6 j2) (* 60 (* h1 h1 h1) h2 (* h3 h3 h3) 
(* h4 h4) h6) (* 100 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 2430 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 
j2 j2)) (* 18046 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)
) (* 55696 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 
87004 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 74434 (* h1 
h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 35130 (* h1 h1 h1) h2 (* h3
 h3 h3) h4 (* h5 h5) (* j2 j2)) (* 8560 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5
) j2) (* 840 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5)) (* 8 (* h1 h1 h1) h2 (* 
h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 600 (* h1 h1 h1) h2 (* h3 
h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 8672 (* h1 h1 h1) h2 (* h3 h3 h3
) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 46508 (* h1 h1 h1) h2 (* h3 h3 h3) h4 h5
 h6 (* j2 j2 j2 j2 j2 j2)) (* 119266 (* h1 h1 h1) h2 (* h3 h3 h3) h4 h5 h6 (* j2
 j2 j2 j2 j2)) (* 166492 (* h1 h1 h1) h2 (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) 
(* 133060 (* h1 h1 h1) h2 (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 60484 (* h1 h1 
h1) h2 (* h3 h3 h3) h4 h5 h6 (* j2 j2)) (* 14498 (* h1 h1 h1) h2 (* h3 h3 h3) h4
 h5 h6 j2) (* 1420 (* h1 h1 h1) h2 (* h3 h3 h3) h4 h5 h6) (* 24 (* h1 h1 h1) h2 
(* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 488 (* h1 h1 h1) h2
 (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3562 (* h1 h1 h1) h2 
(* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 11974 (* h1 h1 h1) h2 (* 
h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 22124 (* h1 h1 h1) h2 (* h3 h3 
h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 24400 (* h1 h1 h1) h2 (* h3 h3 h3) h4 
(* h6 h6) (* j2 j2 j2 j2)) (* 16482 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6) 
(* j2 j2 j2)) (* 6678 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6) (* j2 j2)) (* 
1488 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6) j2) (* 140 (* h1 h1 h1) h2 (* h3 
h3 h3) h4 (* h6 h6)) (* 400 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 
j2 j2 j2 j2 j2)) (* 3520 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 
j2 j2 j2)) (* 11124 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2)
) (* 17312 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 14660 
(* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2)) (* 6840 (* h1 h1 h1) h2 
(* h3 h3 h3) (* h5 h5 h5) (* j2 j2)) (* 1648 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 
h5 h5) j2) (* 160 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5)) (* 400 (* h1 h1 h1)
 h2 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 5540 (* h1 h1 h1) 
h2 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 29122 (* h1 h1 h1) h2 
(* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 75508 (* h1 h1 h1) h2 (* h3 
h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 107308 (* h1 h1 h1) h2 (* h3 h3 h3) 
(* h5 h5) h6 (* j2 j2 j2 j2)) (* 86928 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) h6
 (* j2 j2 j2)) (* 39714 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2)) (* 
9488 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) h6 j2) (* 920 (* h1 h1 h1) h2 (* h3 
h3 h3) (* h5 h5) h6) (* 56 (* h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2
 j2 j2 j2 j2 j2 j2)) (* 1112 (* h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 9466 (* h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 39380 (* h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 88344 (* h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)
) (* 114106 (* h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 86910 
(* h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 38308 (* h1 h1 h1) h2
 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2)) (* 9000 (* h1 h1 h1) h2 (* h3 h3 h3) h5 
(* h6 h6) j2) (* 870 (* h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6)) (* 24 (* h1 h1 
h1) h2 (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 404 (* h1 h1
 h1) h2 (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2532 (* h1 h1 
h1) h2 (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 7824 (* h1 h1 h1) 
h2 (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 13752 (* h1 h1 h1) h2 (* 
h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 14692 (* h1 h1 h1) h2 (* h3 h3 h3)
 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 9716 (* h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6)
 (* j2 j2 j2)) (* 3880 (* h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6) (* j2 j2)) (* 
856 (* h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6) j2) (* 80 (* h1 h1 h1) h2 (* h3 h3
 h3) (* h6 h6 h6)) (* 272 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 
j2 j2 j2 j2)) (* 2942 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 
j2 j2)) (* 10732 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) 
(* 19182 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 18824 (* 
h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 10282 (* h1 h1 h1) h2 
(* h3 h3) (* h4 h4 h4) h5 (* j2 j2)) (* 2908 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 
h4) h5 j2) (* 330 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5) (* 84 (* h1 h1 h1) 
h2 (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 498 (* h1 h1 h1) h2 
(* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 1248 (* h1 h1 h1) h2 (* h3 
h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 1710 (* h1 h1 h1) h2 (* h3 h3) (* h4 
h4 h4) h6 (* j2 j2 j2 j2)) (* 1380 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h6 (* 
j2 j2 j2)) (* 654 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h6 (* j2 j2)) (* 168 
(* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h6 j2) (* 18 (* h1 h1 h1) h2 (* h3 h3) 
(* h4 h4 h4) h6) (* 90 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 1894 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2
 j2 j2 j2 j2 j2)) (* 13450 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) (* j2 
j2 j2 j2 j2 j2)) (* 41986 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2
 j2 j2 j2)) (* 68818 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 
j2)) (* 63594 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 
33158 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 9038 (* h1 h1 
h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) j2) (* 996 (* h1 h1 h1) h2 (* h3 h3) (* h4 
h4) (* h5 h5)) (* 192 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 3498 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 
j2 j2 j2)) (* 21036 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 
j2)) (* 59994 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 
93908 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 85022 (* h1 
h1 h1) h2 (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 44100 (* h1 h1 h1) h2 (* h3
 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 12062 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 
h6 j2) (* 1340 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 h6) (* 52 (* h1 h1 h1) h2 
(* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 614 (* h1 h1 h1) 
h2 (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2586 (* h1 h1 h1) 
h2 (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 5606 (* h1 h1 h1) h2 
(* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 7090 (* h1 h1 h1) h2 (* h3 
h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 5442 (* h1 h1 h1) h2 (* h3 h3) (* h4
 h4) (* h6 h6) (* j2 j2 j2)) (* 2494 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h6 
h6) (* j2 j2)) (* 626 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h6 h6) j2) (* 66 
(* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h6 h6)) (* 90 (* h1 h1 h1) h2 (* h3 h3) 
h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1646 (* h1 h1 h1) h2 (* h3 h3) 
h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 10714 (* h1 h1 h1) h2 (* h3 h3) h4 
(* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 32308 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 
h5 h5) (* j2 j2 j2 j2 j2)) (* 52052 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) 
(* j2 j2 j2 j2)) (* 47466 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2)
) (* 24388 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) (* j2 j2)) (* 6528 (* h1 h1
 h1) h2 (* h3 h3) h4 (* h5 h5 h5) j2) (* 704 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 
h5 h5)) (* 12 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 764 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2
 j2)) (* 9576 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)
) (* 50142 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
133002 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 197972 
(* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 172028 (* h1 h1 h1
) h2 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 86118 (* h1 h1 h1) h2 (* h3 h3) 
h4 (* h5 h5) h6 (* j2 j2)) (* 22854 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) h6 j2
) (* 2476 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) h6) (* 48 (* h1 h1 h1) h2 (* h3
 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1060 (* h1 h1 h1) h2 (* 
h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 9504 (* h1 h1 h1) h2 (* 
h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 41784 (* h1 h1 h1) h2 (* h3 
h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 100996 (* h1 h1 h1) h2 (* h3 h3) 
h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 143288 (* h1 h1 h1) h2 (* h3 h3) h4 h5 
(* h6 h6) (* j2 j2 j2 j2)) (* 121848 (* h1 h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6) 
(* j2 j2 j2)) (* 60648 (* h1 h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 
16148 (* h1 h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6) j2) (* 1764 (* h1 h1 h1) h2 (* 
h3 h3) h4 h5 (* h6 h6)) (* 8 (* h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 168 (* h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6 h6) (* j2 j2
 j2 j2 j2 j2 j2 j2)) (* 1202 (* h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 4140 (* h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 8070 (* h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2))
 (* 9568 (* h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 7038 (* 
h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2)) (* 3132 (* h1 h1 h1) h2 (* 
h3 h3) h4 (* h6 h6 h6) (* j2 j2)) (* 770 (* h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6 
h6) j2) (* 80 (* h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6 h6)) (* 100 (* h1 h1 h1) h2 
(* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 980 (* h1 h1 h1) h2 (* h3
 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 3236 (* h1 h1 h1) h2 (* h3 h3) 
(* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 5244 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 
h5 h5) (* j2 j2 j2 j2)) (* 4680 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) (* j2 
j2 j2)) (* 2336 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) (* j2 j2)) (* 608 (* 
h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) j2) (* 64 (* h1 h1 h1) h2 (* h3 h3) (* h5
 h5 h5 h5)) (* 270 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 3478 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 17628 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)
) (* 45992 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
68122 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 59122 (* h1 
h1 h1) h2 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 29516 (* h1 h1 h1) h2 (* h3
 h3) (* h5 h5 h5) h6 (* j2 j2)) (* 7776 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) 
h6 j2) (* 832 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) h6) (* 56 (* h1 h1 h1) h2 
(* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1172 (* h1 h1 
h1) h2 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 9766 (* h1 
h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 41248 (* h1
 h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 96890 (* h1 
h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 133808 (* h1 h1 
h1) h2 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 110682 (* h1 h1 h1) h2 
(* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 53584 (* h1 h1 h1) h2 (* h3 h3) 
(* h5 h5) (* h6 h6) (* j2 j2)) (* 13902 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5) (* 
h6 h6) j2) (* 1484 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6)) (* 48 (* h1 h1
 h1) h2 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 860 (* h1 
h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6222 (* h1 
h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 23520 (* h1 h1 
h1) h2 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 51442 (* h1 h1 h1) h2
 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 68252 (* h1 h1 h1) h2 (* h3 h3
) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 55442 (* h1 h1 h1) h2 (* h3 h3) h5 (* h6 
h6 h6) (* j2 j2 j2)) (* 26744 (* h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2
)) (* 6974 (* h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6) j2) (* 752 (* h1 h1 h1) h2 
(* h3 h3) h5 (* h6 h6 h6)) (* 8 (* h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 116 (* h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 672 (* h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 2052 (* h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 3712 (* h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 
j2)) (* 4188 (* h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 2976 
(* h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 1292 (* h1 h1 h1) h2 
(* h3 h3) (* h6 h6 h6 h6) (* j2 j2)) (* 312 (* h1 h1 h1) h2 (* h3 h3) (* h6 h6 
h6 h6) j2) (* 32 (* h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6 h6)) (* 138 (* h1 h1 h1) 
h2 h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1438 (* h1 h1 h1) h2 
h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 5368 (* h1 h1 h1) h2 h3 (* 
h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 10076 (* h1 h1 h1) h2 h3 (* h4 h4 h4)
 (* h5 h5) (* j2 j2 j2 j2)) (* 10578 (* h1 h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) 
(* j2 j2 j2)) (* 6286 (* h1 h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 
1964 (* h1 h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) j2) (* 248 (* h1 h1 h1) h2 h3 (* 
h4 h4 h4) (* h5 h5)) (* 108 (* h1 h1 h1) h2 h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2
 j2 j2 j2)) (* 636 (* h1 h1 h1) h2 h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) 
(* 1584 (* h1 h1 h1) h2 h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 2160 (* h1 
h1 h1) h2 h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 1740 (* h1 h1 h1) h2 h3 (* 
h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 828 (* h1 h1 h1) h2 h3 (* h4 h4 h4) h5 h6 (* j2
 j2)) (* 216 (* h1 h1 h1) h2 h3 (* h4 h4 h4) h5 h6 j2) (* 24 (* h1 h1 h1) h2 h3 
(* h4 h4 h4) h5 h6) (* 36 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 622 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2
 j2 j2 j2)) (* 3950 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 
j2)) (* 11996 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 
20008 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 19374 (* h1 
h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 10830 (* h1 h1 h1) h2 h3 
(* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 3224 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5 
h5) j2) (* 392 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5)) (* 108 (* h1 h1 h1) h2
 h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1824 (* h1 h1 h1) h2 
h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 11024 (* h1 h1 h1) h2 h3 
(* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 32660 (* h1 h1 h1) h2 h3 (* h4 
h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 54156 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5
 h5) h6 (* j2 j2 j2 j2)) (* 52784 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) h6 (* 
j2 j2 j2)) (* 29936 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 9084
 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) h6 j2) (* 1128 (* h1 h1 h1) h2 h3 (* h4 
h4) (* h5 h5) h6) (* 60 (* h1 h1 h1) h2 h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2
 j2 j2 j2 j2)) (* 776 (* h1 h1 h1) h2 h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 3392 (* h1 h1 h1) h2 h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 7524 (* h1 h1 h1) h2 h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
9700 (* h1 h1 h1) h2 h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 7600 (* h1 h1
 h1) h2 h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 3576 (* h1 h1 h1) h2 h3 (* h4
 h4) h5 (* h6 h6) (* j2 j2)) (* 932 (* h1 h1 h1) h2 h3 (* h4 h4) h5 (* h6 h6) j2
) (* 104 (* h1 h1 h1) h2 h3 (* h4 h4) h5 (* h6 h6)) (* 10 (* h1 h1 h1) h2 h3 h4 
(* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 154 (* h1 h1 h1) h2 h3 h4 (* h5 
h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 890 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5 h5)
 (* j2 j2 j2 j2 j2 j2)) (* 2502 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5 h5) (* j2 j2 
j2 j2 j2)) (* 3908 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 
3576 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2)) (* 1904 (* h1 h1 h1) h2
 h3 h4 (* h5 h5 h5 h5) (* j2 j2)) (* 544 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5 h5) 
j2) (* 64 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5 h5)) (* 4 (* h1 h1 h1) h2 h3 h4 (* 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 248 (* h1 h1 h1) h2 h3 h4 (* h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2990 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5
) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 15464 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 41936 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2)) (* 65520 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 
61030 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 33344 (* h1 h1 h1) 
h2 h3 h4 (* h5 h5 h5) h6 (* j2 j2)) (* 9800 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5) 
h6 j2) (* 1184 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5) h6) (* 26 (* h1 h1 h1) h2 h3 
h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 600 (* h1 h1 h1) h2 h3
 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 5336 (* h1 h1 h1) h2 h3 
h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 23870 (* h1 h1 h1) h2 h3 h4 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 60114 (* h1 h1 h1) h2 h3 h4 (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 90500 (* h1 h1 h1) h2 h3 h4 (* h5 h5) (* h6
 h6) (* j2 j2 j2 j2)) (* 82988 (* h1 h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6) (* j2 
j2 j2)) (* 45246 (* h1 h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 13392 
(* h1 h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6) j2) (* 1640 (* h1 h1 h1) h2 h3 h4 (* 
h5 h5) (* h6 h6)) (* 8 (* h1 h1 h1) h2 h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 196 (* h1 h1 h1) h2 h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 1544 (* h1 h1 h1) h2 h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 5632 (* h1 h1 h1) h2 h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 11444 
(* h1 h1 h1) h2 h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 14068 (* h1 h1 h1) 
h2 h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 10736 (* h1 h1 h1) h2 h3 h4 h5 (* 
h6 h6 h6) (* j2 j2 j2)) (* 4984 (* h1 h1 h1) h2 h3 h4 h5 (* h6 h6 h6) (* j2 j2))
 (* 1292 (* h1 h1 h1) h2 h3 h4 h5 (* h6 h6 h6) j2) (* 144 (* h1 h1 h1) h2 h3 h4 
h5 (* h6 h6 h6)) (* 40 (* h1 h1 h1) h2 h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 496 (* h1 h1 h1) h2 h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)
) (* 2352 (* h1 h1 h1) h2 h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 5824 
(* h1 h1 h1) h2 h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 8424 (* h1 h1 h1) 
h2 h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 7376 (* h1 h1 h1) h2 h3 (* h5 h5 h5
 h5) h6 (* j2 j2 j2)) (* 3840 (* h1 h1 h1) h2 h3 (* h5 h5 h5 h5) h6 (* j2 j2)) 
(* 1088 (* h1 h1 h1) h2 h3 (* h5 h5 h5 h5) h6 j2) (* 128 (* h1 h1 h1) h2 h3 (* 
h5 h5 h5 h5) h6) (* 20 (* h1 h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 412 (* h1 h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2
 j2 j2 j2 j2)) (* 3328 (* h1 h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 13952 (* h1 h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 33612 (* h1 h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
48924 (* h1 h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 43600 (* h1 
h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 23160 (* h1 h1 h1) h2 h3 
(* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 6688 (* h1 h1 h1) h2 h3 (* h5 h5 h5) (* h6 
h6) j2) (* 800 (* h1 h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6)) (* 26 (* h1 h1 h1) h2 
h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 484 (* h1 h1 h1) h2
 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3582 (* h1 h1 h1) h2 
h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 14036 (* h1 h1 h1) h2 h3 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 32314 (* h1 h1 h1) h2 h3 (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 45780 (* h1 h1 h1) h2 h3 (* h5 h5) (* h6
 h6 h6) (* j2 j2 j2 j2)) (* 40274 (* h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6) (* 
j2 j2 j2)) (* 21348 (* h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 6204
 (* h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6) j2) (* 752 (* h1 h1 h1) h2 h3 (* h5 
h5) (* h6 h6 h6)) (* 8 (* h1 h1 h1) h2 h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 136 (* h1 h1 h1) h2 h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 876 (* h1 h1 h1) h2 h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 2876 (* h1 h1 h1) h2 h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 5504 (* 
h1 h1 h1) h2 h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 6528 (* h1 h1 h1) h2 
h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 4876 (* h1 h1 h1) h2 h3 h5 (* h6 h6 h6
 h6) (* j2 j2 j2)) (* 2236 (* h1 h1 h1) h2 h3 h5 (* h6 h6 h6 h6) (* j2 j2)) (* 
576 (* h1 h1 h1) h2 h3 h5 (* h6 h6 h6 h6) j2) (* 64 (* h1 h1 h1) h2 h3 h5 (* h6 
h6 h6 h6)) (* 18 (* h1 h1 h1) h2 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2)) (* 138 (* h1 h1 h1) h2 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
444 (* h1 h1 h1) h2 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 780 (* h1 
h1 h1) h2 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 810 (* h1 h1 h1) h2 (* 
h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 498 (* h1 h1 h1) h2 (* h4 h4 h4) (* h5 
h5) h6 (* j2 j2)) (* 168 (* h1 h1 h1) h2 (* h4 h4 h4) (* h5 h5) h6 j2) (* 24 (* 
h1 h1 h1) h2 (* h4 h4 h4) (* h5 h5) h6) (* 12 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5
 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 152 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 756 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2)) (* 2000 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2)) (* 3140 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 
j2)) (* 3032 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 1772 (* 
h1 h1 h1) h2 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 576 (* h1 h1 h1) h2 (* h4 
h4) (* h5 h5 h5) h6 j2) (* 80 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5 h5) h6) (* 12 
(* h1 h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
166 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
866 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2364
 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 3800 (* h1
 h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 3742 (* h1 h1 h1) 
h2 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 2226 (* h1 h1 h1) h2 (* h4 h4)
 (* h5 h5) (* h6 h6) (* j2 j2)) (* 736 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5) (* h6
 h6) j2) (* 104 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 h6)) (* 6 (* h1 h1 h1)
 h2 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 76 (* h1 h1 h1) h2 h4 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 372 (* h1 h1 h1) h2 h4 (* h5 h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 960 (* h1 h1 h1) h2 h4 (* h5 h5 h5 h5) h6 
(* j2 j2 j2 j2 j2)) (* 1462 (* h1 h1 h1) h2 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2
)) (* 1364 (* h1 h1 h1) h2 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 768 (* h1 h1 
h1) h2 h4 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 240 (* h1 h1 h1) h2 h4 (* h5 h5 h5 h5
) h6 j2) (* 32 (* h1 h1 h1) h2 h4 (* h5 h5 h5 h5) h6) (* 4 (* h1 h1 h1) h2 h4 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 84 (* h1 h1 h1) h2 h4 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 670 (* h1 h1 h1) h2 h4 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2742 (* h1 h1 h1) h2 h4 (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6552 (* h1 h1 h1) h2 h4 (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 9704 (* h1 h1 h1) h2 h4 (* h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2)) (* 9054 (* h1 h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 
j2)) (* 5190 (* h1 h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 1672 (* h1 
h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6) j2) (* 232 (* h1 h1 h1) h2 h4 (* h5 h5 h5) 
(* h6 h6)) (* 2 (* h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 46 (* h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 384 (* h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2
)) (* 1612 (* h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
3914 (* h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 5862 (* h1
 h1 h1) h2 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 5516 (* h1 h1 h1) h2 h4
 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 3184 (* h1 h1 h1) h2 h4 (* h5 h5) (* h6
 h6 h6) (* j2 j2)) (* 1032 (* h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6 h6) j2) (* 144 
(* h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6 h6)) (* 2 (* h1 h1 h1) h2 (* h5 h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 36 (* h1 h1 h1) h2 (* h5 h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 260 (* h1 h1 h1) h2 (* h5 h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 992 (* h1 h1 h1) h2 (* h5 h5 h5 h5) (* h6
 h6) (* j2 j2 j2 j2 j2 j2)) (* 2242 (* h1 h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* 3164 (* h1 h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2)) (* 2824 (* h1 h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 1552 
(* h1 h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 480 (* h1 h1 h1) h2 (* 
h5 h5 h5 h5) (* h6 h6) j2) (* 64 (* h1 h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6)) (* 4
 (* h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 70
 (* h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 498 
(* h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1900 (* 
h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4344 (* h1 h1 
h1) h2 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 6254 (* h1 h1 h1) h2 (* 
h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 5730 (* h1 h1 h1) h2 (* h5 h5 h5) (* 
h6 h6 h6) (* j2 j2 j2)) (* 3248 (* h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6) (* j2 
j2)) (* 1040 (* h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6) j2) (* 144 (* h1 h1 h1) 
h2 (* h5 h5 h5) (* h6 h6 h6)) (* 2 (* h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 34 (* h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 236 (* h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6 h6) (* j2
 j2 j2 j2 j2 j2 j2)) (* 884 (* h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 1994 (* h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 
j2)) (* 2842 (* h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 2584 
(* h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 1456 (* h1 h1 h1) h2 
(* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 464 (* h1 h1 h1) h2 (* h5 h5) (* h6 h6 
h6 h6) j2) (* 64 (* h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6 h6)) (* 70 (* h1 h1 h1) 
(* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1143 (* h1 h1 h1) 
(* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 4516 (* h1 h1 h1) (* 
h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 8353 (* h1 h1 h1) (* h3 h3 
h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 8620 (* h1 h1 h1) (* h3 h3 h3 h3) (* 
h4 h4) h5 (* j2 j2 j2 j2)) (* 5257 (* h1 h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 (* 
j2 j2 j2)) (* 1884 (* h1 h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2)) (* 367 
(* h1 h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 j2) (* 30 (* h1 h1 h1) (* h3 h3 h3 h3)
 (* h4 h4) h5) (* 100 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 1630 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 
j2 j2 j2)) (* 6406 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 
j2)) (* 11768 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 
12044 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 7274 (* h1 
h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 2578 (* h1 h1 h1) (* h3 h3 
h3 h3) h4 (* h5 h5) (* j2 j2)) (* 496 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) 
j2) (* 40 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5)) (* 20 (* h1 h1 h1) (* h3 h3
 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 558 (* h1 h1 h1) (* h3 h3 h3
 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 5070 (* h1 h1 h1) (* h3 h3 h3 h3) 
h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 17330 (* h1 h1 h1) (* h3 h3 h3 h3) h4 h5 
h6 (* j2 j2 j2 j2 j2 j2)) (* 30126 (* h1 h1 h1) (* h3 h3 h3 h3) h4 h5 h6 (* j2 
j2 j2 j2 j2)) (* 30078 (* h1 h1 h1) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) 
(* 17986 (* h1 h1 h1) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 6366 (* h1 h1 h1
) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2)) (* 1230 (* h1 h1 h1) (* h3 h3 h3 h3) h4 h5
 h6 j2) (* 100 (* h1 h1 h1) (* h3 h3 h3 h3) h4 h5 h6) (* 200 (* h1 h1 h1) (* h3 
h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3260 (* h1 h1 h1) (* h3 
h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 12812 (* h1 h1 h1) (* h3 h3 
h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 23536 (* h1 h1 h1) (* h3 h3 h3 h3)
 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 24088 (* h1 h1 h1) (* h3 h3 h3 h3) (* h5 h5
) h6 (* j2 j2 j2 j2)) (* 14548 (* h1 h1 h1) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 
j2 j2)) (* 5156 (* h1 h1 h1) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2)) (* 992 (* 
h1 h1 h1) (* h3 h3 h3 h3) (* h5 h5) h6 j2) (* 80 (* h1 h1 h1) (* h3 h3 h3 h3) 
(* h5 h5) h6) (* 40 (* h1 h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 836 (* h1 h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 5568 (* h1 h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 16596 (* h1 h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)
) (* 26840 (* h1 h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
25676 (* h1 h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 14944 (* h1 
h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 5196 (* h1 h1 h1) (* h3 h3 
h3 h3) h5 (* h6 h6) (* j2 j2)) (* 992 (* h1 h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6) 
j2) (* 80 (* h1 h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6)) (* 105 (* h1 h1 h1) (* h3 
h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1277 (* h1 h1 h1) (* h3 
h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 5064 (* h1 h1 h1) (* h3 h3 
h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 10008 (* h1 h1 h1) (* h3 h3 h3) 
(* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 11317 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4 
h4) h5 (* j2 j2 j2 j2)) (* 7653 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 
j2 j2)) (* 3054 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2)) (* 662 (* 
h1 h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 j2) (* 60 (* h1 h1 h1) (* h3 h3 h3) (* h4
 h4 h4) h5) (* 5 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2
 j2 j2 j2 j2)) (* 337 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 3609 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 
j2 j2 j2 j2 j2)) (* 14175 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2
 j2 j2 j2 j2)) (* 28304 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 
j2 j2 j2)) (* 32391 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2
)) (* 22071 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 8815 
(* h1 h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 1899 (* h1 h1 h1) 
(* h3 h3 h3) (* h4 h4) (* h5 h5) j2) (* 170 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) 
(* h5 h5)) (* 30 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 817 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 6947 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 
j2)) (* 24680 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) 
(* 46382 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 51013 
(* h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 33919 (* h1 h1 h1)
 (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 13390 (* h1 h1 h1) (* h3 h3 h3) 
(* h4 h4) h5 h6 (* j2 j2)) (* 2882 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 h6 j2)
 (* 260 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 h6) (* 200 (* h1 h1 h1) (* h3 h3 
h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1960 (* h1 h1 h1) (* h3 h3 
h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 7322 (* h1 h1 h1) (* h3 h3 h3) 
h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 14218 (* h1 h1 h1) (* h3 h3 h3) h4 (* 
h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 15986 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5)
 (* j2 j2 j2 j2)) (* 10750 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2
)) (* 4244 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2)) (* 904 (* h1 h1 
h1) (* h3 h3 h3) h4 (* h5 h5 h5) j2) (* 80 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5
 h5)) (* 65 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2
 j2)) (* 1536 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 12769 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)
) (* 46171 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
88842 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 99698 (* 
h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 67163 (* h1 h1 h1) 
(* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 26637 (* h1 h1 h1) (* h3 h3 h3) h4
 (* h5 h5) h6 (* j2 j2)) (* 5713 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) h6 j2) 
(* 510 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) h6) (* 90 (* h1 h1 h1) (* h3 h3 h3
) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1716 (* h1 h1 h1) (* h3 h3 
h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 11902 (* h1 h1 h1) (* h3 h3 
h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 38592 (* h1 h1 h1) (* h3 h3 h3)
 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 69090 (* h1 h1 h1) (* h3 h3 h3) h4 h5
 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 73820 (* h1 h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6
) (* j2 j2 j2 j2)) (* 48186 (* h1 h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 
j2)) (* 18792 (* h1 h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 4012 (* h1
 h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6) j2) (* 360 (* h1 h1 h1) (* h3 h3 h3) h4 h5 
(* h6 h6)) (* 400 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 3920 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2)) (* 14644 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 28436 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 31972 
(* h1 h1 h1) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 21500 (* h1 h1 h1)
 (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 8488 (* h1 h1 h1) (* h3 h3 h3) 
(* h5 h5 h5) h6 (* j2 j2)) (* 1808 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5 h5) h6 j2)
 (* 160 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5 h5) h6) (* 110 (* h1 h1 h1) (* h3 h3 
h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1724 (* h1 h1 h1) (* 
h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 11102 (* h1 h1 h1)
 (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 35642 (* h1 h1 h1
) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 64468 (* h1 h1 h1) 
(* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 69832 (* h1 h1 h1) (* h3
 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 46042 (* h1 h1 h1) (* h3 h3 h3) 
(* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 18014 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5) 
(* h6 h6) (* j2 j2)) (* 3830 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6) j2) 
(* 340 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6)) (* 60 (* h1 h1 h1) (* h3 
h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1004 (* h1 h1 h1) (* 
h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6232 (* h1 h1 h1) (* 
h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 18976 (* h1 h1 h1) (* h3 
h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 32716 (* h1 h1 h1) (* h3 h3 h3)
 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 34124 (* h1 h1 h1) (* h3 h3 h3) h5 (* h6
 h6 h6) (* j2 j2 j2 j2)) (* 21920 (* h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6) (* 
j2 j2 j2)) (* 8456 (* h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 1792 
(* h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6) j2) (* 160 (* h1 h1 h1) (* h3 h3 h3) 
h5 (* h6 h6 h6)) (* 105 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2
 j2 j2 j2)) (* 612 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 
j2)) (* 1503 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 
2010 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 1575 (* h1 h1
 h1) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2)) (* 720 (* h1 h1 h1) (* h3 h3) 
(* h4 h4 h4 h4) h5 (* j2 j2)) (* 177 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4 h4) h5 
j2) (* 18 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4 h4) h5) (* 80 (* h1 h1 h1) (* h3 h3
) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1112 (* h1 h1 h1) (* h3
 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 4932 (* h1 h1 h1) (* h3
 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 10885 (* h1 h1 h1) (* h3 
h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 13774 (* h1 h1 h1) (* h3 h3) 
(* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 10446 (* h1 h1 h1) (* h3 h3) (* h4 h4
 h4) (* h5 h5) (* j2 j2 j2)) (* 4676 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 
h5) (* j2 j2)) (* 1133 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) j2) (* 114 
(* h1 h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5)) (* 65 (* h1 h1 h1) (* h3 h3) (* 
h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 971 (* h1 h1 h1) (* h3 h3) (* h4
 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 4383 (* h1 h1 h1) (* h3 h3) (* h4 h4 
h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 9727 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 
h6 (* j2 j2 j2 j2 j2)) (* 12325 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 
j2 j2 j2)) (* 9345 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 
4181 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2)) (* 1013 (* h1 h1 h1) 
(* h3 h3) (* h4 h4 h4) h5 h6 j2) (* 102 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 
h6) (* 5 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 232 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 2122 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 
j2 j2 j2)) (* 8117 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 
j2 j2)) (* 16592 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2
)) (* 19963 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 
14553 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 6292 (* h1 
h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 1476 (* h1 h1 h1) (* h3 h3
) (* h4 h4) (* h5 h5 h5) j2) (* 144 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5
)) (* 40 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 846 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 6877 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2)) (* 25573 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2
 j2 j2)) (* 51972 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 
j2)) (* 62816 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 
46325 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 20373 (* h1
 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 4882 (* h1 h1 h1) (* h3 
h3) (* h4 h4) (* h5 h5) h6 j2) (* 488 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5)
 h6) (* 10 (* h1 h1 h1) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2
 j2 j2)) (* 339 (* h1 h1 h1) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 3004 (* h1 h1 h1) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 11353 (* h1 h1 h1) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2
 j2 j2)) (* 23082 (* h1 h1 h1) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 27785 (* h1 h1 h1) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 
20384 (* h1 h1 h1) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 8919 (* h1 
h1 h1) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 2128 (* h1 h1 h1) (* h3 h3
) (* h4 h4) h5 (* h6 h6) j2) (* 212 (* h1 h1 h1) (* h3 h3) (* h4 h4) h5 (* h6 h6
)) (* 50 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 540 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
2108 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 4240 
(* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 4962 (* h1 h1 
h1) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 3508 (* h1 h1 h1) (* h3 h3)
 h4 (* h5 h5 h5 h5) (* j2 j2 j2)) (* 1472 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5 
h5) (* j2 j2)) (* 336 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) j2) (* 32 (* h1 
h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5)) (* 45 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5
) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1013 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 7578 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 26727 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5)
 h6 (* j2 j2 j2 j2 j2 j2)) (* 52462 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2)) (* 61698 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 
j2 j2)) (* 44367 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 
19022 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2)) (* 4440 (* h1 h1 h1) 
(* h3 h3) h4 (* h5 h5 h5) h6 j2) (* 432 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) 
h6) (* 120 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2
 j2 j2)) (* 1968 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 12778 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 41989 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2
 j2 j2 j2)) (* 79374 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2)) (* 91670 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) 
(* 65618 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 28293 
(* h1 h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 6694 (* h1 h1 h1) 
(* h3 h3) h4 (* h5 h5) (* h6 h6) j2) (* 664 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5) 
(* h6 h6)) (* 30 (* h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 562 (* h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 3790 (* h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 12558 (* h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 23702 (* h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 27230 
(* h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 19362 (* h1 h1 h1)
 (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 8290 (* h1 h1 h1) (* h3 h3) h4 h5
 (* h6 h6 h6) (* j2 j2)) (* 1948 (* h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6) j2) 
(* 192 (* h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6)) (* 100 (* h1 h1 h1) (* h3 h3) 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1080 (* h1 h1 h1) (* h3 h3) 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 4216 (* h1 h1 h1) (* h3 h3) (* 
h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 8480 (* h1 h1 h1) (* h3 h3) (* h5 h5 
h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 9924 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5 h5) h6 
(* j2 j2 j2 j2)) (* 7016 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2))
 (* 2944 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 672 (* h1 h1 h1
) (* h3 h3) (* h5 h5 h5 h5) h6 j2) (* 64 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5 h5) 
h6) (* 70 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 1098 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 6668 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 20986 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2
 j2 j2)) (* 38556 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 43544 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 
30522 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 12876 (* h1
 h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 2976 (* h1 h1 h1) (* h3 
h3) (* h5 h5 h5) (* h6 h6) j2) (* 288 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 
h6)) (* 80 (* h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2
 j2 j2)) (* 1192 (* h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 6944 (* h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2
 j2 j2 j2)) (* 21142 (* h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 37940 (* h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2
 j2)) (* 42268 (* h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) 
(* 29504 (* h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 12502 
(* h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 2924 (* h1 h1 h1) 
(* h3 h3) (* h5 h5) (* h6 h6 h6) j2) (* 288 (* h1 h1 h1) (* h3 h3) (* h5 h5) (* 
h6 h6 h6)) (* 20 (* h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 288 (* h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 1652 (* h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 4976 (* h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 8844 (* h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 9760 
(* h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 6748 (* h1 h1 h1) 
(* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 2832 (* h1 h1 h1) (* h3 h3) h5 (* 
h6 h6 h6 h6) (* j2 j2)) (* 656 (* h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6 h6) j2) (* 
64 (* h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6 h6)) (* 45 (* h1 h1 h1) h3 (* h4 h4 h4 
h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 273 (* h1 h1 h1) h3 (* h4 h4 h4 h4) 
(* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 702 (* h1 h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5
) (* j2 j2 j2 j2 j2)) (* 990 (* h1 h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 
j2 j2)) (* 825 (* h1 h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 405 
(* h1 h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2)) (* 108 (* h1 h1 h1) h3 (* 
h4 h4 h4 h4) (* h5 h5) j2) (* 12 (* h1 h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5)) (* 
30 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 332
 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1378 (* 
h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 3000 (* h1 h1 
h1) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 3850 (* h1 h1 h1) h3 (* 
h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 3020 (* h1 h1 h1) h3 (* h4 h4 h4) (* 
h5 h5 h5) (* j2 j2 j2)) (* 1422 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 
j2)) (* 368 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) j2) (* 40 (* h1 h1 h1) h3 
(* h4 h4 h4) (* h5 h5 h5)) (* 30 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 457 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2)) (* 2143 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 
j2 j2 j2 j2)) (* 4986 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 
j2)) (* 6680 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 5405 
(* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 2607 (* h1 h1 h1) h3 
(* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 688 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 
h5) h6 j2) (* 76 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) h6) (* 15 (* h1 h1 h1) 
h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 166 (* h1 h1 h1) h3
 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 674 (* h1 h1 h1) h3 (* 
h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1424 (* h1 h1 h1) h3 (* h4 h4) 
(* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 1767 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 
h5 h5) (* j2 j2 j2 j2)) (* 1338 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 
j2 j2)) (* 608 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 152 (* h1
 h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) j2) (* 16 (* h1 h1 h1) h3 (* h4 h4) (* h5 
h5 h5 h5)) (* 10 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 254 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 2035 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2)) (* 7539 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 15556 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 19400 
(* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 14979 (* h1 h1 h1)
 h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 6995 (* h1 h1 h1) h3 (* h4 h4) 
(* h5 h5 h5) h6 (* j2 j2)) (* 1804 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) h6 j2)
 (* 196 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) h6) (* 5 (* h1 h1 h1) h3 (* h4 h4
) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 167 (* h1 h1 h1) h3 (* 
h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1526 (* h1 h1 h1) h3 
(* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 6024 (* h1 h1 h1) h3 
(* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 12901 (* h1 h1 h1) h3 
(* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 16495 (* h1 h1 h1) h3 (* h4
 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 12972 (* h1 h1 h1) h3 (* h4 h4) (* 
h5 h5) (* h6 h6) (* j2 j2 j2)) (* 6146 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5) (* h6
 h6) (* j2 j2)) (* 1604 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5) (* h6 h6) j2) (* 176
 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5) (* h6 h6)) (* 5 (* h1 h1 h1) h3 h4 (* h5 h5
 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 112 (* h1 h1 h1) h3 h4 (* h5 h5 h5
 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 854 (* h1 h1 h1) h3 h4 (* h5 h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 3044 (* h1 h1 h1) h3 h4 (* h5 h5 h5 h5) h6 (* j2
 j2 j2 j2 j2 j2)) (* 6053 (* h1 h1 h1) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 
j2)) (* 7276 (* h1 h1 h1) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 5416 (* 
h1 h1 h1) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 2440 (* h1 h1 h1) h3 h4 (* 
h5 h5 h5 h5) h6 (* j2 j2)) (* 608 (* h1 h1 h1) h3 h4 (* h5 h5 h5 h5) h6 j2) (* 
64 (* h1 h1 h1) h3 h4 (* h5 h5 h5 h5) h6) (* 30 (* h1 h1 h1) h3 h4 (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 547 (* h1 h1 h1) h3 h4 (* h5 h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3739 (* h1 h1 h1) h3 h4 (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 12820 (* h1 h1 h1) h3 h4 (* h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 25364 (* h1 h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6)
 (* j2 j2 j2 j2 j2)) (* 30875 (* h1 h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2
 j2 j2)) (* 23507 (* h1 h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 
10894 (* h1 h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 2800 (* h1 h1 h1) 
h3 h4 (* h5 h5 h5) (* h6 h6) j2) (* 304 (* h1 h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6
)) (* 15 (* h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2
)) (* 291 (* h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2))
 (* 2054 (* h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
7166 (* h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 14331 
(* h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 17575 (* h1 h1 
h1) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 13456 (* h1 h1 h1) h3 h4 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 6264 (* h1 h1 h1) h3 h4 (* h5 h5) (* h6 
h6 h6) (* j2 j2)) (* 1616 (* h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6) j2) (* 176 
(* h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6)) (* 10 (* h1 h1 h1) h3 (* h5 h5 h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 164 (* h1 h1 h1) h3 (* h5 h5 h5 h5
) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1044 (* h1 h1 h1) h3 (* h5 h5 h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3392 (* h1 h1 h1) h3 (* h5 h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6410 (* h1 h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* 7484 (* h1 h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2)) (* 5480 (* h1 h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 2448 
(* h1 h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 608 (* h1 h1 h1) h3 (* 
h5 h5 h5 h5) (* h6 h6) j2) (* 64 (* h1 h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6)) (* 
20 (* h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
318 (* h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
1994 (* h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 6508
 (* h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 12504 (* h1
 h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 14950 (* h1 h1 h1) 
h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 11258 (* h1 h1 h1) h3 (* h5 h5 
h5) (* h6 h6 h6) (* j2 j2 j2)) (* 5184 (* h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6)
 (* j2 j2)) (* 1328 (* h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6) j2) (* 144 (* h1 
h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6)) (* 10 (* h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 154 (* h1 h1 h1) h3 (* h5 h5) (* h6 h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 940 (* h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6
 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3012 (* h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2)) (* 5714 (* h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 
j2 j2 j2 j2)) (* 6770 (* h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2))
 (* 5064 (* h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 2320 (* h1 
h1 h1) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 592 (* h1 h1 h1) h3 (* h5 h5) 
(* h6 h6 h6 h6) j2) (* 64 (* h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6 h6)) (* 160 (* 
h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2 j2)) (* 1104 (* h1 h1) (* 
h2 h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2)) (* 2016 (* h1 h1) (* h2 h2 h2 h2) 
(* h3 h3 h3) h5 (* j2 j2 j2)) (* 1520 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h5 
(* j2 j2)) (* 512 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h5 j2) (* 64 (* h1 h1) 
(* h2 h2 h2 h2) (* h3 h3 h3) h5) (* 64 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h6
 (* j2 j2 j2 j2 j2 j2)) (* 512 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h6 (* j2 
j2 j2 j2 j2)) (* 1296 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2 j2))
 (* 1520 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2)) (* 912 (* h1 h1
) (* h2 h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2)) (* 272 (* h1 h1) (* h2 h2 h2 h2) 
(* h3 h3 h3) h6 j2) (* 32 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h6) (* 16 (* h1
 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 416 (* h1 h1) (* 
h2 h2 h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 2080 (* h1 h1) (* h2 h2 h2 
h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2)) (* 3968 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3)
 h4 h5 (* j2 j2 j2)) (* 3440 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* j2 j2)
) (* 1344 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h5 j2) (* 192 (* h1 h1) (* h2 
h2 h2 h2) (* h3 h3) h4 h5) (* 96 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h6 (* j2
 j2 j2 j2 j2 j2)) (* 656 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2 
j2 j2)) (* 1680 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 
2128 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2)) (* 1424 (* h1 h1) 
(* h2 h2 h2 h2) (* h3 h3) h4 h6 (* j2 j2)) (* 480 (* h1 h1) (* h2 h2 h2 h2) (* 
h3 h3) h4 h6 j2) (* 64 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h6) (* 320 (* h1 
h1) (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 1488 (* h1 h1) 
(* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 2704 (* h1 h1) (* h2 h2 
h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2)) (* 2304 (* h1 h1) (* h2 h2 h2 h2) (* h3
 h3) (* h5 h5) (* j2 j2)) (* 896 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) 
j2) (* 128 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h5 h5)) (* 176 (* h1 h1) (* h2
 h2 h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 1136 (* h1 h1) (* h2 h2 h2 
h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 3264 (* h1 h1) (* h2 h2 h2 h2) (* h3 
h3) h5 h6 (* j2 j2 j2 j2)) (* 4848 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 h6 (* 
j2 j2 j2)) (* 3728 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 h6 (* j2 j2)) (* 1376 
(* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 h6 j2) (* 192 (* h1 h1) (* h2 h2 h2 h2) 
(* h3 h3) h5 h6) (* 96 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2
 j2 j2 j2)) (* 656 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 1680 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 
2128 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2)) (* 1424 (* h1 
h1) (* h2 h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2)) (* 480 (* h1 h1) (* h2 h2 h2 
h2) (* h3 h3) (* h6 h6) j2) (* 64 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h6 h6))
 (* 16 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 304 
(* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 1376 (* h1 h1) 
(* h2 h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2)) (* 2672 (* h1 h1) (* h2 h2 h2 
h2) h3 h4 (* h5 h5) (* j2 j2 j2)) (* 2544 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h5 
h5) (* j2 j2)) (* 1152 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h5 h5) j2) (* 192 (* 
h1 h1) (* h2 h2 h2 h2) h3 h4 (* h5 h5)) (* 128 (* h1 h1) (* h2 h2 h2 h2) h3 h4 
h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 864 (* h1 h1) (* h2 h2 h2 h2) h3 h4 h5 h6 (* j2 
j2 j2 j2 j2)) (* 2272 (* h1 h1) (* h2 h2 h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2)) (* 
3040 (* h1 h1) (* h2 h2 h2 h2) h3 h4 h5 h6 (* j2 j2 j2)) (* 2208 (* h1 h1) (* h2
 h2 h2 h2) h3 h4 h5 h6 (* j2 j2)) (* 832 (* h1 h1) (* h2 h2 h2 h2) h3 h4 h5 h6 
j2) (* 128 (* h1 h1) (* h2 h2 h2 h2) h3 h4 h5 h6) (* 32 (* h1 h1) (* h2 h2 h2 h2
) h3 h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 176 (* h1 h1) (* h2 h2 h2 h2) h3 h4 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 400 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h6 h6) 
(* j2 j2 j2 j2)) (* 480 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2)) 
(* 320 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h6 h6) (* j2 j2)) (* 112 (* h1 h1) (* 
h2 h2 h2 h2) h3 h4 (* h6 h6) j2) (* 16 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h6 h6)
) (* 80 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 432 (* 
h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 880 (* h1 h1) (* h2 
h2 h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2)) (* 848 (* h1 h1) (* h2 h2 h2 h2) h3 (* 
h5 h5 h5) (* j2 j2)) (* 384 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5 h5) j2) (* 64 
(* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5 h5)) (* 112 (* h1 h1) (* h2 h2 h2 h2) h3 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 816 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5
) h6 (* j2 j2 j2 j2 j2)) (* 2352 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) h6 (* j2
 j2 j2 j2)) (* 3504 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2)) (* 
2848 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) h6 (* j2 j2)) (* 1184 (* h1 h1) (* 
h2 h2 h2 h2) h3 (* h5 h5) h6 j2) (* 192 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) 
h6) (* 128 (* h1 h1) (* h2 h2 h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
832 (* h1 h1) (* h2 h2 h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2128 (* h1 
h1) (* h2 h2 h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 2784 (* h1 h1) (* h2 h2 
h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2)) (* 1984 (* h1 h1) (* h2 h2 h2 h2) h3 h5 (* 
h6 h6) (* j2 j2)) (* 736 (* h1 h1) (* h2 h2 h2 h2) h3 h5 (* h6 h6) j2) (* 112 
(* h1 h1) (* h2 h2 h2 h2) h3 h5 (* h6 h6)) (* 32 (* h1 h1) (* h2 h2 h2 h2) h3 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 176 (* h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6
 h6) (* j2 j2 j2 j2 j2)) (* 400 (* h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6 h6) (* j2 
j2 j2 j2)) (* 480 (* h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2)) (* 320
 (* h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6 h6) (* j2 j2)) (* 112 (* h1 h1) (* h2 h2 
h2 h2) h3 (* h6 h6 h6) j2) (* 16 (* h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6 h6)) (* 
32 (* h1 h1) (* h2 h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 256 (* h1
 h1) (* h2 h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 832 (* h1 h1) (* h2 
h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 1408 (* h1 h1) (* h2 h2 h2 h2) h4 
(* h5 h5) h6 (* j2 j2 j2)) (* 1312 (* h1 h1) (* h2 h2 h2 h2) h4 (* h5 h5) h6 (* 
j2 j2)) (* 640 (* h1 h1) (* h2 h2 h2 h2) h4 (* h5 h5) h6 j2) (* 128 (* h1 h1) 
(* h2 h2 h2 h2) h4 (* h5 h5) h6) (* 16 (* h1 h1) (* h2 h2 h2 h2) h4 h5 (* h6 h6)
 (* j2 j2 j2 j2 j2 j2)) (* 112 (* h1 h1) (* h2 h2 h2 h2) h4 h5 (* h6 h6) (* j2 
j2 j2 j2 j2)) (* 320 (* h1 h1) (* h2 h2 h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) 
(* 480 (* h1 h1) (* h2 h2 h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 400 (* h1 h1) 
(* h2 h2 h2 h2) h4 h5 (* h6 h6) (* j2 j2)) (* 176 (* h1 h1) (* h2 h2 h2 h2) h4 
h5 (* h6 h6) j2) (* 32 (* h1 h1) (* h2 h2 h2 h2) h4 h5 (* h6 h6)) (* 16 (* h1 h1
) (* h2 h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 128 (* h1 h1) (* h2 
h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 416 (* h1 h1) (* h2 h2 h2 h2) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 704 (* h1 h1) (* h2 h2 h2 h2) (* h5 h5 h5) 
h6 (* j2 j2 j2)) (* 656 (* h1 h1) (* h2 h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2)) (* 
320 (* h1 h1) (* h2 h2 h2 h2) (* h5 h5 h5) h6 j2) (* 64 (* h1 h1) (* h2 h2 h2 h2
) (* h5 h5 h5) h6) (* 32 (* h1 h1) (* h2 h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 240 (* h1 h1) (* h2 h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2)) (* 736 (* h1 h1) (* h2 h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) 
(* 1184 (* h1 h1) (* h2 h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 1056 (* 
h1 h1) (* h2 h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 j2)) (* 496 (* h1 h1) (* h2 h2 
h2 h2) (* h5 h5) (* h6 h6) j2) (* 96 (* h1 h1) (* h2 h2 h2 h2) (* h5 h5) (* h6 
h6)) (* 16 (* h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
112 (* h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 320 (* h1 
h1) (* h2 h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 480 (* h1 h1) (* h2 h2 
h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 400 (* h1 h1) (* h2 h2 h2 h2) h5 (* h6 
h6 h6) (* j2 j2)) (* 176 (* h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6 h6) j2) (* 32 (* 
h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6 h6)) (* 160 (* h1 h1) (* h2 h2 h2) (* h3 h3 
h3 h3) h5 (* j2 j2 j2 j2 j2 j2)) (* 1184 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) 
h5 (* j2 j2 j2 j2 j2)) (* 2568 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* j2 
j2 j2 j2)) (* 2528 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2 j2)) (* 
1272 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2)) (* 320 (* h1 h1) (* h2
 h2 h2) (* h3 h3 h3 h3) h5 j2) (* 32 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h5) 
(* 64 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 544
 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2 j2 j2 j2 j2)) (* 1552 (* h1 
h1) (* h2 h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2 j2 j2 j2)) (* 2168 (* h1 h1) (* h2 
h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2 j2 j2)) (* 1672 (* h1 h1) (* h2 h2 h2) (* h3 
h3 h3 h3) h6 (* j2 j2 j2)) (* 728 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h6 (* 
j2 j2)) (* 168 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h6 j2) (* 16 (* h1 h1) (* 
h2 h2 h2) (* h3 h3 h3 h3) h6) (* 32 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h5 
(* j2 j2 j2 j2 j2 j2 j2)) (* 1032 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* 
j2 j2 j2 j2 j2 j2)) (* 7792 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 
j2 j2 j2)) (* 20072 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2)) 
(* 23768 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2)) (* 14128 (* h1 
h1) (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2)) (* 4104 (* h1 h1) (* h2 h2 h2) 
(* h3 h3 h3) h4 h5 j2) (* 464 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h5) (* 192 
(* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2048 (* 
h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2)) (* 6864 (* h1 h1) 
(* h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 11088 (* h1 h1) (* h2 h2 
h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 9816 (* h1 h1) (* h2 h2 h2) (* h3 h3 
h3) h4 h6 (* j2 j2 j2)) (* 4872 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 
j2)) (* 1272 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h6 j2) (* 136 (* h1 h1) (* 
h2 h2 h2) (* h3 h3 h3) h4 h6) (* 480 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h5 
h5) (* j2 j2 j2 j2 j2 j2)) (* 3752 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h5 h5)
 (* j2 j2 j2 j2 j2)) (* 10264 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* 
j2 j2 j2 j2)) (* 12736 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2
)) (* 7760 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2)) (* 2272 (* 
h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) j2) (* 256 (* h1 h1) (* h2 h2 h2) (* 
h3 h3 h3) (* h5 h5)) (* 256 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 
j2 j2 j2 j2 j2)) (* 2584 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 
j2 j2 j2)) (* 10528 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2)
) (* 21064 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 22160 
(* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2)) (* 12384 (* h1 h1) (* h2
 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2)) (* 3472 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3
) h5 h6 j2) (* 384 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 h6) (* 192 (* h1 h1) 
(* h2 h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2048 (* h1 h1) 
(* h2 h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6864 (* h1 h1) (* 
h2 h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 11088 (* h1 h1) (* h2 h2
 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 9816 (* h1 h1) (* h2 h2 h2) (* 
h3 h3 h3) (* h6 h6) (* j2 j2 j2)) (* 4872 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) 
(* h6 h6) (* j2 j2)) (* 1272 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h6 h6) j2) 
(* 136 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h6 h6)) (* 32 (* h1 h1) (* h2 h2 
h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 816 (* h1 h1) (* h2 h2 
h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 5568 (* h1 h1) (* h2 h2 h2)
 (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 15144 (* h1 h1) (* h2 h2 h2) (* 
h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 20104 (* h1 h1) (* h2 h2 h2) (* h3 h3) 
(* h4 h4) h5 (* j2 j2 j2)) (* 13752 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h4 h4) 
h5 (* j2 j2)) (* 4600 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 j2) (* 592 
(* h1 h1) (* h2 h2 h2) (* h3 h3) (* h4 h4) h5) (* 80 (* h1 h1) (* h2 h2 h2) (* 
h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 904 (* h1 h1) (* h2 h2 h2) (* 
h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 3328 (* h1 h1) (* h2 h2 h2) (* h3 
h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 5992 (* h1 h1) (* h2 h2 h2) (* h3 h3) 
(* h4 h4) h6 (* j2 j2 j2 j2)) (* 5968 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h4 h4)
 h6 (* j2 j2 j2)) (* 3352 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2
)) (* 992 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h4 h4) h6 j2) (* 120 (* h1 h1) (* 
h2 h2 h2) (* h3 h3) (* h4 h4) h6) (* 56 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1520 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* 
h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 9688 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h5 
h5) (* j2 j2 j2 j2 j2)) (* 24832 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) 
(* j2 j2 j2 j2)) (* 31504 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2
 j2)) (* 20848 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2)) (* 6816 
(* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) j2) (* 864 (* h1 h1) (* h2 h2 h2) 
(* h3 h3) h4 (* h5 h5)) (* 416 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 
j2 j2 j2 j2 j2 j2)) (* 4856 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 
j2 j2 j2 j2)) (* 20544 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 
j2)) (* 43280 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 
49776 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 31368 (* h1 h1)
 (* h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2)) (* 10032 (* h1 h1) (* h2 h2 h2) (* 
h3 h3) h4 h5 h6 j2) (* 1264 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 h6) (* 192 
(* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2000 
(* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 7144 (* 
h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 12664 (* h1 h1
) (* h2 h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 12496 (* h1 h1) (* h2 
h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2)) (* 6976 (* h1 h1) (* h2 h2 h2) (* h3
 h3) h4 (* h6 h6) (* j2 j2)) (* 2056 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h6 
h6) j2) (* 248 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h6 h6)) (* 280 (* h1 h1) 
(* h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2112 (* h1 h1) (* 
h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 6040 (* h1 h1) (* h2 h2 
h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 8256 (* h1 h1) (* h2 h2 h2) (* h3
 h3) (* h5 h5 h5) (* j2 j2 j2)) (* 5704 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 
h5 h5) (* j2 j2)) (* 1896 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) j2) (* 
240 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5 h5)) (* 264 (* h1 h1) (* h2 h2 h2)
 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 3008 (* h1 h1) (* h2 h2 h2)
 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 12704 (* h1 h1) (* h2 h2 h2) 
(* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 26792 (* h1 h1) (* h2 h2 h2) (* h3
 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 30848 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* 
h5 h5) h6 (* j2 j2 j2)) (* 19440 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) h6 
(* j2 j2)) (* 6200 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) h6 j2) (* 776 (* 
h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) h6) (* 384 (* h1 h1) (* h2 h2 h2) (* h3 
h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4008 (* h1 h1) (* h2 h2 h2) (* h3 
h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 14816 (* h1 h1) (* h2 h2 h2) (* h3 h3
) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 27808 (* h1 h1) (* h2 h2 h2) (* h3 h3) h5 
(* h6 h6) (* j2 j2 j2 j2)) (* 29320 (* h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* h6 h6
) (* j2 j2 j2)) (* 17408 (* h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2)
) (* 5368 (* h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* h6 h6) j2) (* 664 (* h1 h1) (* 
h2 h2 h2) (* h3 h3) h5 (* h6 h6)) (* 112 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1096 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3816 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6 
h6) (* j2 j2 j2 j2 j2)) (* 6672 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6 h6) 
(* j2 j2 j2 j2)) (* 6528 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 
j2)) (* 3624 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2)) (* 1064 
(* h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6 h6) j2) (* 128 (* h1 h1) (* h2 h2 h2) 
(* h3 h3) (* h6 h6 h6)) (* 24 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 536 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* 
j2 j2 j2 j2 j2 j2)) (* 3384 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 
j2 j2 j2 j2)) (* 9304 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 
j2)) (* 13160 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 
9968 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2)) (* 3800 (* h1 h1) 
(* h2 h2 h2) h3 (* h4 h4) (* h5 h5) j2) (* 560 (* h1 h1) (* h2 h2 h2) h3 (* h4 
h4) (* h5 h5)) (* 104 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 
j2 j2 j2)) (* 1168 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 
j2)) (* 4384 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 
8160 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 8520 (* h1 h1
) (* h2 h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2)) (* 5104 (* h1 h1) (* h2 h2 h2) 
h3 (* h4 h4) h5 h6 (* j2 j2)) (* 1648 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) h5 h6 
j2) (* 224 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) h5 h6) (* 16 (* h1 h1) (* h2 h2 
h2) h3 (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 104 (* h1 h1) (* h2 h2 
h2) h3 (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 288 (* h1 h1) (* h2 h2 h2) 
h3 (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 440 (* h1 h1) (* h2 h2 h2) h3 (* 
h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 400 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* 
h6 h6) (* j2 j2 j2)) (* 216 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 
j2)) (* 64 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h6 h6) j2) (* 8 (* h1 h1) (* 
h2 h2 h2) h3 (* h4 h4) (* h6 h6)) (* 16 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5 h5
) (* j2 j2 j2 j2 j2 j2 j2)) (* 408 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* 
j2 j2 j2 j2 j2 j2)) (* 2672 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 
j2 j2 j2)) (* 7352 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2)) 
(* 10272 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2)) (* 7648 (* h1 
h1) (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2)) (* 2864 (* h1 h1) (* h2 h2 h2) h3
 h4 (* h5 h5 h5) j2) (* 416 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5 h5)) (* 240 
(* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2896 (* 
h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 12680 (* h1 h1)
 (* h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 27944 (* h1 h1) (* h2 h2
 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 34328 (* h1 h1) (* h2 h2 h2) h3 h4 
(* h5 h5) h6 (* j2 j2 j2)) (* 23736 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) h6 
(* j2 j2)) (* 8560 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) h6 j2) (* 1232 (* h1 
h1) (* h2 h2 h2) h3 h4 (* h5 h5) h6) (* 240 (* h1 h1) (* h2 h2 h2) h3 h4 h5 (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2544 (* h1 h1) (* h2 h2 h2) h3 h4 h5 (* h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 9344 (* h1 h1) (* h2 h2 h2) h3 h4 h5 (* h6 h6) (* 
j2 j2 j2 j2 j2)) (* 17200 (* h1 h1) (* h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 
j2)) (* 17840 (* h1 h1) (* h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2)) (* 10640 
(* h1 h1) (* h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2)) (* 3424 (* h1 h1) (* h2 h2 
h2) h3 h4 h5 (* h6 h6) j2) (* 464 (* h1 h1) (* h2 h2 h2) h3 h4 h5 (* h6 h6)) (* 
32 (* h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 208 
(* h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 576 (* h1 h1
) (* h2 h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 880 (* h1 h1) (* h2 h2 
h2) h3 h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 800 (* h1 h1) (* h2 h2 h2) h3 h4 (* 
h6 h6 h6) (* j2 j2 j2)) (* 432 (* h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6 h6) (* j2 
j2)) (* 128 (* h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6 h6) j2) (* 16 (* h1 h1) (* h2 
h2 h2) h3 h4 (* h6 h6 h6)) (* 40 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* j2
 j2 j2 j2 j2 j2)) (* 256 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* j2 j2 j2 
j2 j2)) (* 656 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 864
 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* j2 j2 j2)) (* 616 (* h1 h1) (* h2 
h2 h2) h3 (* h5 h5 h5 h5) (* j2 j2)) (* 224 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 
h5 h5) j2) (* 32 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5 h5)) (* 88 (* h1 h1) (* 
h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 976 (* h1 h1) (* h2 h2
 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 4240 (* h1 h1) (* h2 h2 h2) h3
 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 9520 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 
h5) h6 (* j2 j2 j2 j2)) (* 11992 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2
 j2 j2)) (* 8480 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2)) (* 3104 
(* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) h6 j2) (* 448 (* h1 h1) (* h2 h2 h2) h3 
(* h5 h5 h5) h6) (* 216 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 2328 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 9104 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2)) (* 18168 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) 
(* 20560 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 13336 
(* h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2)) (* 4600 (* h1 h1) (* h2
 h2 h2) h3 (* h5 h5) (* h6 h6) j2) (* 648 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5) 
(* h6 h6)) (* 136 (* h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2
 j2)) (* 1376 (* h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 4960 (* h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 9040 
(* h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 9320 (* h1 h1) (* 
h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 5536 (* h1 h1) (* h2 h2 h2) h3 h5 
(* h6 h6 h6) (* j2 j2)) (* 1776 (* h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6 h6) j2) 
(* 240 (* h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6 h6)) (* 16 (* h1 h1) (* h2 h2 h2) 
h3 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 104 (* h1 h1) (* h2 h2 h2) h3 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 288 (* h1 h1) (* h2 h2 h2) h3 (* h6 h6
 h6 h6) (* j2 j2 j2 j2 j2)) (* 440 (* h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6 h6) (* 
j2 j2 j2 j2)) (* 400 (* h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 
216 (* h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6 h6) (* j2 j2)) (* 64 (* h1 h1) (* h2 
h2 h2) h3 (* h6 h6 h6 h6) j2) (* 8 (* h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6 h6)) 
(* 24 (* h1 h1) (* h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 288 (* h1 h1) (* h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
1312 (* h1 h1) (* h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 3072 
(* h1 h1) (* h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 4088 (* h1 h1)
 (* h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 3136 (* h1 h1) (* h2 h2 h2
) (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 1296 (* h1 h1) (* h2 h2 h2) (* h4 h4) (* 
h5 h5) h6 j2) (* 224 (* h1 h1) (* h2 h2 h2) (* h4 h4) (* h5 h5) h6) (* 8 (* h1 
h1) (* h2 h2 h2) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 64 (* h1 h1
) (* h2 h2 h2) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 216 (* h1 h1) 
(* h2 h2 h2) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 400 (* h1 h1) (* h2 
h2 h2) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 440 (* h1 h1) (* h2 h2 h2) (* 
h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 288 (* h1 h1) (* h2 h2 h2) (* h4 h4) h5 (* 
h6 h6) (* j2 j2)) (* 104 (* h1 h1) (* h2 h2 h2) (* h4 h4) h5 (* h6 h6) j2) (* 16
 (* h1 h1) (* h2 h2 h2) (* h4 h4) h5 (* h6 h6)) (* 32 (* h1 h1) (* h2 h2 h2) h4 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 360 (* h1 h1) (* h2 h2 h2) h4 (* h5
 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 1576 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5 h5)
 h6 (* j2 j2 j2 j2 j2)) (* 3584 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5 h5) h6 (* j2 
j2 j2 j2)) (* 4656 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 
3496 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2)) (* 1416 (* h1 h1) (* 
h2 h2 h2) h4 (* h5 h5 h5) h6 j2) (* 240 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5 h5) 
h6) (* 56 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 632 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 2784 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
6384 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 8376 (* 
h1 h1) (* h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 6360 (* h1 h1) (* h2
 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 2608 (* h1 h1) (* h2 h2 h2) h4 (* 
h5 h5) (* h6 h6) j2) (* 448 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5) (* h6 h6)) (* 16
 (* h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 128 (* 
h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 432 (* h1 h1) 
(* h2 h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 800 (* h1 h1) (* h2 h2 h2
) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 880 (* h1 h1) (* h2 h2 h2) h4 h5 (* h6 
h6 h6) (* j2 j2 j2)) (* 576 (* h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2))
 (* 208 (* h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6 h6) j2) (* 32 (* h1 h1) (* h2 h2 
h2) h4 h5 (* h6 h6 h6)) (* 8 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2)) (* 72 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2)) (* 272 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
560 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 680 (* h1 h1) 
(* h2 h2 h2) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 488 (* h1 h1) (* h2 h2 h2) (* 
h5 h5 h5 h5) h6 (* j2 j2)) (* 192 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5 h5) h6 j2) 
(* 32 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5 h5) h6) (* 32 (* h1 h1) (* h2 h2 h2) 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 352 (* h1 h1) (* h2 h2 h2) 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1520 (* h1 h1) (* h2 h2 h2) (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 3424 (* h1 h1) (* h2 h2 h2) (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2)) (* 4416 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5) (* h6
 h6) (* j2 j2 j2)) (* 3296 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 
j2)) (* 1328 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5) (* h6 h6) j2) (* 224 (* h1 h1) 
(* h2 h2 h2) (* h5 h5 h5) (* h6 h6)) (* 32 (* h1 h1) (* h2 h2 h2) (* h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 344 (* h1 h1) (* h2 h2 h2) (* h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1472 (* h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2)) (* 3312 (* h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6 h6)
 (* j2 j2 j2 j2)) (* 4288 (* h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2
 j2)) (* 3224 (* h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 1312 
(* h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6 h6) j2) (* 224 (* h1 h1) (* h2 h2 h2) 
(* h5 h5) (* h6 h6 h6)) (* 8 (* h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 64 (* h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 216 (* h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
400 (* h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 440 (* h1 h1) 
(* h2 h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 288 (* h1 h1) (* h2 h2 h2) h5 
(* h6 h6 h6 h6) (* j2 j2)) (* 104 (* h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6 h6) j2) 
(* 16 (* h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6 h6)) (* 8 (* h1 h1) (* h2 h2) (* h3 
h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 412 (* h1 h1) (* h2 h2) (* h3 h3
 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 4332 (* h1 h1) (* h2 h2) (* h3 h3 h3 
h3) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 13560 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4
 h5 (* j2 j2 j2 j2 j2)) (* 19732 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2
 j2 j2 j2)) (* 15360 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2)) (* 
6608 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2)) (* 1484 (* h1 h1) (* 
h2 h2) (* h3 h3 h3 h3) h4 h5 j2) (* 136 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 
h5) (* 64 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2 j2))
 (* 1056 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
4304 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2)) (* 8280 
(* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 8952 (* h1 h1) 
(* h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 5760 (* h1 h1) (* h2 h2) (* 
h3 h3 h3 h3) h4 h6 (* j2 j2 j2)) (* 2192 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 
h6 (* j2 j2)) (* 456 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h6 j2) (* 40 (* h1 
h1) (* h2 h2) (* h3 h3 h3 h3) h4 h6) (* 80 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) 
(* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1472 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) 
(* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 5756 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* 
h5 h5) (* j2 j2 j2 j2 j2)) (* 9432 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h5 h5)
 (* j2 j2 j2 j2)) (* 7824 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2
 j2)) (* 3472 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2)) (* 788 
(* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) j2) (* 72 (* h1 h1) (* h2 h2) (* 
h3 h3 h3 h3) (* h5 h5)) (* 40 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2
 j2 j2 j2 j2 j2 j2)) (* 956 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 
j2 j2 j2 j2 j2)) (* 5492 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 
j2 j2 j2)) (* 13736 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2)
) (* 17972 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 13196 
(* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2)) (* 5476 (* h1 h1) (* h2 
h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2)) (* 1200 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3)
 h5 h6 j2) (* 108 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 h6) (* 64 (* h1 h1) (* 
h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1056 (* h1 h1) 
(* h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4304 (* h1 h1) 
(* h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 8280 (* h1 h1) (* 
h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 8952 (* h1 h1) (* h2 h2)
 (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 5760 (* h1 h1) (* h2 h2) (* h3 h3
 h3 h3) (* h6 h6) (* j2 j2 j2)) (* 2192 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* 
h6 h6) (* j2 j2)) (* 456 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h6 h6) j2) (* 40
 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h6 h6)) (* 20 (* h1 h1) (* h2 h2) (* h3 
h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 900 (* h1 h1) (* h2 h2) (* 
h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 8744 (* h1 h1) (* h2 h2) (* 
h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 30008 (* h1 h1) (* h2 h2) (* h3
 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 49848 (* h1 h1) (* h2 h2) (* h3 h3 
h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 44748 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* 
h4 h4) h5 (* j2 j2 j2)) (* 22104 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 
(* j2 j2)) (* 5640 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 j2) (* 580 (* 
h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h5) (* 64 (* h1 h1) (* h2 h2) (* h3 h3 
h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 976 (* h1 h1) (* h2 h2) (* h3 
h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 4224 (* h1 h1) (* h2 h2) (* h3 
h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 8868 (* h1 h1) (* h2 h2) (* h3 h3 
h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 10584 (* h1 h1) (* h2 h2) (* h3 h3 h3) 
(* h4 h4) h6 (* j2 j2 j2 j2)) (* 7560 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4)
 h6 (* j2 j2 j2)) (* 3200 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2
)) (* 740 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h6 j2) (* 72 (* h1 h1) (* 
h2 h2) (* h3 h3 h3) (* h4 h4) h6) (* 28 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1232 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 
(* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 11044 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4
 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 37636 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 
(* h5 h5) (* j2 j2 j2 j2 j2)) (* 63324 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h5
 h5) (* j2 j2 j2 j2)) (* 57596 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* 
j2 j2 j2)) (* 28600 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2)) (* 
7272 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) j2) (* 740 (* h1 h1) (* h2 h2
) (* h3 h3 h3) h4 (* h5 h5)) (* 248 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 h6 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4504 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 27660 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 h6 (* 
j2 j2 j2 j2 j2 j2)) (* 78564 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 
j2 j2 j2)) (* 118896 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) 
(* 101416 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 48628 (* h1
 h1) (* h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2)) (* 12188 (* h1 h1) (* h2 h2) (* 
h3 h3 h3) h4 h5 h6 j2) (* 1240 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 h6) (* 160
 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
2160 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
9032 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
18660 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 22068
 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 15672 (* h1 
h1) (* h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2)) (* 6608 (* h1 h1) (* h2 h2
) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2)) (* 1524 (* h1 h1) (* h2 h2) (* h3 h3 h3) 
h4 (* h6 h6) j2) (* 148 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h6 h6)) (* 140 
(* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1756 
(* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 6700 (* 
h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 11908 (* h1 h1
) (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 11140 (* h1 h1) (* h2 
h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2)) (* 5596 (* h1 h1) (* h2 h2) (* h3 h3
 h3) (* h5 h5 h5) (* j2 j2)) (* 1424 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5 
h5) j2) (* 144 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5 h5)) (* 100 (* h1 h1) 
(* h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2132 (* h1 
h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 13532 (* h1
 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 40016 (* h1 
h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 63168 (* h1 h1) 
(* h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 55700 (* h1 h1) (* h2 h2
) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 27204 (* h1 h1) (* h2 h2) (* h3 h3 
h3) (* h5 h5) h6 (* j2 j2)) (* 6848 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) 
h6 j2) (* 692 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) h6) (* 244 (* h1 h1) 
(* h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3652 (* h1 
h1) (* h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 18904 (* h1
 h1) (* h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 48324 (* h1 
h1) (* h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 68636 (* h1 h1) 
(* h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 56316 (* h1 h1) (* h2 h2
) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 26360 (* h1 h1) (* h2 h2) (* h3 h3 
h3) h5 (* h6 h6) (* j2 j2)) (* 6508 (* h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* h6 h6
) j2) (* 656 (* h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* h6 h6)) (* 96 (* h1 h1) (* 
h2 h2) (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1184 (* h1 h1) 
(* h2 h2) (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4808 (* h1 h1) 
(* h2 h2) (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 9792 (* h1 h1) (* 
h2 h2) (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 11484 (* h1 h1) (* h2 h2
) (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 8112 (* h1 h1) (* h2 h2) (* h3 
h3 h3) (* h6 h6 h6) (* j2 j2 j2)) (* 3408 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h6
 h6 h6) (* j2 j2)) (* 784 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6 h6) j2) (* 
76 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6 h6)) (* 192 (* h1 h1) (* h2 h2) (* 
h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 2428 (* h1 h1) (* h2 h2) (* 
h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 9692 (* h1 h1) (* h2 h2) (* h3 
h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 18500 (* h1 h1) (* h2 h2) (* h3 h3) 
(* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 19120 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4
 h4) h5 (* j2 j2 j2)) (* 10892 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* 
j2 j2)) (* 3188 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 j2) (* 372 (* h1 
h1) (* h2 h2) (* h3 h3) (* h4 h4 h4) h5) (* 104 (* h1 h1) (* h2 h2) (* h3 h3) 
(* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 620 (* h1 h1) (* h2 h2) (* h3 h3) 
(* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 1564 (* h1 h1) (* h2 h2) (* h3 h3) (* 
h4 h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 2160 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4 
h4) h6 (* j2 j2 j2 j2)) (* 1760 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4 h4) h6 
(* j2 j2 j2)) (* 844 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4 h4) h6 (* j2 j2)) 
(* 220 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4 h4) h6 j2) (* 24 (* h1 h1) (* h2 
h2) (* h3 h3) (* h4 h4 h4) h6) (* 32 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1140 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 
h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 9892 (* h1 h1) (* h2 h2) (* h3 h3) 
(* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 34408 (* h1 h1) (* h2 h2) (* h3 h3
) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 60844 (* h1 h1) (* h2 h2) (* h3 h3)
 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 59708 (* h1 h1) (* h2 h2) (* h3 h3) (* 
h4 h4) (* h5 h5) (* j2 j2 j2)) (* 32736 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) 
(* h5 h5) (* j2 j2)) (* 9312 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) 
j2) (* 1064 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5)) (* 136 (* h1 h1) 
(* h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2516 (* h1 
h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 15780 (* h1
 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 47512 (* h1 
h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 78532 (* h1 h1) 
(* h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 74764 (* h1 h1) (* h2 h2
) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 40548 (* h1 h1) (* h2 h2) (* h3 h3)
 (* h4 h4) h5 h6 (* j2 j2)) (* 11528 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 
h6 j2) (* 1324 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 h6) (* 32 (* h1 h1) 
(* h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 536 (* 
h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2540
 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
5860 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
7720 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 6112 
(* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 2876 (* h1 h1
) (* h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2)) (* 740 (* h1 h1) (* h2 h2) 
(* h3 h3) (* h4 h4) (* h6 h6) j2) (* 80 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) 
(* h6 h6)) (* 24 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 784 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 
j2 j2 j2)) (* 6376 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 
j2 j2)) (* 21836 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2
)) (* 38648 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 
38064 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2)) (* 20864 (* h1
 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2)) (* 5892 (* h1 h1) (* h2 h2) 
(* h3 h3) h4 (* h5 h5 h5) j2) (* 664 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5 
h5)) (* 272 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 4704 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 29100 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2
 j2)) (* 86576 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2))
 (* 140900 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 
131748 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 70136 (* 
h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 19596 (* h1 h1) (* h2 
h2) (* h3 h3) h4 (* h5 h5) h6 j2) (* 2216 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5
 h5) h6) (* 328 (* h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 4780 (* h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 25064 (* h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2
 j2 j2)) (* 66988 (* h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 102364 (* h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) 
(* 92524 (* h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 48504 
(* h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 13500 (* h1 h1) (* 
h2 h2) (* h3 h3) h4 h5 (* h6 h6) j2) (* 1532 (* h1 h1) (* h2 h2) (* h3 h3) h4 h5
 (* h6 h6)) (* 64 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 760 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 3220 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 7028 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 
j2)) (* 8960 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 
6944 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2)) (* 3220 (* h1 
h1) (* h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2)) (* 820 (* h1 h1) (* h2 h2) 
(* h3 h3) h4 (* h6 h6 h6) j2) (* 88 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6 h6
)) (* 40 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2))
 (* 496 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 
1972 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 3712 
(* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 3740 (* h1 h1)
 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 2056 (* h1 h1) (* h2 h2) 
(* h3 h3) (* h5 h5 h5 h5) (* j2 j2)) (* 576 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 
h5 h5 h5) j2) (* 64 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5 h5)) (* 68 (* h1 
h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1304 (* 
h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 8096 (* 
h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 24404 (* h1
 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 40564 (* h1 h1) 
(* h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 38708 (* h1 h1) (* h2 h2
) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 20880 (* h1 h1) (* h2 h2) (* h3 h3)
 (* h5 h5 h5) h6 (* j2 j2)) (* 5848 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) 
h6 j2) (* 656 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) h6) (* 256 (* h1 h1) 
(* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3620 (* 
h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
19216 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 51920 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 79536 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 
71536 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 37136 
(* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 10212 (* h1 h1) 
(* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) j2) (* 1144 (* h1 h1) (* h2 h2) (* h3 h3
) (* h5 h5) (* h6 h6)) (* 192 (* h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 2456 (* h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 11712 (* h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2)) (* 29168 (* h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2)) (* 42332 (* h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2
 j2 j2 j2)) (* 36880 (* h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2))
 (* 18848 (* h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 5160 (* h1
 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6 h6) j2) (* 580 (* h1 h1) (* h2 h2) (* h3 h3
) h5 (* h6 h6 h6)) (* 32 (* h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 328 (* h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 1300 (* h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 2732 (* h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 
j2 j2 j2)) (* 3400 (* h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2)
) (* 2592 (* h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 1188 
(* h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6 h6) (* j2 j2)) (* 300 (* h1 h1) (* h2 
h2) (* h3 h3) (* h6 h6 h6 h6) j2) (* 32 (* h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 
h6 h6)) (* 108 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 
j2 j2)) (* 1276 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 
j2)) (* 5200 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) 
(* 10484 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 11708
 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 7348 (* h1 h1) 
(* h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 2408 (* h1 h1) (* h2 h2) h3 
(* h4 h4 h4) (* h5 h5) j2) (* 316 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) (* h5 h5))
 (* 132 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
796 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 2040 (* 
h1 h1) (* h2 h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 2880 (* h1 h1) (* 
h2 h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 2420 (* h1 h1) (* h2 h2) h3 (* 
h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 1212 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) h5 h6 
(* j2 j2)) (* 336 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) h5 h6 j2) (* 40 (* h1 h1) 
(* h2 h2) h3 (* h4 h4 h4) h5 h6) (* 12 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5
 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 344 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 2812 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 
h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 9928 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5 
h5) (* j2 j2 j2 j2 j2)) (* 18472 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) 
(* j2 j2 j2 j2)) (* 19544 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2
 j2)) (* 11784 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 3744 
(* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) j2) (* 480 (* h1 h1) (* h2 h2) h3 
(* h4 h4) (* h5 h5 h5)) (* 80 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 1412 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 8888 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 27644 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) h6 
(* j2 j2 j2 j2 j2)) (* 48248 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2
 j2 j2 j2)) (* 49468 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2))
 (* 29448 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 9348 (* h1
 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) h6 j2) (* 1208 (* h1 h1) (* h2 h2) h3 (* 
h4 h4) (* h5 h5) h6) (* 36 (* h1 h1) (* h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 668 (* h1 h1) (* h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 3284 (* h1 h1) (* h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 7800 (* h1 h1) (* h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 
j2 j2 j2 j2)) (* 10600 (* h1 h1) (* h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2
 j2)) (* 8716 (* h1 h1) (* h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 
4308 (* h1 h1) (* h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 1184 (* h1 h1) 
(* h2 h2) h3 (* h4 h4) h5 (* h6 h6) j2) (* 140 (* h1 h1) (* h2 h2) h3 (* h4 h4) 
h5 (* h6 h6)) (* 4 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 116 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2
 j2)) (* 872 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) 
(* 2860 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 5008 
(* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 5040 (* h1 h1) (* 
h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2)) (* 2916 (* h1 h1) (* h2 h2) h3 h4 (* 
h5 h5 h5 h5) (* j2 j2)) (* 896 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5 h5) j2) (* 
112 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5 h5)) (* 96 (* h1 h1) (* h2 h2) h3 h4 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1540 (* h1 h1) (* h2 h2) h3 h4 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 9260 (* h1 h1) (* h2 h2) h3 h4 (* 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 27960 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2)) (* 47656 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) h6 
(* j2 j2 j2 j2)) (* 47836 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2)
) (* 27916 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2)) (* 8696 (* h1 h1
) (* h2 h2) h3 h4 (* h5 h5 h5) h6 j2) (* 1104 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5
 h5) h6) (* 188 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 2676 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 14408 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2
 j2 j2)) (* 40324 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 65524 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 
63980 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 36848 (* h1
 h1) (* h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 11452 (* h1 h1) (* h2 h2)
 h3 h4 (* h5 h5) (* h6 h6) j2) (* 1464 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* h6
 h6)) (* 72 (* h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 940 (* h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 4180 (* h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 9480
 (* h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 12560 (* h1 h1
) (* h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 10172 (* h1 h1) (* h2 h2) 
h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 4980 (* h1 h1) (* h2 h2) h3 h4 h5 (* h6 
h6 h6) (* j2 j2)) (* 1360 (* h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6 h6) j2) (* 160 
(* h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6 h6)) (* 12 (* h1 h1) (* h2 h2) h3 (* h5 h5
 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 216 (* h1 h1) (* h2 h2) h3 (* h5 h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1264 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 3656 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) h6 
(* j2 j2 j2 j2 j2)) (* 6004 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2 
j2 j2)) (* 5856 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 3344 
(* h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 1024 (* h1 h1) (* h2 h2)
 h3 (* h5 h5 h5 h5) h6 j2) (* 128 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) h6) (* 
88 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 1212 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 6452 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
17940 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 28948
 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 28012 (* h1 
h1) (* h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 15952 (* h1 h1) (* h2 
h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 4892 (* h1 h1) (* h2 h2) h3 (* h5 h5
 h5) (* h6 h6) j2) (* 616 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* h6 h6)) (* 108 
(* h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
1372 (* h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
6796 (* h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
17880 (* h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 27760
 (* h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 26220 (* h1 
h1) (* h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 14748 (* h1 h1) (* h2 
h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 4512 (* h1 h1) (* h2 h2) h3 (* h5 h5
) (* h6 h6 h6) j2) (* 572 (* h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6 h6)) (* 36 
(* h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 404 
(* h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1692 (* 
h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3720 (* h1 h1) 
(* h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 4840 (* h1 h1) (* h2 h2) 
h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 3876 (* h1 h1) (* h2 h2) h3 h5 (* h6 
h6 h6 h6) (* j2 j2 j2)) (* 1884 (* h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 
j2)) (* 512 (* h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6 h6) j2) (* 60 (* h1 h1) (* h2 
h2) h3 h5 (* h6 h6 h6 h6)) (* 24 (* h1 h1) (* h2 h2) (* h4 h4 h4) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 188 (* h1 h1) (* h2 h2) (* h4 h4 h4) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 620 (* h1 h1) (* h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* 
j2 j2 j2 j2 j2)) (* 1120 (* h1 h1) (* h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 
j2 j2)) (* 1200 (* h1 h1) (* h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 
764 (* h1 h1) (* h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 268 (* h1 h1) 
(* h2 h2) (* h4 h4 h4) (* h5 h5) h6 j2) (* 40 (* h1 h1) (* h2 h2) (* h4 h4 h4) 
(* h5 h5) h6) (* 12 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2
 j2 j2 j2 j2)) (* 168 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2)) (* 892 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2)) (* 2488 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2)) (* 4100 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 
4152 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 2548 (* h1 
h1) (* h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 872 (* h1 h1) (* h2 h2) 
(* h4 h4) (* h5 h5 h5) h6 j2) (* 128 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5 h5) 
h6) (* 8 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 144 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 844 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 2476 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2
 j2 j2)) (* 4200 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2)) (* 4328 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 
2684 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 924 (* h1 
h1) (* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) j2) (* 136 (* h1 h1) (* h2 h2) (* h4
 h4) (* h5 h5) (* h6 h6)) (* 8 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 104 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2
 j2 j2 j2 j2 j2)) (* 528 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2)) (* 1424 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2))
 (* 2280 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 2248 (* 
h1 h1) (* h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 1344 (* h1 h1) (* h2 h2)
 h4 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 448 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5 h5) 
h6 j2) (* 64 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5 h5) h6) (* 28 (* h1 h1) (* h2 h2
) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 368 (* h1 h1) (* h2 
h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1892 (* h1 h1) (* h2 
h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 5176 (* h1 h1) (* h2 h2)
 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 8420 (* h1 h1) (* h2 h2) h4 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 8448 (* h1 h1) (* h2 h2) h4 (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2)) (* 5148 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5) (* h6 h6
) (* j2 j2)) (* 1752 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5) (* h6 h6) j2) (* 256 
(* h1 h1) (* h2 h2) h4 (* h5 h5 h5) (* h6 h6)) (* 16 (* h1 h1) (* h2 h2) h4 (* 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 216 (* h1 h1) (* h2 h2) h4 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1124 (* h1 h1) (* h2 h2) h4 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3092 (* h1 h1) (* h2 h2) h4 (* 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 5040 (* h1 h1) (* h2 h2) h4 (* h5 h5)
 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 5056 (* h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6
 h6) (* j2 j2 j2)) (* 3076 (* h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 
j2)) (* 1044 (* h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6 h6) j2) (* 152 (* h1 h1) 
(* h2 h2) h4 (* h5 h5) (* h6 h6 h6)) (* 8 (* h1 h1) (* h2 h2) (* h5 h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 104 (* h1 h1) (* h2 h2) (* h5 h5 h5 h5
) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 528 (* h1 h1) (* h2 h2) (* h5 h5 h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1424 (* h1 h1) (* h2 h2) (* h5 h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 2280 (* h1 h1) (* h2 h2) (* h5 h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2)) (* 2248 (* h1 h1) (* h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* j2
 j2 j2)) (* 1344 (* h1 h1) (* h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 448
 (* h1 h1) (* h2 h2) (* h5 h5 h5 h5) (* h6 h6) j2) (* 64 (* h1 h1) (* h2 h2) (* 
h5 h5 h5 h5) (* h6 h6)) (* 16 (* h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 200 (* h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 1000 (* h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 2688 (* h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2)) (* 4320 (* h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2)) (* 4296 (* h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 
2600 (* h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 880 (* h1 h1) 
(* h2 h2) (* h5 h5 h5) (* h6 h6 h6) j2) (* 128 (* h1 h1) (* h2 h2) (* h5 h5 h5) 
(* h6 h6 h6)) (* 8 (* h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 96 (* h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2
 j2 j2 j2)) (* 468 (* h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 1236 (* h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)
) (* 1960 (* h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 1928
 (* h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 1156 (* h1 h1) 
(* h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 388 (* h1 h1) (* h2 h2) (* h5 
h5) (* h6 h6 h6 h6) j2) (* 56 (* h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6 h6)) (* 
108 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
2094 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 9096
 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 18130 (* h1
 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 19906 (* h1 h1) h2 
(* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 12790 (* h1 h1) h2 (* h3 h3 h3 
h3) (* h4 h4) h5 (* j2 j2 j2)) (* 4792 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h5
 (* j2 j2)) (* 970 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h5 j2) (* 82 (* h1 h1)
 h2 (* h3 h3 h3 h3) (* h4 h4) h5) (* 112 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 664 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h6
 (* j2 j2 j2 j2 j2 j2 j2)) (* 1692 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h6 (* 
j2 j2 j2 j2 j2 j2)) (* 2418 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 
j2 j2 j2)) (* 2118 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2)) 
(* 1164 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2)) (* 392 (* h1 h1)
 h2 (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2)) (* 74 (* h1 h1) h2 (* h3 h3 h3 h3) 
(* h4 h4) h6 j2) (* 6 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h6) (* 100 (* h1 h1
) h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2190 (* h1 h1)
 h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 10770 (* h1 h1) h2
 (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 23354 (* h1 h1) h2 (* h3
 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 27056 (* h1 h1) h2 (* h3 h3 h3 h3
) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 17930 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h5 
h5) (* j2 j2 j2)) (* 6814 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2)) 
(* 1382 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h5 h5) j2) (* 116 (* h1 h1) h2 (* h3 
h3 h3 h3) h4 (* h5 h5)) (* 16 (* h1 h1) h2 (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 736 (* h1 h1) h2 (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 7280 (* h1 h1) h2 (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2
 j2)) (* 26526 (* h1 h1) h2 (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 
48834 (* h1 h1) h2 (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 51306 (* h1 
h1) h2 (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 32084 (* h1 h1) h2 (* h3 h3 
h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 11810 (* h1 h1) h2 (* h3 h3 h3 h3) h4 h5 h6 (* 
j2 j2)) (* 2362 (* h1 h1) h2 (* h3 h3 h3 h3) h4 h5 h6 j2) (* 198 (* h1 h1) h2 
(* h3 h3 h3 h3) h4 h5 h6) (* 32 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 448 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 2016 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 4600 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 6198 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 5238 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 2812 
(* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2)) (* 932 (* h1 h1) h2 (* 
h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2)) (* 174 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* 
h6 h6) j2) (* 14 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6)) (* 200 (* h1 h1) h2 
(* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1260 (* h1 h1) h2 (* 
h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 3012 (* h1 h1) h2 (* h3 h3 
h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 3656 (* h1 h1) h2 (* h3 h3 h3 h3) (* 
h5 h5 h5) (* j2 j2 j2 j2)) (* 2476 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* 
j2 j2 j2)) (* 948 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2)) (* 192 
(* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5 h5) j2) (* 16 (* h1 h1) h2 (* h3 h3 h3 h3)
 (* h5 h5 h5)) (* 220 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 2938 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2)) (* 12530 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 
j2)) (* 25446 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
28436 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 18442 (* h1 
h1) h2 (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 6914 (* h1 h1) h2 (* h3 h3 
h3 h3) (* h5 h5) h6 (* j2 j2)) (* 1390 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) h6
 j2) (* 116 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) h6) (* 32 (* h1 h1) h2 (* h3 
h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 684 (* h1 h1) h2 (* h3
 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 5198 (* h1 h1) h2 (* h3 
h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 17192 (* h1 h1) h2 (* h3 h3 
h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 30176 (* h1 h1) h2 (* h3 h3 h3 h3)
 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 30842 (* h1 h1) h2 (* h3 h3 h3 h3) h5 (* h6
 h6) (* j2 j2 j2 j2)) (* 18954 (* h1 h1) h2 (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 
j2 j2)) (* 6896 (* h1 h1) h2 (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2)) (* 1368 (* 
h1 h1) h2 (* h3 h3 h3 h3) h5 (* h6 h6) j2) (* 114 (* h1 h1) h2 (* h3 h3 h3 h3) 
h5 (* h6 h6)) (* 32 (* h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 336 (* h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 1352 (* h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 2908 (* h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2))
 (* 3780 (* h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 3120 
(* h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1648 (* h1 h1) h2 
(* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2)) (* 540 (* h1 h1) h2 (* h3 h3 h3 h3) 
(* h6 h6 h6) (* j2 j2)) (* 100 (* h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6 h6) j2) (* 
8 (* h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6 h6)) (* 122 (* h1 h1) h2 (* h3 h3 h3) 
(* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1930 (* h1 h1) h2 (* h3 h3 h3) 
(* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 8682 (* h1 h1) h2 (* h3 h3 h3) (* 
h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 18758 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 
h4) h5 (* j2 j2 j2 j2 j2)) (* 22758 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h5 
(* j2 j2 j2 j2)) (* 16302 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2)
) (* 6822 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2)) (* 1538 (* h1 h1)
 h2 (* h3 h3 h3) (* h4 h4 h4) h5 j2) (* 144 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 
h4) h5) (* 56 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 360 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 998 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 1556 
(* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 1490 (* h1 h1) 
h2 (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2)) (* 896 (* h1 h1) h2 (* h3 h3 h3
) (* h4 h4 h4) h6 (* j2 j2 j2)) (* 330 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h6
 (* j2 j2)) (* 68 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h6 j2) (* 6 (* h1 h1) 
h2 (* h3 h3 h3) (* h4 h4 h4) h6) (* 2 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h5 
h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 378 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) 
(* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 5112 (* h1 h1) h2 (* h3 h3 h3) (* h4 
h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 22816 (* h1 h1) h2 (* h3 h3 h3) (* h4
 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 50140 (* h1 h1) h2 (* h3 h3 h3) (* h4 
h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 62046 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) 
(* h5 h5) (* j2 j2 j2 j2)) (* 45118 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h5 h5
) (* j2 j2 j2)) (* 19018 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)
) (* 4284 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) j2) (* 398 (* h1 h1) h2 
(* h3 h3 h3) (* h4 h4) (* h5 h5)) (* 24 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1018 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) 
h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 9694 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) 
h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 37054 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 
h6 (* j2 j2 j2 j2 j2 j2)) (* 74018 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 h6 (* 
j2 j2 j2 j2 j2)) (* 85850 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 
j2)) (* 59786 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 24562 
(* h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 5470 (* h1 h1) h2 (* h3 
h3 h3) (* h4 h4) h5 h6 j2) (* 508 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 h6) (* 
16 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (* 288 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 1476 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2
)) (* 3748 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 5580 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
5196 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 3068 (* 
h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 1116 (* h1 h1) h2 
(* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2)) (* 228 (* h1 h1) h2 (* h3 h3 h3) (* 
h4 h4) (* h6 h6) j2) (* 20 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h6 h6)) (* 190
 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2646 
(* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 12238 (* 
h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 27754 (* h1 h1)
 h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 35168 (* h1 h1) h2 (* h3
 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 25954 (* h1 h1) h2 (* h3 h3 h3) h4 
(* h5 h5 h5) (* j2 j2 j2)) (* 11004 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5 h5) 
(* j2 j2)) (* 2474 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5 h5) j2) (* 228 (* h1 h1
) h2 (* h3 h3 h3) h4 (* h5 h5 h5)) (* 44 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1620 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5
) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 15040 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5
) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 58512 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2)) (* 120070 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6 
(* j2 j2 j2 j2 j2)) (* 142824 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2
 j2 j2)) (* 101346 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 
42058 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 9380 (* h1 h1) h2 
(* h3 h3 h3) h4 (* h5 h5) h6 j2) (* 866 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) 
h6) (* 112 (* h1 h1) h2 (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 2102 (* h1 h1) h2 (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 14878 (* h1 h1) h2 (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 50250 (* h1 h1) h2 (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
94146 (* h1 h1) h2 (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 105150 
(* h1 h1) h2 (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 71498 (* h1 h1) h2
 (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 28918 (* h1 h1) h2 (* h3 h3 h3) 
h4 h5 (* h6 h6) (* j2 j2)) (* 6374 (* h1 h1) h2 (* h3 h3 h3) h4 h5 (* h6 h6) j2)
 (* 588 (* h1 h1) h2 (* h3 h3 h3) h4 h5 (* h6 h6)) (* 32 (* h1 h1) h2 (* h3 h3 
h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 408 (* h1 h1) h2 (* h3 h3
 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1872 (* h1 h1) h2 (* h3 h3 
h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4502 (* h1 h1) h2 (* h3 h3 h3) 
h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6492 (* h1 h1) h2 (* h3 h3 h3) h4 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 5922 (* h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6 h6) 
(* j2 j2 j2 j2)) (* 3448 (* h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2))
 (* 1242 (* h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2)) (* 252 (* h1 h1) 
h2 (* h3 h3 h3) h4 (* h6 h6 h6) j2) (* 22 (* h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6 
h6)) (* 100 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 680 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1796 
(* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 2436 (* h1 h1) 
h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 1848 (* h1 h1) h2 (* h3 h3 
h3) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 788 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5 
h5) (* j2 j2)) (* 176 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5 h5) j2) (* 16 (* h1 
h1) h2 (* h3 h3 h3) (* h5 h5 h5 h5)) (* 310 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3524 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 14840 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5)
 h6 (* j2 j2 j2 j2 j2 j2)) (* 31942 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2)) (* 39230 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 
j2 j2)) (* 28404 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 
11904 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2)) (* 2658 (* h1 h1) h2 
(* h3 h3 h3) (* h5 h5 h5) h6 j2) (* 244 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) 
h6) (* 66 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 1354 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 10070 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2
 j2 j2 j2)) (* 35534 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 69222 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2
 j2)) (* 79824 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) 
(* 55538 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 22754 
(* h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 5032 (* h1 h1) h2 
(* h3 h3 h3) (* h5 h5) (* h6 h6) j2) (* 462 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5) 
(* h6 h6)) (* 88 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 1206 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 7114 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 21878 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)
) (* 38886 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
42058 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 28014 (* h1 
h1) h2 (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 11178 (* h1 h1) h2 (* h3 h3
 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 2442 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6 h6
) j2) (* 224 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6 h6)) (* 16 (* h1 h1) h2 (* h3
 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 176 (* h1 h1) h2 (* 
h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 756 (* h1 h1) h2 (* h3
 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1752 (* h1 h1) h2 (* h3 h3 
h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2468 (* h1 h1) h2 (* h3 h3 h3) (* 
h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2216 (* h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6 
h6) (* j2 j2 j2 j2)) (* 1276 (* h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 
j2)) (* 456 (* h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2)) (* 92 (* h1 h1)
 h2 (* h3 h3 h3) (* h6 h6 h6 h6) j2) (* 8 (* h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6 
h6)) (* 172 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 1074 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 2808
 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 3974 (* h1 h1)
 h2 (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 3276 (* h1 h1) h2 (* h3 h3)
 (* h4 h4 h4 h4) h5 (* j2 j2 j2)) (* 1566 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4 h4)
 h5 (* j2 j2)) (* 400 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4 h4) h5 j2) (* 42 (* h1 
h1) h2 (* h3 h3) (* h4 h4 h4 h4) h5) (* 132 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) 
(* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1926 (* h1 h1) h2 (* h3 h3) (* h4 h4 
h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 9078 (* h1 h1) h2 (* h3 h3) (* h4 h4 
h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 21260 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4
) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 28432 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) (* 
h5 h5) (* j2 j2 j2 j2)) (* 22676 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) 
(* j2 j2 j2)) (* 10616 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2)) 
(* 2674 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) j2) (* 278 (* h1 h1) h2 
(* h3 h3) (* h4 h4 h4) (* h5 h5)) (* 138 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1734 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 7686 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 h6 
(* j2 j2 j2 j2 j2 j2)) (* 17366 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 
j2 j2 j2 j2)) (* 22666 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2)
) (* 17762 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 8210 (* h1
 h1) h2 (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2)) (* 2050 (* h1 h1) h2 (* h3 h3) 
(* h4 h4 h4) h5 h6 j2) (* 212 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 h6) (* 2 
(* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 246 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 2924 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)
) (* 12974 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) 
(* 29598 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 
38954 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 30634 
(* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 14122 (* h1 h1) 
h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 3494 (* h1 h1) h2 (* h3 h3) 
(* h4 h4) (* h5 h5 h5) j2) (* 356 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5 h5))
 (* 30 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 1094 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 10026 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2
 j2 j2)) (* 39774 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 
j2 j2)) (* 85252 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2
)) (* 108136 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 
83356 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 38156 (* h1
 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 9472 (* h1 h1) h2 (* h3 
h3) (* h4 h4) (* h5 h5) h6 j2) (* 976 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5)
 h6) (* 32 (* h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2
 j2 j2)) (* 678 (* h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 5130 (* h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 18632 (* h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2
 j2 j2)) (* 37950 (* h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 46536 (* h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 
35014 (* h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 15744 (* h1
 h1) h2 (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 3858 (* h1 h1) h2 (* h3 
h3) (* h4 h4) h5 (* h6 h6) j2) (* 394 (* h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* h6 
h6)) (* 50 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 720 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
3470 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 8226 
(* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 10980 (* h1 h1)
 h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 8630 (* h1 h1) h2 (* h3 h3)
 h4 (* h5 h5 h5 h5) (* j2 j2 j2)) (* 3940 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5 
h5) (* j2 j2)) (* 960 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5 h5) j2) (* 96 (* h1 
h1) h2 (* h3 h3) h4 (* h5 h5 h5 h5)) (* 28 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5
) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 972 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 8634 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 33886 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5)
 h6 (* j2 j2 j2 j2 j2 j2)) (* 72338 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2)) (* 91432 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 
j2 j2)) (* 70062 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 
31762 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2)) (* 7778 (* h1 h1) h2 
(* h3 h3) h4 (* h5 h5 h5) h6 j2) (* 788 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) 
h6) (* 108 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2
 j2 j2)) (* 2136 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 15314 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 54030 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2
 j2 j2 j2)) (* 108382 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2)) (* 131894 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2))
 (* 98928 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 44464 
(* h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 10908 (* h1 h1) h2 
(* h3 h3) h4 (* h5 h5) (* h6 h6) j2) (* 1116 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5)
 (* h6 h6)) (* 64 (* h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2 j2)) (* 942 (* h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 5746 (* h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 18502 (* h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)
) (* 35034 (* h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
40970 (* h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 29846 (* h1 
h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 13122 (* h1 h1) h2 (* h3 h3
) h4 h5 (* h6 h6 h6) (* j2 j2)) (* 3166 (* h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6
) j2) (* 320 (* h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6)) (* 80 (* h1 h1) h2 (* h3
 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 972 (* h1 h1) h2 (* h3 
h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 4356 (* h1 h1) h2 (* h3 h3) 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 9952 (* h1 h1) h2 (* h3 h3) (* h5 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 13024 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5)
 h6 (* j2 j2 j2 j2)) (* 10132 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2
 j2)) (* 4604 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 1120 (* h1
 h1) h2 (* h3 h3) (* h5 h5 h5 h5) h6 j2) (* 112 (* h1 h1) h2 (* h3 h3) (* h5 h5 
h5 h5) h6) (* 38 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2 j2)) (* 796 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 5858 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 21006 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2
 j2 j2 j2 j2)) (* 42594 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2)) (* 52132 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2
)) (* 39116 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 17490
 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 4246 (* h1 h1) h2 
(* h3 h3) (* h5 h5 h5) (* h6 h6) j2) (* 428 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5) 
(* h6 h6)) (* 78 (* h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2 j2)) (* 1174 (* h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 7214 (* h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2
 j2 j2 j2 j2 j2)) (* 23334 (* h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 44390 (* h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2
 j2 j2 j2)) (* 52190 (* h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2)) (* 38248 (* h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 
16924 (* h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 4110 (* h1 h1)
 h2 (* h3 h3) (* h5 h5) (* h6 h6 h6) j2) (* 418 (* h1 h1) h2 (* h3 h3) (* h5 h5)
 (* h6 h6 h6)) (* 32 (* h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2 j2)) (* 402 (* h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 2178 (* h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 6482 (* h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 11642 (* h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
13126 (* h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 9318 (* h1 
h1) h2 (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 4022 (* h1 h1) h2 (* h3 h3)
 h5 (* h6 h6 h6 h6) (* j2 j2)) (* 958 (* h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6 h6) 
j2) (* 96 (* h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6 h6)) (* 78 (* h1 h1) h2 h3 (* h4
 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 512 (* h1 h1) h2 h3 (* h4 h4 
h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1416 (* h1 h1) h2 h3 (* h4 h4 h4 h4) 
(* h5 h5) (* j2 j2 j2 j2 j2)) (* 2136 (* h1 h1) h2 h3 (* h4 h4 h4 h4) (* h5 h5) 
(* j2 j2 j2 j2)) (* 1894 (* h1 h1) h2 h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2))
 (* 984 (* h1 h1) h2 h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2)) (* 276 (* h1 h1) h2
 h3 (* h4 h4 h4 h4) (* h5 h5) j2) (* 32 (* h1 h1) h2 h3 (* h4 h4 h4 h4) (* h5 h5
)) (* 42 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 554 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
2580 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 6156 
(* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 8546 (* h1 h1) 
h2 h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 7186 (* h1 h1) h2 h3 (* h4 
h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 3600 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5 
h5) (* j2 j2)) (* 984 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5 h5) j2) (* 112 (* h1
 h1) h2 h3 (* h4 h4 h4) (* h5 h5 h5)) (* 66 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 850 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5
) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 3940 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) h6
 (* j2 j2 j2 j2 j2 j2)) (* 9412 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* 13114 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)
) (* 11082 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 5584 (* h1
 h1) h2 h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 1536 (* h1 h1) h2 h3 (* h4 h4
 h4) (* h5 h5) h6 j2) (* 176 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) h6) (* 26 
(* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 334 
(* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1516 (* 
h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 3522 (* h1 h1) 
h2 h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 4756 (* h1 h1) h2 h3 (* 
h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 3888 (* h1 h1) h2 h3 (* h4 h4) (* h5 
h5 h5 h5) (* j2 j2 j2)) (* 1894 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 
j2)) (* 504 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5 h5) j2) (* 56 (* h1 h1) h2 h3 
(* h4 h4) (* h5 h5 h5 h5)) (* 8 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 316 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) h6 (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 2940 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2)) (* 11994 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2)) (* 26772 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2)) (* 35784 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 
29420 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 14546 (* h1 h1)
 h2 h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 3948 (* h1 h1) h2 h3 (* h4 h4) 
(* h5 h5 h5) h6 j2) (* 448 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) h6) (* 16 (* 
h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
350 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 2714 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 10260 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 22036 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
28822 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 23394 
(* h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 11480 (* h1 h1) 
h2 h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 3104 (* h1 h1) h2 h3 (* h4 h4)
 (* h5 h5) (* h6 h6) j2) (* 352 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* h6 h6)) 
(* 4 (* h1 h1) h2 h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
138 (* h1 h1) h2 h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1258 
(* h1 h1) h2 h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 5062 (* h1 h1
) h2 h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 11124 (* h1 h1) h2 h3 h4
 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 14602 (* h1 h1) h2 h3 h4 (* h5 h5 h5 
h5) h6 (* j2 j2 j2 j2)) (* 11766 (* h1 h1) h2 h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 
j2)) (* 5694 (* h1 h1) h2 h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 1512 (* h1 h1) 
h2 h3 h4 (* h5 h5 h5 h5) h6 j2) (* 168 (* h1 h1) h2 h3 h4 (* h5 h5 h5 h5) h6) 
(* 32 (* h1 h1) h2 h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 642 (* h1 h1) h2 h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 4710 (* h1 h1) h2 h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
17236 (* h1 h1) h2 h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 36276 
(* h1 h1) h2 h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 46826 (* h1 h1)
 h2 h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 37678 (* h1 h1) h2 h3 h4 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 18384 (* h1 h1) h2 h3 h4 (* h5 h5 h5) 
(* h6 h6) (* j2 j2)) (* 4952 (* h1 h1) h2 h3 h4 (* h5 h5 h5) (* h6 h6) j2) (* 
560 (* h1 h1) h2 h3 h4 (* h5 h5 h5) (* h6 h6)) (* 32 (* h1 h1) h2 h3 h4 (* h5 h5
) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 502 (* h1 h1) h2 h3 h4 (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3190 (* h1 h1) h2 h3 h4 (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 10748 (* h1 h1) h2 h3 h4 (* h5 h5)
 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 21500 (* h1 h1) h2 h3 h4 (* h5 h5) (* h6
 h6 h6) (* j2 j2 j2 j2 j2)) (* 26846 (* h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2)) (* 21118 (* h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)
) (* 10144 (* h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 2704 (* h1 h1
) h2 h3 h4 (* h5 h5) (* h6 h6 h6) j2) (* 304 (* h1 h1) h2 h3 h4 (* h5 h5) (* h6 
h6 h6)) (* 6 (* h1 h1) h2 h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 126 (* h1 h1) h2 h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2
 j2)) (* 964 (* h1 h1) h2 h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2))
 (* 3606 (* h1 h1) h2 h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
7652 (* h1 h1) h2 h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 9868 (* h1
 h1) h2 h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 7882 (* h1 h1) h2 h3 
(* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 3800 (* h1 h1) h2 h3 (* h5 h5 h5 h5) 
(* h6 h6) (* j2 j2)) (* 1008 (* h1 h1) h2 h3 (* h5 h5 h5 h5) (* h6 h6) j2) (* 
112 (* h1 h1) h2 h3 (* h5 h5 h5 h5) (* h6 h6)) (* 24 (* h1 h1) h2 h3 (* h5 h5 h5
) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 368 (* h1 h1) h2 h3 (* h5 h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2324 (* h1 h1) h2 h3 (* h5 h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 7822 (* h1 h1) h2 h3 (* h5 h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 15660 (* h1 h1) h2 h3 (* h5 h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2)) (* 19588 (* h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2)) (* 15444 (* h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)
) (* 7438 (* h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 1988 (* h1 h1)
 h2 h3 (* h5 h5 h5) (* h6 h6 h6) j2) (* 224 (* h1 h1) h2 h3 (* h5 h5 h5) (* h6 
h6 h6)) (* 16 (* h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 218 (* h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2
 j2)) (* 1248 (* h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 3916 (* h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
7460 (* h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 9002 (* h1
 h1) h2 h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 6912 (* h1 h1) h2 h3 
(* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 3264 (* h1 h1) h2 h3 (* h5 h5) (* h6 
h6 h6 h6) (* j2 j2)) (* 860 (* h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6 h6) j2) (* 96 
(* h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6 h6)) (* 6 (* h1 h1) h2 (* h4 h4 h4) (* h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 52 (* h1 h1) h2 (* h4 h4 h4) (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 194 (* h1 h1) h2 (* h4 h4 h4) (* h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2)) (* 408 (* h1 h1) h2 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2
 j2 j2 j2 j2)) (* 530 (* h1 h1) h2 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2))
 (* 436 (* h1 h1) h2 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 222 (* h1 h1)
 h2 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 64 (* h1 h1) h2 (* h4 h4 h4) (* 
h5 h5 h5) h6 j2) (* 8 (* h1 h1) h2 (* h4 h4 h4) (* h5 h5 h5) h6) (* 6 (* h1 h1) 
h2 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 52 (* h1 h1) h2 
(* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 194 (* h1 h1) h2 (* h4
 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 408 (* h1 h1) h2 (* h4 h4) (* 
h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 530 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5 h5
) h6 (* j2 j2 j2 j2)) (* 436 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 
j2)) (* 222 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 64 (* h1 h1)
 h2 (* h4 h4) (* h5 h5 h5 h5) h6 j2) (* 8 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5 h5)
 h6) (* 2 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 40 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 262 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 876 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 1742 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 2192 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 1770 
(* h1 h1) h2 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 892 (* h1 h1) h2 
(* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 256 (* h1 h1) h2 (* h4 h4) (* h5 
h5 h5) (* h6 h6) j2) (* 32 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5) (* h6 h6)) (* 2 
(* h1 h1) h2 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 34 
(* h1 h1) h2 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 210 
(* h1 h1) h2 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 682 (* h1
 h1) h2 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1334 (* h1 h1) h2
 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1662 (* h1 h1) h2 h4 (* h5 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 1334 (* h1 h1) h2 h4 (* h5 h5 h5 h5) (* 
h6 h6) (* j2 j2 j2)) (* 670 (* h1 h1) h2 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2))
 (* 192 (* h1 h1) h2 h4 (* h5 h5 h5 h5) (* h6 h6) j2) (* 24 (* h1 h1) h2 h4 (* 
h5 h5 h5 h5) (* h6 h6)) (* 4 (* h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 62 (* h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 368 (* h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2
 j2 j2 j2 j2)) (* 1170 (* h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 2260 (* h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 2794 (* h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 2232 (* h1
 h1) h2 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 1118 (* h1 h1) h2 h4 (* h5
 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 320 (* h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6 h6)
 j2) (* 40 (* h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6 h6)) (* 2 (* h1 h1) h2 (* h5 h5
 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 28 (* h1 h1) h2 (* h5 h5
 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 158 (* h1 h1) h2 (* h5 h5 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 488 (* h1 h1) h2 (* h5 h5 h5 h5
) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 926 (* h1 h1) h2 (* h5 h5 h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2)) (* 1132 (* h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2)) (* 898 (* h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 
448 (* h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 128 (* h1 h1) h2 (* 
h5 h5 h5 h5) (* h6 h6 h6) j2) (* 16 (* h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6 h6)) 
(* 2 (* h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 28 (* h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
158 (* h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 488 
(* h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 926 (* h1 h1
) h2 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1132 (* h1 h1) h2 (* h5
 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 898 (* h1 h1) h2 (* h5 h5 h5) (* h6 
h6 h6 h6) (* j2 j2 j2)) (* 448 (* h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 
j2)) (* 128 (* h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6 h6) j2) (* 16 (* h1 h1) h2 (* 
h5 h5 h5) (* h6 h6 h6 h6)) (* 140 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 816 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2
 j2 j2 j2 j2 j2 j2)) (* 2039 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 
j2 j2 j2 j2)) (* 2849 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 
j2)) (* 2432 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 1298 
(* h1 h1) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 423 (* h1 h1) (* h3 
h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2)) (* 77 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4 h4
) h5 j2) (* 6 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4 h4) h5) (* 10 (* h1 h1) (* h3 
h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 359 (* h1 h1) 
(* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2157 (* h1 
h1) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 5786 (* h1 
h1) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 8612 (* h1 h1)
 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 7713 (* h1 h1) (* h3
 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 4251 (* h1 h1) (* h3 h3 h3 h3
) (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 1410 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) 
(* h5 h5) (* j2 j2)) (* 258 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) j2) 
(* 20 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5)) (* 40 (* h1 h1) (* h3 h3 h3
 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 836 (* h1 h1) (* h3 h3 
h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4098 (* h1 h1) (* h3 h3 
h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 9603 (* h1 h1) (* h3 h3 h3 
h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 12983 (* h1 h1) (* h3 h3 h3 h3) 
(* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 10868 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4)
 h5 h6 (* j2 j2 j2 j2)) (* 5728 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 
j2 j2)) (* 1851 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 335 (* 
h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 h6 j2) (* 26 (* h1 h1) (* h3 h3 h3 h3) (* h4
 h4) h5 h6) (* 100 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 730 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2
 j2)) (* 2136 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) 
(* 3334 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 3066 
(* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 1712 (* h1 h1) (* 
h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2)) (* 570 (* h1 h1) (* h3 h3 h3 h3) h4 
(* h5 h5 h5) (* j2 j2)) (* 104 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5 h5) j2) (* 
8 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5 h5)) (* 50 (* h1 h1) (* h3 h3 h3 h3) h4 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1145 (* h1 h1) (* h3 h3 h3 h3) 
h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6480 (* h1 h1) (* h3 h3 h3 h3) 
h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 17062 (* h1 h1) (* h3 h3 h3 h3) h4 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 25205 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 
h5) h6 (* j2 j2 j2 j2 j2)) (* 22493 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) h6 
(* j2 j2 j2 j2)) (* 12372 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)
) (* 4098 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 749 (* h1 h1) 
(* h3 h3 h3 h3) h4 (* h5 h5) h6 j2) (* 58 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5)
 h6) (* 120 (* h1 h1) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
 j2)) (* 1528 (* h1 h1) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 6582 (* h1 h1) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2))
 (* 14536 (* h1 h1) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
19006 (* h1 h1) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 15580 (* 
h1 h1) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 8098 (* h1 h1) (* h3 
h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 2592 (* h1 h1) (* h3 h3 h3 h3) h4 h5 
(* h6 h6) (* j2 j2)) (* 466 (* h1 h1) (* h3 h3 h3 h3) h4 h5 (* h6 h6) j2) (* 36 
(* h1 h1) (* h3 h3 h3 h3) h4 h5 (* h6 h6)) (* 200 (* h1 h1) (* h3 h3 h3 h3) (* 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1460 (* h1 h1) (* h3 h3 h3 h3) (* 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 4272 (* h1 h1) (* h3 h3 h3 h3) (* h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 6668 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2)) (* 6132 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 
j2 j2 j2)) (* 3424 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 
1140 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2)) (* 208 (* h1 h1) (* h3
 h3 h3 h3) (* h5 h5 h5) h6 j2) (* 16 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5 h5) h6) 
(* 60 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 854 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 4332 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 10980 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2
 j2)) (* 15962 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2))
 (* 14134 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 7740
 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 2556 (* h1 h1) 
(* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 466 (* h1 h1) (* h3 h3 h3 h3) 
(* h5 h5) (* h6 h6) j2) (* 36 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6)) (* 
80 (* h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
832 (* h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
3300 (* h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 6972
 (* h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 8872 (* h1 
h1) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 7144 (* h1 h1) (* h3 
h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 3668 (* h1 h1) (* h3 h3 h3 h3) h5 
(* h6 h6 h6) (* j2 j2 j2)) (* 1164 (* h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* 
j2 j2)) (* 208 (* h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6 h6) j2) (* 16 (* h1 h1) (* 
h3 h3 h3 h3) h5 (* h6 h6 h6)) (* 70 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4 h4) h5 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 443 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4 h4) h5 
(* j2 j2 j2 j2 j2 j2 j2)) (* 1206 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* 
j2 j2 j2 j2 j2 j2)) (* 1841 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 
j2 j2 j2)) (* 1720 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2)) 
(* 1005 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2)) (* 358 (* h1 h1)
 (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2)) (* 71 (* h1 h1) (* h3 h3 h3) (* h4 
h4 h4 h4) h5 j2) (* 6 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4 h4) h5) (* 15 (* h1 h1)
 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 421 (* 
h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2441 
(* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 6635 
(* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 10305 
(* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 9831 (* h1 
h1) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 5855 (* h1 h1) (* h3
 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 2117 (* h1 h1) (* h3 h3 h3) (* 
h4 h4 h4) (* h5 h5) (* j2 j2)) (* 424 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h5 
h5) j2) (* 36 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5)) (* 20 (* h1 h1) (* 
h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 498 (* h1 h1) 
(* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2696 (* h1 h1) 
(* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 6930 (* h1 h1) (* 
h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 10272 (* h1 h1) (* h3 h3 
h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 9430 (* h1 h1) (* h3 h3 h3) (* h4 
h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 5448 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 h6 
(* j2 j2 j2)) (* 1926 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2)) (* 
380 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 h6 j2) (* 32 (* h1 h1) (* h3 h3 h3) 
(* h4 h4 h4) h5 h6) (* 20 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2
 j2 j2 j2 j2 j2 j2 j2)) (* 413 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 2372 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 6594 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2)) (* 10509 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) 
(* j2 j2 j2 j2 j2)) (* 10245 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2
 j2 j2 j2)) (* 6192 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) 
(* 2254 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 451 (* h1 h1
) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) j2) (* 38 (* h1 h1) (* h3 h3 h3) (* h4 h4)
 (* h5 h5 h5)) (* 120 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 2048 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 10705 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 27887 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6
 (* j2 j2 j2 j2 j2 j2)) (* 42380 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 
(* j2 j2 j2 j2 j2)) (* 39934 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2
 j2 j2 j2)) (* 23609 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2))
 (* 8499 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 1698 (* h1 
h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 j2) (* 144 (* h1 h1) (* h3 h3 h3) (* h4 
h4) (* h5 h5) h6) (* 80 (* h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 1222 (* h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 5911 (* h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 14454 (* h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6)
 (* j2 j2 j2 j2 j2 j2)) (* 20837 (* h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* 18800 (* h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2
 j2 j2 j2)) (* 10737 (* h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2))
 (* 3766 (* h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 739 (* h1 
h1) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) j2) (* 62 (* h1 h1) (* h3 h3 h3) (* h4 
h4) h5 (* h6 h6)) (* 50 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2
 j2 j2 j2 j2)) (* 390 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 
j2 j2 j2)) (* 1238 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 
j2)) (* 2116 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 
2142 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 1318 (* h1 h1
) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2)) (* 482 (* h1 h1) (* h3 h3 h3) h4
 (* h5 h5 h5 h5) (* j2 j2)) (* 96 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5 h5) j2) 
(* 8 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5 h5)) (* 80 (* h1 h1) (* h3 h3 h3) h4 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1327 (* h1 h1) (* h3 h3 h3) 
h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 7233 (* h1 h1) (* h3 h3 h3) 
h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 19731 (* h1 h1) (* h3 h3 h3) h4 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 31198 (* h1 h1) (* h3 h3 h3) h4 (* h5 
h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 30307 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) h6
 (* j2 j2 j2 j2)) (* 18287 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2
)) (* 6651 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2)) (* 1330 (* h1 h1
) (* h3 h3 h3) h4 (* h5 h5 h5) h6 j2) (* 112 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 
h5) h6) (* 255 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 3197 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 15028 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2
 j2 j2 j2 j2 j2)) (* 37216 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 55005 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2
 j2 j2 j2)) (* 50985 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2)) (* 29842 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 
10678 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 2126 (* h1 h1)
 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) j2) (* 180 (* h1 h1) (* h3 h3 h3) h4 (* h5 
h5) (* h6 h6)) (* 100 (* h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 1230 (* h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 5506 (* h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 12942 (* h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 18222 (* h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 16190 (* h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 9150 (* 
h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 3186 (* h1 h1) (* h3 h3 
h3) h4 h5 (* h6 h6 h6) (* j2 j2)) (* 622 (* h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6 
h6) j2) (* 52 (* h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6 h6)) (* 100 (* h1 h1) (* h3 
h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 780 (* h1 h1) (* h3 h3
 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2476 (* h1 h1) (* h3 h3 h3)
 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 4232 (* h1 h1) (* h3 h3 h3) (* h5 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 4284 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5 h5) 
h6 (* j2 j2 j2 j2)) (* 2636 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 
j2)) (* 964 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 192 (* h1 h1
) (* h3 h3 h3) (* h5 h5 h5 h5) h6 j2) (* 16 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5 
h5) h6) (* 80 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2 j2)) (* 1002 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2
 j2 j2 j2 j2)) (* 4978 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2
 j2 j2 j2 j2)) (* 13086 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 20360 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2
 j2 j2)) (* 19634 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2))
 (* 11806 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 4286 
(* h1 h1) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 856 (* h1 h1) (* h3 
h3 h3) (* h5 h5 h5) (* h6 h6) j2) (* 72 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5) (* 
h6 h6)) (* 150 (* h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 1570 (* h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 6764 (* h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 15964 (* h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2
 j2 j2 j2 j2)) (* 22930 (* h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2)) (* 20882 (* h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2
)) (* 12088 (* h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 4296 
(* h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 852 (* h1 h1) (* h3 
h3 h3) (* h5 h5) (* h6 h6 h6) j2) (* 72 (* h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 
h6 h6)) (* 40 (* h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 436 (* h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2
 j2)) (* 1848 (* h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 4212 (* h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
5816 (* h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 5100 (* h1
 h1) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 2856 (* h1 h1) (* h3 h3
 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 988 (* h1 h1) (* h3 h3 h3) h5 (* h6 h6 
h6 h6) (* j2 j2)) (* 192 (* h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6 h6) j2) (* 16 (* 
h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6 h6)) (* 55 (* h1 h1) (* h3 h3) (* h4 h4 h4 h4
) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 392 (* h1 h1) (* h3 h3) (* h4 h4 h4 
h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1203 (* h1 h1) (* h3 h3) (* h4 h4 h4 
h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2072 (* h1 h1) (* h3 h3) (* h4 h4 h4 h4)
 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 2185 (* h1 h1) (* h3 h3) (* h4 h4 h4 h4) (* h5
 h5) (* j2 j2 j2 j2)) (* 1440 (* h1 h1) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* 
j2 j2 j2)) (* 577 (* h1 h1) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2)) (* 
128 (* h1 h1) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) j2) (* 12 (* h1 h1) (* h3 h3) 
(* h4 h4 h4 h4) (* h5 h5)) (* 10 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 229 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5
 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1345 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5
 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 3837 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5
 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 6359 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5
 h5) (* j2 j2 j2 j2 j2)) (* 6545 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) 
(* j2 j2 j2 j2)) (* 4239 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 
j2)) (* 1675 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2)) (* 367 (* 
h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) j2) (* 34 (* h1 h1) (* h3 h3) (* h4 
h4 h4) (* h5 h5 h5)) (* 25 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 465 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2597 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 7251 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2)) (* 11889 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6
 (* j2 j2 j2 j2 j2)) (* 12175 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* 
j2 j2 j2 j2)) (* 7875 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)
) (* 3117 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 686 (* h1 
h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 j2) (* 64 (* h1 h1) (* h3 h3) (* h4 h4 
h4) (* h5 h5) h6) (* 5 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2
 j2 j2 j2 j2 j2 j2)) (* 107 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 642 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 1870 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* 
j2 j2 j2 j2 j2 j2)) (* 3137 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 
j2 j2 j2 j2)) (* 3239 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 
j2)) (* 2088 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 816 
(* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 176 (* h1 h1) (* h3 
h3) (* h4 h4) (* h5 h5 h5 h5) j2) (* 16 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 
h5 h5)) (* 70 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2
 j2 j2 j2)) (* 1118 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2
 j2 j2 j2 j2)) (* 5961 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2
 j2 j2 j2 j2)) (* 16275 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2)) (* 26326 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2
 j2 j2)) (* 26700 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2))
 (* 17133 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 6731 
(* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 1470 (* h1 h1) (* h3
 h3) (* h4 h4) (* h5 h5 h5) h6 j2) (* 136 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5
 h5) h6) (* 100 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 1255 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 6076 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 15771 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 24764 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5
) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 24665 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5)
 (* h6 h6) (* j2 j2 j2 j2)) (* 15660 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* 
h6 h6) (* j2 j2 j2)) (* 6121 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) 
(* j2 j2)) (* 1336 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) j2) (* 124 
(* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6)) (* 20 (* h1 h1) (* h3 h3) h4 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 348 (* h1 h1) (* h3 h3) h4
 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1986 (* h1 h1) (* h3 h3) h4 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 5680 (* h1 h1) (* h3 h3) h4 (* 
h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 9456 (* h1 h1) (* h3 h3) h4 (* h5 h5 
h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 9732 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) h6 
(* j2 j2 j2 j2)) (* 6266 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2))
 (* 2448 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 528 (* h1 h1) 
(* h3 h3) h4 (* h5 h5 h5 h5) h6 j2) (* 48 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5)
 h6) (* 140 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 1751 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 8468 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 21966 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2
 j2 j2 j2)) (* 34465 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2)) (* 34285 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) 
(* 21726 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 8468 (* 
h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 1841 (* h1 h1) (* h3 h3
) h4 (* h5 h5 h5) (* h6 h6) j2) (* 170 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* h6
 h6)) (* 125 (* h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 1335 (* h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 5929 (* h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 14601 (* h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2
 j2 j2 j2)) (* 22149 (* h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2)) (* 21545 (* h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) 
(* 13455 (* h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 5199 (* 
h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 1126 (* h1 h1) (* h3 h3
) h4 (* h5 h5) (* h6 h6 h6) j2) (* 104 (* h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6
 h6)) (* 20 (* h1 h1) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 268 (* h1 h1) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 1404 (* h1 h1) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 3880 (* h1 h1) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 6364 (* h1 h1) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 6508 (* h1 h1) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 
4180 (* h1 h1) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 1632 (* h1 
h1) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 352 (* h1 h1) (* h3 h3) 
(* h5 h5 h5 h5) (* h6 h6) j2) (* 32 (* h1 h1) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6
)) (* 80 (* h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 862 (* h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 3852 (* h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 9528 (* h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 14498 (* h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2
)) (* 14130 (* h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 
8832 (* h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 3412 (* h1 
h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 738 (* h1 h1) (* h3 h3) 
(* h5 h5 h5) (* h6 h6 h6) j2) (* 68 (* h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6
)) (* 50 (* h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 490 (* h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 2058 (* h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 4878 (* h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 7202 (* h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)
) (* 6870 (* h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 4230
 (* h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 1618 (* h1 h1) 
(* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 348 (* h1 h1) (* h3 h3) (* h5 
h5) (* h6 h6 h6 h6) j2) (* 32 (* h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6)) (* 
15 (* h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 106
 (* h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 325 (* 
h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 564 (* h1 h1) 
h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 605 (* h1 h1) h3 (* h4 h4
 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 410 (* h1 h1) h3 (* h4 h4 h4 h4) (* h5 
h5 h5) (* j2 j2 j2)) (* 171 (* h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2))
 (* 40 (* h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5 h5) j2) (* 4 (* h1 h1) h3 (* h4 h4 
h4 h4) (* h5 h5 h5)) (* 15 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 106 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 
j2 j2 j2 j2)) (* 325 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2
 j2)) (* 564 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 
605 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 410 (* h1 h1) 
h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 171 (* h1 h1) h3 (* h4 h4 h4) 
(* h5 h5 h5 h5) (* j2 j2)) (* 40 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5 h5) j2) 
(* 4 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5 h5)) (* 5 (* h1 h1) h3 (* h4 h4 h4) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 122 (* h1 h1) h3 (* h4 h4 h4)
 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 723 (* h1 h1) h3 (* h4 h4 h4) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2080 (* h1 h1) h3 (* h4 h4 h4) (* 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 3499 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2)) (* 3690 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* 
j2 j2 j2 j2)) (* 2477 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) 
(* 1028 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 240 (* h1 h1) h3
 (* h4 h4 h4) (* h5 h5 h5) h6 j2) (* 24 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) 
h6) (* 5 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2
)) (* 107 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2))
 (* 617 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
1755 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 2935 
(* h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 3085 (* h1 h1) 
h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 2067 (* h1 h1) h3 (* h4 h4) 
(* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 857 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) 
h6 (* j2 j2)) (* 200 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) h6 j2) (* 20 (* h1 
h1) h3 (* h4 h4) (* h5 h5 h5 h5) h6) (* 20 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 323 (* h1 h1) h3 (* h4 h4) (* h5 h5
 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1726 (* h1 h1) h3 (* h4 h4) (* h5
 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4745 (* h1 h1) h3 (* h4 h4) (* h5
 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 7792 (* h1 h1) h3 (* h4 h4) (* h5 h5
 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 8105 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2)) (* 5398 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6)
 (* j2 j2 j2)) (* 2231 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2)) 
(* 520 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) j2) (* 52 (* h1 h1) h3 (* 
h4 h4) (* h5 h5 h5) (* h6 h6)) (* 15 (* h1 h1) h3 h4 (* h5 h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 216 (* h1 h1) h3 h4 (* h5 h5 h5 h5) (* h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1109 (* h1 h1) h3 h4 (* h5 h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 2990 (* h1 h1) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 4857 (* h1 h1) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2)) (* 5020 (* h1 h1) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) 
(* 3331 (* h1 h1) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 1374 (* h1 h1
) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 320 (* h1 h1) h3 h4 (* h5 h5 h5 
h5) (* h6 h6) j2) (* 32 (* h1 h1) h3 h4 (* h5 h5 h5 h5) (* h6 h6)) (* 25 (* h1 
h1) h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 340 (* h1
 h1) h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1707 (* h1 
h1) h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4550 (* h1 h1) 
h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 7343 (* h1 h1) h3 h4 
(* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 7560 (* h1 h1) h3 h4 (* h5 h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 5005 (* h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6 
h6) (* j2 j2 j2)) (* 2062 (* h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) 
(* 480 (* h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6 h6) j2) (* 48 (* h1 h1) h3 h4 (* h5
 h5 h5) (* h6 h6 h6)) (* 10 (* h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 124 (* h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2
 j2 j2 j2 j2 j2 j2)) (* 598 (* h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 1560 (* h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 2486 (* h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2))
 (* 2540 (* h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1674 (* 
h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 688 (* h1 h1) h3 (* h5 
h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 160 (* h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6 
h6) j2) (* 16 (* h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6 h6)) (* 10 (* h1 h1) h3 (* 
h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 124 (* h1 h1) h3 
(* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 598 (* h1 h1) h3 
(* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1560 (* h1 h1) h3 (* 
h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2486 (* h1 h1) h3 (* h5 h5 
h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2540 (* h1 h1) h3 (* h5 h5 h5) (* h6 
h6 h6 h6) (* j2 j2 j2 j2)) (* 1674 (* h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* 
j2 j2 j2)) (* 688 (* h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 160 
(* h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6 h6) j2) (* 16 (* h1 h1) h3 (* h5 h5 h5) 
(* h6 h6 h6 h6)) (* 32 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 
j2)) (* 624 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 2064 h1
 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2)) (* 2768 h1 (* h2 h2 h2 h2) 
(* h3 h3 h3) h4 h5 (* j2 j2 j2)) (* 1776 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 
(* j2 j2)) (* 544 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 j2) (* 64 h1 (* h2 h2 h2
 h2) (* h3 h3 h3) h4 h5) (* 128 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 
j2 j2 j2 j2)) (* 576 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) 
(* 1056 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 1008 h1 (* h2 
h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2)) (* 528 h1 (* h2 h2 h2 h2) (* h3 h3 h3
) h4 h6 (* j2 j2)) (* 144 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h6 j2) (* 16 h1 (* 
h2 h2 h2 h2) (* h3 h3 h3) h4 h6) (* 160 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5
) (* j2 j2 j2 j2 j2)) (* 784 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 
j2 j2)) (* 1248 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2)) (* 864 
h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2)) (* 272 h1 (* h2 h2 h2 h2) 
(* h3 h3 h3) (* h5 h5) j2) (* 32 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5)) (* 
96 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 688 h1 (* h2 
h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 1824 h1 (* h2 h2 h2 h2) (* 
h3 h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 2256 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h5 h6 
(* j2 j2 j2)) (* 1392 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2)) (* 416 h1
 (* h2 h2 h2 h2) (* h3 h3 h3) h5 h6 j2) (* 48 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h5
 h6) (* 128 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
576 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1056 h1 (* 
h2 h2 h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 1008 h1 (* h2 h2 h2 h2) 
(* h3 h3 h3) (* h6 h6) (* j2 j2 j2)) (* 528 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* 
h6 h6) (* j2 j2)) (* 144 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h6 h6) j2) (* 16 h1 
(* h2 h2 h2 h2) (* h3 h3 h3) (* h6 h6)) (* 48 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4
 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 560 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 
(* j2 j2 j2 j2 j2)) (* 1872 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 
j2 j2)) (* 2784 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 2048 
h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2)) (* 720 h1 (* h2 h2 h2 h2) 
(* h3 h3) (* h4 h4) h5 j2) (* 96 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5) (* 
64 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 320 h1 
(* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 656 h1 (* h2 h2 h2
 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2)) (* 704 h1 (* h2 h2 h2 h2) (* h3 h3)
 (* h4 h4) h6 (* j2 j2 j2)) (* 416 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h6 (* 
j2 j2)) (* 128 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h6 j2) (* 16 h1 (* h2 h2 
h2 h2) (* h3 h3) (* h4 h4) h6) (* 64 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) 
(* j2 j2 j2 j2 j2 j2)) (* 784 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2
 j2 j2 j2)) (* 2560 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) 
(* 3744 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 2736 h1 (* h2
 h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2)) (* 960 h1 (* h2 h2 h2 h2) (* h3 h3)
 h4 (* h5 h5) j2) (* 128 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5)) (* 288 h1 
(* h2 h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 1824 h1 (* h2 h2 h2
 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 4720 h1 (* h2 h2 h2 h2) (* h3 h3)
 h4 h5 h6 (* j2 j2 j2 j2)) (* 6192 h1 (* h2 h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 
j2 j2)) (* 4272 h1 (* h2 h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2)) (* 1456 h1 (* 
h2 h2 h2 h2) (* h3 h3) h4 h5 h6 j2) (* 192 h1 (* h2 h2 h2 h2) (* h3 h3) h4 h5 h6
) (* 128 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 640
 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1312 h1 (* h2 
h2 h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 1408 h1 (* h2 h2 h2 h2) (* 
h3 h3) h4 (* h6 h6) (* j2 j2 j2)) (* 832 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h6 
h6) (* j2 j2)) (* 256 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h6 h6) j2) (* 32 h1 (* 
h2 h2 h2 h2) (* h3 h3) h4 (* h6 h6)) (* 80 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5
 h5) (* j2 j2 j2 j2 j2)) (* 432 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 
j2 j2 j2)) (* 800 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2)) (* 656
 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2)) (* 240 h1 (* h2 h2 h2 h2) 
(* h3 h3) (* h5 h5 h5) j2) (* 32 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5)) (* 
128 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 912 h1 
(* h2 h2 h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 2512 h1 (* h2 h2 
h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 3440 h1 (* h2 h2 h2 h2) (* h3 
h3) (* h5 h5) h6 (* j2 j2 j2)) (* 2448 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) h6
 (* j2 j2)) (* 848 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) h6 j2) (* 112 h1 (* h2
 h2 h2 h2) (* h3 h3) (* h5 h5) h6) (* 240 h1 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 1264 h1 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* 
j2 j2 j2 j2 j2)) (* 2848 h1 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 
j2)) (* 3408 h1 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 2224 h1 
(* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2)) (* 736 h1 (* h2 h2 h2 h2) (* 
h3 h3) h5 (* h6 h6) j2) (* 96 h1 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6)) (* 64 
h1 (* h2 h2 h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 320 h1 (* h2
 h2 h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 656 h1 (* h2 h2 h2 h2) 
(* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 704 h1 (* h2 h2 h2 h2) (* h3 h3) (* 
h6 h6 h6) (* j2 j2 j2)) (* 416 h1 (* h2 h2 h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 
j2)) (* 128 h1 (* h2 h2 h2 h2) (* h3 h3) (* h6 h6 h6) j2) (* 16 h1 (* h2 h2 h2 
h2) (* h3 h3) (* h6 h6 h6)) (* 32 h1 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* 
j2 j2 j2 j2 j2 j2)) (* 336 h1 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2
 j2 j2)) (* 1152 h1 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 
1856 h1 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 1536 h1 (* h2 h2
 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2)) (* 624 h1 (* h2 h2 h2 h2) h3 (* h4 h4)
 (* h5 h5) j2) (* 96 h1 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5)) (* 80 h1 (* h2 
h2 h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 416 h1 (* h2 h2 h2 h2) h3
 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 896 h1 (* h2 h2 h2 h2) h3 (* h4 h4) h5 
h6 (* j2 j2 j2 j2)) (* 1024 h1 (* h2 h2 h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2)) 
(* 656 h1 (* h2 h2 h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2)) (* 224 h1 (* h2 h2 h2 h2
) h3 (* h4 h4) h5 h6 j2) (* 32 h1 (* h2 h2 h2 h2) h3 (* h4 h4) h5 h6) (* 16 h1 
(* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 208 h1 (* h2 h2 h2 
h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 752 h1 (* h2 h2 h2 h2) h3 h4 (* h5
 h5 h5) (* j2 j2 j2 j2)) (* 1232 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 
j2)) (* 1024 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2)) (* 416 h1 (* h2 h2
 h2 h2) h3 h4 (* h5 h5 h5) j2) (* 64 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5)) (* 
160 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 1088 h1 (* 
h2 h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 2992 h1 (* h2 h2 h2 h2) 
h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 4240 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5) 
h6 (* j2 j2 j2)) (* 3248 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2)) (* 
1264 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5) h6 j2) (* 192 h1 (* h2 h2 h2 h2) h3 h4 
(* h5 h5) h6) (* 160 h1 (* h2 h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)
) (* 832 h1 (* h2 h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1792 h1 
(* h2 h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 2048 h1 (* h2 h2 h2 h2) 
h3 h4 h5 (* h6 h6) (* j2 j2 j2)) (* 1312 h1 (* h2 h2 h2 h2) h3 h4 h5 (* h6 h6) 
(* j2 j2)) (* 448 h1 (* h2 h2 h2 h2) h3 h4 h5 (* h6 h6) j2) (* 64 h1 (* h2 h2 h2
 h2) h3 h4 h5 (* h6 h6)) (* 32 h1 (* h2 h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2
 j2 j2 j2)) (* 256 h1 (* h2 h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
800 h1 (* h2 h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 1248 h1 (* h2 h2 
h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 1024 h1 (* h2 h2 h2 h2) h3 (* h5 h5 
h5) h6 (* j2 j2)) (* 416 h1 (* h2 h2 h2 h2) h3 (* h5 h5 h5) h6 j2) (* 64 h1 (* 
h2 h2 h2 h2) h3 (* h5 h5 h5) h6) (* 128 h1 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6
) (* j2 j2 j2 j2 j2 j2)) (* 752 h1 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2)) (* 1840 h1 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2))
 (* 2384 h1 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 1712 h1 (* 
h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2)) (* 640 h1 (* h2 h2 h2 h2) h3 (* 
h5 h5) (* h6 h6) j2) (* 96 h1 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6)) (* 80 h1 
(* h2 h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 416 h1 (* h2 h2 h2 
h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 896 h1 (* h2 h2 h2 h2) h3 h5 (* h6
 h6 h6) (* j2 j2 j2 j2)) (* 1024 h1 (* h2 h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 
j2)) (* 656 h1 (* h2 h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2)) (* 224 h1 (* h2 h2 
h2 h2) h3 h5 (* h6 h6 h6) j2) (* 32 h1 (* h2 h2 h2 h2) h3 h5 (* h6 h6 h6)) (* 16
 h1 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 112 h1 (* 
h2 h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 320 h1 (* h2 h2 h2 h2
) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 480 h1 (* h2 h2 h2 h2) (* h4 h4) 
(* h5 h5) h6 (* j2 j2 j2)) (* 400 h1 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* 
j2 j2)) (* 176 h1 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5) h6 j2) (* 32 h1 (* h2 h2 
h2 h2) (* h4 h4) (* h5 h5) h6) (* 16 h1 (* h2 h2 h2 h2) h4 (* h5 h5 h5) h6 (* j2
 j2 j2 j2 j2 j2)) (* 112 h1 (* h2 h2 h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2
)) (* 320 h1 (* h2 h2 h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 480 h1 (* h2
 h2 h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 400 h1 (* h2 h2 h2 h2) h4 (* h5 
h5 h5) h6 (* j2 j2)) (* 176 h1 (* h2 h2 h2 h2) h4 (* h5 h5 h5) h6 j2) (* 32 h1 
(* h2 h2 h2 h2) h4 (* h5 h5 h5) h6) (* 32 h1 (* h2 h2 h2 h2) h4 (* h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 224 h1 (* h2 h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2)) (* 640 h1 (* h2 h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2
)) (* 960 h1 (* h2 h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 800 h1 (* 
h2 h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 352 h1 (* h2 h2 h2 h2) h4 (* 
h5 h5) (* h6 h6) j2) (* 64 h1 (* h2 h2 h2 h2) h4 (* h5 h5) (* h6 h6)) (* 16 h1 
(* h2 h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 112 h1 (* h2 h2
 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 320 h1 (* h2 h2 h2 h2) (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 480 h1 (* h2 h2 h2 h2) (* h5 h5 h5) (* 
h6 h6) (* j2 j2 j2)) (* 400 h1 (* h2 h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2))
 (* 176 h1 (* h2 h2 h2 h2) (* h5 h5 h5) (* h6 h6) j2) (* 32 h1 (* h2 h2 h2 h2) 
(* h5 h5 h5) (* h6 h6)) (* 16 h1 (* h2 h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2
 j2 j2 j2 j2)) (* 112 h1 (* h2 h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2)) (* 320 h1 (* h2 h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 480 h1
 (* h2 h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 400 h1 (* h2 h2 h2 h2) 
(* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 176 h1 (* h2 h2 h2 h2) (* h5 h5) (* h6 h6 
h6) j2) (* 32 h1 (* h2 h2 h2 h2) (* h5 h5) (* h6 h6 h6)) (* 32 h1 (* h2 h2 h2) 
(* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 640 h1 (* h2 h2 h2) (* h3 h3 
h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 2376 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 
h5 (* j2 j2 j2 j2 j2)) (* 3800 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2
 j2)) (* 3160 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2)) (* 1432 h1 (* 
h2 h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2)) (* 336 h1 (* h2 h2 h2) (* h3 h3 h3 h3
) h4 h5 j2) (* 32 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5) (* 128 h1 (* h2 h2 h2) 
(* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 640 h1 (* h2 h2 h2) (* h3 h3 
h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2)) (* 1344 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 
h6 (* j2 j2 j2 j2 j2)) (* 1536 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2
 j2)) (* 1032 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2)) (* 408 h1 (* 
h2 h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2)) (* 88 h1 (* h2 h2 h2) (* h3 h3 h3 h3)
 h4 h6 j2) (* 8 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h6) (* 160 h1 (* h2 h2 h2) 
(* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 864 h1 (* h2 h2 h2) (* h3 h3
 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 1640 h1 (* h2 h2 h2) (* h3 h3 h3 h3) 
(* h5 h5) (* j2 j2 j2 j2)) (* 1488 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* 
j2 j2 j2)) (* 704 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2)) (* 168 h1
 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) j2) (* 16 h1 (* h2 h2 h2) (* h3 h3 h3 h3
) (* h5 h5)) (* 96 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2
)) (* 736 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 2168 
h1 (* h2 h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 3168 h1 (* h2 h2 h2
) (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 2520 h1 (* h2 h2 h2) (* h3 h3 h3 h3)
 h5 h6 (* j2 j2 j2)) (* 1112 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2)) 
(* 256 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h5 h6 j2) (* 24 h1 (* h2 h2 h2) (* h3 h3 
h3 h3) h5 h6) (* 128 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2)) (* 640 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2))
 (* 1344 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1536 
h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 1032 h1 (* h2 h2 
h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2)) (* 408 h1 (* h2 h2 h2) (* h3 h3 h3 
h3) (* h6 h6) (* j2 j2)) (* 88 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h6 h6) j2) (* 
8 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h6 h6)) (* 96 h1 (* h2 h2 h2) (* h3 h3 h3) 
(* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 1648 h1 (* h2 h2 h2) (* h3 h3 h3) (* 
h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 6912 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) 
h5 (* j2 j2 j2 j2 j2)) (* 12848 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 
j2 j2 j2)) (* 12432 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 
6488 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2)) (* 1728 h1 (* h2 h2 h2
) (* h3 h3 h3) (* h4 h4) h5 j2) (* 184 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5
) (* 128 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
704 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 1632 h1 
(* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 2064 h1 (* h2 h2 
h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2)) (* 1536 h1 (* h2 h2 h2) (* h3 h3 
h3) (* h4 h4) h6 (* j2 j2 j2)) (* 672 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h6 
(* j2 j2)) (* 160 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h6 j2) (* 16 h1 (* h2 
h2 h2) (* h3 h3 h3) (* h4 h4) h6) (* 96 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5
) (* j2 j2 j2 j2 j2 j2 j2)) (* 1640 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) 
(* j2 j2 j2 j2 j2 j2)) (* 7056 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 
j2 j2 j2 j2)) (* 13656 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)
) (* 13696 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 7304 h1 
(* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2)) (* 1960 h1 (* h2 h2 h2) (* h3 
h3 h3) h4 (* h5 h5) j2) (* 208 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5)) (* 480
 h1 (* h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 4512 h1 (* 
h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 15880 h1 (* h2 h2 h2) 
(* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 27464 h1 (* h2 h2 h2) (* h3 h3 h3) 
h4 h5 h6 (* j2 j2 j2 j2)) (* 25672 h1 (* h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 
j2 j2)) (* 13160 h1 (* h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2)) (* 3472 h1 (* 
h2 h2 h2) (* h3 h3 h3) h4 h5 h6 j2) (* 368 h1 (* h2 h2 h2) (* h3 h3 h3) h4 h5 h6
) (* 256 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
1408 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3264 h1
 (* h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 4128 h1 (* h2 h2 
h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 3072 h1 (* h2 h2 h2) (* h3 h3 
h3) h4 (* h6 h6) (* j2 j2 j2)) (* 1344 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6)
 (* j2 j2)) (* 320 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6) j2) (* 32 h1 (* h2 
h2 h2) (* h3 h3 h3) h4 (* h6 h6)) (* 160 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 
h5) (* j2 j2 j2 j2 j2 j2)) (* 944 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* 
j2 j2 j2 j2 j2)) (* 2032 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 
j2)) (* 2112 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2)) (* 1136 h1 
(* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2)) (* 304 h1 (* h2 h2 h2) (* h3 
h3 h3) (* h5 h5 h5) j2) (* 32 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5)) (* 192 
h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1864 h1 
(* h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 6984 h1 (* h2 
h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 12952 h1 (* h2 h2 h2) 
(* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 12808 h1 (* h2 h2 h2) (* h3 h3 h3)
 (* h5 h5) h6 (* j2 j2 j2)) (* 6792 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 
(* j2 j2)) (* 1816 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 j2) (* 192 h1 (* h2
 h2 h2) (* h3 h3 h3) (* h5 h5) h6) (* 384 h1 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2864 h1 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 8968 h1 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 
j2 j2 j2 j2)) (* 14616 h1 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)
) (* 13240 h1 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 6672 h1 
(* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2)) (* 1744 h1 (* h2 h2 h2) (* h3 
h3 h3) h5 (* h6 h6) j2) (* 184 h1 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6)) (* 128
 h1 (* h2 h2 h2) (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 704 h1 
(* h2 h2 h2) (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1632 h1 (* h2 
h2 h2) (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2064 h1 (* h2 h2 h2) (* 
h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1536 h1 (* h2 h2 h2) (* h3 h3 h3) (* 
h6 h6 h6) (* j2 j2 j2)) (* 672 h1 (* h2 h2 h2) (* h3 h3 h3) (* h6 h6 h6) (* j2 
j2)) (* 160 h1 (* h2 h2 h2) (* h3 h3 h3) (* h6 h6 h6) j2) (* 16 h1 (* h2 h2 h2) 
(* h3 h3 h3) (* h6 h6 h6)) (* 40 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2
 j2 j2 j2 j2 j2 j2)) (* 672 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 
j2 j2 j2 j2)) (* 3056 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 
j2)) (* 6344 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 6968 
h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 4160 h1 (* h2 h2 h2) 
(* h3 h3) (* h4 h4 h4) h5 (* j2 j2)) (* 1264 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 
h4) h5 j2) (* 152 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5) (* 32 h1 (* h2 h2 
h2) (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 192 h1 (* h2 h2 h2) 
(* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 488 h1 (* h2 h2 h2) (* h3 h3
) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 680 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 
h4) h6 (* j2 j2 j2 j2)) (* 560 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h6 (* j2 
j2 j2)) (* 272 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h6 (* j2 j2)) (* 72 h1 (* 
h2 h2 h2) (* h3 h3) (* h4 h4 h4) h6 j2) (* 8 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 
h4) h6) (* 120 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 
j2 j2)) (* 1816 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 
j2)) (* 7856 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) 
(* 15768 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 16888
 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 9888 h1 (* h2 h2
 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 2960 h1 (* h2 h2 h2) (* h3 h3) 
(* h4 h4) (* h5 h5) j2) (* 352 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5)) 
(* 328 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
3112 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 11600 
h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 21984 h1 (* h2 
h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 23032 h1 (* h2 h2 h2) (* h3
 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 13400 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) 
h5 h6 (* j2 j2)) (* 4016 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 j2) (* 480 h1
 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6) (* 96 h1 (* h2 h2 h2) (* h3 h3) (* h4 
h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 576 h1 (* h2 h2 h2) (* h3 h3) (* h4 
h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1464 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4)
 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2040 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h6
 h6) (* j2 j2 j2 j2)) (* 1680 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* 
j2 j2 j2)) (* 816 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2)) (* 
216 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) j2) (* 24 h1 (* h2 h2 h2) (* 
h3 h3) (* h4 h4) (* h6 h6)) (* 56 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 888 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2
 j2 j2 j2 j2)) (* 3992 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 
j2)) (* 8360 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 9296 
h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2)) (* 5584 h1 (* h2 h2 h2) 
(* h3 h3) h4 (* h5 h5 h5) (* j2 j2)) (* 1688 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 
h5 h5) j2) (* 200 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5)) (* 464 h1 (* h2 h2 
h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 4640 h1 (* h2 h2 h2) 
(* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 17488 h1 (* h2 h2 h2) (* h3 
h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 33032 h1 (* h2 h2 h2) (* h3 h3) h4 
(* h5 h5) h6 (* j2 j2 j2 j2)) (* 34320 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6
 (* j2 j2 j2)) (* 19776 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 
5872 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 j2) (* 696 h1 (* h2 h2 h2) (* h3 
h3) h4 (* h5 h5) h6) (* 536 h1 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 4208 h1 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 14032 h1 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)
) (* 24936 h1 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 25160 
h1 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 14320 h1 (* h2 h2 h2)
 (* h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 4240 h1 (* h2 h2 h2) (* h3 h3) h4 h5 
(* h6 h6) j2) (* 504 h1 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6)) (* 96 h1 (* h2 
h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 576 h1 (* h2 h2 h2
) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1464 h1 (* h2 h2 h2) (* h3
 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2040 h1 (* h2 h2 h2) (* h3 h3) h4 
(* h6 h6 h6) (* j2 j2 j2 j2)) (* 1680 h1 (* h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6) 
(* j2 j2 j2)) (* 816 h1 (* h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2)) (* 216
 h1 (* h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6) j2) (* 24 h1 (* h2 h2 h2) (* h3 h3) 
h4 (* h6 h6 h6)) (* 40 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 
j2 j2)) (* 256 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 
616 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 728 h1 (* h2 
h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 448 h1 (* h2 h2 h2) (* h3 h3) 
(* h5 h5 h5 h5) (* j2 j2)) (* 136 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) j2) 
(* 16 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5)) (* 104 h1 (* h2 h2 h2) (* h3 h3
) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1040 h1 (* h2 h2 h2) (* h3 h3) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 4104 h1 (* h2 h2 h2) (* h3 h3) (* h5 
h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 8224 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 
(* j2 j2 j2 j2)) (* 9008 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2))
 (* 5384 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2)) (* 1624 h1 (* h2 
h2 h2) (* h3 h3) (* h5 h5 h5) h6 j2) (* 192 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 
h5) h6) (* 344 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 2824 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 9632 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 17264 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 17432
 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 9888 h1 (* h2 h2
 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 2912 h1 (* h2 h2 h2) (* h3 h3) 
(* h5 h5) (* h6 h6) j2) (* 344 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6)) 
(* 248 h1 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
1768 h1 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 5488 h1
 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 9296 h1 (* h2 h2 
h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 9096 h1 (* h2 h2 h2) (* h3 h3)
 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 5080 h1 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6)
 (* j2 j2)) (* 1488 h1 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) j2) (* 176 h1 (* 
h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6)) (* 32 h1 (* h2 h2 h2) (* h3 h3) (* h6 h6 h6
 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 192 h1 (* h2 h2 h2) (* h3 h3) (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 488 h1 (* h2 h2 h2) (* h3 h3) (* h6 h6 h6 h6) (* j2 j2
 j2 j2 j2)) (* 680 h1 (* h2 h2 h2) (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) 
(* 560 h1 (* h2 h2 h2) (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 272 h1 (* h2 
h2 h2) (* h3 h3) (* h6 h6 h6 h6) (* j2 j2)) (* 72 h1 (* h2 h2 h2) (* h3 h3) (* 
h6 h6 h6 h6) j2) (* 8 h1 (* h2 h2 h2) (* h3 h3) (* h6 h6 h6 h6)) (* 24 h1 (* h2 
h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 368 h1 (* h2 h2 h2
) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1720 h1 (* h2 h2 h2) h3 
(* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 3816 h1 (* h2 h2 h2) h3 (* h4 h4 
h4) (* h5 h5) (* j2 j2 j2 j2)) (* 4592 h1 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5)
 (* j2 j2 j2)) (* 3064 h1 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 
1056 h1 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) j2) (* 144 h1 (* h2 h2 h2) h3 (* 
h4 h4 h4) (* h5 h5)) (* 40 h1 (* h2 h2 h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 
j2 j2 j2)) (* 248 h1 (* h2 h2 h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) 
(* 656 h1 (* h2 h2 h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 960 h1 (* h2
 h2 h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 840 h1 (* h2 h2 h2) h3 (* h4 
h4 h4) h5 h6 (* j2 j2 j2)) (* 440 h1 (* h2 h2 h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2
)) (* 128 h1 (* h2 h2 h2) h3 (* h4 h4 h4) h5 h6 j2) (* 16 h1 (* h2 h2 h2) h3 (* 
h4 h4 h4) h5 h6) (* 32 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 
j2 j2 j2)) (* 480 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2
)) (* 2192 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 4760
 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 5616 h1 (* h2 h2 
h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 3680 h1 (* h2 h2 h2) h3 (* h4 h4)
 (* h5 h5 h5) (* j2 j2)) (* 1248 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) j2) 
(* 168 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5)) (* 176 h1 (* h2 h2 h2) h3 (* 
h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1728 h1 (* h2 h2 h2) h3 (* h4 
h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 6744 h1 (* h2 h2 h2) h3 (* h4 h4) (* 
h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 13656 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6
 (* j2 j2 j2 j2)) (* 15608 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2
)) (* 10104 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 3424 h1 (* 
h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 j2) (* 464 h1 (* h2 h2 h2) h3 (* h4 h4) (* 
h5 h5) h6) (* 120 h1 (* h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2
 j2)) (* 744 h1 (* h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 1968 h1 (* h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2880 h1
 (* h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 2520 h1 (* h2 h2 h2)
 h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 1320 h1 (* h2 h2 h2) h3 (* h4 h4) h5
 (* h6 h6) (* j2 j2)) (* 384 h1 (* h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6) j2) (* 48
 h1 (* h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6)) (* 8 h1 (* h2 h2 h2) h3 h4 (* h5 h5 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 112 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2)) (* 480 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 
j2 j2)) (* 992 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 1128 h1
 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2)) (* 720 h1 (* h2 h2 h2) h3 h4 
(* h5 h5 h5 h5) (* j2 j2)) (* 240 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) j2) (* 
32 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5)) (* 136 h1 (* h2 h2 h2) h3 h4 (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1368 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 5360 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2
 j2 j2)) (* 10800 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 
12232 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 7832 h1 (* h2 h2 h2
) h3 h4 (* h5 h5 h5) h6 (* j2 j2)) (* 2624 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5) h6
 j2) (* 352 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5) h6) (* 280 h1 (* h2 h2 h2) h3 h4 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2352 h1 (* h2 h2 h2) h3 h4 (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 8328 h1 (* h2 h2 h2) h3 h4 (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 15864 h1 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6)
 (* j2 j2 j2 j2)) (* 17440 h1 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2
)) (* 11016 h1 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 3680 h1 (* 
h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) j2) (* 496 h1 (* h2 h2 h2) h3 h4 (* h5 h5) 
(* h6 h6)) (* 120 h1 (* h2 h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 744 h1 (* h2 h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1968 h1
 (* h2 h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2880 h1 (* h2 h2 h2) 
h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 2520 h1 (* h2 h2 h2) h3 h4 h5 (* h6 h6
 h6) (* j2 j2 j2)) (* 1320 h1 (* h2 h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2)) (* 
384 h1 (* h2 h2 h2) h3 h4 h5 (* h6 h6 h6) j2) (* 48 h1 (* h2 h2 h2) h3 h4 h5 (* 
h6 h6 h6)) (* 16 h1 (* h2 h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2))
 (* 144 h1 (* h2 h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 528 h1 
(* h2 h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 1024 h1 (* h2 h2 h2) 
h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 1136 h1 (* h2 h2 h2) h3 (* h5 h5 h5 h5
) h6 (* j2 j2 j2)) (* 720 h1 (* h2 h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 
240 h1 (* h2 h2 h2) h3 (* h5 h5 h5 h5) h6 j2) (* 32 h1 (* h2 h2 h2) h3 (* h5 h5 
h5 h5) h6) (* 104 h1 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2
 j2)) (* 888 h1 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 3168 h1 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 6040 h1
 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 6616 h1 (* h2 h2 h2)
 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 4152 h1 (* h2 h2 h2) h3 (* h5 h5 h5)
 (* h6 h6) (* j2 j2)) (* 1376 h1 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) j2) (* 
184 h1 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6)) (* 128 h1 (* h2 h2 h2) h3 (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 992 h1 (* h2 h2 h2) h3 (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3304 h1 (* h2 h2 h2) h3 (* h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2)) (* 6024 h1 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2)) (* 6424 h1 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) 
(* 3976 h1 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 1312 h1 (* h2 h2
 h2) h3 (* h5 h5) (* h6 h6 h6) j2) (* 176 h1 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 
h6)) (* 40 h1 (* h2 h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
248 h1 (* h2 h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 656 h1 (* h2
 h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 960 h1 (* h2 h2 h2) h3 h5 
(* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 840 h1 (* h2 h2 h2) h3 h5 (* h6 h6 h6 h6) 
(* j2 j2 j2)) (* 440 h1 (* h2 h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2)) (* 128 h1 
(* h2 h2 h2) h3 h5 (* h6 h6 h6 h6) j2) (* 16 h1 (* h2 h2 h2) h3 h5 (* h6 h6 h6 
h6)) (* 8 h1 (* h2 h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 64 h1 (* h2 h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 216 h1
 (* h2 h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 400 h1 (* h2 h2 
h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 440 h1 (* h2 h2 h2) (* h4 h4 
h4) (* h5 h5) h6 (* j2 j2 j2)) (* 288 h1 (* h2 h2 h2) (* h4 h4 h4) (* h5 h5) h6 
(* j2 j2)) (* 104 h1 (* h2 h2 h2) (* h4 h4 h4) (* h5 h5) h6 j2) (* 16 h1 (* h2 
h2 h2) (* h4 h4 h4) (* h5 h5) h6) (* 16 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 128 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 432 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2
 j2 j2 j2)) (* 800 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) 
(* 880 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 576 h1 (* h2 
h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 208 h1 (* h2 h2 h2) (* h4 h4) (* 
h5 h5 h5) h6 j2) (* 32 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5) h6) (* 24 h1 (* h2
 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 192 h1 (* h2 
h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 648 h1 (* h2 h2 
h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1200 h1 (* h2 h2 h2) 
(* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 1320 h1 (* h2 h2 h2) (* h4 h4)
 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 864 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5) 
(* h6 h6) (* j2 j2)) (* 312 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) j2) 
(* 48 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6)) (* 8 h1 (* h2 h2 h2) h4 (* 
h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 64 h1 (* h2 h2 h2) h4 (* h5 h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 216 h1 (* h2 h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2
 j2 j2 j2 j2)) (* 400 h1 (* h2 h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 
440 h1 (* h2 h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 288 h1 (* h2 h2 h2) 
h4 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 104 h1 (* h2 h2 h2) h4 (* h5 h5 h5 h5) h6 j2
) (* 16 h1 (* h2 h2 h2) h4 (* h5 h5 h5 h5) h6) (* 32 h1 (* h2 h2 h2) h4 (* h5 h5
 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 256 h1 (* h2 h2 h2) h4 (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 864 h1 (* h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6
) (* j2 j2 j2 j2 j2)) (* 1600 h1 (* h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2
 j2 j2)) (* 1760 h1 (* h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 1152
 h1 (* h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 416 h1 (* h2 h2 h2) h4 
(* h5 h5 h5) (* h6 h6) j2) (* 64 h1 (* h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6)) (* 
24 h1 (* h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 192 h1
 (* h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 648 h1 (* h2 
h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1200 h1 (* h2 h2 h2) h4 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1320 h1 (* h2 h2 h2) h4 (* h5 h5) (* 
h6 h6 h6) (* j2 j2 j2)) (* 864 h1 (* h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 
j2)) (* 312 h1 (* h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6) j2) (* 48 h1 (* h2 h2 h2) 
h4 (* h5 h5) (* h6 h6 h6)) (* 8 h1 (* h2 h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 64 h1 (* h2 h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 216 h1 (* h2 h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 400 h1 (* h2 h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 440 h1 (* 
h2 h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 288 h1 (* h2 h2 h2) (* h5 
h5 h5 h5) (* h6 h6) (* j2 j2)) (* 104 h1 (* h2 h2 h2) (* h5 h5 h5 h5) (* h6 h6) 
j2) (* 16 h1 (* h2 h2 h2) (* h5 h5 h5 h5) (* h6 h6)) (* 16 h1 (* h2 h2 h2) (* h5
 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 128 h1 (* h2 h2 h2) (* h5 h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 432 h1 (* h2 h2 h2) (* h5 h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 800 h1 (* h2 h2 h2) (* h5 h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2)) (* 880 h1 (* h2 h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) 
(* 576 h1 (* h2 h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 208 h1 (* h2 h2 
h2) (* h5 h5 h5) (* h6 h6 h6) j2) (* 32 h1 (* h2 h2 h2) (* h5 h5 h5) (* h6 h6 h6
)) (* 8 h1 (* h2 h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
64 h1 (* h2 h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 216 h1 
(* h2 h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 400 h1 (* h2 h2 h2
) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 440 h1 (* h2 h2 h2) (* h5 h5) 
(* h6 h6 h6 h6) (* j2 j2 j2)) (* 288 h1 (* h2 h2 h2) (* h5 h5) (* h6 h6 h6 h6) 
(* j2 j2)) (* 104 h1 (* h2 h2 h2) (* h5 h5) (* h6 h6 h6 h6) j2) (* 16 h1 (* h2 
h2 h2) (* h5 h5) (* h6 h6 h6 h6)) (* 32 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) 
h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 896 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5
 (* j2 j2 j2 j2 j2 j2 j2)) (* 4456 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* 
j2 j2 j2 j2 j2 j2)) (* 9720 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 
j2 j2 j2)) (* 11424 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) 
(* 7752 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 3040 h1 (* h2
 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2)) (* 640 h1 (* h2 h2) (* h3 h3 h3 h3)
 (* h4 h4) h5 j2) (* 56 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5) (* 64 h1 (* 
h2 h2) (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 384 h1 (* h2
 h2) (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 992 h1 (* h2 h2) 
(* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 1440 h1 (* h2 h2) (* h3 
h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 1284 h1 (* h2 h2) (* h3 h3 h3 h3) 
(* h4 h4) h6 (* j2 j2 j2 j2)) (* 720 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h6 
(* j2 j2 j2)) (* 248 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2)) (* 48 
h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h6 j2) (* 4 h1 (* h2 h2) (* h3 h3 h3 h3) 
(* h4 h4) h6) (* 16 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 576 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2
 j2)) (* 3452 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) 
(* 8624 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 11120 
h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 7992 h1 (* h2 h2) 
(* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 3232 h1 (* h2 h2) (* h3 h3 h3 h3) 
h4 (* h5 h5) (* j2 j2)) (* 688 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) j2) (* 
60 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5)) (* 128 h1 (* h2 h2) (* h3 h3 h3 h3
) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2112 h1 (* h2 h2) (* h3 h3 h3 h3) h4 
h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 9584 h1 (* h2 h2) (* h3 h3 h3 h3) h4 h5 h6 
(* j2 j2 j2 j2 j2 j2)) (* 20208 h1 (* h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 
j2 j2 j2)) (* 23364 h1 (* h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 
15708 h1 (* h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 6124 h1 (* h2 h2) 
(* h3 h3 h3 h3) h4 h5 h6 (* j2 j2)) (* 1284 h1 (* h2 h2) (* h3 h3 h3 h3) h4 h5 
h6 j2) (* 112 h1 (* h2 h2) (* h3 h3 h3 h3) h4 h5 h6) (* 128 h1 (* h2 h2) (* h3 
h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 768 h1 (* h2 h2) (* h3 h3
 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1984 h1 (* h2 h2) (* h3 h3 h3 
h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2880 h1 (* h2 h2) (* h3 h3 h3 h3) h4 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 2568 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6) 
(* j2 j2 j2 j2)) (* 1440 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2))
 (* 496 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2)) (* 96 h1 (* h2 h2) 
(* h3 h3 h3 h3) h4 (* h6 h6) j2) (* 8 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6))
 (* 40 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
316 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 940 h1 
(* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 1348 h1 (* h2 h2) 
(* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 1028 h1 (* h2 h2) (* h3 h3 h3 
h3) (* h5 h5 h5) (* j2 j2 j2)) (* 428 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) 
(* j2 j2)) (* 92 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) j2) (* 8 h1 (* h2 h2)
 (* h3 h3 h3 h3) (* h5 h5 h5)) (* 32 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 640 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 3456 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2)) (* 8332 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 
j2 j2 j2)) (* 10580 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) 
(* 7544 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 3036 h1 (* h2
 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2)) (* 644 h1 (* h2 h2) (* h3 h3 h3 h3)
 (* h5 h5) h6 j2) (* 56 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6) (* 96 h1 (* 
h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1216 h1 (* 
h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 5128 h1 (* h2 
h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 10488 h1 (* h2 h2) 
(* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 11940 h1 (* h2 h2) (* h3 h3 
h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 7956 h1 (* h2 h2) (* h3 h3 h3 h3) h5 (* 
h6 h6) (* j2 j2 j2)) (* 3084 h1 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2)
) (* 644 h1 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) j2) (* 56 h1 (* h2 h2) (* h3 
h3 h3 h3) h5 (* h6 h6)) (* 64 h1 (* h2 h2) (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2
 j2 j2 j2 j2 j2 j2)) (* 384 h1 (* h2 h2) (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 992 h1 (* h2 h2) (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2
 j2 j2)) (* 1440 h1 (* h2 h2) (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 1284 h1 (* h2 h2) (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 720 h1 (* 
h2 h2) (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2)) (* 248 h1 (* h2 h2) (* h3 h3 
h3 h3) (* h6 h6 h6) (* j2 j2)) (* 48 h1 (* h2 h2) (* h3 h3 h3 h3) (* h6 h6 h6) 
j2) (* 4 h1 (* h2 h2) (* h3 h3 h3 h3) (* h6 h6 h6)) (* 32 h1 (* h2 h2) (* h3 h3 
h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 776 h1 (* h2 h2) (* h3 h3 h3
) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 4084 h1 (* h2 h2) (* h3 h3 h3) 
(* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 9748 h1 (* h2 h2) (* h3 h3 h3) (* h4 
h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 12724 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5
 (* j2 j2 j2 j2)) (* 9652 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2)
) (* 4232 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2)) (* 992 h1 (* h2 
h2) (* h3 h3 h3) (* h4 h4 h4) h5 j2) (* 96 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4
) h5) (* 32 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 208 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 584 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 924 
h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 900 h1 (* h2 h2
) (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2)) (* 552 h1 (* h2 h2) (* h3 h3 h3)
 (* h4 h4 h4) h6 (* j2 j2 j2)) (* 208 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h6 
(* j2 j2)) (* 44 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h6 j2) (* 4 h1 (* h2 h2)
 (* h3 h3 h3) (* h4 h4 h4) h6) (* 84 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 
h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1752 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 9092 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* 
h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 21880 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5
 h5) (* j2 j2 j2 j2 j2)) (* 28928 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) 
(* j2 j2 j2 j2)) (* 22176 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2
 j2)) (* 9772 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 2288 
h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) j2) (* 220 h1 (* h2 h2) (* h3 h3 
h3) (* h4 h4) (* h5 h5)) (* 256 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 3288 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 
j2 j2 j2 j2 j2 j2)) (* 14740 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 
j2 j2 j2 j2)) (* 32884 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 
j2)) (* 41464 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 
30844 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 13368 h1 (* h2 
h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 3112 h1 (* h2 h2) (* h3 h3 h3) 
(* h4 h4) h5 h6 j2) (* 300 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6) (* 96 h1 
(* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 624 
h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1752 
h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2772 h1 
(* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2700 h1 (* h2 
h2) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 1656 h1 (* h2 h2) (* h3
 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 624 h1 (* h2 h2) (* h3 h3 h3) (* h4
 h4) (* h6 h6) (* j2 j2)) (* 132 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6) 
j2) (* 12 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6)) (* 28 h1 (* h2 h2) (* 
h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 664 h1 (* h2 h2) (* h3
 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 3908 h1 (* h2 h2) (* h3 h3 
h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 10316 h1 (* h2 h2) (* h3 h3 h3) h4
 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 14588 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5
 h5) (* j2 j2 j2 j2)) (* 11708 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 
j2 j2)) (* 5296 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2)) (* 1252 h1 
(* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) j2) (* 120 h1 (* h2 h2) (* h3 h3 h3) h4 
(* h5 h5 h5)) (* 272 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 4060 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 19372 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)
) (* 45028 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
58512 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 44432 h1 (* 
h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 19472 h1 (* h2 h2) (* h3 h3
 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 4544 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) 
h6 j2) (* 436 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6) (* 416 h1 (* h2 h2) (* 
h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4248 h1 (* h2 h2) (* 
h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 17228 h1 (* h2 h2) (* h3 
h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 36524 h1 (* h2 h2) (* h3 h3 h3)
 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 44756 h1 (* h2 h2) (* h3 h3 h3) h4 h5 
(* h6 h6) (* j2 j2 j2 j2)) (* 32732 h1 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) 
(* j2 j2 j2)) (* 14040 h1 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 
3248 h1 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) j2) (* 312 h1 (* h2 h2) (* h3 h3 
h3) h4 h5 (* h6 h6)) (* 96 h1 (* h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 624 h1 (* h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 1752 h1 (* h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 2772 h1 (* h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 2700 h1 (* h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1656 h1 
(* h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2)) (* 624 h1 (* h2 h2) (* h3 
h3 h3) h4 (* h6 h6 h6) (* j2 j2)) (* 132 h1 (* h2 h2) (* h3 h3 h3) h4 (* h6 h6 
h6) j2) (* 12 h1 (* h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6)) (* 20 h1 (* h2 h2) (* 
h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 168 h1 (* h2 h2) (* h3 h3
 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 544 h1 (* h2 h2) (* h3 h3 h3) (* 
h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 872 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5
) (* j2 j2 j2 j2)) (* 752 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2)
) (* 352 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2)) (* 84 h1 (* h2 h2)
 (* h3 h3 h3) (* h5 h5 h5 h5) j2) (* 8 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5)
) (* 44 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 744 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
4008 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 10236 
h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 14276 h1 (* h2 
h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 11388 h1 (* h2 h2) (* h3 h3
 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 5136 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5
) h6 (* j2 j2)) (* 1212 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 j2) (* 116 h1 
(* h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6) (* 188 h1 (* h2 h2) (* h3 h3 h3) (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2308 h1 (* h2 h2) (* h3 h3 h3) (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 10280 h1 (* h2 h2) (* h3 h3 h3) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 23148 h1 (* h2 h2) (* h3 h3 h3) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 29584 h1 (* h2 h2) (* h3 h3 h3) (* h5
 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 22256 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* 
h6 h6) (* j2 j2 j2)) (* 9700 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2
 j2)) (* 2256 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) j2) (* 216 h1 (* h2 
h2) (* h3 h3 h3) (* h5 h5) (* h6 h6)) (* 192 h1 (* h2 h2) (* h3 h3 h3) h5 (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1736 h1 (* h2 h2) (* h3 h3 h3) h5 (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 6572 h1 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 13388 h1 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2)) (* 16016 h1 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 
j2 j2)) (* 11540 h1 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 4904
 h1 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 1128 h1 (* h2 h2) (* h3
 h3 h3) h5 (* h6 h6 h6) j2) (* 108 h1 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6)) 
(* 32 h1 (* h2 h2) (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
208 h1 (* h2 h2) (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 584 
h1 (* h2 h2) (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 924 h1 (* h2
 h2) (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 900 h1 (* h2 h2) (* h3 
h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 552 h1 (* h2 h2) (* h3 h3 h3) (* h6 
h6 h6 h6) (* j2 j2 j2)) (* 208 h1 (* h2 h2) (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 
j2)) (* 44 h1 (* h2 h2) (* h3 h3 h3) (* h6 h6 h6 h6) j2) (* 4 h1 (* h2 h2) (* h3
 h3 h3) (* h6 h6 h6 h6)) (* 92 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 
j2 j2 j2 j2 j2 j2)) (* 624 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2
 j2 j2 j2)) (* 1744 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2)
) (* 2608 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 2252 h1 
(* h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2)) (* 1120 h1 (* h2 h2) (* h3 
h3) (* h4 h4 h4 h4) h5 (* j2 j2)) (* 296 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) 
h5 j2) (* 32 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5) (* 40 h1 (* h2 h2) (* h3
 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 832 h1 (* h2 h2) (* 
h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 4504 h1 (* h2 h2) (* 
h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 11500 h1 (* h2 h2) (* h3
 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 16384 h1 (* h2 h2) (* h3 h3) 
(* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 13740 h1 (* h2 h2) (* h3 h3) (* h4 h4
 h4) (* h5 h5) (* j2 j2 j2)) (* 6708 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 
h5) (* j2 j2)) (* 1752 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) j2) (* 188 
h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5)) (* 64 h1 (* h2 h2) (* h3 h3) (* 
h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 816 h1 (* h2 h2) (* h3 h3) (* h4
 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 3856 h1 (* h2 h2) (* h3 h3) (* h4 h4 
h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 9312 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 
h6 (* j2 j2 j2 j2 j2)) (* 12912 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 
j2 j2 j2)) (* 10672 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 
5168 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2)) (* 1344 h1 (* h2 h2) 
(* h3 h3) (* h4 h4 h4) h5 h6 j2) (* 144 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 
h6) (* 52 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 960 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 
j2)) (* 5088 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)
) (* 12952 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 
18480 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 15512 h1
 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 7556 h1 (* h2 h2) 
(* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 1960 h1 (* h2 h2) (* h3 h3) (* h4
 h4) (* h5 h5 h5) j2) (* 208 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5)) (* 
252 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 3348 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 15872 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 38164 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
52644 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 43320 h1
 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 20908 h1 (* h2 h2) 
(* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 5424 h1 (* h2 h2) (* h3 h3) (* h4
 h4) (* h5 h5) h6 j2) (* 580 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6) (* 
192 h1 (* h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 1896 h1 (* h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 7824 h1 (* h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
17472 h1 (* h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 23088
 h1 (* h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 18504 h1 (* 
h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 8784 h1 (* h2 h2) (* h3
 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 2256 h1 (* h2 h2) (* h3 h3) (* h4 h4) 
h5 (* h6 h6) j2) (* 240 h1 (* h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6)) (* 8 h1 
(* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 180 h1 
(* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1096 h1 (* 
h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 3072 h1 (* h2 h2) 
(* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 4680 h1 (* h2 h2) (* h3 h3) 
h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 4096 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 
h5 h5) (* j2 j2 j2)) (* 2040 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2)
) (* 532 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) j2) (* 56 h1 (* h2 h2) (* h3 
h3) h4 (* h5 h5 h5 h5)) (* 156 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 2236 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2)) (* 10980 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2)) (* 27004 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2)) (* 37824 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 
31408 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 15200 h1 (* h2 
h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2)) (* 3928 h1 (* h2 h2) (* h3 h3) h4 
(* h5 h5 h5) h6 j2) (* 416 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6) (* 384 h1 
(* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4200 
h1 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 18232
 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 41828 
h1 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 56136 h1 
(* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 45420 h1 (* h2 h2
) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 21692 h1 (* h2 h2) (* h3 h3)
 h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 5592 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5) 
(* h6 h6) j2) (* 596 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6)) (* 192 h1 
(* h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1712 h1 
(* h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 6576 h1 (* 
h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 13984 h1 (* h2 h2)
 (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 17872 h1 (* h2 h2) (* h3 h3
) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 14000 h1 (* h2 h2) (* h3 h3) h4 h5 (* 
h6 h6 h6) (* j2 j2 j2)) (* 6544 h1 (* h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 
j2)) (* 1664 h1 (* h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) j2) (* 176 h1 (* h2 h2) 
(* h3 h3) h4 h5 (* h6 h6 h6)) (* 12 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 204 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 1148 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2)) (* 3124 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 
j2 j2 j2)) (* 4704 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) 
(* 4100 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 2040 h1 (* h2
 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 532 h1 (* h2 h2) (* h3 h3) (* h5
 h5 h5 h5) h6 j2) (* 56 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6) (* 104 h1 (* 
h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1276 h1 
(* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 5892 h1 
(* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 14052 h1 
(* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 19344 h1 (* h2
 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 15896 h1 (* h2 h2) (* 
h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 7644 h1 (* h2 h2) (* h3 h3) (* h5
 h5 h5) (* h6 h6) (* j2 j2)) (* 1968 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 
h6) j2) (* 208 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6)) (* 172 h1 (* h2 h2
) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1684 h1 (* h2
 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 6864 h1 (* h2
 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 15164 h1 (* h2 
h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 19876 h1 (* h2 h2) 
(* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 15840 h1 (* h2 h2) (* h3 h3
) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 7492 h1 (* h2 h2) (* h3 h3) (* h5 h5) 
(* h6 h6 h6) (* j2 j2)) (* 1920 h1 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) j2
) (* 204 h1 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6)) (* 64 h1 (* h2 h2) (* h3
 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 540 h1 (* h2 h2) (* h3 
h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1984 h1 (* h2 h2) (* h3 h3) 
h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4080 h1 (* h2 h2) (* h3 h3) h5 (* 
h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 5088 h1 (* h2 h2) (* h3 h3) h5 (* h6 h6 h6 
h6) (* j2 j2 j2 j2)) (* 3916 h1 (* h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 
j2)) (* 1808 h1 (* h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2)) (* 456 h1 (* 
h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) j2) (* 48 h1 (* h2 h2) (* h3 h3) h5 (* h6 h6
 h6 h6)) (* 44 h1 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2
)) (* 316 h1 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 
944 h1 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 1524 h1 (* 
h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 1436 h1 (* h2 h2) h3 (* 
h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 788 h1 (* h2 h2) h3 (* h4 h4 h4 h4) (* 
h5 h5) (* j2 j2)) (* 232 h1 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) j2) (* 28 h1 
(* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5)) (* 12 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5
 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 228 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1264 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 
h5) (* j2 j2 j2 j2 j2 j2)) (* 3400 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) (* 
j2 j2 j2 j2 j2)) (* 5188 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 
j2)) (* 4724 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 2536 h1 
(* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2)) (* 736 h1 (* h2 h2) h3 (* h4 
h4 h4) (* h5 h5 h5) j2) (* 88 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5)) (* 32 
h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 424 h1
 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2100 h1 (* 
h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 5376 h1 (* h2 h2) 
h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 7996 h1 (* h2 h2) h3 (* h4 
h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 7176 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 
h5) h6 (* j2 j2 j2)) (* 3820 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)
) (* 1104 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 j2) (* 132 h1 (* h2 h2) h3 
(* h4 h4 h4) (* h5 h5) h6) (* 8 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 144 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2
 j2 j2 j2 j2 j2)) (* 776 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 
j2 j2 j2)) (* 2040 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2))
 (* 3048 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 2720 h1 
(* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 1432 h1 (* h2 h2) h3 (* 
h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 408 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 
h5) j2) (* 48 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5)) (* 76 h1 (* h2 h2) h3 
(* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 980 h1 (* h2 h2) h3 
(* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 4748 h1 (* h2 h2) h3 (* 
h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 11960 h1 (* h2 h2) h3 (* h4 h4)
 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 17584 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5
 h5) h6 (* j2 j2 j2 j2)) (* 15652 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* 
j2 j2 j2)) (* 8284 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 2384 
h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 j2) (* 284 h1 (* h2 h2) h3 (* h4 h4) 
(* h5 h5 h5) h6) (* 96 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 1008 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2
 j2 j2 j2 j2 j2)) (* 4404 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2
 j2 j2 j2 j2)) (* 10464 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2)) (* 14844 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2
)) (* 12912 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 6732 
h1 (* h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 1920 h1 (* h2 h2) h3
 (* h4 h4) (* h5 h5) (* h6 h6) j2) (* 228 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5) 
(* h6 h6)) (* 24 h1 (* h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 348 h1 (* h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
1760 h1 (* h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 4508 h1 (* 
h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 6656 h1 (* h2 h2) h3 h4 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 5908 h1 (* h2 h2) h3 h4 (* h5 h5 h5 h5) 
h6 (* j2 j2 j2)) (* 3104 h1 (* h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 884
 h1 (* h2 h2) h3 h4 (* h5 h5 h5 h5) h6 j2) (* 104 h1 (* h2 h2) h3 h4 (* h5 h5 h5
 h5) h6) (* 116 h1 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 1276 h1 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 5704 h1 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 13720 h1 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 19604 
h1 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 17132 h1 (* h2 h2)
 h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 8960 h1 (* h2 h2) h3 h4 (* h5 h5 
h5) (* h6 h6) (* j2 j2)) (* 2560 h1 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) j2) 
(* 304 h1 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6)) (* 96 h1 (* h2 h2) h3 h4 (* h5
 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 920 h1 (* h2 h2) h3 h4 (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3772 h1 (* h2 h2) h3 h4 (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 8576 h1 (* h2 h2) h3 h4 (* h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2)) (* 11796 h1 (* h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2)) (* 10040 h1 (* h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)
) (* 5156 h1 (* h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 1456 h1 (* h2 
h2) h3 h4 (* h5 h5) (* h6 h6 h6) j2) (* 172 h1 (* h2 h2) h3 h4 (* h5 h5) (* h6 
h6 h6)) (* 16 h1 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 204 h1 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 984 h1 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2468 
h1 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 3608 h1 (* h2 
h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 3188 h1 (* h2 h2) h3 (* h5 
h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 1672 h1 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 
h6) (* j2 j2)) (* 476 h1 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) j2) (* 56 h1 (* 
h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6)) (* 52 h1 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 524 h1 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2220 h1 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 5160 h1 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2)) (* 7208 h1 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2))
 (* 6204 h1 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 3212 h1 (* 
h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 912 h1 (* h2 h2) h3 (* h5 h5 
h5) (* h6 h6 h6) j2) (* 108 h1 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6)) (* 32 h1 
(* h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 292 h1 
(* h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1152 h1 (* 
h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2544 h1 (* h2 h2) 
h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 3424 h1 (* h2 h2) h3 (* h5 
h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 2868 h1 (* h2 h2) h3 (* h5 h5) (* h6 h6 
h6 h6) (* j2 j2 j2)) (* 1456 h1 (* h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)
) (* 408 h1 (* h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) j2) (* 48 h1 (* h2 h2) h3 (* 
h5 h5) (* h6 h6 h6 h6)) (* 4 h1 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 36 h1 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2)) (* 140 h1 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2
 j2)) (* 308 h1 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
420 h1 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 364 h1 (* h2 
h2) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 196 h1 (* h2 h2) (* h4 h4 h4) 
(* h5 h5 h5) h6 (* j2 j2)) (* 60 h1 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5) h6 j2) 
(* 8 h1 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5) h6) (* 4 h1 (* h2 h2) (* h4 h4) (* 
h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 36 h1 (* h2 h2) (* h4 h4) (* h5 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 140 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5
 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 308 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5 h5) h6 
(* j2 j2 j2 j2 j2)) (* 420 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2
 j2)) (* 364 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 196 h1 
(* h2 h2) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 60 h1 (* h2 h2) (* h4 h4) 
(* h5 h5 h5 h5) h6 j2) (* 8 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5 h5) h6) (* 12 h1 
(* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 108 
h1 (* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 420 
h1 (* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 924 h1 
(* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1260 h1 (* h2 
h2) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 1092 h1 (* h2 h2) (* h4
 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 588 h1 (* h2 h2) (* h4 h4) (* h5 h5
 h5) (* h6 h6) (* j2 j2)) (* 180 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6) 
j2) (* 24 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6)) (* 8 h1 (* h2 h2) h4 
(* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 72 h1 (* h2 h2) h4 (* 
h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 280 h1 (* h2 h2) h4 (* h5 h5
 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 616 h1 (* h2 h2) h4 (* h5 h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 840 h1 (* h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2)) (* 728 h1 (* h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) 
(* 392 h1 (* h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 120 h1 (* h2 h2) 
h4 (* h5 h5 h5 h5) (* h6 h6) j2) (* 16 h1 (* h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6)
) (* 12 h1 (* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 108 h1 (* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
420 h1 (* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 924 h1 
(* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1260 h1 (* h2 h2) 
h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1092 h1 (* h2 h2) h4 (* h5 h5 
h5) (* h6 h6 h6) (* j2 j2 j2)) (* 588 h1 (* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6) 
(* j2 j2)) (* 180 h1 (* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6) j2) (* 24 h1 (* h2 
h2) h4 (* h5 h5 h5) (* h6 h6 h6)) (* 4 h1 (* h2 h2) (* h5 h5 h5 h5) (* h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 36 h1 (* h2 h2) (* h5 h5 h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 140 h1 (* h2 h2) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2)) (* 308 h1 (* h2 h2) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2)) (* 420 h1 (* h2 h2) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 364
 h1 (* h2 h2) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 196 h1 (* h2 h2) (* 
h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 60 h1 (* h2 h2) (* h5 h5 h5 h5) (* h6 h6
 h6) j2) (* 8 h1 (* h2 h2) (* h5 h5 h5 h5) (* h6 h6 h6)) (* 4 h1 (* h2 h2) (* h5
 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 36 h1 (* h2 h2) (* h5 h5
 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 140 h1 (* h2 h2) (* h5 h5 h5) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 308 h1 (* h2 h2) (* h5 h5 h5) (* h6 h6
 h6 h6) (* j2 j2 j2 j2 j2)) (* 420 h1 (* h2 h2) (* h5 h5 h5) (* h6 h6 h6 h6) (* 
j2 j2 j2 j2)) (* 364 h1 (* h2 h2) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 
196 h1 (* h2 h2) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 60 h1 (* h2 h2) (* 
h5 h5 h5) (* h6 h6 h6 h6) j2) (* 8 h1 (* h2 h2) (* h5 h5 h5) (* h6 h6 h6 h6)) 
(* 136 h1 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 888
 h1 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 2442 h1 h2 
(* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 3700 h1 h2 (* h3 h3 h3
 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 3382 h1 h2 (* h3 h3 h3 h3) (* h4 h4 
h4) h5 (* j2 j2 j2 j2)) (* 1912 h1 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 
j2)) (* 654 h1 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2)) (* 124 h1 h2 (* h3 
h3 h3 h3) (* h4 h4 h4) h5 j2) (* 10 h1 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h5) (* 4 
h1 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 270
 h1 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1974 
h1 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 6112 h1 
h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 10188 h1 h2 (* 
h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 9988 h1 h2 (* h3 h3 h3 
h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 5916 h1 h2 (* h3 h3 h3 h3) (* h4 h4)
 (* h5 h5) (* j2 j2 j2)) (* 2078 h1 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2
 j2)) (* 398 h1 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) j2) (* 32 h1 h2 (* h3 h3 
h3 h3) (* h4 h4) (* h5 h5)) (* 32 h1 h2 (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2
 j2 j2 j2 j2 j2 j2 j2)) (* 680 h1 h2 (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 3632 h1 h2 (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 
j2 j2 j2)) (* 9242 h1 h2 (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) 
(* 13440 h1 h2 (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 11982 h1 
h2 (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 6664 h1 h2 (* h3 h3 h3 h3
) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 2254 h1 h2 (* h3 h3 h3 h3) (* h4 h4) h5 h6 
(* j2 j2)) (* 424 h1 h2 (* h3 h3 h3 h3) (* h4 h4) h5 h6 j2) (* 34 h1 h2 (* h3 h3
 h3 h3) (* h4 h4) h5 h6) (* 80 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 712 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2
 j2 j2)) (* 2512 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) 
(* 4576 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 4752 h1 h2 
(* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 2912 h1 h2 (* h3 h3 h3 h3) 
h4 (* h5 h5 h5) (* j2 j2 j2)) (* 1040 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* 
j2 j2)) (* 200 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) j2) (* 16 h1 h2 (* h3 h3 h3
 h3) h4 (* h5 h5 h5)) (* 24 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 660 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 4312 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2)) (* 12818 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
20952 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 20318 h1 h2 
(* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 11954 h1 h2 (* h3 h3 h3 h3) 
h4 (* h5 h5) h6 (* j2 j2 j2)) (* 4180 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* 
j2 j2)) (* 798 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5) h6 j2) (* 64 h1 h2 (* h3 h3 h3
 h3) h4 (* h5 h5) h6) (* 64 h1 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 952 h1 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 4600 h1 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 11158 h1 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
15780 h1 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 13818 h1 h2 
(* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 7592 h1 h2 (* h3 h3 h3 h3) 
h4 h5 (* h6 h6) (* j2 j2 j2)) (* 2546 h1 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* 
j2 j2)) (* 476 h1 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6) j2) (* 38 h1 h2 (* h3 h3 h3
 h3) h4 h5 (* h6 h6)) (* 80 h1 h2 (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2
 j2 j2 j2 j2)) (* 712 h1 h2 (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2
 j2)) (* 2512 h1 h2 (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
4576 h1 h2 (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 4752 h1 h2 (* 
h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 2912 h1 h2 (* h3 h3 h3 h3) (* 
h5 h5 h5) h6 (* j2 j2 j2)) (* 1040 h1 h2 (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 
j2)) (* 200 h1 h2 (* h3 h3 h3 h3) (* h5 h5 h5) h6 j2) (* 16 h1 h2 (* h3 h3 h3 h3
) (* h5 h5 h5) h6) (* 20 h1 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 390 h1 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 2338 h1 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 6706 h1 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 10764 h1 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 10330 h1 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 6038 h1 
h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 2102 h1 h2 (* h3 h3 h3 
h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 400 h1 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 
h6) j2) (* 32 h1 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6)) (* 32 h1 h2 (* h3 h3 h3
 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 408 h1 h2 (* h3 h3 h3 h3
) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1856 h1 h2 (* h3 h3 h3 h3) h5 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4358 h1 h2 (* h3 h3 h3 h3) h5 (* h6 h6
 h6) (* j2 j2 j2 j2 j2 j2)) (* 6040 h1 h2 (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 
j2 j2 j2 j2)) (* 5218 h1 h2 (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 
2840 h1 h2 (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 946 h1 h2 (* h3 h3 
h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 176 h1 h2 (* h3 h3 h3 h3) h5 (* h6 h6 h6) 
j2) (* 14 h1 h2 (* h3 h3 h3 h3) h5 (* h6 h6 h6)) (* 68 h1 h2 (* h3 h3 h3) (* h4 
h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 478 h1 h2 (* h3 h3 h3) (* h4 h4 h4 
h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 1426 h1 h2 (* h3 h3 h3) (* h4 h4 h4 h4) h5 
(* j2 j2 j2 j2 j2 j2)) (* 2358 h1 h2 (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2
 j2 j2)) (* 2362 h1 h2 (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 1466 
h1 h2 (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2)) (* 550 h1 h2 (* h3 h3 h3) 
(* h4 h4 h4 h4) h5 (* j2 j2)) (* 114 h1 h2 (* h3 h3 h3) (* h4 h4 h4 h4) h5 j2) 
(* 10 h1 h2 (* h3 h3 h3) (* h4 h4 h4 h4) h5) (* 6 h1 h2 (* h3 h3 h3) (* h4 h4 h4
) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 338 h1 h2 (* h3 h3 h3) (* h4 h4 
h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2320 h1 h2 (* h3 h3 h3) (* h4 h4 
h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 7088 h1 h2 (* h3 h3 h3) (* h4 h4 h4) 
(* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 12098 h1 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 
h5) (* j2 j2 j2 j2 j2)) (* 12490 h1 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2
 j2 j2 j2)) (* 7948 h1 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 
3036 h1 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 636 h1 h2 (* h3 h3 
h3) (* h4 h4 h4) (* h5 h5) j2) (* 56 h1 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5)) 
(* 16 h1 h2 (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
416 h1 h2 (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2460 
h1 h2 (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 6872 h1 h2 
(* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 10976 h1 h2 (* h3 h3 
h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 10764 h1 h2 (* h3 h3 h3) (* h4 h4 
h4) h5 h6 (* j2 j2 j2 j2)) (* 6588 h1 h2 (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 
j2 j2)) (* 2448 h1 h2 (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2)) (* 504 h1 h2 
(* h3 h3 h3) (* h4 h4 h4) h5 h6 j2) (* 44 h1 h2 (* h3 h3 h3) (* h4 h4 h4) h5 h6)
 (* 8 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 298 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 2148 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
6958 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 12468 
h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 13352 h1 h2 (* 
h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 8708 h1 h2 (* h3 h3 h3) (* 
h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 3370 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 
h5) (* j2 j2)) (* 708 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) j2) (* 62 h1 h2 
(* h3 h3 h3) (* h4 h4) (* h5 h5 h5)) (* 66 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5
) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1422 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 8416 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 24168 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5)
 h6 (* j2 j2 j2 j2 j2 j2)) (* 39894 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 
(* j2 j2 j2 j2 j2)) (* 40366 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 
j2 j2)) (* 25364 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 9612
 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 2004 h1 h2 (* h3 h3 h3)
 (* h4 h4) (* h5 h5) h6 j2) (* 176 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) h6) 
(* 48 h1 h2 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 840 h1 h2 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 4512 h1 h2 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
12060 h1 h2 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 18780 
h1 h2 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 18120 h1 h2 (* 
h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 10968 h1 h2 (* h3 h3 h3) 
(* h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 4044 h1 h2 (* h3 h3 h3) (* h4 h4) h5 (* 
h6 h6) (* j2 j2)) (* 828 h1 h2 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) j2) (* 72 h1 
h2 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6)) (* 40 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5 
h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 376 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 1424 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2
 j2 j2 j2 j2)) (* 2832 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2))
 (* 3248 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 2208 h1 h2 
(* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2)) (* 872 h1 h2 (* h3 h3 h3) h4 (* h5
 h5 h5 h5) (* j2 j2)) (* 184 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) j2) (* 16 h1 
h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5)) (* 32 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 732 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 4792 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2
 j2 j2 j2 j2 j2)) (* 14956 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2)) (* 26324 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
27920 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 18108 h1 h2 (* 
h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 6984 h1 h2 (* h3 h3 h3) h4 (* h5 
h5 h5) h6 (* j2 j2)) (* 1464 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5) h6 j2) (* 128 h1
 h2 (* h3 h3 h3) h4 (* h5 h5 h5) h6) (* 114 h1 h2 (* h3 h3 h3) h4 (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1830 h1 h2 (* h3 h3 h3) h4 (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 9872 h1 h2 (* h3 h3 h3) h4 (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 27072 h1 h2 (* h3 h3 h3) h4 (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 43494 h1 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6)
 (* j2 j2 j2 j2 j2)) (* 43262 h1 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2
 j2 j2)) (* 26884 h1 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 
10116 h1 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 2100 h1 h2 (* h3 
h3 h3) h4 (* h5 h5) (* h6 h6) j2) (* 184 h1 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 
h6)) (* 48 h1 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (* 704 h1 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
3556 h1 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 9208 h1 
h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 14064 h1 h2 (* h3 
h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 13396 h1 h2 (* h3 h3 h3) h4 h5 
(* h6 h6 h6) (* j2 j2 j2 j2)) (* 8036 h1 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* 
j2 j2 j2)) (* 2944 h1 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2)) (* 600 h1 h2
 (* h3 h3 h3) h4 h5 (* h6 h6 h6) j2) (* 52 h1 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6)
) (* 40 h1 h2 (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
376 h1 h2 (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1424 h1 
h2 (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 2832 h1 h2 (* h3 h3
 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 3248 h1 h2 (* h3 h3 h3) (* h5 h5 
h5 h5) h6 (* j2 j2 j2 j2)) (* 2208 h1 h2 (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 
j2 j2)) (* 872 h1 h2 (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 184 h1 h2 (* 
h3 h3 h3) (* h5 h5 h5 h5) h6 j2) (* 16 h1 h2 (* h3 h3 h3) (* h5 h5 h5 h5) h6) 
(* 24 h1 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 434 h1 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 2644 h1 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
7998 h1 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 13856 
h1 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 14568 h1 h2 (* 
h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 9400 h1 h2 (* h3 h3 h3) (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 3614 h1 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 
h6) (* j2 j2)) (* 756 h1 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) j2) (* 66 h1 h2 
(* h3 h3 h3) (* h5 h5 h5) (* h6 h6)) (* 54 h1 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 746 h1 h2 (* h3 h3 h3) (* h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3776 h1 h2 (* h3 h3 h3) (* h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 9992 h1 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 15698 h1 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2)) (* 15386 h1 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2)) (* 9468 h1 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 3540 
h1 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 732 h1 h2 (* h3 h3 h3) 
(* h5 h5) (* h6 h6 h6) j2) (* 64 h1 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6)) (* 
16 h1 h2 (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 212 
h1 h2 (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1026 h1 h2
 (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2594 h1 h2 (* h3 
h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3902 h1 h2 (* h3 h3 h3) h5 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 3678 h1 h2 (* h3 h3 h3) h5 (* h6 h6 h6 h6
) (* j2 j2 j2 j2)) (* 2190 h1 h2 (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) 
(* 798 h1 h2 (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2)) (* 162 h1 h2 (* h3 h3 h3
) h5 (* h6 h6 h6 h6) j2) (* 14 h1 h2 (* h3 h3 h3) h5 (* h6 h6 h6 h6)) (* 62 h1 
h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 468 h1 h2
 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1520 h1 h2 (* 
h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2766 h1 h2 (* h3 h3) 
(* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 3074 h1 h2 (* h3 h3) (* h4 h4 
h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 2128 h1 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 
h5) (* j2 j2 j2)) (* 892 h1 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2)) 
(* 206 h1 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) j2) (* 20 h1 h2 (* h3 h3) (* h4
 h4 h4 h4) (* h5 h5)) (* 4 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2
 j2 j2 j2 j2 j2 j2)) (* 178 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 1260 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 
j2 j2 j2 j2 j2)) (* 4072 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 
j2 j2 j2)) (* 7452 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2))
 (* 8336 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 5796 h1 
h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 2432 h1 h2 (* h3 h3) (* 
h4 h4 h4) (* h5 h5 h5) (* j2 j2)) (* 560 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 
h5) j2) (* 54 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5)) (* 18 h1 h2 (* h3 h3) 
(* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 420 h1 h2 (* h3 h3)
 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2574 h1 h2 (* h3 h3) 
(* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 7698 h1 h2 (* h3 h3) (* 
h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 13394 h1 h2 (* h3 h3) (* h4 h4 
h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 14474 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5
 h5) h6 (* j2 j2 j2 j2)) (* 9834 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2
 j2 j2)) (* 4070 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 932 h1 
h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 j2) (* 90 h1 h2 (* h3 h3) (* h4 h4 h4) 
(* h5 h5) h6) (* 2 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 76 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 574 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2
 j2)) (* 1968 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) 
(* 3760 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 4324 h1
 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 3050 h1 h2 (* h3 h3)
 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 1284 h1 h2 (* h3 h3) (* h4 h4) (* h5
 h5 h5 h5) (* j2 j2)) (* 294 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) j2) (* 28
 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5)) (* 36 h1 h2 (* h3 h3) (* h4 h4) (* 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 756 h1 h2 (* h3 h3) (* h4 h4) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4652 h1 h2 (* h3 h3) (* h4 h4) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 14142 h1 h2 (* h3 h3) (* h4 h4) (* 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 25008 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2)) (* 27380 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 
(* j2 j2 j2 j2)) (* 18772 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)
) (* 7806 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 1788 h1 h2 (* 
h3 h3) (* h4 h4) (* h5 h5 h5) h6 j2) (* 172 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 
h5) h6) (* 54 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2 j2)) (* 888 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 4914 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 13974 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2
 j2 j2 j2)) (* 23586 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2)) (* 24978 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) 
(* 16734 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 6858 h1 
h2 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 1560 h1 h2 (* h3 h3) 
(* h4 h4) (* h5 h5) (* h6 h6) j2) (* 150 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5) (* 
h6 h6)) (* 8 h1 h2 (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2
)) (* 190 h1 h2 (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
1308 h1 h2 (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 4332 h1 
h2 (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 8150 h1 h2 (* h3 h3
) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 9306 h1 h2 (* h3 h3) h4 (* h5 h5 
h5 h5) h6 (* j2 j2 j2 j2)) (* 6544 h1 h2 (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 
j2 j2)) (* 2752 h1 h2 (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 630 h1 h2 
(* h3 h3) h4 (* h5 h5 h5 h5) h6 j2) (* 60 h1 h2 (* h3 h3) h4 (* h5 h5 h5 h5) h6)
 (* 60 h1 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (* 978 h1 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 5524 h1 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
16068 h1 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 27660 
h1 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 29752 h1 h2 (* 
h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 20156 h1 h2 (* h3 h3) h4 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 8316 h1 h2 (* h3 h3) h4 (* h5 h5 h5) (* 
h6 h6) (* j2 j2)) (* 1896 h1 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) j2) (* 182 
h1 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6)) (* 54 h1 h2 (* h3 h3) h4 (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 764 h1 h2 (* h3 h3) h4 (* h5 h5)
 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3978 h1 h2 (* h3 h3) h4 (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 10934 h1 h2 (* h3 h3) h4 (* h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 18054 h1 h2 (* h3 h3) h4 (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2)) (* 18830 h1 h2 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2
 j2 j2 j2)) (* 12478 h1 h2 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 
5074 h1 h2 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 1148 h1 h2 (* h3 h3
) h4 (* h5 h5) (* h6 h6 h6) j2) (* 110 h1 h2 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6)
) (* 6 h1 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (* 114 h1 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 734 h1 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
2364 h1 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4390 h1
 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 4982 h1 h2 (* h3 
h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 3494 h1 h2 (* h3 h3) (* h5 h5 
h5 h5) (* h6 h6) (* j2 j2 j2)) (* 1468 h1 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6)
 (* j2 j2)) (* 336 h1 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) j2) (* 32 h1 h2 (* 
h3 h3) (* h5 h5 h5 h5) (* h6 h6)) (* 28 h1 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 400 h1 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2132 h1 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 5998 h1 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 10104 h1 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2)) (* 10708 h1 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)
) (* 7180 h1 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 2942 h1 h2 
(* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 668 h1 h2 (* h3 h3) (* h5 h5 
h5) (* h6 h6 h6) j2) (* 64 h1 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6)) (* 18 h1 
h2 (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 234 h1
 h2 (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1170 h1 
h2 (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3138 h1 h2 
(* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 5096 h1 h2 (* h3 
h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 5252 h1 h2 (* h3 h3) (* h5 
h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 3450 h1 h2 (* h3 h3) (* h5 h5) (* h6 h6 
h6 h6) (* j2 j2 j2)) (* 1394 h1 h2 (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)
) (* 314 h1 h2 (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) j2) (* 30 h1 h2 (* h3 h3) (* 
h5 h5) (* h6 h6 h6 h6)) (* 16 h1 h2 h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 126 h1 h2 h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 
j2 j2)) (* 426 h1 h2 h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 
808 h1 h2 h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 940 h1 h2 h3 
(* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 686 h1 h2 h3 (* h4 h4 h4 h4) 
(* h5 h5 h5) (* j2 j2 j2)) (* 306 h1 h2 h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2
)) (* 76 h1 h2 h3 (* h4 h4 h4 h4) (* h5 h5 h5) j2) (* 8 h1 h2 h3 (* h4 h4 h4 h4)
 (* h5 h5 h5)) (* 16 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 126 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 426 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 808 h1 h2
 h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 940 h1 h2 h3 (* h4 h4 h4
) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 686 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5 h5) 
(* j2 j2 j2)) (* 306 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 76 h1 
h2 h3 (* h4 h4 h4) (* h5 h5 h5 h5) j2) (* 8 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5 h5
)) (* 4 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 108 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 712
 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2260 h1 h2 
h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 4160 h1 h2 h3 (* h4 h4
 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 4764 h1 h2 h3 (* h4 h4 h4) (* h5 h5 
h5) h6 (* j2 j2 j2 j2)) (* 3448 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 
j2)) (* 1532 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 380 h1 h2 h3 
(* h4 h4 h4) (* h5 h5 h5) h6 j2) (* 40 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5) h6) 
(* 4 h1 h2 h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 92
 h1 h2 h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 586 h1 h2
 h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1834 h1 h2 h3 (* 
h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 3352 h1 h2 h3 (* h4 h4) (* 
h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 3824 h1 h2 h3 (* h4 h4) (* h5 h5 h5 h5) 
h6 (* j2 j2 j2 j2)) (* 2762 h1 h2 h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) 
(* 1226 h1 h2 h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 304 h1 h2 h3 (* h4 
h4) (* h5 h5 h5 h5) h6 j2) (* 32 h1 h2 h3 (* h4 h4) (* h5 h5 h5 h5) h6) (* 12 h1
 h2 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 228 
h1 h2 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1380 
h1 h2 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4224 h1 
h2 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 7632 h1 h2 h3 
(* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 8652 h1 h2 h3 (* h4 h4) 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 6228 h1 h2 h3 (* h4 h4) (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2)) (* 2760 h1 h2 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 
j2)) (* 684 h1 h2 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) j2) (* 72 h1 h2 h3 (* h4 
h4) (* h5 h5 h5) (* h6 h6)) (* 8 h1 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 136 h1 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 794 h1 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 2390 h1 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
4280 h1 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 4828 h1 h2 h3 
h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 3466 h1 h2 h3 h4 (* h5 h5 h5 h5
) (* h6 h6) (* j2 j2 j2)) (* 1534 h1 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2
)) (* 380 h1 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6) j2) (* 40 h1 h2 h3 h4 (* h5 h5 
h5 h5) (* h6 h6)) (* 12 h1 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 196 h1 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 1128 h1 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 3372 h1 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6016 h1 
h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 6772 h1 h2 h3 h4 (* h5
 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 4856 h1 h2 h3 h4 (* h5 h5 h5) (* h6 h6 
h6) (* j2 j2 j2)) (* 2148 h1 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 
532 h1 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6) j2) (* 56 h1 h2 h3 h4 (* h5 h5 h5) (* 
h6 h6 h6)) (* 4 h1 h2 h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
 j2)) (* 60 h1 h2 h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 334 h1 h2 h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 982 h1
 h2 h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1736 h1 h2 h3 (* 
h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1944 h1 h2 h3 (* h5 h5 h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2)) (* 1390 h1 h2 h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* 
j2 j2 j2)) (* 614 h1 h2 h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 152 h1 h2 
h3 (* h5 h5 h5 h5) (* h6 h6 h6) j2) (* 16 h1 h2 h3 (* h5 h5 h5 h5) (* h6 h6 h6))
 (* 4 h1 h2 h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
60 h1 h2 h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 334 h1 
h2 h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 982 h1 h2 h3 (* 
h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1736 h1 h2 h3 (* h5 h5 h5) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1944 h1 h2 h3 (* h5 h5 h5) (* h6 h6 h6 h6
) (* j2 j2 j2 j2)) (* 1390 h1 h2 h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) 
(* 614 h1 h2 h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 152 h1 h2 h3 (* h5 h5
 h5) (* h6 h6 h6 h6) j2) (* 16 h1 h2 h3 (* h5 h5 h5) (* h6 h6 h6 h6)) (* 20 h1 
(* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 168 h1
 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 589 h1 
(* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1145 h1 (* 
h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1369 h1 (* h3 h3 
h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 1048 h1 (* h3 h3 h3 h3) (* 
h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 515 h1 (* h3 h3 h3 h3) (* h4 h4 h4) (* 
h5 h5) (* j2 j2 j2)) (* 157 h1 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2))
 (* 27 h1 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) j2) (* 2 h1 (* h3 h3 h3 h3) (* 
h4 h4 h4) (* h5 h5)) (* 10 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2
 j2 j2 j2 j2 j2 j2)) (* 99 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 403 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 
j2 j2 j2 j2)) (* 886 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2
 j2)) (* 1166 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 
958 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 494 h1 (* h3 
h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 155 h1 (* h3 h3 h3 h3) (* h4 
h4) (* h5 h5 h5) (* j2 j2)) (* 27 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) j2) 
(* 2 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5)) (* 80 h1 (* h3 h3 h3 h3) (* h4 
h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 672 h1 (* h3 h3 h3 h3) (* h4
 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2356 h1 (* h3 h3 h3 h3) (* h4 
h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 4580 h1 (* h3 h3 h3 h3) (* h4 h4) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 5476 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 
h5) h6 (* j2 j2 j2 j2 j2)) (* 4192 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* 
j2 j2 j2 j2)) (* 2060 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) 
(* 628 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 108 h1 (* h3 h3 
h3 h3) (* h4 h4) (* h5 h5) h6 j2) (* 8 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6
) (* 30 h1 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 297 h1 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
1209 h1 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2658 h1 
(* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 3498 h1 (* h3 h3 h3
 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 2874 h1 (* h3 h3 h3 h3) h4 (* h5 
h5 h5) h6 (* j2 j2 j2 j2)) (* 1482 h1 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 
j2 j2)) (* 465 h1 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2)) (* 81 h1 (* h3 
h3 h3 h3) h4 (* h5 h5 h5) h6 j2) (* 6 h1 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6) (* 
100 h1 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 840 h1 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 2945 h1 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
5725 h1 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6845 h1
 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 5240 h1 (* h3 h3 
h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 2575 h1 (* h3 h3 h3 h3) h4 (* 
h5 h5) (* h6 h6) (* j2 j2 j2)) (* 785 h1 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) 
(* j2 j2)) (* 135 h1 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) j2) (* 10 h1 (* h3 
h3 h3 h3) h4 (* h5 h5) (* h6 h6)) (* 20 h1 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 198 h1 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 806 h1 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6
) (* j2 j2 j2 j2 j2 j2 j2)) (* 1772 h1 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 2332 h1 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2)) (* 1916 h1 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2))
 (* 988 h1 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 310 h1 (* h3 
h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 54 h1 (* h3 h3 h3 h3) (* h5 h5 h5
) (* h6 h6) j2) (* 4 h1 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6)) (* 40 h1 (* h3 
h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 336 h1 (* h3
 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1178 h1 (* h3 
h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2290 h1 (* h3 h3 
h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2738 h1 (* h3 h3 h3 h3) 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2096 h1 (* h3 h3 h3 h3) (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2)) (* 1030 h1 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2)) (* 314 h1 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 54 
h1 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) j2) (* 4 h1 (* h3 h3 h3 h3) (* h5 h5) 
(* h6 h6 h6)) (* 10 h1 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 89 h1 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 334 h1 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2
 j2)) (* 700 h1 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) 
(* 907 h1 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 755 h1 
(* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 404 h1 (* h3 h3 h3) 
(* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 134 h1 (* h3 h3 h3) (* h4 h4 h4 h4) 
(* h5 h5) (* j2 j2)) (* 25 h1 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) j2) (* 2 h1
 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5)) (* 20 h1 (* h3 h3 h3) (* h4 h4 h4) (* 
h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 178 h1 (* h3 h3 h3) (* h4 h4 h4) 
(* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 668 h1 (* h3 h3 h3) (* h4 h4 h4) 
(* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1400 h1 (* h3 h3 h3) (* h4 h4 h4) (* 
h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1814 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 
h5) (* j2 j2 j2 j2 j2)) (* 1510 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 
j2 j2 j2)) (* 808 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 268
 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2)) (* 50 h1 (* h3 h3 h3) (* 
h4 h4 h4) (* h5 h5 h5) j2) (* 4 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5)) (* 50
 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
445 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
1670 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 3500
 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 4535 h1 (* 
h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 3775 h1 (* h3 h3 h3) 
(* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 2020 h1 (* h3 h3 h3) (* h4 h4 h4) 
(* h5 h5) h6 (* j2 j2 j2)) (* 670 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* 
j2 j2)) (* 125 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 j2) (* 10 h1 (* h3 h3 
h3) (* h4 h4 h4) (* h5 h5) h6) (* 5 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 52 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 225 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 532 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2
 j2 j2 j2 j2 j2)) (* 760 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 
j2 j2)) (* 682 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 385
 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 132 h1 (* h3 h3 h3) 
(* h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 25 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5
 h5) j2) (* 2 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5)) (* 80 h1 (* h3 h3 h3) 
(* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 712 h1 (* h3 h3 h3)
 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2672 h1 (* h3 h3 h3) 
(* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 5600 h1 (* h3 h3 h3) (* 
h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 7256 h1 (* h3 h3 h3) (* h4 h4) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 6040 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 
h5) h6 (* j2 j2 j2 j2)) (* 3232 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 
j2 j2)) (* 1072 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 200 h1 
(* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 j2) (* 16 h1 (* h3 h3 h3) (* h4 h4) (* h5
 h5 h5) h6) (* 90 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 801 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 3006 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 6300 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 8163 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2)) (* 6795 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)
) (* 3636 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 1206 h1
 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 225 h1 (* h3 h3 h3) 
(* h4 h4) (* h5 h5) (* h6 h6) j2) (* 18 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* 
h6 h6)) (* 15 h1 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 156 h1 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 675 h1 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1596 
h1 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 2280 h1 (* h3 h3
 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 2046 h1 (* h3 h3 h3) h4 (* h5 
h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 1155 h1 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* 
j2 j2 j2)) (* 396 h1 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 75 h1 (* 
h3 h3 h3) h4 (* h5 h5 h5 h5) h6 j2) (* 6 h1 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6) 
(* 100 h1 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (* 890 h1 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 3340 h1 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
7000 h1 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 9070 h1
 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 7550 h1 (* h3 h3 
h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 4040 h1 (* h3 h3 h3) h4 (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2)) (* 1340 h1 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6)
 (* j2 j2)) (* 250 h1 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) j2) (* 20 h1 (* h3 
h3 h3) h4 (* h5 h5 h5) (* h6 h6)) (* 70 h1 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 623 h1 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2338 h1 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4900 h1 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 6349 h1 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2)) (* 5285 h1 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2))
 (* 2828 h1 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 938 h1 (* h3
 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 175 h1 (* h3 h3 h3) h4 (* h5 h5)
 (* h6 h6 h6) j2) (* 14 h1 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6)) (* 10 h1 (* 
h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 104 h1 
(* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 450 h1 
(* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1064 h1 (* 
h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1520 h1 (* h3 h3 
h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1364 h1 (* h3 h3 h3) (* h5 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 770 h1 (* h3 h3 h3) (* h5 h5 h5 h5) (* 
h6 h6) (* j2 j2 j2)) (* 264 h1 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2))
 (* 50 h1 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) j2) (* 4 h1 (* h3 h3 h3) (* h5 
h5 h5 h5) (* h6 h6)) (* 40 h1 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2
 j2 j2 j2 j2 j2 j2)) (* 356 h1 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 1336 h1 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 2800 h1 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 3628 h1 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2))
 (* 3020 h1 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1616 h1 
(* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 536 h1 (* h3 h3 h3) (* 
h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 100 h1 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 
h6) j2) (* 8 h1 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6)) (* 20 h1 (* h3 h3 h3) 
(* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 178 h1 (* h3 h3 h3)
 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 668 h1 (* h3 h3 h3) 
(* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1400 h1 (* h3 h3 h3) (* 
h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1814 h1 (* h3 h3 h3) (* h5 h5) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1510 h1 (* h3 h3 h3) (* h5 h5) (* h6 h6 
h6 h6) (* j2 j2 j2 j2)) (* 808 h1 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 
j2 j2)) (* 268 h1 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 50 h1 (* 
h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) j2) (* 4 h1 (* h3 h3 h3) (* h5 h5) (* h6 h6 
h6 h6)) (* 5 h1 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 47 h1 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 188 h1 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 423 h1 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 592 
h1 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 535 h1 (* h3 h3
) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 312 h1 (* h3 h3) (* h4 h4 h4 
h4) (* h5 h5 h5) (* j2 j2 j2)) (* 113 h1 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) 
(* j2 j2)) (* 23 h1 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) j2) (* 2 h1 (* h3 h3)
 (* h4 h4 h4 h4) (* h5 h5 h5)) (* 5 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 47 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 188 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 423 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2
 j2 j2 j2 j2 j2)) (* 592 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 
j2 j2)) (* 535 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 312
 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 113 h1 (* h3 h3) (* 
h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 23 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5
 h5) j2) (* 2 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5)) (* 25 h1 (* h3 h3) (* 
h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 235 h1 (* h3 h3) 
(* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 940 h1 (* h3 h3) 
(* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2115 h1 (* h3 h3) (* 
h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 2960 h1 (* h3 h3) (* h4 h4 
h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 2675 h1 (* h3 h3) (* h4 h4 h4) (* h5 
h5 h5) h6 (* j2 j2 j2 j2)) (* 1560 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* 
j2 j2 j2)) (* 565 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 115 h1
 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 j2) (* 10 h1 (* h3 h3) (* h4 h4 h4) (* 
h5 h5 h5) h6) (* 20 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 188 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 752 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 1692 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2))
 (* 2368 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 2140 
h1 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 1248 h1 (* h3 h3) 
(* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 452 h1 (* h3 h3) (* h4 h4) (* h5 
h5 h5 h5) h6 (* j2 j2)) (* 92 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 j2) (* 8
 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6) (* 45 h1 (* h3 h3) (* h4 h4) (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 423 h1 (* h3 h3) (* h4 h4) 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1692 h1 (* h3 h3) (* h4 
h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3807 h1 (* h3 h3) (* h4 
h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 5328 h1 (* h3 h3) (* h4 h4)
 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 4815 h1 (* h3 h3) (* h4 h4) (* h5
 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 2808 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2)) (* 1017 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) 
(* j2 j2)) (* 207 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) j2) (* 18 h1 (* 
h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6)) (* 25 h1 (* h3 h3) h4 (* h5 h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 235 h1 (* h3 h3) h4 (* h5 h5 h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 940 h1 (* h3 h3) h4 (* h5 h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2115 h1 (* h3 h3) h4 (* h5 h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2960 h1 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* 2675 h1 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2)) (* 1560 h1 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 565 
h1 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 115 h1 (* h3 h3) h4 (* 
h5 h5 h5 h5) (* h6 h6) j2) (* 10 h1 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6)) (* 
35 h1 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
329 h1 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
1316 h1 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2961
 h1 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4144 h1 (* 
h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 3745 h1 (* h3 h3) h4 
(* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 2184 h1 (* h3 h3) h4 (* h5 h5 h5) 
(* h6 h6 h6) (* j2 j2 j2)) (* 791 h1 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* 
j2 j2)) (* 161 h1 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) j2) (* 14 h1 (* h3 h3) 
h4 (* h5 h5 h5) (* h6 h6 h6)) (* 10 h1 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 94 h1 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 376 h1 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 846 h1 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2)) (* 1184 h1 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2)) (* 1070 h1 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 
624 h1 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 226 h1 (* h3 h3) 
(* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 46 h1 (* h3 h3) (* h5 h5 h5 h5) (* h6
 h6 h6) j2) (* 4 h1 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6)) (* 10 h1 (* h3 h3) 
(* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 94 h1 (* h3 h3) 
(* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 376 h1 (* h3 h3) 
(* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 846 h1 (* h3 h3) (* h5
 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1184 h1 (* h3 h3) (* h5 h5 h5)
 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1070 h1 (* h3 h3) (* h5 h5 h5) (* h6 h6 
h6 h6) (* j2 j2 j2 j2)) (* 624 h1 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 
j2 j2)) (* 226 h1 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 46 h1 (* 
h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) j2) (* 4 h1 (* h3 h3) (* h5 h5 h5) (* h6 h6 
h6 h6)) (* 64 (* h2 h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) 
(* 384 (* h2 h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 848 (* 
h2 h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 912 (* h2 h2 h2 h2) 
(* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 512 (* h2 h2 h2 h2) (* h3 h3 h3) (* 
h4 h4) h5 (* j2 j2)) (* 144 (* h2 h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 j2) (* 16 
(* h2 h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5) (* 32 (* h2 h2 h2 h2) (* h3 h3 h3) h4
 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 240 (* h2 h2 h2 h2) (* h3 h3 h3) h4 (* h5 
h5) (* j2 j2 j2 j2 j2)) (* 656 (* h2 h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 
j2 j2 j2)) (* 816 (* h2 h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 496
 (* h2 h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2)) (* 144 (* h2 h2 h2 h2) (* 
h3 h3 h3) h4 (* h5 h5) j2) (* 16 (* h2 h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5)) (* 
128 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 768 (* h2 h2
 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 1696 (* h2 h2 h2 h2) (* h3 
h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 1824 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 h6 
(* j2 j2 j2)) (* 1024 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2)) (* 288 
(* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 h6 j2) (* 32 (* h2 h2 h2 h2) (* h3 h3 h3) h4 
h5 h6) (* 32 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 240 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 656 (* 
h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 816 (* h2 h2 h2 h2) 
(* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 496 (* h2 h2 h2 h2) (* h3 h3 h3) (* 
h5 h5) h6 (* j2 j2)) (* 144 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 j2) (* 16 
(* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6) (* 64 (* h2 h2 h2 h2) (* h3 h3 h3) h5
 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 384 (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* h6 
h6) (* j2 j2 j2 j2 j2)) (* 848 (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 
j2 j2 j2)) (* 912 (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 512
 (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2)) (* 144 (* h2 h2 h2 h2) (* 
h3 h3 h3) h5 (* h6 h6) j2) (* 16 (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6)) (* 
32 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 208 (* h2
 h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 512 (* h2 h2 h2 h2) 
(* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 624 (* h2 h2 h2 h2) (* h3 h3) (* 
h4 h4 h4) h5 (* j2 j2 j2)) (* 400 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* 
j2 j2)) (* 128 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 j2) (* 16 (* h2 h2 h2 
h2) (* h3 h3) (* h4 h4 h4) h5) (* 64 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 
h5) (* j2 j2 j2 j2 j2 j2)) (* 416 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) 
(* j2 j2 j2 j2 j2)) (* 1024 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 
j2 j2 j2)) (* 1248 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2)) 
(* 800 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 256 (* h2 h2 
h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) j2) (* 32 (* h2 h2 h2 h2) (* h3 h3) (* h4 
h4) (* h5 h5)) (* 96 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2
 j2)) (* 624 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 
1536 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 1872 (* h2 h2
 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 1200 (* h2 h2 h2 h2) (* h3 h3
) (* h4 h4) h5 h6 (* j2 j2)) (* 384 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 j2
) (* 48 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6) (* 16 (* h2 h2 h2 h2) (* h3 
h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 128 (* h2 h2 h2 h2) (* h3 h3) h4 
(* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 384 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5
) (* j2 j2 j2 j2)) (* 544 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2)
) (* 384 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2)) (* 128 (* h2 h2 h2
 h2) (* h3 h3) h4 (* h5 h5 h5) j2) (* 16 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5 
h5)) (* 128 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
832 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 2048 (* h2 
h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 2496 (* h2 h2 h2 h2) (* 
h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 1600 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 
h5) h6 (* j2 j2)) (* 512 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 j2) (* 64 (* 
h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6) (* 96 (* h2 h2 h2 h2) (* h3 h3) h4 h5 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 624 (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6
) (* j2 j2 j2 j2 j2)) (* 1536 (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2
 j2 j2)) (* 1872 (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 1200
 (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 384 (* h2 h2 h2 h2) (* 
h3 h3) h4 h5 (* h6 h6) j2) (* 48 (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6)) (* 
16 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 128 (* h2
 h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 384 (* h2 h2 h2 h2) 
(* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 544 (* h2 h2 h2 h2) (* h3 h3) (* 
h5 h5 h5) h6 (* j2 j2 j2)) (* 384 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* 
j2 j2)) (* 128 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 j2) (* 16 (* h2 h2 h2 
h2) (* h3 h3) (* h5 h5 h5) h6) (* 64 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 416 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* 1024 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 
j2 j2 j2)) (* 1248 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) 
(* 800 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 256 (* h2 h2 
h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) j2) (* 32 (* h2 h2 h2 h2) (* h3 h3) (* h5 
h5) (* h6 h6)) (* 32 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2
 j2)) (* 208 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
512 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 624 (* h2 h2 
h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 400 (* h2 h2 h2 h2) (* h3 h3) 
h5 (* h6 h6 h6) (* j2 j2)) (* 128 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) j2) 
(* 16 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6)) (* 16 (* h2 h2 h2 h2) h3 (* h4 
h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 112 (* h2 h2 h2 h2) h3 (* h4 h4 h4) 
(* h5 h5) (* j2 j2 j2 j2 j2)) (* 304 (* h2 h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) 
(* j2 j2 j2 j2)) (* 416 (* h2 h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) 
(* 304 (* h2 h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 112 (* h2 h2 h2 
h2) h3 (* h4 h4 h4) (* h5 h5) j2) (* 16 (* h2 h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5
)) (* 16 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 112
 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 304 (* h2 h2 
h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 416 (* h2 h2 h2 h2) h3 (* 
h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 304 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5 
h5) (* j2 j2)) (* 112 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) j2) (* 16 (* h2 
h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5)) (* 48 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5
) h6 (* j2 j2 j2 j2 j2 j2)) (* 336 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* 
j2 j2 j2 j2 j2)) (* 912 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2
)) (* 1248 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 912 (* h2 
h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 336 (* h2 h2 h2 h2) h3 (* h4 
h4) (* h5 h5) h6 j2) (* 48 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6) (* 32 (* 
h2 h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 224 (* h2 h2 h2 h2)
 h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 608 (* h2 h2 h2 h2) h3 h4 (* h5 h5
 h5) h6 (* j2 j2 j2 j2)) (* 832 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 
j2)) (* 608 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2)) (* 224 (* h2 h2 h2 
h2) h3 h4 (* h5 h5 h5) h6 j2) (* 32 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) h6) (* 48
 (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 336 (* h2 
h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 912 (* h2 h2 h2 h2) 
h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 1248 (* h2 h2 h2 h2) h3 h4 (* h5 
h5) (* h6 h6) (* j2 j2 j2)) (* 912 (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* 
j2 j2)) (* 336 (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) j2) (* 48 (* h2 h2 h2 
h2) h3 h4 (* h5 h5) (* h6 h6)) (* 16 (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 112 (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2
 j2 j2 j2)) (* 304 (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) 
(* 416 (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 304 (* h2 h2 
h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 112 (* h2 h2 h2 h2) h3 (* h5 h5 
h5) (* h6 h6) j2) (* 16 (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6)) (* 16 (* h2 
h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 112 (* h2 h2 h2 h2
) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 304 (* h2 h2 h2 h2) h3 (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 416 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2)) (* 304 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2)) 
(* 112 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) j2) (* 16 (* h2 h2 h2 h2) h3 
(* h5 h5) (* h6 h6 h6)) (* 64 (* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2
 j2 j2 j2 j2 j2)) (* 416 (* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 
j2 j2 j2)) (* 1040 (* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2))
 (* 1336 (* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 968 (* h2
 h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 400 (* h2 h2 h2) (* h3 h3 
h3 h3) (* h4 h4) h5 (* j2 j2)) (* 88 (* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 
j2) (* 8 (* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5) (* 32 (* h2 h2 h2) (* h3 h3 
h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 256 (* h2 h2 h2) (* h3 h3 h3 h3
) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 776 (* h2 h2 h2) (* h3 h3 h3 h3) h4 (* 
h5 h5) (* j2 j2 j2 j2 j2)) (* 1144 (* h2 h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* 
j2 j2 j2 j2)) (* 904 (* h2 h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 
392 (* h2 h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2)) (* 88 (* h2 h2 h2) (* 
h3 h3 h3 h3) h4 (* h5 h5) j2) (* 8 (* h2 h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5)) 
(* 128 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 832 
(* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 2080 (* h2 h2 h2
) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 2672 (* h2 h2 h2) (* h3 h3 h3 
h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 1936 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* 
j2 j2 j2)) (* 800 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2)) (* 176 (* h2 
h2 h2) (* h3 h3 h3 h3) h4 h5 h6 j2) (* 16 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 h6)
 (* 32 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
256 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 776 (* 
h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 1144 (* h2 h2 h2) 
(* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 904 (* h2 h2 h2) (* h3 h3 h3 h3
) (* h5 h5) h6 (* j2 j2 j2)) (* 392 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 
(* j2 j2)) (* 88 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 j2) (* 8 (* h2 h2 h2)
 (* h3 h3 h3 h3) (* h5 h5) h6) (* 64 (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 416 (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2
 j2 j2 j2 j2 j2)) (* 1040 (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 
j2 j2)) (* 1336 (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 
968 (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 400 (* h2 h2 h2) 
(* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2)) (* 88 (* h2 h2 h2) (* h3 h3 h3 h3) h5 
(* h6 h6) j2) (* 8 (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6)) (* 64 (* h2 h2 h2)
 (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 448 (* h2 h2 h2) (* 
h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 1232 (* h2 h2 h2) (* h3 h3 
h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 1760 (* h2 h2 h2) (* h3 h3 h3) (* h4 
h4 h4) h5 (* j2 j2 j2 j2)) (* 1424 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* 
j2 j2 j2)) (* 656 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2)) (* 160 
(* h2 h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 j2) (* 16 (* h2 h2 h2) (* h3 h3 h3) 
(* h4 h4 h4) h5) (* 112 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 
j2 j2 j2 j2 j2)) (* 808 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 
j2 j2 j2 j2)) (* 2296 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 
j2 j2)) (* 3376 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) 
(* 2792 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 1304 (* 
h2 h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 320 (* h2 h2 h2) (* h3 
h3 h3) (* h4 h4) (* h5 h5) j2) (* 32 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 
h5)) (* 192 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 1344 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 3696
 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 5280 (* h2 h2 
h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 4272 (* h2 h2 h2) (* h3 h3 
h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 1968 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5
 h6 (* j2 j2)) (* 480 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 j2) (* 48 (* h2 
h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6) (* 32 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5
 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 272 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2)) (* 896 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2
 j2 j2 j2)) (* 1472 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) 
(* 1312 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2)) (* 640 (* h2 h2 
h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2)) (* 160 (* h2 h2 h2) (* h3 h3 h3) h4 
(* h5 h5 h5) j2) (* 16 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5)) (* 224 (* h2 
h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1616 (* h2 h2 
h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 4592 (* h2 h2 h2) (* 
h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 6752 (* h2 h2 h2) (* h3 h3 h3) 
h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 5584 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) 
h6 (* j2 j2 j2)) (* 2608 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2)) 
(* 640 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 j2) (* 64 (* h2 h2 h2) (* h3 h3
 h3) h4 (* h5 h5) h6) (* 192 (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 1344 (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 3696 (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2))
 (* 5280 (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 4272 (* 
h2 h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 1968 (* h2 h2 h2) (* h3 
h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 480 (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* h6 
h6) j2) (* 48 (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6)) (* 32 (* h2 h2 h2) (* 
h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 272 (* h2 h2 h2) (* h3 h3
 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 896 (* h2 h2 h2) (* h3 h3 h3) (* 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 1472 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) 
h6 (* j2 j2 j2 j2)) (* 1312 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 
j2)) (* 640 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2)) (* 160 (* h2 h2
 h2) (* h3 h3 h3) (* h5 h5 h5) h6 j2) (* 16 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 
h5) h6) (* 112 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 808 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 2296 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 3376 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 2792 
(* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 1304 (* h2 h2 h2)
 (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 320 (* h2 h2 h2) (* h3 h3 h3) 
(* h5 h5) (* h6 h6) j2) (* 32 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6)) (* 
64 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 448 
(* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1232 (* h2 
h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1760 (* h2 h2 h2) (* 
h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1424 (* h2 h2 h2) (* h3 h3 h3) h5 
(* h6 h6 h6) (* j2 j2 j2)) (* 656 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* 
j2 j2)) (* 160 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) j2) (* 16 (* h2 h2 h2) 
(* h3 h3 h3) h5 (* h6 h6 h6)) (* 16 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 
(* j2 j2 j2 j2 j2 j2 j2)) (* 120 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2
 j2 j2 j2 j2 j2)) (* 360 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 
j2 j2)) (* 568 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 512
 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2)) (* 264 (* h2 h2 h2) (* 
h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2)) (* 72 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4 h4
) h5 j2) (* 8 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5) (* 64 (* h2 h2 h2) (* 
h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 480 (* h2 h2 h2) (* 
h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1440 (* h2 h2 h2) (* h3 
h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 2272 (* h2 h2 h2) (* h3 h3) 
(* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 2048 (* h2 h2 h2) (* h3 h3) (* h4 h4 
h4) (* h5 h5) (* j2 j2 j2)) (* 1056 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5
) (* j2 j2)) (* 288 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) j2) (* 32 (* 
h2 h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5)) (* 64 (* h2 h2 h2) (* h3 h3) (* h4 
h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 480 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4
) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 1440 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6
 (* j2 j2 j2 j2 j2)) (* 2272 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 
j2 j2)) (* 2048 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 1056 
(* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2)) (* 288 (* h2 h2 h2) (* h3 
h3) (* h4 h4 h4) h5 h6 j2) (* 32 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6) (* 
56 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
432 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1336
 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 2168 (* h2
 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 2000 (* h2 h2 h2) 
(* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 1048 (* h2 h2 h2) (* h3 h3) 
(* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 288 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 
h5 h5) j2) (* 32 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5)) (* 192 (* h2 h2 
h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1440 (* h2 h2 
h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 4320 (* h2 h2 h2)
 (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 6816 (* h2 h2 h2) (* h3
 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 6144 (* h2 h2 h2) (* h3 h3) (* 
h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 3168 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5
 h5) h6 (* j2 j2)) (* 864 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 j2) (* 
96 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6) (* 96 (* h2 h2 h2) (* h3 h3) 
(* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 720 (* h2 h2 h2) (* h3 h3) 
(* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2160 (* h2 h2 h2) (* h3 h3) (* 
h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 3408 (* h2 h2 h2) (* h3 h3) (* h4 h4)
 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 3072 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* h6
 h6) (* j2 j2 j2)) (* 1584 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 
j2)) (* 432 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6) j2) (* 48 (* h2 h2 h2)
 (* h3 h3) (* h4 h4) h5 (* h6 h6)) (* 8 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5
) (* j2 j2 j2 j2 j2 j2 j2)) (* 72 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* 
j2 j2 j2 j2 j2 j2)) (* 256 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2
 j2 j2)) (* 464 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 
464 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2)) (* 256 (* h2 h2 h2) 
(* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2)) (* 72 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5
 h5 h5) j2) (* 8 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5)) (* 112 (* h2 h2 h2) 
(* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 864 (* h2 h2 h2) (* h3
 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 2672 (* h2 h2 h2) (* h3 h3) h4
 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 4336 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 
h5) h6 (* j2 j2 j2 j2)) (* 4000 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 
j2 j2)) (* 2096 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2)) (* 576 (* 
h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 j2) (* 64 (* h2 h2 h2) (* h3 h3) h4 (* h5
 h5 h5) h6) (* 192 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 1440 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 4320 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)
) (* 6816 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 6144
 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 3168 (* h2 h2 h2
) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 864 (* h2 h2 h2) (* h3 h3) h4 
(* h5 h5) (* h6 h6) j2) (* 96 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6)) (* 
64 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 480 
(* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1440 (* h2 
h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2272 (* h2 h2 h2) (* 
h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 2048 (* h2 h2 h2) (* h3 h3) h4 h5 
(* h6 h6 h6) (* j2 j2 j2)) (* 1056 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* 
j2 j2)) (* 288 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) j2) (* 32 (* h2 h2 h2) 
(* h3 h3) h4 h5 (* h6 h6 h6)) (* 8 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2)) (* 72 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2)) (* 256 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2
)) (* 464 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 464 (* 
h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 256 (* h2 h2 h2) (* h3 
h3) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 72 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) 
h6 j2) (* 8 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6) (* 56 (* h2 h2 h2) (* h3 
h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 432 (* h2 h2 h2) (* h3 
h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1336 (* h2 h2 h2) (* h3 h3)
 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2168 (* h2 h2 h2) (* h3 h3) (* h5
 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 2000 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2)) (* 1048 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) 
(* j2 j2)) (* 288 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) j2) (* 32 (* h2 
h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6)) (* 64 (* h2 h2 h2) (* h3 h3) (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 480 (* h2 h2 h2) (* h3 h3) (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1440 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2272 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2)) (* 2048 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2
 j2 j2)) (* 1056 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 288
 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) j2) (* 32 (* h2 h2 h2) (* h3 h3) 
(* h5 h5) (* h6 h6 h6)) (* 16 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2
 j2 j2 j2 j2 j2)) (* 120 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 360 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 568 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 512 (* h2 
h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 264 (* h2 h2 h2) (* h3 h3) 
h5 (* h6 h6 h6 h6) (* j2 j2)) (* 72 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) j2
) (* 8 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6)) (* 8 (* h2 h2 h2) h3 (* h4 h4 
h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 64 (* h2 h2 h2) h3 (* h4 h4 h4 h4)
 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 208 (* h2 h2 h2) h3 (* h4 h4 h4 h4) (* h5 
h5) (* j2 j2 j2 j2 j2)) (* 360 (* h2 h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 
j2 j2 j2)) (* 360 (* h2 h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 208
 (* h2 h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2)) (* 64 (* h2 h2 h2) h3 (* 
h4 h4 h4 h4) (* h5 h5) j2) (* 8 (* h2 h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5)) (* 16
 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 128 (* 
h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 416 (* h2 h2 h2
) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 720 (* h2 h2 h2) h3 (* h4 
h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 720 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 
h5 h5) (* j2 j2 j2)) (* 416 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2))
 (* 128 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) j2) (* 16 (* h2 h2 h2) h3 (* 
h4 h4 h4) (* h5 h5 h5)) (* 32 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2
 j2 j2 j2 j2 j2)) (* 256 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 
j2 j2 j2)) (* 832 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) 
(* 1440 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 1440 (* h2
 h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 832 (* h2 h2 h2) h3 (* h4 
h4 h4) (* h5 h5) h6 (* j2 j2)) (* 256 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 
j2) (* 32 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6) (* 8 (* h2 h2 h2) h3 (* h4 
h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 64 (* h2 h2 h2) h3 (* h4 h4) 
(* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 208 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5
 h5 h5) (* j2 j2 j2 j2 j2)) (* 360 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) (* 
j2 j2 j2 j2)) (* 360 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 
208 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 64 (* h2 h2 h2) h3 
(* h4 h4) (* h5 h5 h5 h5) j2) (* 8 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5)) 
(* 48 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 384
 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 1248 (* h2 
h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 2160 (* h2 h2 h2) h3 
(* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 2160 (* h2 h2 h2) h3 (* h4 h4) (* 
h5 h5 h5) h6 (* j2 j2 j2)) (* 1248 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* 
j2 j2)) (* 384 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 j2) (* 48 (* h2 h2 h2) 
h3 (* h4 h4) (* h5 h5 h5) h6) (* 48 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6
) (* j2 j2 j2 j2 j2 j2 j2)) (* 384 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6)
 (* j2 j2 j2 j2 j2 j2)) (* 1248 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* 2160 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 
j2 j2 j2)) (* 2160 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) 
(* 1248 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 384 (* h2 h2
 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) j2) (* 48 (* h2 h2 h2) h3 (* h4 h4) (* h5 
h5) (* h6 h6)) (* 16 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2)) (* 128 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 416 
(* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 720 (* h2 h2 h2) h3
 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 720 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5
) h6 (* j2 j2 j2)) (* 416 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 
128 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) h6 j2) (* 16 (* h2 h2 h2) h3 h4 (* h5 h5 
h5 h5) h6) (* 48 (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 384 (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
1248 (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2160 (* h2
 h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 2160 (* h2 h2 h2) h3 h4
 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 1248 (* h2 h2 h2) h3 h4 (* h5 h5 h5) 
(* h6 h6) (* j2 j2)) (* 384 (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) j2) (* 48 
(* h2 h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6)) (* 32 (* h2 h2 h2) h3 h4 (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 256 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6
 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 832 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2)) (* 1440 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2)) (* 1440 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 832 
(* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 256 (* h2 h2 h2) h3 h4 
(* h5 h5) (* h6 h6 h6) j2) (* 32 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6)) (* 8
 (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 64 (* h2
 h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 208 (* h2 h2 h2) 
h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 360 (* h2 h2 h2) h3 (* h5 h5
 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 360 (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* h6 
h6) (* j2 j2 j2)) (* 208 (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) 
(* 64 (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) j2) (* 8 (* h2 h2 h2) h3 (* h5 
h5 h5 h5) (* h6 h6)) (* 16 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2
 j2 j2 j2 j2)) (* 128 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 416 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
720 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 720 (* h2 h2 
h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 416 (* h2 h2 h2) h3 (* h5 h5 
h5) (* h6 h6 h6) (* j2 j2)) (* 128 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) j2)
 (* 16 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6)) (* 8 (* h2 h2 h2) h3 (* h5 h5)
 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 64 (* h2 h2 h2) h3 (* h5 h5) (* h6
 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 208 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6 
h6) (* j2 j2 j2 j2 j2)) (* 360 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 
j2 j2 j2)) (* 360 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 208
 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 64 (* h2 h2 h2) h3 (* 
h5 h5) (* h6 h6 h6 h6) j2) (* 8 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6)) (* 32
 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 240 
(* h2 h2) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 728 (* h2
 h2) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 1188 (* h2 h2) 
(* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 1152 (* h2 h2) (* h3 h3 
h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 684 (* h2 h2) (* h3 h3 h3 h3) (* h4 
h4 h4) h5 (* j2 j2 j2)) (* 244 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 
j2)) (* 48 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4 h4) h5 j2) (* 4 (* h2 h2) (* h3 h3
 h3 h3) (* h4 h4 h4) h5) (* 32 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 288 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 1032 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) 
(* j2 j2 j2 j2 j2 j2)) (* 1920 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* 
j2 j2 j2 j2 j2)) (* 2048 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 
j2 j2)) (* 1296 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 
480 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 96 (* h2 h2) (* 
h3 h3 h3 h3) (* h4 h4) (* h5 h5) j2) (* 8 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) 
(* h5 h5)) (* 96 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 720 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2
)) (* 2184 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 
3564 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 3456 (* h2
 h2) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 2052 (* h2 h2) (* h3 h3
 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 732 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4)
 h5 h6 (* j2 j2)) (* 144 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 h6 j2) (* 12 (* 
h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 h6) (* 8 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 84 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5 
h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 352 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2)) (* 756 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2
 j2 j2 j2)) (* 900 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) 
(* 612 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2)) (* 236 (* h2 h2) 
(* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2)) (* 48 (* h2 h2) (* h3 h3 h3 h3) h4 
(* h5 h5 h5) j2) (* 4 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5 h5)) (* 64 (* h2 h2)
 (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 576 (* h2 h2) 
(* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2064 (* h2 h2) (* 
h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 3840 (* h2 h2) (* h3 h3 
h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 4096 (* h2 h2) (* h3 h3 h3 h3) h4 
(* h5 h5) h6 (* j2 j2 j2 j2)) (* 2592 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) h6 
(* j2 j2 j2)) (* 960 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 192
 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) h6 j2) (* 16 (* h2 h2) (* h3 h3 h3 h3) 
h4 (* h5 h5) h6) (* 96 (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 720 (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2)) (* 2184 (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)
) (* 3564 (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 3456 
(* h2 h2) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 2052 (* h2 h2) (* 
h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 732 (* h2 h2) (* h3 h3 h3 h3) h4 
h5 (* h6 h6) (* j2 j2)) (* 144 (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* h6 h6) j2) (* 
12 (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* h6 h6)) (* 8 (* h2 h2) (* h3 h3 h3 h3) (* 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 84 (* h2 h2) (* h3 h3 h3 h3) (* h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 352 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5
) h6 (* j2 j2 j2 j2 j2 j2)) (* 756 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2)) (* 900 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2
)) (* 612 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 236 (* h2 
h2) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2)) (* 48 (* h2 h2) (* h3 h3 h3 h3) 
(* h5 h5 h5) h6 j2) (* 4 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) h6) (* 32 (* h2 
h2) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 288 (* 
h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1032 (* 
h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1920 (* h2 
h2) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2048 (* h2 h2) 
(* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 1296 (* h2 h2) (* h3 h3 
h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 480 (* h2 h2) (* h3 h3 h3 h3) (* h5 
h5) (* h6 h6) (* j2 j2)) (* 96 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) j2)
 (* 8 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6)) (* 32 (* h2 h2) (* h3 h3 h3
 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 240 (* h2 h2) (* h3 h3 h3 
h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 728 (* h2 h2) (* h3 h3 h3 h3) 
h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1188 (* h2 h2) (* h3 h3 h3 h3) h5 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1152 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6 h6) 
(* j2 j2 j2 j2)) (* 684 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) 
(* 244 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 48 (* h2 h2) (* 
h3 h3 h3 h3) h5 (* h6 h6 h6) j2) (* 4 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6 h6))
 (* 16 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 128 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 
420 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 748 (* 
h2 h2) (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 796 (* h2 h2) (* 
h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 520 (* h2 h2) (* h3 h3 h3) (* 
h4 h4 h4 h4) h5 (* j2 j2 j2)) (* 204 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4 h4) h5 
(* j2 j2)) (* 44 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4 h4) h5 j2) (* 4 (* h2 h2) 
(* h3 h3 h3) (* h4 h4 h4 h4) h5) (* 56 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* h5
 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 460 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1552 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* 
h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2836 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* h5 
h5) (* j2 j2 j2 j2 j2)) (* 3084 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) 
(* j2 j2 j2 j2)) (* 2048 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 
j2)) (* 812 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 176 (* 
h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) j2) (* 16 (* h2 h2) (* h3 h3 h3) (* 
h4 h4 h4) (* h5 h5)) (* 64 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 512 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 
j2 j2 j2 j2)) (* 1680 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 
j2 j2)) (* 2992 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) 
(* 3184 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 2080 (* h2
 h2) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 816 (* h2 h2) (* h3 h3 h3)
 (* h4 h4 h4) h5 h6 (* j2 j2)) (* 176 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 h6 
j2) (* 16 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 h6) (* 32 (* h2 h2) (* h3 h3 h3
) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 304 (* h2 h2) (* h3 h3 
h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1168 (* h2 h2) (* h3 h3 
h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2368 (* h2 h2) (* h3 h3 h3)
 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 2784 (* h2 h2) (* h3 h3 h3) (* h4
 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 1952 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* 
h5 h5 h5) (* j2 j2 j2)) (* 800 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* 
j2 j2)) (* 176 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) j2) (* 16 (* h2 h2)
 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5)) (* 168 (* h2 h2) (* h3 h3 h3) (* h4 h4) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1380 (* h2 h2) (* h3 h3 h3) (* h4 
h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 4656 (* h2 h2) (* h3 h3 h3) (* h4 
h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 8508 (* h2 h2) (* h3 h3 h3) (* h4 h4)
 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 9252 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5
 h5) h6 (* j2 j2 j2 j2)) (* 6144 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 
(* j2 j2 j2)) (* 2436 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2)) 
(* 528 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 j2) (* 48 (* h2 h2) (* h3 
h3 h3) (* h4 h4) (* h5 h5) h6) (* 96 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 768 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2520 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4488 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* h6 
h6) (* j2 j2 j2 j2 j2)) (* 4776 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) 
(* j2 j2 j2 j2)) (* 3120 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 
j2)) (* 1224 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 264 (* 
h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) j2) (* 24 (* h2 h2) (* h3 h3 h3) (* 
h4 h4) h5 (* h6 h6)) (* 4 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 44 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 
j2 j2 j2)) (* 196 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2
)) (* 456 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 600 
(* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 456 (* h2 h2) (* 
h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2)) (* 196 (* h2 h2) (* h3 h3 h3) h4 (* 
h5 h5 h5 h5) (* j2 j2)) (* 44 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5 h5) j2) (* 4
 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5 h5)) (* 64 (* h2 h2) (* h3 h3 h3) h4 (* 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 608 (* h2 h2) (* h3 h3 h3) h4 (* h5
 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2336 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 4736 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2)) (* 5568 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 
j2 j2)) (* 3904 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 1600 
(* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2)) (* 352 (* h2 h2) (* h3 h3 
h3) h4 (* h5 h5 h5) h6 j2) (* 32 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) h6) (* 
168 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 1380 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 4656 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
8508 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 9252 
(* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 6144 (* h2 h2)
 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 2436 (* h2 h2) (* h3 h3 h3
) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 528 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) 
(* h6 h6) j2) (* 48 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6)) (* 64 (* h2 
h2) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 512 (* h2 h2
) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1680 (* h2 h2) 
(* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2992 (* h2 h2) (* h3 
h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 3184 (* h2 h2) (* h3 h3 h3) h4 
h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 2080 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6 
h6) (* j2 j2 j2)) (* 816 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2)) 
(* 176 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6 h6) j2) (* 16 (* h2 h2) (* h3 h3 h3
) h4 h5 (* h6 h6 h6)) (* 4 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 44 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2
 j2 j2 j2)) (* 196 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2)) (* 456 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 600
 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 456 (* h2 h2) (* 
h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 196 (* h2 h2) (* h3 h3 h3) (* h5 
h5 h5 h5) h6 (* j2 j2)) (* 44 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) h6 j2) (* 4
 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) h6) (* 32 (* h2 h2) (* h3 h3 h3) (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 304 (* h2 h2) (* h3 h3 h3) (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1168 (* h2 h2) (* h3 h3 h3) (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2368 (* h2 h2) (* h3 h3 h3) (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2784 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5)
 (* h6 h6) (* j2 j2 j2 j2)) (* 1952 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6
) (* j2 j2 j2)) (* 800 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2)) 
(* 176 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) j2) (* 16 (* h2 h2) (* h3 
h3 h3) (* h5 h5 h5) (* h6 h6)) (* 56 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 460 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1552 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2836 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2)) (* 3084 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2)) (* 2048 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 
j2)) (* 812 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 176 (* 
h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) j2) (* 16 (* h2 h2) (* h3 h3 h3) (* 
h5 h5) (* h6 h6 h6)) (* 16 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 128 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 420 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2
 j2)) (* 748 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
796 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 520 (* h2 h2) 
(* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 204 (* h2 h2) (* h3 h3 h3) h5 
(* h6 h6 h6 h6) (* j2 j2)) (* 44 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6 h6) j2) 
(* 4 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6 h6)) (* 16 (* h2 h2) (* h3 h3) (* h4 
h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 136 (* h2 h2) (* h3 h3) (* 
h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 480 (* h2 h2) (* h3 h3) (* 
h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 928 (* h2 h2) (* h3 h3) (* h4 
h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 1080 (* h2 h2) (* h3 h3) (* h4 h4 h4 
h4) (* h5 h5) (* j2 j2 j2 j2)) (* 776 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) (* h5 
h5) (* j2 j2 j2)) (* 336 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2)
) (* 80 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) j2) (* 8 (* h2 h2) (* h3 
h3) (* h4 h4 h4 h4) (* h5 h5)) (* 28 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5 
h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 244 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 884 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 
h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1752 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5 
h5) (* j2 j2 j2 j2 j2)) (* 2084 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) 
(* j2 j2 j2 j2)) (* 1524 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 
j2)) (* 668 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2)) (* 160 (* 
h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) j2) (* 16 (* h2 h2) (* h3 h3) (* h4 
h4 h4) (* h5 h5 h5)) (* 64 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 544 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2)) (* 1920 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2)) (* 3712 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* 4320 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 
j2)) (* 3104 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 1344
 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 320 (* h2 h2) (* h3
 h3) (* h4 h4 h4) (* h5 h5) h6 j2) (* 32 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 
h5) h6) (* 8 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 80 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2
 j2)) (* 328 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)
) (* 720 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 
928 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 720 (* h2 
h2) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 328 (* h2 h2) (* h3 h3)
 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 80 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 
h5 h5 h5) j2) (* 8 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5)) (* 84 (* h2 h2
) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 732 (* h2 
h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2652 (* h2 
h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 5256 (* h2 h2)
 (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 6252 (* h2 h2) (* h3
 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 4572 (* h2 h2) (* h3 h3) (* 
h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 2004 (* h2 h2) (* h3 h3) (* h4 h4) (* h5
 h5 h5) h6 (* j2 j2)) (* 480 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 j2) 
(* 48 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6) (* 96 (* h2 h2) (* h3 h3) 
(* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 816 (* h2 h2) (* 
h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2880 (* h2 h2)
 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 5568 (* h2 h2
) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 6480 (* h2 h2) 
(* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 4656 (* h2 h2) (* h3
 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 2016 (* h2 h2) (* h3 h3) (* 
h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 480 (* h2 h2) (* h3 h3) (* h4 h4) (* h5
 h5) (* h6 h6) j2) (* 48 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6)) (* 
16 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 160
 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 656 (* 
h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 1440 (* h2 h2) 
(* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 1856 (* h2 h2) (* h3 h3) 
h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 1440 (* h2 h2) (* h3 h3) h4 (* h5 h5 
h5 h5) h6 (* j2 j2 j2)) (* 656 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 
j2)) (* 160 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) h6 j2) (* 16 (* h2 h2) (* h3 
h3) h4 (* h5 h5 h5 h5) h6) (* 84 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 732 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6
) (* j2 j2 j2 j2 j2 j2 j2)) (* 2652 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6
) (* j2 j2 j2 j2 j2 j2)) (* 5256 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* 6252 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2)) (* 4572 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) 
(* 2004 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 480 (* h2 h2
) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) j2) (* 48 (* h2 h2) (* h3 h3) h4 (* h5 h5 
h5) (* h6 h6)) (* 64 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 544 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 1920 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 3712 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2)) (* 4320 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) 
(* 3104 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 1344 (* 
h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 320 (* h2 h2) (* h3 h3)
 h4 (* h5 h5) (* h6 h6 h6) j2) (* 32 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6 
h6)) (* 8 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 80 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2
)) (* 328 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 720 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 928 
(* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 720 (* h2 h2) 
(* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 328 (* h2 h2) (* h3 h3) (* 
h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 80 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* 
h6 h6) j2) (* 8 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6)) (* 28 (* h2 h2) 
(* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 244 (* h2 h2
) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 884 (* h2 h2)
 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1752 (* h2 h2) 
(* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2084 (* h2 h2) (* h3 
h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1524 (* h2 h2) (* h3 h3) (* h5
 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 668 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6
 h6 h6) (* j2 j2)) (* 160 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) j2) (* 
16 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6)) (* 16 (* h2 h2) (* h3 h3) (* 
h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 136 (* h2 h2) (* h3 h3) 
(* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 480 (* h2 h2) (* h3 h3) 
(* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 928 (* h2 h2) (* h3 h3) (* 
h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1080 (* h2 h2) (* h3 h3) (* h5 h5)
 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 776 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 
h6 h6) (* j2 j2 j2)) (* 336 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 
j2)) (* 80 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) j2) (* 8 (* h2 h2) (* 
h3 h3) (* h5 h5) (* h6 h6 h6 h6)) (* 4 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5 h5)
 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 36 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 136 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2
 j2 j2 j2 j2 j2)) (* 284 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 
j2 j2)) (* 360 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 284
 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 136 (* h2 h2) h3 (* 
h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2)) (* 36 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5
 h5) j2) (* 4 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5 h5)) (* 4 (* h2 h2) h3 (* h4
 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 36 (* h2 h2) h3 (* h4 h4
 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 136 (* h2 h2) h3 (* h4 h4 h4) 
(* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 284 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5
 h5 h5) (* j2 j2 j2 j2 j2)) (* 360 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* 
j2 j2 j2 j2)) (* 284 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 
136 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 36 (* h2 h2) h3 (* 
h4 h4 h4) (* h5 h5 h5 h5) j2) (* 4 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5 h5)) 
(* 16 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
144 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 544 
(* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 1136 (* h2 
h2) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 1440 (* h2 h2) h3 (* 
h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 1136 (* h2 h2) h3 (* h4 h4 h4) (* 
h5 h5 h5) h6 (* j2 j2 j2)) (* 544 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* 
j2 j2)) (* 144 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) h6 j2) (* 16 (* h2 h2) h3 
(* h4 h4 h4) (* h5 h5 h5) h6) (* 12 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 108 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 408 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2
 j2 j2 j2 j2 j2)) (* 852 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 
j2 j2)) (* 1080 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 
852 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 408 (* h2 h2) h3 
(* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 108 (* h2 h2) h3 (* h4 h4) (* h5 h5 
h5 h5) h6 j2) (* 12 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) h6) (* 24 (* h2 h2) 
h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 216 (* h2 h2
) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 816 (* h2 h2)
 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1704 (* h2 h2) h3
 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2160 (* h2 h2) h3 (* h4
 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 1704 (* h2 h2) h3 (* h4 h4) (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 816 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* 
h6 h6) (* j2 j2)) (* 216 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) j2) (* 24
 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6)) (* 12 (* h2 h2) h3 h4 (* h5 h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 108 (* h2 h2) h3 h4 (* h5 h5 h5
 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 408 (* h2 h2) h3 h4 (* h5 h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 852 (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* h6 h6
) (* j2 j2 j2 j2 j2)) (* 1080 (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2
 j2 j2)) (* 852 (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 408 
(* h2 h2) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 108 (* h2 h2) h3 h4 (* 
h5 h5 h5 h5) (* h6 h6) j2) (* 12 (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* h6 h6)) (* 
16 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 144
 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 544 (* 
h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1136 (* h2 h2) 
h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1440 (* h2 h2) h3 h4 (* 
h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1136 (* h2 h2) h3 h4 (* h5 h5 h5) (* 
h6 h6 h6) (* j2 j2 j2)) (* 544 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 
j2)) (* 144 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6 h6) j2) (* 16 (* h2 h2) h3 h4 
(* h5 h5 h5) (* h6 h6 h6)) (* 4 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 36 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 136 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2
 j2 j2)) (* 284 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 360 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 284 (* h2 
h2) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 136 (* h2 h2) h3 (* h5 h5 
h5 h5) (* h6 h6 h6) (* j2 j2)) (* 36 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6 h6) 
j2) (* 4 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6 h6)) (* 4 (* h2 h2) h3 (* h5 h5 
h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 36 (* h2 h2) h3 (* h5 h5 h5)
 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 136 (* h2 h2) h3 (* h5 h5 h5) (* 
h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 284 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6
 h6) (* j2 j2 j2 j2 j2)) (* 360 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 
j2 j2 j2)) (* 284 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 136
 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 36 (* h2 h2) h3 (* h5 
h5 h5) (* h6 h6 h6 h6) j2) (* 4 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6 h6)) (* 8 
h2 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 80 
h2 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 330 h2
 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 738 h2 (* 
h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 992 h2 (* h3 h3 h3
 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 836 h2 (* h3 h3 h3 h3) (* h4 
h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 444 h2 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 
h5) (* j2 j2 j2)) (* 144 h2 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2)) 
(* 26 h2 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) j2) (* 2 h2 (* h3 h3 h3 h3) (* 
h4 h4 h4) (* h5 h5)) (* 4 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 46 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 218 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2
 j2 j2 j2)) (* 554 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 
j2)) (* 828 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 756
 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 424 h2 (* h3 h3 
h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 142 h2 (* h3 h3 h3 h3) (* h4 h4) 
(* h5 h5 h5) (* j2 j2)) (* 26 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) j2) (* 2
 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5)) (* 24 h2 (* h3 h3 h3 h3) (* h4 h4) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 240 h2 (* h3 h3 h3 h3) (* h4 h4)
 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 990 h2 (* h3 h3 h3 h3) (* h4 h4) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2214 h2 (* h3 h3 h3 h3) (* h4 h4) (* 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 2976 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) 
h6 (* j2 j2 j2 j2 j2)) (* 2508 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 
j2 j2 j2)) (* 1332 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 
432 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 78 h2 (* h3 h3 h3 h3
) (* h4 h4) (* h5 h5) h6 j2) (* 6 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6) (* 
8 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 92 h2
 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 436 h2 (* h3
 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1108 h2 (* h3 h3 h3 
h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 1656 h2 (* h3 h3 h3 h3) h4 (* 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 1512 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 
(* j2 j2 j2 j2)) (* 848 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 
284 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2)) (* 52 h2 (* h3 h3 h3 h3) h4
 (* h5 h5 h5) h6 j2) (* 4 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6) (* 24 h2 (* h3 
h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 240 h2 (* h3
 h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 990 h2 (* h3 
h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2214 h2 (* h3 h3 
h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2976 h2 (* h3 h3 h3 h3) 
h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2508 h2 (* h3 h3 h3 h3) h4 (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2)) (* 1332 h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6)
 (* j2 j2 j2)) (* 432 h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 78
 h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) j2) (* 6 h2 (* h3 h3 h3 h3) h4 (* h5 
h5) (* h6 h6)) (* 4 h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 46 h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 218 h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2
 j2)) (* 554 h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 828 h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 756 h2 
(* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 424 h2 (* h3 h3 h3 h3
) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 142 h2 (* h3 h3 h3 h3) (* h5 h5 h5) 
(* h6 h6) (* j2 j2)) (* 26 h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) j2) (* 2 h2
 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6)) (* 8 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6
 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 80 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6
 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 330 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 738 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6
) (* j2 j2 j2 j2 j2 j2)) (* 992 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2)) (* 836 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) 
(* 444 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 144 h2 (* h3 
h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 26 h2 (* h3 h3 h3 h3) (* h5 h5) 
(* h6 h6 h6) j2) (* 2 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6)) (* 4 h2 (* h3 
h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 42 h2 (* h3 
h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 184 h2 (* h3 h3
 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 442 h2 (* h3 h3 h3) 
(* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 644 h2 (* h3 h3 h3) (* h4 h4
 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 592 h2 (* h3 h3 h3) (* h4 h4 h4 h4) (* 
h5 h5) (* j2 j2 j2 j2)) (* 344 h2 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 
j2 j2)) (* 122 h2 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2)) (* 24 h2 (* 
h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) j2) (* 2 h2 (* h3 h3 h3) (* h4 h4 h4 h4) (* 
h5 h5)) (* 8 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 84 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 368 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 884 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1288 
h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 1184 h2 (* h3 
h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 688 h2 (* h3 h3 h3) (* h4 
h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 244 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 
h5) (* j2 j2)) (* 48 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) j2) (* 4 h2 (* h3
 h3 h3) (* h4 h4 h4) (* h5 h5 h5)) (* 16 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 168 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5)
 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 736 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1768 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 2576 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* 2368 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2))
 (* 1376 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 488 h2 (* h3
 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 96 h2 (* h3 h3 h3) (* h4 h4 h4) 
(* h5 h5) h6 j2) (* 8 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6) (* 2 h2 (* h3 
h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 24 h2 (* h3 
h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 120 h2 (* h3 h3
 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 326 h2 (* h3 h3 h3) 
(* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 528 h2 (* h3 h3 h3) (* h4 h4
) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 528 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 
h5 h5) (* j2 j2 j2 j2)) (* 326 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 
j2 j2)) (* 120 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 24 h2 (* 
h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) j2) (* 2 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 
h5 h5)) (* 24 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 252 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2
 j2)) (* 1104 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)
) (* 2652 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
3864 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 3552 h2 
(* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 2064 h2 (* h3 h3 h3) 
(* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 732 h2 (* h3 h3 h3) (* h4 h4) (* h5 
h5 h5) h6 (* j2 j2)) (* 144 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 j2) (* 12 
h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6) (* 24 h2 (* h3 h3 h3) (* h4 h4) (* h5
 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 252 h2 (* h3 h3 h3) (* h4 h4) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1104 h2 (* h3 h3 h3) (* h4 
h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2652 h2 (* h3 h3 h3) (* h4 
h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3864 h2 (* h3 h3 h3) (* h4 h4)
 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 3552 h2 (* h3 h3 h3) (* h4 h4) (* h5
 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 2064 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* 
h6 h6) (* j2 j2 j2)) (* 732 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 
j2)) (* 144 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) j2) (* 12 h2 (* h3 h3 
h3) (* h4 h4) (* h5 h5) (* h6 h6)) (* 4 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 48 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 240 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2)) (* 652 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2)) (* 1056 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 1056 
h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 652 h2 (* h3 h3 h3) h4
 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 240 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 
(* j2 j2)) (* 48 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 j2) (* 4 h2 (* h3 h3 h3) 
h4 (* h5 h5 h5 h5) h6) (* 24 h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 252 h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2
 j2 j2 j2 j2 j2 j2)) (* 1104 h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 2652 h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 3864 h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2))
 (* 3552 h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 2064 h2 
(* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 732 h2 (* h3 h3 h3) h4 
(* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 144 h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 
h6) j2) (* 12 h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6)) (* 16 h2 (* h3 h3 h3) 
h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 168 h2 (* h3 h3 h3)
 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 736 h2 (* h3 h3 h3) 
h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1768 h2 (* h3 h3 h3) h4 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2576 h2 (* h3 h3 h3) h4 (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2368 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2)) (* 1376 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 
j2 j2)) (* 488 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 96 h2 (* 
h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) j2) (* 8 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 
h6 h6)) (* 2 h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 24 h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 120 h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 326 h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 528 
h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 528 h2 (* h3 h3
 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 326 h2 (* h3 h3 h3) (* h5 h5 
h5 h5) (* h6 h6) (* j2 j2 j2)) (* 120 h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) 
(* j2 j2)) (* 24 h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) j2) (* 2 h2 (* h3 h3 
h3) (* h5 h5 h5 h5) (* h6 h6)) (* 8 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 84 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 368 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 884 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2)) (* 1288 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2)) (* 1184 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 
688 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 244 h2 (* h3 h3 
h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 48 h2 (* h3 h3 h3) (* h5 h5 h5) (* 
h6 h6 h6) j2) (* 4 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6)) (* 4 h2 (* h3 h3 
h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 42 h2 (* h3 h3 
h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 184 h2 (* h3 h3 h3
) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 442 h2 (* h3 h3 h3) (* 
h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 644 h2 (* h3 h3 h3) (* h5 h5) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 592 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6
 h6) (* j2 j2 j2 j2)) (* 344 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 
j2)) (* 122 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 24 h2 (* h3 
h3 h3) (* h5 h5) (* h6 h6 h6 h6) j2) (* 2 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 
h6)) (* 2 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 22 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 102 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
262 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 412 h2 
(* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 412 h2 (* h3 h3) 
(* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 262 h2 (* h3 h3) (* h4 h4 h4 h4
) (* h5 h5 h5) (* j2 j2 j2)) (* 102 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) 
(* j2 j2)) (* 22 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) j2) (* 2 h2 (* h3 h3)
 (* h4 h4 h4 h4) (* h5 h5 h5)) (* 2 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 22 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 102 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 262 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2
 j2 j2 j2 j2 j2)) (* 412 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 
j2 j2)) (* 412 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 262
 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 102 h2 (* h3 h3) (* 
h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 22 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5
 h5) j2) (* 2 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5)) (* 8 h2 (* h3 h3) (* h4
 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 88 h2 (* h3 h3) (* h4
 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 408 h2 (* h3 h3) (* h4 
h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1048 h2 (* h3 h3) (* h4 h4 
h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 1648 h2 (* h3 h3) (* h4 h4 h4) (* 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 1648 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) 
h6 (* j2 j2 j2 j2)) (* 1048 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 
j2)) (* 408 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 88 h2 (* h3 
h3) (* h4 h4 h4) (* h5 h5 h5) h6 j2) (* 8 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5)
 h6) (* 6 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 66 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 306 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
786 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 1236 h2 
(* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 1236 h2 (* h3 h3) 
(* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 786 h2 (* h3 h3) (* h4 h4) (* 
h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 306 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 
(* j2 j2)) (* 66 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 j2) (* 6 h2 (* h3 h3)
 (* h4 h4) (* h5 h5 h5 h5) h6) (* 12 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 132 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 612 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5
) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1572 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5
) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2472 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 2472 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2)) (* 1572 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2
 j2 j2)) (* 612 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 132 
h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) j2) (* 12 h2 (* h3 h3) (* h4 h4) 
(* h5 h5 h5) (* h6 h6)) (* 6 h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 66 h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 306 h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2
 j2 j2 j2 j2)) (* 786 h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 1236 h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 1236 h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 786 h2 (* 
h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 306 h2 (* h3 h3) h4 (* h5 
h5 h5 h5) (* h6 h6) (* j2 j2)) (* 66 h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) 
j2) (* 6 h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6)) (* 8 h2 (* h3 h3) h4 (* h5 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 88 h2 (* h3 h3) h4 (* h5 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 408 h2 (* h3 h3) h4 (* h5 h5
 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1048 h2 (* h3 h3) h4 (* h5 h5 h5)
 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1648 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2)) (* 1648 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2)) (* 1048 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) 
(* 408 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 88 h2 (* h3 h3) 
h4 (* h5 h5 h5) (* h6 h6 h6) j2) (* 8 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6))
 (* 2 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 22 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
102 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 262 
h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 412 h2 (* h3
 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 412 h2 (* h3 h3) (* h5 
h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 262 h2 (* h3 h3) (* h5 h5 h5 h5) (* 
h6 h6 h6) (* j2 j2 j2)) (* 102 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 
j2)) (* 22 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) j2) (* 2 h2 (* h3 h3) (* h5
 h5 h5 h5) (* h6 h6 h6)) (* 2 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2
 j2 j2 j2 j2 j2 j2 j2)) (* 22 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2
 j2 j2 j2 j2 j2 j2)) (* 102 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 262 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2
 j2 j2)) (* 412 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 412 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 262 h2 (* 
h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 102 h2 (* h3 h3) (* h5 h5 
h5) (* h6 h6 h6 h6) (* j2 j2)) (* 22 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) 
j2) (* 2 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6))) 0)))
(check-sat)
(exit)

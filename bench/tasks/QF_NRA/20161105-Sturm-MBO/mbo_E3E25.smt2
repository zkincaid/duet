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
(set-info :instance |E3E25|)
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
(+ (* 10 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2 j2 j2)) (* 180
 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2 j2)) (* 1088 (* h1 h1 
h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2)) (* 2928 (* h1 h1 h1 h1) (* h2 
h2 h2) (* h3 h3) h5 (* j2 j2 j2)) (* 3808 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3)
 h5 (* j2 j2)) (* 2304 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 j2) (* 512 (* 
h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5) (* 2 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 
h3) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 42 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h6
 (* j2 j2 j2 j2 j2 j2)) (* 328 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h6 (* j2 
j2 j2 j2 j2)) (* 1280 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h6 (* j2 j2 j2 j2))
 (* 2752 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h6 (* j2 j2 j2)) (* 3296 (* h1 
h1 h1 h1) (* h2 h2 h2) (* h3 h3) h6 (* j2 j2)) (* 2048 (* h1 h1 h1 h1) (* h2 h2 
h2) (* h3 h3) h6 j2) (* 512 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h6) (* 10 (* 
h1 h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 110 (* h1 h1 h1
 h1) (* h2 h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 468 (* h1 h1 h1 h1) (* h2 
h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2)) (* 992 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* 
h5 h5) (* j2 j2 j2)) (* 1104 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* j2 j2)
) (* 608 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) j2) (* 128 (* h1 h1 h1 h1) 
(* h2 h2 h2) h3 (* h5 h5)) (* 3 (* h1 h1 h1 h1) (* h2 h2 h2) h3 h5 h6 (* j2 j2 
j2 j2 j2 j2 j2)) (* 48 (* h1 h1 h1 h1) (* h2 h2 h2) h3 h5 h6 (* j2 j2 j2 j2 j2 
j2)) (* 307 (* h1 h1 h1 h1) (* h2 h2 h2) h3 h5 h6 (* j2 j2 j2 j2 j2)) (* 1018 
(* h1 h1 h1 h1) (* h2 h2 h2) h3 h5 h6 (* j2 j2 j2 j2)) (* 1900 (* h1 h1 h1 h1) 
(* h2 h2 h2) h3 h5 h6 (* j2 j2 j2)) (* 2008 (* h1 h1 h1 h1) (* h2 h2 h2) h3 h5 
h6 (* j2 j2)) (* 1120 (* h1 h1 h1 h1) (* h2 h2 h2) h3 h5 h6 j2) (* 256 (* h1 h1 
h1 h1) (* h2 h2 h2) h3 h5 h6) (* 2 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 28 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 162 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6) (* j2 j2 j2 j2 j2
)) (* 504 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6) (* j2 j2 j2 j2)) (* 912 (* 
h1 h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6) (* j2 j2 j2)) (* 960 (* h1 h1 h1 h1) (* 
h2 h2 h2) h3 (* h6 h6) (* j2 j2)) (* 544 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h6 
h6) j2) (* 128 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6)) (* (* h1 h1 h1 h1) (* 
h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 13 (* h1 h1 h1 h1) (* h2 h2 
h2) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 69 (* h1 h1 h1 h1) (* h2 h2 h2) (* h5
 h5) h6 (* j2 j2 j2 j2 j2)) (* 195 (* h1 h1 h1 h1) (* h2 h2 h2) (* h5 h5) h6 (* 
j2 j2 j2 j2)) (* 318 (* h1 h1 h1 h1) (* h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2)) (* 
300 (* h1 h1 h1 h1) (* h2 h2 h2) (* h5 h5) h6 (* j2 j2)) (* 152 (* h1 h1 h1 h1) 
(* h2 h2 h2) (* h5 h5) h6 j2) (* 32 (* h1 h1 h1 h1) (* h2 h2 h2) (* h5 h5) h6) 
(* (* h1 h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 13 (* 
h1 h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 69 (* h1 h1 h1 
h1) (* h2 h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 195 (* h1 h1 h1 h1) (* h2 
h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 318 (* h1 h1 h1 h1) (* h2 h2 h2) h5 (* 
h6 h6) (* j2 j2 j2)) (* 300 (* h1 h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6) (* j2 j2))
 (* 152 (* h1 h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6) j2) (* 32 (* h1 h1 h1 h1) (* 
h2 h2 h2) h5 (* h6 h6)) (* 10 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* j2 j2
 j2 j2 j2 j2 j2)) (* 280 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 
j2 j2 j2)) (* 2848 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2 j2))
 (* 13168 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2)) (* 30016 
(* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2)) (* 34816 (* h1 h1 h1 h1)
 (* h2 h2) (* h3 h3 h3) h5 (* j2 j2)) (* 19456 (* h1 h1 h1 h1) (* h2 h2) (* h3 
h3 h3) h5 j2) (* 4096 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5) (* 2 (* h1 h1 
h1 h1) (* h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 62 (* h1 h1 h1 
h1) (* h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 740 (* h1 h1 h1 h1) 
(* h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2 j2 j2 j2)) (* 4408 (* h1 h1 h1 h1) (* h2 
h2) (* h3 h3 h3) h6 (* j2 j2 j2 j2 j2)) (* 14544 (* h1 h1 h1 h1) (* h2 h2) (* h3
 h3 h3) h6 (* j2 j2 j2 j2)) (* 27712 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h6 
(* j2 j2 j2)) (* 30208 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h6 (* j2 j2)) (* 
17408 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h6 j2) (* 4096 (* h1 h1 h1 h1) (* 
h2 h2) (* h3 h3 h3) h6) (* 2 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* j2 j2 
j2 j2 j2 j2 j2)) (* 108 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2
 j2 j2)) (* 1210 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2 j2)) 
(* 5560 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2)) (* 12264 (* 
h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2)) (* 13696 (* h1 h1 h1 h1) 
(* h2 h2) (* h3 h3) h4 h5 (* j2 j2)) (* 7424 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3)
 h4 h5 j2) (* 1536 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5) (* 12 (* h1 h1 h1 
h1) (* h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 192 (* h1 h1 h1 h1) 
(* h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2)) (* 1228 (* h1 h1 h1 h1) (* h2 
h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 4072 (* h1 h1 h1 h1) (* h2 h2) (* h3 
h3) h4 h6 (* j2 j2 j2 j2)) (* 7600 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h6 (* 
j2 j2 j2)) (* 8032 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h6 (* j2 j2)) (* 4480 
(* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h6 j2) (* 1024 (* h1 h1 h1 h1) (* h2 h2) 
(* h3 h3) h4 h6) (* 20 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2
 j2 j2 j2 j2)) (* 420 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 
j2 j2 j2)) (* 3056 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2 
j2)) (* 10624 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 
19744 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2)) (* 19968 (* h1
 h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* j2 j2)) (* 10240 (* h1 h1 h1 h1) (* 
h2 h2) (* h3 h3) (* h5 h5) j2) (* 2048 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h5
 h5)) (* 5 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 136 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
1411 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 7508 
(* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 22500 (* h1 h1 
h1 h1) (* h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 38800 (* h1 h1 h1 h1) (* h2
 h2) (* h3 h3) h5 h6 (* j2 j2 j2)) (* 37888 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) 
h5 h6 (* j2 j2)) (* 19456 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h5 h6 j2) (* 4096 
(* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h5 h6) (* 4 (* h1 h1 h1 h1) (* h2 h2) (* h3 
h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 96 (* h1 h1 h1 h1) (* h2 h2) (* h3
 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 884 (* h1 h1 h1 h1) (* h2 h2) (* h3 
h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4216 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3)
 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 11584 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* 
h6 h6) (* j2 j2 j2 j2)) (* 18976 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6) 
(* j2 j2 j2)) (* 18240 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6) (* j2 j2)) 
(* 9472 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6) j2) (* 2048 (* h1 h1 h1 h1
) (* h2 h2) (* h3 h3) (* h6 h6)) (* 2 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 74 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* j2 
j2 j2 j2 j2 j2)) (* 622 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2
 j2)) (* 2238 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2)) (* 4112
 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2)) (* 4024 (* h1 h1 h1 h1)
 (* h2 h2) h3 h4 (* h5 h5) (* j2 j2)) (* 1984 (* h1 h1 h1 h1) (* h2 h2) h3 h4 
(* h5 h5) j2) (* 384 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5)) (* 16 (* h1 h1 
h1 h1) (* h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 208 (* h1 h1 h1 h1) 
(* h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 1104 (* h1 h1 h1 h1) (* h2 h2) 
h3 h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 3120 (* h1 h1 h1 h1) (* h2 h2) h3 h4 h5 h6 
(* j2 j2 j2 j2)) (* 5088 (* h1 h1 h1 h1) (* h2 h2) h3 h4 h5 h6 (* j2 j2 j2)) (* 
4800 (* h1 h1 h1 h1) (* h2 h2) h3 h4 h5 h6 (* j2 j2)) (* 2432 (* h1 h1 h1 h1) 
(* h2 h2) h3 h4 h5 h6 j2) (* 512 (* h1 h1 h1 h1) (* h2 h2) h3 h4 h5 h6) (* 4 (* 
h1 h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 52 (* h1 h1 
h1 h1) (* h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 276 (* h1 h1 h1 h1) 
(* h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 780 (* h1 h1 h1 h1) (* h2 h2) 
h3 h4 (* h6 h6) (* j2 j2 j2 j2)) (* 1272 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h6 
h6) (* j2 j2 j2)) (* 1200 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6) (* j2 j2)) 
(* 608 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6) j2) (* 128 (* h1 h1 h1 h1) (* 
h2 h2) h3 h4 (* h6 h6)) (* 10 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* j2 j2
 j2 j2 j2 j2 j2)) (* 140 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 
j2 j2 j2)) (* 778 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) 
(* 2216 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 3504 (* h1
 h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2)) (* 3088 (* h1 h1 h1 h1) (* h2
 h2) h3 (* h5 h5 h5) (* j2 j2)) (* 1408 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5
) j2) (* 256 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5)) (* 4 (* h1 h1 h1 h1) (* 
h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 90 (* h1 h1 h1 h1) (* h2 
h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 764 (* h1 h1 h1 h1) (* h2 h2) 
h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 3330 (* h1 h1 h1 h1) (* h2 h2) h3 (* 
h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 8340 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5) h6 
(* j2 j2 j2 j2)) (* 12456 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2)
) (* 10928 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5) h6 (* j2 j2)) (* 5184 (* h1 h1
 h1 h1) (* h2 h2) h3 (* h5 h5) h6 j2) (* 1024 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5
 h5) h6) (* 6 (* h1 h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 114 (* h1 h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 874 (* h1 h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3566 
(* h1 h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 8552 (* h1 h1 
h1 h1) (* h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 12440 (* h1 h1 h1 h1) (* h2
 h2) h3 h5 (* h6 h6) (* j2 j2 j2)) (* 10784 (* h1 h1 h1 h1) (* h2 h2) h3 h5 (* 
h6 h6) (* j2 j2)) (* 5120 (* h1 h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6) j2) (* 1024 
(* h1 h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6)) (* 2 (* h1 h1 h1 h1) (* h2 h2) h3 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 34 (* h1 h1 h1 h1) (* h2 h2) h3 (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 242 (* h1 h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6
) (* j2 j2 j2 j2 j2 j2)) (* 942 (* h1 h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6) (* j2 
j2 j2 j2 j2)) (* 2196 (* h1 h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2 j2))
 (* 3144 (* h1 h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2)) (* 2704 (* h1 
h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6) (* j2 j2)) (* 1280 (* h1 h1 h1 h1) (* h2 h2)
 h3 (* h6 h6 h6) j2) (* 256 (* h1 h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6)) (* 4 (* 
h1 h1 h1 h1) (* h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 48 (* h1 h1 
h1 h1) (* h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 232 (* h1 h1 h1 h1) 
(* h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 592 (* h1 h1 h1 h1) (* h2 h2) 
h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 868 (* h1 h1 h1 h1) (* h2 h2) h4 (* h5 h5) 
h6 (* j2 j2 j2)) (* 736 (* h1 h1 h1 h1) (* h2 h2) h4 (* h5 h5) h6 (* j2 j2)) (* 
336 (* h1 h1 h1 h1) (* h2 h2) h4 (* h5 h5) h6 j2) (* 64 (* h1 h1 h1 h1) (* h2 h2
) h4 (* h5 h5) h6) (* 2 (* h1 h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2
 j2 j2 j2)) (* 24 (* h1 h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2
)) (* 116 (* h1 h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 296 
(* h1 h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 434 (* h1 h1 h1 h1
) (* h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 368 (* h1 h1 h1 h1) (* h2 h2) h4 h5
 (* h6 h6) (* j2 j2)) (* 168 (* h1 h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6) j2) (* 32
 (* h1 h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6)) (* (* h1 h1 h1 h1) (* h2 h2) (* h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 106 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2)) (* 380 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5 h5) h6 (* j2
 j2 j2 j2 j2)) (* 809 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2))
 (* 1052 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 820 (* h1 h1
 h1 h1) (* h2 h2) (* h5 h5 h5) h6 (* j2 j2)) (* 352 (* h1 h1 h1 h1) (* h2 h2) 
(* h5 h5 h5) h6 j2) (* 64 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5 h5) h6) (* 2 (* h1 
h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 32 (* h1
 h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 212 (* h1 
h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 760 (* h1 h1 
h1 h1) (* h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1618 (* h1 h1 h1 h1)
 (* h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 2104 (* h1 h1 h1 h1) (* h2 h2
) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 1640 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5) 
(* h6 h6) (* j2 j2)) (* 704 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6) j2) 
(* 128 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6)) (* (* h1 h1 h1 h1) (* h2 
h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1 h1 h1) (* h2 h2)
 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 106 (* h1 h1 h1 h1) (* h2 h2) h5 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 380 (* h1 h1 h1 h1) (* h2 h2) h5 (* h6 h6
 h6) (* j2 j2 j2 j2 j2)) (* 809 (* h1 h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6) (* j2 
j2 j2 j2)) (* 1052 (* h1 h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 
820 (* h1 h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6) (* j2 j2)) (* 352 (* h1 h1 h1 h1) 
(* h2 h2) h5 (* h6 h6 h6) j2) (* 64 (* h1 h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6)) 
(* 2 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 108 
(* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 1742 (* h1 h1
 h1 h1) h2 (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 12068 (* h1 h1 h1 h1) h2
 (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 42176 (* h1 h1 h1 h1) h2 (* h3 h3 h3)
 h4 h5 (* j2 j2 j2 j2)) (* 79104 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h5 (* j2 j2 
j2)) (* 80128 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h5 (* j2 j2)) (* 40960 (* h1 h1
 h1 h1) h2 (* h3 h3 h3) h4 h5 j2) (* 8192 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h5)
 (* 8 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 192 
(* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1736 (* h1 h1
 h1 h1) h2 (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2)) (* 8112 (* h1 h1 h1 h1) h2 
(* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 21984 (* h1 h1 h1 h1) h2 (* h3 h3 h3) 
h4 h6 (* j2 j2 j2 j2)) (* 35904 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h6 (* j2 j2 
j2)) (* 34816 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h6 (* j2 j2)) (* 18432 (* h1 h1
 h1 h1) h2 (* h3 h3 h3) h4 h6 j2) (* 4096 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h6)
 (* 100 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
2120 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 15600 
(* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 54336 (* h1 h1 
h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 98944 (* h1 h1 h1 h1) h2 
(* h3 h3 h3) (* h5 h5) (* j2 j2 j2)) (* 95232 (* h1 h1 h1 h1) h2 (* h3 h3 h3) 
(* h5 h5) (* j2 j2)) (* 45056 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) j2) (* 
8192 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5)) (* 40 (* h1 h1 h1 h1) h2 (* h3 
h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 976 (* h1 h1 h1 h1) h2 (* h3 h3 h3)
 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 9024 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h5 h6 
(* j2 j2 j2 j2 j2 j2)) (* 43064 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h5 h6 (* j2 j2 
j2 j2 j2)) (* 117664 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 
188672 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h5 h6 (* j2 j2 j2)) (* 173568 (* h1 h1 h1
 h1) h2 (* h3 h3 h3) h5 h6 (* j2 j2)) (* 83968 (* h1 h1 h1 h1) h2 (* h3 h3 h3) 
h5 h6 j2) (* 16384 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h5 h6) (* 4 (* h1 h1 h1 h1) 
h2 (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 112 (* h1 h1 h1 h1)
 h2 (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1252 (* h1 h1 h1 h1) 
h2 (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 7528 (* h1 h1 h1 h1) h2 
(* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 27216 (* h1 h1 h1 h1) h2 (* h3 
h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 61920 (* h1 h1 h1 h1) h2 (* h3 h3 h3) 
(* h6 h6) (* j2 j2 j2 j2)) (* 89216 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6) 
(* j2 j2 j2)) (* 78848 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6) (* j2 j2)) (* 
38912 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6) j2) (* 8192 (* h1 h1 h1 h1) h2 
(* h3 h3 h3) (* h6 h6)) (* 12 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* j2 j2
 j2 j2 j2 j2 j2)) (* 308 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 
j2 j2 j2)) (* 2460 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2))
 (* 8908 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 16472 (* 
h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 16128 (* h1 h1 h1 h1) h2
 (* h3 h3) (* h4 h4) h5 (* j2 j2)) (* 7936 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4
) h5 j2) (* 1536 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5) (* 16 (* h1 h1 h1 h1
) h2 (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 208 (* h1 h1 h1 h1) h2 
(* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 1104 (* h1 h1 h1 h1) h2 (* h3 
h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 3120 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 
h4) h6 (* j2 j2 j2 j2)) (* 5088 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h6 (* j2 
j2 j2)) (* 4800 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h6 (* j2 j2)) (* 2432 (* 
h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h6 j2) (* 512 (* h1 h1 h1 h1) h2 (* h3 h3) 
(* h4 h4) h6) (* 4 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 148 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2
 j2)) (* 1908 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) 
(* 11004 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 32472 
(* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 52672 (* h1 h1 h1 
h1) h2 (* h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 47360 (* h1 h1 h1 h1) h2 (* h3 h3
) h4 (* h5 h5) (* j2 j2)) (* 22016 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) j2)
 (* 4096 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5)) (* 16 (* h1 h1 h1 h1) h2 (* 
h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 484 (* h1 h1 h1 h1) h2 (* h3 h3)
 h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 4696 (* h1 h1 h1 h1) h2 (* h3 h3) h4 h5 
h6 (* j2 j2 j2 j2 j2 j2)) (* 22244 (* h1 h1 h1 h1) h2 (* h3 h3) h4 h5 h6 (* j2 
j2 j2 j2 j2)) (* 58944 (* h1 h1 h1 h1) h2 (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) 
(* 90656 (* h1 h1 h1 h1) h2 (* h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 79936 (* h1 h1 
h1 h1) h2 (* h3 h3) h4 h5 h6 (* j2 j2)) (* 37376 (* h1 h1 h1 h1) h2 (* h3 h3) h4
 h5 h6 j2) (* 7168 (* h1 h1 h1 h1) h2 (* h3 h3) h4 h5 h6) (* 16 (* h1 h1 h1 h1) 
h2 (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 272 (* h1 h1 h1 h1) h2
 (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1936 (* h1 h1 h1 h1) h2 (* 
h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 7536 (* h1 h1 h1 h1) h2 (* h3 h3) 
h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 17568 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h6 
h6) (* j2 j2 j2 j2)) (* 25152 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6) (* j2 j2
 j2)) (* 21632 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6) (* j2 j2)) (* 10240 (* 
h1 h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6) j2) (* 2048 (* h1 h1 h1 h1) h2 (* h3 h3) 
h4 (* h6 h6)) (* 100 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2
 j2 j2)) (* 1420 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)
) (* 7960 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 22576
 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 34752 (* h1 h1 h1
 h1) h2 (* h3 h3) (* h5 h5 h5) (* j2 j2 j2)) (* 29056 (* h1 h1 h1 h1) h2 (* h3 
h3) (* h5 h5 h5) (* j2 j2)) (* 12288 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) 
j2) (* 2048 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5)) (* 60 (* h1 h1 h1 h1) h2 
(* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1160 (* h1 h1 h1 h1) h2 
(* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 8964 (* h1 h1 h1 h1) h2 (* 
h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 36544 (* h1 h1 h1 h1) h2 (* h3 h3)
 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 86632 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5
) h6 (* j2 j2 j2 j2)) (* 122720 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5) h6 (* j2 
j2 j2)) (* 101632 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5) h6 (* j2 j2)) (* 45056 
(* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5) h6 j2) (* 8192 (* h1 h1 h1 h1) h2 (* h3 
h3) (* h5 h5) h6) (* 8 (* h1 h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 212 (* h1 h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2
 j2 j2 j2 j2)) (* 2248 (* h1 h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 12756 (* h1 h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 43256 (* h1 h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
91680 (* h1 h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 121728 (* h1
 h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 97920 (* h1 h1 h1 h1) h2 
(* h3 h3) h5 (* h6 h6) (* j2 j2)) (* 43520 (* h1 h1 h1 h1) h2 (* h3 h3) h5 (* h6
 h6) j2) (* 8192 (* h1 h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6)) (* 4 (* h1 h1 h1 h1)
 h2 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 84 (* h1 h1 h1 h1)
 h2 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 756 (* h1 h1 h1 h1) 
h2 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3820 (* h1 h1 h1 h1) h2 
(* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 11928 (* h1 h1 h1 h1) h2 (* h3 
h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 23856 (* h1 h1 h1 h1) h2 (* h3 h3) (* h6
 h6 h6) (* j2 j2 j2 j2)) (* 30560 (* h1 h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6) (* 
j2 j2 j2)) (* 24192 (* h1 h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6) (* j2 j2)) (* 
10752 (* h1 h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6) j2) (* 2048 (* h1 h1 h1 h1) h2 
(* h3 h3) (* h6 h6 h6)) (* 8 (* h1 h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* j2 j2 
j2 j2 j2 j2 j2)) (* 168 (* h1 h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2
 j2 j2)) (* 1128 (* h1 h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) 
(* 3448 (* h1 h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 5520 (* h1
 h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 4800 (* h1 h1 h1 h1) h2 h3
 (* h4 h4) (* h5 h5) (* j2 j2)) (* 2144 (* h1 h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5
) j2) (* 384 (* h1 h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5)) (* 20 (* h1 h1 h1 h1) h2
 h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 216 (* h1 h1 h1 h1) h2 h3 (* h4
 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 952 (* h1 h1 h1 h1) h2 h3 (* h4 h4) h5 h6 
(* j2 j2 j2 j2 j2)) (* 2304 (* h1 h1 h1 h1) h2 h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2
)) (* 3316 (* h1 h1 h1 h1) h2 h3 (* h4 h4) h5 h6 (* j2 j2 j2)) (* 2824 (* h1 h1 
h1 h1) h2 h3 (* h4 h4) h5 h6 (* j2 j2)) (* 1312 (* h1 h1 h1 h1) h2 h3 (* h4 h4) 
h5 h6 j2) (* 256 (* h1 h1 h1 h1) h2 h3 (* h4 h4) h5 h6) (* 2 (* h1 h1 h1 h1) h2 
h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 60 (* h1 h1 h1 h1) h2 h3 h4 
(* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 580 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5 
h5) (* j2 j2 j2 j2 j2 j2)) (* 2648 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5 h5) (* j2 
j2 j2 j2 j2)) (* 6506 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 
9084 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5 h5) (* j2 j2 j2)) (* 7200 (* h1 h1 h1 h1)
 h2 h3 h4 (* h5 h5 h5) (* j2 j2)) (* 3008 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5 h5) 
j2) (* 512 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5 h5)) (* 12 (* h1 h1 h1 h1) h2 h3 h4
 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 272 (* h1 h1 h1 h1) h2 h3 h4 (* h5
 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2248 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 9312 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5) h6 (* j2 j2 j2
 j2 j2)) (* 21724 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 
29744 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5) h6 (* j2 j2 j2)) (* 23664 (* h1 h1 h1 
h1) h2 h3 h4 (* h5 h5) h6 (* j2 j2)) (* 10112 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5)
 h6 j2) (* 1792 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5) h6) (* 18 (* h1 h1 h1 h1) h2 
h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 276 (* h1 h1 h1 h1) h2 h3 h4 
h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1740 (* h1 h1 h1 h1) h2 h3 h4 h5 (* h6
 h6) (* j2 j2 j2 j2 j2 j2)) (* 5968 (* h1 h1 h1 h1) h2 h3 h4 h5 (* h6 h6) (* j2 
j2 j2 j2 j2)) (* 12386 (* h1 h1 h1 h1) h2 h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2)) 
(* 16012 (* h1 h1 h1 h1) h2 h3 h4 h5 (* h6 h6) (* j2 j2 j2)) (* 12592 (* h1 h1 
h1 h1) h2 h3 h4 h5 (* h6 h6) (* j2 j2)) (* 5504 (* h1 h1 h1 h1) h2 h3 h4 h5 (* 
h6 h6) j2) (* 1024 (* h1 h1 h1 h1) h2 h3 h4 h5 (* h6 h6)) (* 20 (* h1 h1 h1 h1) 
h2 h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 324 (* h1 h1 h1 h1) h2 h3 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2164 (* h1 h1 h1 h1) h2 h3 (* h5 h5
 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 7756 (* h1 h1 h1 h1) h2 h3 (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2)) (* 16296 (* h1 h1 h1 h1) h2 h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2))
 (* 20576 (* h1 h1 h1 h1) h2 h3 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 15296 (* h1 h1 
h1 h1) h2 h3 (* h5 h5 h5) h6 (* j2 j2)) (* 6144 (* h1 h1 h1 h1) h2 h3 (* h5 h5 
h5) h6 j2) (* 1024 (* h1 h1 h1 h1) h2 h3 (* h5 h5 h5) h6) (* 5 (* h1 h1 h1 h1) 
h2 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 116 (* h1 h1 h1 h1)
 h2 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1096 (* h1 h1 h1 h1) 
h2 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 5586 (* h1 h1 h1 h1) h2 
h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 17059 (* h1 h1 h1 h1) h2 h3 (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 32618 (* h1 h1 h1 h1) h2 h3 (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2)) (* 39264 (* h1 h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6) 
(* j2 j2 j2)) (* 28832 (* h1 h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6) (* j2 j2)) (* 
11776 (* h1 h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6) j2) (* 2048 (* h1 h1 h1 h1) h2 
h3 (* h5 h5) (* h6 h6)) (* 4 (* h1 h1 h1 h1) h2 h3 h5 (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 80 (* h1 h1 h1 h1) h2 h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 672 (* h1 h1 h1 h1) h2 h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 3120 (* h1 h1 h1 h1) h2 h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
8884 (* h1 h1 h1 h1) h2 h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 16224 (* h1 h1
 h1 h1) h2 h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 19080 (* h1 h1 h1 h1) h2 h3 h5
 (* h6 h6 h6) (* j2 j2 j2)) (* 13952 (* h1 h1 h1 h1) h2 h3 h5 (* h6 h6 h6) (* j2
 j2)) (* 5760 (* h1 h1 h1 h1) h2 h3 h5 (* h6 h6 h6) j2) (* 1024 (* h1 h1 h1 h1) 
h2 h3 h5 (* h6 h6 h6)) (* 4 (* h1 h1 h1 h1) h2 (* h4 h4) (* h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2)) (* 44 (* h1 h1 h1 h1) h2 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 
j2 j2)) (* 192 (* h1 h1 h1 h1) h2 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
440 (* h1 h1 h1 h1) h2 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 580 (* h1 h1 
h1 h1) h2 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 444 (* h1 h1 h1 h1) h2 (* h4 
h4) (* h5 h5) h6 (* j2 j2)) (* 184 (* h1 h1 h1 h1) h2 (* h4 h4) (* h5 h5) h6 j2)
 (* 32 (* h1 h1 h1 h1) h2 (* h4 h4) (* h5 h5) h6) (* 2 (* h1 h1 h1 h1) h2 h4 (* 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 30 (* h1 h1 h1 h1) h2 h4 (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 184 (* h1 h1 h1 h1) h2 h4 (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 604 (* h1 h1 h1 h1) h2 h4 (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2)) (* 1170 (* h1 h1 h1 h1) h2 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 1382 
(* h1 h1 h1 h1) h2 h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 980 (* h1 h1 h1 h1) h2 h4
 (* h5 h5 h5) h6 (* j2 j2)) (* 384 (* h1 h1 h1 h1) h2 h4 (* h5 h5 h5) h6 j2) (* 
64 (* h1 h1 h1 h1) h2 h4 (* h5 h5 h5) h6) (* 4 (* h1 h1 h1 h1) h2 h4 (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 60 (* h1 h1 h1 h1) h2 h4 (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 368 (* h1 h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6
) (* j2 j2 j2 j2 j2 j2)) (* 1208 (* h1 h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6) (* j2
 j2 j2 j2 j2)) (* 2340 (* h1 h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)
) (* 2764 (* h1 h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 1960 (* h1 
h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 768 (* h1 h1 h1 h1) h2 h4 (* 
h5 h5) (* h6 h6) j2) (* 128 (* h1 h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6)) (* (* h1 
h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 19 (* h1 
h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 152 (* h1 h1
 h1 h1) h2 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 670 (* h1 h1 h1 
h1) h2 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1793 (* h1 h1 h1 h1) h2 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 3031 (* h1 h1 h1 h1) h2 (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2)) (* 3254 (* h1 h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6)
 (* j2 j2 j2)) (* 2152 (* h1 h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 
800 (* h1 h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6) j2) (* 128 (* h1 h1 h1 h1) h2 (* 
h5 h5 h5) (* h6 h6)) (* (* h1 h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 19 (* h1 h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2
 j2 j2 j2 j2)) (* 152 (* h1 h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 670 (* h1 h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2
)) (* 1793 (* h1 h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 3031
 (* h1 h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 3254 (* h1 h1 h1 
h1) h2 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 2152 (* h1 h1 h1 h1) h2 (* h5 h5)
 (* h6 h6 h6) (* j2 j2)) (* 800 (* h1 h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6) j2) 
(* 128 (* h1 h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6)) (* 8 (* h1 h1 h1 h1) (* h3 h3 
h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 216 (* h1 h1 h1 h1) (* h3 h3 h3
) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 2216 (* h1 h1 h1 h1) (* h3 h3 h3) 
(* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 11304 (* h1 h1 h1 h1) (* h3 h3 h3) (* h4 
h4) h5 (* j2 j2 j2 j2 j2)) (* 31632 (* h1 h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 
(* j2 j2 j2 j2)) (* 50496 (* h1 h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2)
) (* 45568 (* h1 h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2)) (* 21504 (* h1 
h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 j2) (* 4096 (* h1 h1 h1 h1) (* h3 h3 h3) (* 
h4 h4) h5) (* 20 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 544 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2
)) (* 5628 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 
28880 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 80480 (* 
h1 h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 125312 (* h1 h1 h1 h1
) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 107520 (* h1 h1 h1 h1) (* h3 h3 h3)
 h4 (* h5 h5) (* j2 j2)) (* 47104 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) j2) 
(* 8192 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5)) (* 4 (* h1 h1 h1 h1) (* h3 h3
 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 164 (* h1 h1 h1 h1) (* h3 h3 h3
) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2468 (* h1 h1 h1 h1) (* h3 h3 h3) h4 
h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 18028 (* h1 h1 h1 h1) (* h3 h3 h3) h4 h5 h6 
(* j2 j2 j2 j2 j2 j2)) (* 72808 (* h1 h1 h1 h1) (* h3 h3 h3) h4 h5 h6 (* j2 j2 
j2 j2 j2)) (* 172800 (* h1 h1 h1 h1) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 
245248 (* h1 h1 h1 h1) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 203264 (* h1 h1 h1
 h1) (* h3 h3 h3) h4 h5 h6 (* j2 j2)) (* 90112 (* h1 h1 h1 h1) (* h3 h3 h3) h4 
h5 h6 j2) (* 16384 (* h1 h1 h1 h1) (* h3 h3 h3) h4 h5 h6) (* 100 (* h1 h1 h1 h1)
 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2340 (* h1 h1 h1 h1) 
(* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 20224 (* h1 h1 h1 h1) (* 
h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 87872 (* h1 h1 h1 h1) (* h3 h3 
h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 213504 (* h1 h1 h1 h1) (* h3 h3 h3) (* 
h5 h5) h6 (* j2 j2 j2 j2)) (* 299264 (* h1 h1 h1 h1) (* h3 h3 h3) (* h5 h5) h6 
(* j2 j2 j2)) (* 237568 (* h1 h1 h1 h1) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2)) (* 
98304 (* h1 h1 h1 h1) (* h3 h3 h3) (* h5 h5) h6 j2) (* 16384 (* h1 h1 h1 h1) (* 
h3 h3 h3) (* h5 h5) h6) (* 20 (* h1 h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2
 j2 j2 j2 j2 j2 j2 j2)) (* 544 (* h1 h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 5828 (* h1 h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 33080 (* h1 h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 110912 (* h1 h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2
 j2)) (* 229312 (* h1 h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 
293632 (* h1 h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 225280 (* h1 
h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2)) (* 94208 (* h1 h1 h1 h1) (* h3 h3
 h3) h5 (* h6 h6) j2) (* 16384 (* h1 h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6)) (* 16 
(* h1 h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 256 (* h1
 h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 1536 (* h1 h1 h1 
h1) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 4512 (* h1 h1 h1 h1) (* h3 
h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 7152 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4 
h4) h5 (* j2 j2 j2)) (* 6240 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2)
) (* 2816 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 j2) (* 512 (* h1 h1 h1 h1) 
(* h3 h3) (* h4 h4 h4) h5) (* 8 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 208 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5
) (* j2 j2 j2 j2 j2 j2 j2)) (* 2016 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5
) (* j2 j2 j2 j2 j2 j2)) (* 9488 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) 
(* j2 j2 j2 j2 j2)) (* 23960 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* j2
 j2 j2 j2)) (* 34208 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2))
 (* 27648 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 11776 (* 
h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) j2) (* 2048 (* h1 h1 h1 h1) (* h3 h3)
 (* h4 h4) (* h5 h5)) (* 16 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 400 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2
 j2 j2 j2 j2)) (* 3536 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 
j2 j2)) (* 15408 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) 
(* 37216 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 51968 (* 
h1 h1 h1 h1) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 41600 (* h1 h1 h1 h1) 
(* h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 17664 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4
) h5 h6 j2) (* 3072 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) h5 h6) (* 20 (* h1 h1 h1
 h1) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 404 (* h1 h1 h1 
h1) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 3260 (* h1 h1 h1 h1) 
(* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 13612 (* h1 h1 h1 h1) (* h3 
h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 31888 (* h1 h1 h1 h1) (* h3 h3) h4 
(* h5 h5 h5) (* j2 j2 j2 j2)) (* 42784 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5)
 (* j2 j2 j2)) (* 32384 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2)) (* 
12800 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) j2) (* 2048 (* h1 h1 h1 h1) (* 
h3 h3) h4 (* h5 h5 h5)) (* 6 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 196 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2
 j2 j2 j2 j2 j2 j2)) (* 2560 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2)) (* 16708 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 
j2 j2 j2)) (* 60570 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)
) (* 128824 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 163872
 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 122240 (* h1 h1 h1 
h1) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 49152 (* h1 h1 h1 h1) (* h3 h3) h4 
(* h5 h5) h6 j2) (* 8192 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5) h6) (* 4 (* h1 
h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 176 (* h1
 h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2256 (* h1 
h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 13880 (* h1 h1 
h1 h1) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 47980 (* h1 h1 h1 h1)
 (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 99096 (* h1 h1 h1 h1) (* h3 h3
) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 124096 (* h1 h1 h1 h1) (* h3 h3) h4 h5 (* 
h6 h6) (* j2 j2 j2)) (* 91904 (* h1 h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2
)) (* 36864 (* h1 h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6) j2) (* 6144 (* h1 h1 h1 h1
) (* h3 h3) h4 h5 (* h6 h6)) (* 100 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1640 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 11044 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2)) (* 39584 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2)) (* 82048 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) 
(* 100352 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 70912 (* h1
 h1 h1 h1) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2)) (* 26624 (* h1 h1 h1 h1) (* h3 
h3) (* h5 h5 h5) h6 j2) (* 4096 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5 h5) h6) (* 30
 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 666 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 6122 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 30542 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 91056 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
168400 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 193792 
(* h1 h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 134400 (* h1 h1 
h1 h1) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 51200 (* h1 h1 h1 h1) (* h3 
h3) (* h5 h5) (* h6 h6) j2) (* 8192 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6
)) (* 20 (* h1 h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2
)) (* 404 (* h1 h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2))
 (* 3460 (* h1 h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
16412 (* h1 h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 47320 
(* h1 h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 85760 (* h1 h1 
h1 h1) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 97600 (* h1 h1 h1 h1) (* h3
 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 67328 (* h1 h1 h1 h1) (* h3 h3) h5 (* h6 
h6 h6) (* j2 j2)) (* 25600 (* h1 h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6) j2) (* 4096
 (* h1 h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6)) (* 8 (* h1 h1 h1 h1) h3 (* h4 h4 h4)
 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 120 (* h1 h1 h1 h1) h3 (* h4 h4 h4) (* 
h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 656 (* h1 h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) 
(* j2 j2 j2 j2 j2)) (* 1712 (* h1 h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 
j2 j2)) (* 2408 (* h1 h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 1880 
(* h1 h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 768 (* h1 h1 h1 h1) h3 
(* h4 h4 h4) (* h5 h5) j2) (* 128 (* h1 h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5)) (* 
4 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 76 
(* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 568 (* h1
 h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2168 (* h1 h1 h1 
h1) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 4628 (* h1 h1 h1 h1) h3 (* 
h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 5756 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 
h5 h5) (* j2 j2 j2)) (* 4144 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2)
) (* 1600 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) j2) (* 256 (* h1 h1 h1 h1) 
h3 (* h4 h4) (* h5 h5 h5)) (* 8 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 192 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2
 j2 j2 j2 j2 j2)) (* 1584 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 
j2 j2 j2)) (* 6304 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2))
 (* 13704 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 17184 
(* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 12416 (* h1 h1 h1 h1)
 h3 (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 4800 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5
 h5) h6 j2) (* 768 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5) h6) (* 2 (* h1 h1 h1 
h1) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 66 (* h1 h1 h1 h1) 
h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 740 (* h1 h1 h1 h1) h3 h4 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 4100 (* h1 h1 h1 h1) h3 h4 (* h5 h5
 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 12810 (* h1 h1 h1 h1) h3 h4 (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2)) (* 23866 (* h1 h1 h1 h1) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 
j2)) (* 26992 (* h1 h1 h1 h1) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 18144 (* h1
 h1 h1 h1) h3 h4 (* h5 h5 h5) h6 (* j2 j2)) (* 6656 (* h1 h1 h1 h1) h3 h4 (* h5 
h5 h5) h6 j2) (* 1024 (* h1 h1 h1 h1) h3 h4 (* h5 h5 h5) h6) (* 2 (* h1 h1 h1 h1
) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 86 (* h1 h1 h1 h1
) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1044 (* h1 h1 h1 h1)
 h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 5980 (* h1 h1 h1 h1) h3 
h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 18970 (* h1 h1 h1 h1) h3 h4 (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 35598 (* h1 h1 h1 h1) h3 h4 (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2)) (* 40400 (* h1 h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6) 
(* j2 j2 j2)) (* 27200 (* h1 h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 
9984 (* h1 h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6) j2) (* 1536 (* h1 h1 h1 h1) h3 h4
 (* h5 h5) (* h6 h6)) (* 10 (* h1 h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 192 (* h1 h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2
 j2 j2 j2 j2 j2 j2)) (* 1548 (* h1 h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 6840 (* h1 h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 18186 (* h1 h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)
) (* 30168 (* h1 h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 31344 
(* h1 h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 19776 (* h1 h1 h1 h1)
 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 6912 (* h1 h1 h1 h1) h3 (* h5 h5 h5) 
(* h6 h6) j2) (* 1024 (* h1 h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6)) (* 10 (* h1 h1 
h1 h1) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 192 (* h1 h1
 h1 h1) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1548 (* h1 h1 
h1 h1) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 6840 (* h1 h1 h1 
h1) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 18186 (* h1 h1 h1 h1) h3
 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 30168 (* h1 h1 h1 h1) h3 (* h5 h5
) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 31344 (* h1 h1 h1 h1) h3 (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2)) (* 19776 (* h1 h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2)) 
(* 6912 (* h1 h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6) j2) (* 1024 (* h1 h1 h1 h1) h3
 (* h5 h5) (* h6 h6 h6)) (* 10 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 (* j2 
j2 j2 j2 j2)) (* 140 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2)) 
(* 528 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2)) (* 816 (* h1 h1 
h1) (* h2 h2 h2 h2) (* h3 h3) h5 (* j2 j2)) (* 544 (* h1 h1 h1) (* h2 h2 h2 h2) 
(* h3 h3) h5 j2) (* 128 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5) (* 2 (* h1 h1
 h1) (* h2 h2 h2 h2) (* h3 h3) h6 (* j2 j2 j2 j2 j2 j2)) (* 34 (* h1 h1 h1) (* 
h2 h2 h2 h2) (* h3 h3) h6 (* j2 j2 j2 j2 j2)) (* 192 (* h1 h1 h1) (* h2 h2 h2 h2
) (* h3 h3) h6 (* j2 j2 j2 j2)) (* 512 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h6
 (* j2 j2 j2)) (* 704 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h6 (* j2 j2)) (* 
480 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h6 j2) (* 128 (* h1 h1 h1) (* h2 h2 
h2 h2) (* h3 h3) h6) (* 10 (* h1 h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) (* j2 j2 j2
 j2 j2)) (* 70 (* h1 h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2)) (* 188
 (* h1 h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) (* j2 j2 j2)) (* 240 (* h1 h1 h1) (* 
h2 h2 h2 h2) h3 (* h5 h5) (* j2 j2)) (* 144 (* h1 h1 h1) (* h2 h2 h2 h2) h3 (* 
h5 h5) j2) (* 32 (* h1 h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5)) (* 3 (* h1 h1 h1) 
(* h2 h2 h2 h2) h3 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 36 (* h1 h1 h1) (* h2 h2 h2 
h2) h3 h5 h6 (* j2 j2 j2 j2 j2)) (* 163 (* h1 h1 h1) (* h2 h2 h2 h2) h3 h5 h6 
(* j2 j2 j2 j2)) (* 366 (* h1 h1 h1) (* h2 h2 h2 h2) h3 h5 h6 (* j2 j2 j2)) (* 
436 (* h1 h1 h1) (* h2 h2 h2 h2) h3 h5 h6 (* j2 j2)) (* 264 (* h1 h1 h1) (* h2 
h2 h2 h2) h3 h5 h6 j2) (* 64 (* h1 h1 h1) (* h2 h2 h2 h2) h3 h5 h6) (* 2 (* h1 
h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 20 (* h1 h1 h1) 
(* h2 h2 h2 h2) h3 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 82 (* h1 h1 h1) (* h2 h2 h2 
h2) h3 (* h6 h6) (* j2 j2 j2 j2)) (* 176 (* h1 h1 h1) (* h2 h2 h2 h2) h3 (* h6 
h6) (* j2 j2 j2)) (* 208 (* h1 h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6) (* j2 j2)) 
(* 128 (* h1 h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6) j2) (* 32 (* h1 h1 h1) (* h2 h2
 h2 h2) h3 (* h6 h6)) (* (* h1 h1 h1) (* h2 h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2 
j2 j2 j2)) (* 9 (* h1 h1 h1) (* h2 h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) 
(* 33 (* h1 h1 h1) (* h2 h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 63 (* h1 h1 
h1) (* h2 h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2)) (* 66 (* h1 h1 h1) (* h2 h2 h2 h2
) (* h5 h5) h6 (* j2 j2)) (* 36 (* h1 h1 h1) (* h2 h2 h2 h2) (* h5 h5) h6 j2) 
(* 8 (* h1 h1 h1) (* h2 h2 h2 h2) (* h5 h5) h6) (* (* h1 h1 h1) (* h2 h2 h2 h2) 
h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 9 (* h1 h1 h1) (* h2 h2 h2 h2) h5 (* h6 
h6) (* j2 j2 j2 j2 j2)) (* 33 (* h1 h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6) (* j2 j2
 j2 j2)) (* 63 (* h1 h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6) (* j2 j2 j2)) (* 66 (* 
h1 h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6) (* j2 j2)) (* 36 (* h1 h1 h1) (* h2 h2 h2
 h2) h5 (* h6 h6) j2) (* 8 (* h1 h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6)) (* 40 (* 
h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2 j2 j2)) (* 700 (* h1 h1 h1
) (* h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2 j2)) (* 4112 (* h1 h1 h1) (* h2 h2
 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2)) (* 11136 (* h1 h1 h1) (* h2 h2 h2) (* h3 
h3 h3) h5 (* j2 j2 j2)) (* 14752 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 (* j2
 j2)) (* 9088 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 j2) (* 2048 (* h1 h1 h1)
 (* h2 h2 h2) (* h3 h3 h3) h5) (* 8 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 164 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h6 (* j2
 j2 j2 j2 j2 j2)) (* 1252 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2 
j2 j2)) (* 4856 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2 j2)) (* 
10512 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2)) (* 12768 (* h1 h1 
h1) (* h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2)) (* 8064 (* h1 h1 h1) (* h2 h2 h2) 
(* h3 h3 h3) h6 j2) (* 2048 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h6) (* (* h1 
h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 66 (* h1 h1 h1)
 (* h2 h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 855 (* h1 h1 h1) (* h2 
h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 4258 (* h1 h1 h1) (* h2 h2 h2) (* 
h3 h3) h4 h5 (* j2 j2 j2 j2)) (* 9796 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 
(* j2 j2 j2)) (* 11192 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 (* j2 j2)) (* 
6144 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 j2) (* 1280 (* h1 h1 h1) (* h2 h2
 h2) (* h3 h3) h4 h5) (* 8 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2
 j2 j2 j2 j2)) (* 144 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2 
j2 j2)) (* 984 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 
3392 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 6480 (* h1 h1
 h1) (* h2 h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2)) (* 6944 (* h1 h1 h1) (* h2 h2 h2
) (* h3 h3) h4 h6 (* j2 j2)) (* 3904 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h6 
j2) (* 896 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h6) (* 70 (* h1 h1 h1) (* h2 
h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 810 (* h1 h1 h1) (* h2 h2 
h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 3556 (* h1 h1 h1) (* h2 h2 h2) 
(* h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 7696 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3)
 (* h5 h5) (* j2 j2 j2)) (* 8688 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) 
(* j2 j2)) (* 4832 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) j2) (* 1024 (* 
h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5)) (* 19 (* h1 h1 h1) (* h2 h2 h2) (* 
h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 306 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3
) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 2093 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 h6
 (* j2 j2 j2 j2 j2)) (* 7626 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 h6 (* j2 j2 
j2 j2)) (* 15204 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2)) (* 
16488 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 h6 (* j2 j2)) (* 9152 (* h1 h1 h1) 
(* h2 h2 h2) (* h3 h3) h5 h6 j2) (* 2048 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 
h6) (* 12 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 188 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 1196 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
3972 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 7448 (* 
h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2)) (* 7920 (* h1 h1 h1) 
(* h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2)) (* 4448 (* h1 h1 h1) (* h2 h2 h2) 
(* h3 h3) (* h6 h6) j2) (* 1024 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6)) 
(* (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 49 (* 
h1 h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 457 (* h1 h1 h1
) (* h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 1735 (* h1 h1 h1) (* h2 h2
 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2)) (* 3290 (* h1 h1 h1) (* h2 h2 h2) h3 h4 
(* h5 h5) (* j2 j2 j2)) (* 3284 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) (* j2 
j2)) (* 1640 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) j2) (* 320 (* h1 h1 h1) 
(* h2 h2 h2) h3 h4 (* h5 h5)) (* 11 (* h1 h1 h1) (* h2 h2 h2) h3 h4 h5 h6 (* j2 
j2 j2 j2 j2 j2 j2)) (* 159 (* h1 h1 h1) (* h2 h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2 
j2 j2)) (* 895 (* h1 h1 h1) (* h2 h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 2617
 (* h1 h1 h1) (* h2 h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2)) (* 4354 (* h1 h1 h1) (* 
h2 h2 h2) h3 h4 h5 h6 (* j2 j2 j2)) (* 4156 (* h1 h1 h1) (* h2 h2 h2) h3 h4 h5 
h6 (* j2 j2)) (* 2120 (* h1 h1 h1) (* h2 h2 h2) h3 h4 h5 h6 j2) (* 448 (* h1 h1 
h1) (* h2 h2 h2) h3 h4 h5 h6) (* 4 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 52 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 276 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2 j2 j2
)) (* 780 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2 j2)) (* 1272 (* 
h1 h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2)) (* 1200 (* h1 h1 h1) (* h2 
h2 h2) h3 h4 (* h6 h6) (* j2 j2)) (* 608 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h6 
h6) j2) (* 128 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6)) (* 20 (* h1 h1 h1) (* 
h2 h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 200 (* h1 h1 h1) (* h2 h2 h2
) h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 756 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 
h5 h5) (* j2 j2 j2 j2)) (* 1408 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) (* j2 
j2 j2)) (* 1376 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) (* j2 j2)) (* 672 (* 
h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) j2) (* 128 (* h1 h1 h1) (* h2 h2 h2) h3 
(* h5 h5 h5)) (* 12 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 174 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 998 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 2978 (* 
h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 5030 (* h1 h1 h1) (* 
h2 h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2)) (* 4832 (* h1 h1 h1) (* h2 h2 h2) h3 (* 
h5 h5) h6 (* j2 j2)) (* 2456 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) h6 j2) (* 
512 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) h6) (* 15 (* h1 h1 h1) (* h2 h2 h2) 
h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 199 (* h1 h1 h1) (* h2 h2 h2) h3 h5
 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1071 (* h1 h1 h1) (* h2 h2 h2) h3 h5 (* h6 
h6) (* j2 j2 j2 j2 j2)) (* 3057 (* h1 h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6) (* j2 
j2 j2 j2)) (* 5022 (* h1 h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2)) (* 
4764 (* h1 h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6) (* j2 j2)) (* 2424 (* h1 h1 h1) 
(* h2 h2 h2) h3 h5 (* h6 h6) j2) (* 512 (* h1 h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6
)) (* 4 (* h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
52 (* h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 276 (* h1
 h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 780 (* h1 h1 h1) (* 
h2 h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1272 (* h1 h1 h1) (* h2 h2 h2) h3 
(* h6 h6 h6) (* j2 j2 j2)) (* 1200 (* h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6) (* 
j2 j2)) (* 608 (* h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6) j2) (* 128 (* h1 h1 h1)
 (* h2 h2 h2) h3 (* h6 h6 h6)) (* 3 (* h1 h1 h1) (* h2 h2 h2) h4 (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 38 (* h1 h1 h1) (* h2 h2 h2) h4 (* h5 h5) h6 (* j2 
j2 j2 j2 j2 j2)) (* 190 (* h1 h1 h1) (* h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2
 j2)) (* 496 (* h1 h1 h1) (* h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 739 
(* h1 h1 h1) (* h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 634 (* h1 h1 h1) (* 
h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2)) (* 292 (* h1 h1 h1) (* h2 h2 h2) h4 (* h5 
h5) h6 j2) (* 56 (* h1 h1 h1) (* h2 h2 h2) h4 (* h5 h5) h6) (* 2 (* h1 h1 h1) 
(* h2 h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 24 (* h1 h1 h1) (* h2 
h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 116 (* h1 h1 h1) (* h2 h2 h2) 
h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 296 (* h1 h1 h1) (* h2 h2 h2) h4 h5 (* h6
 h6) (* j2 j2 j2 j2)) (* 434 (* h1 h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6) (* j2 j2 
j2)) (* 368 (* h1 h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6) (* j2 j2)) (* 168 (* h1 h1
 h1) (* h2 h2 h2) h4 h5 (* h6 h6) j2) (* 32 (* h1 h1 h1) (* h2 h2 h2) h4 h5 (* 
h6 h6)) (* 2 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2))
 (* 24 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 116 
(* h1 h1 h1) (* h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 296 (* h1 h1 h1
) (* h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 434 (* h1 h1 h1) (* h2 h2 h2)
 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 368 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5 h5) h6 
(* j2 j2)) (* 168 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5 h5) h6 j2) (* 32 (* h1 h1 
h1) (* h2 h2 h2) (* h5 h5 h5) h6) (* 4 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5) (* h6
 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 48 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 232 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* 592 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 
j2 j2 j2)) (* 868 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2)) 
(* 736 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 j2)) (* 336 (* h1 h1 
h1) (* h2 h2 h2) (* h5 h5) (* h6 h6) j2) (* 64 (* h1 h1 h1) (* h2 h2 h2) (* h5 
h5) (* h6 h6)) (* 2 (* h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 24 (* h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 116 (* h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 296 (* 
h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 434 (* h1 h1 h1) (* 
h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 368 (* h1 h1 h1) (* h2 h2 h2) h5 (* 
h6 h6 h6) (* j2 j2)) (* 168 (* h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6) j2) (* 32 
(* h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6)) (* 20 (* h1 h1 h1) (* h2 h2) (* h3 h3
 h3 h3) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 520 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 
h3) h5 (* j2 j2 j2 j2 j2 j2)) (* 4736 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 
(* j2 j2 j2 j2 j2)) (* 18784 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2 
j2 j2)) (* 37568 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2 j2)) (* 
39424 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2)) (* 20480 (* h1 h1 h1)
 (* h2 h2) (* h3 h3 h3 h3) h5 j2) (* 4096 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3)
 h5) (* 4 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2 j2 j2 j2 j2 j2 j2))
 (* 116 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
1264 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2 j2 j2 j2 j2)) (* 6720 
(* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2 j2 j2 j2)) (* 19840 (* h1 h1 
h1) (* h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2 j2 j2)) (* 34240 (* h1 h1 h1) (* h2 h2
) (* h3 h3 h3 h3) h6 (* j2 j2 j2)) (* 34304 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 
h3) h6 (* j2 j2)) (* 18432 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h6 j2) (* 4096
 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h6) (* (* h1 h1 h1) (* h2 h2) (* h3 h3 
h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 92 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3)
 h4 h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 1849 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 
h5 (* j2 j2 j2 j2 j2 j2)) (* 14026 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 (* 
j2 j2 j2 j2 j2)) (* 50644 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 
j2)) (* 96552 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2)) (* 98880 
(* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2)) (* 50944 (* h1 h1 h1) (* h2
 h2) (* h3 h3 h3) h4 h5 j2) (* 10240 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5) 
(* 10 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
272 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2618 
(* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2)) (* 12572 (* h1 
h1 h1) (* h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 34328 (* h1 h1 h1) 
(* h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 55856 (* h1 h1 h1) (* h2 h2) 
(* h3 h3 h3) h4 h6 (* j2 j2 j2)) (* 53632 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4
 h6 (* j2 j2)) (* 28032 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h6 j2) (* 6144 
(* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h6) (* 70 (* h1 h1 h1) (* h2 h2) (* h3 h3
 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1390 (* h1 h1 h1) (* h2 h2) (* h3 h3
 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 9996 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3
) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 35960 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* 
h5 h5) (* j2 j2 j2 j2)) (* 69792 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) 
(* j2 j2 j2)) (* 72384 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2)) 
(* 36864 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) j2) (* 7168 (* h1 h1 h1) 
(* h2 h2) (* h3 h3 h3) (* h5 h5)) (* 17 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 440 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 h6
 (* j2 j2 j2 j2 j2 j2 j2)) (* 4597 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 h6 (* 
j2 j2 j2 j2 j2 j2)) (* 25214 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 
j2 j2 j2)) (* 77440 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2)) 
(* 136208 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2)) (* 134848 (* 
h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2)) (* 69376 (* h1 h1 h1) (* h2 h2
) (* h3 h3 h3) h5 h6 j2) (* 14336 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 h6) (* 
14 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 352 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 3246 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
15204 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 40888
 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 65904 (* h1 
h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2)) (* 62912 (* h1 h1 h1) (* 
h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2)) (* 32768 (* h1 h1 h1) (* h2 h2) (* h3 
h3 h3) (* h6 h6) j2) (* 7168 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6)) (* 
14 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 
422 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 3630
 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 13458 (* 
h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 25004 (* h1 h1 h1
) (* h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 24432 (* h1 h1 h1) (* h2 h2)
 (* h3 h3) (* h4 h4) h5 (* j2 j2)) (* 11968 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* 
h4 h4) h5 j2) (* 2304 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5) (* 28 (* h1
 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 380 (* h1 
h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 2044 (* h1 h1 
h1) (* h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 5764 (* h1 h1 h1) 
(* h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2)) (* 9304 (* h1 h1 h1) (* h2 h2)
 (* h3 h3) (* h4 h4) h6 (* j2 j2 j2)) (* 8656 (* h1 h1 h1) (* h2 h2) (* h3 h3) 
(* h4 h4) h6 (* j2 j2)) (* 4320 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h6 j2
) (* 896 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h6) (* 2 (* h1 h1 h1) (* h2 
h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 148 (* h1 h1 h1) (* 
h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 2180 (* h1 h1 h1) (* 
h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 12988 (* h1 h1 h1) (* h2
 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 38938 (* h1 h1 h1) (* h2 h2) 
(* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 63992 (* h1 h1 h1) (* h2 h2) (* h3 h3
) h4 (* h5 h5) (* j2 j2 j2)) (* 58216 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 
h5) (* j2 j2)) (* 27328 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) j2) (* 
5120 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5)) (* 23 (* h1 h1 h1) (* h2 h2)
 (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 547 (* h1 h1 h1) (* h2 h2) 
(* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 5039 (* h1 h1 h1) (* h2 h2) (* 
h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 24101 (* h1 h1 h1) (* h2 h2) (* h3 h3)
 h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 65358 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6
 (* j2 j2 j2 j2)) (* 102756 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 
j2)) (* 92344 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2)) (* 43936 (* 
h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6 j2) (* 8576 (* h1 h1 h1) (* h2 h2) (* h3 
h3) h4 h5 h6) (* 12 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2
 j2 j2 j2 j2)) (* 256 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 2096 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 8888 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 21812 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 
32168 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2)) (* 28112 (* h1
 h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2)) (* 13408 (* h1 h1 h1) (* h2 
h2) (* h3 h3) h4 (* h6 h6) j2) (* 2688 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h6
 h6)) (* 60 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 
j2)) (* 840 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2))
 (* 4888 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 
14916 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 24840 
(* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2)) (* 22352 (* h1 h1 h1
) (* h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2)) (* 10112 (* h1 h1 h1) (* h2 h2) 
(* h3 h3) (* h5 h5 h5) j2) (* 1792 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5)
) (* 21 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 471 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)
) (* 4273 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 20049 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
53202 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 82432 
(* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 73424 (* h1 h1 h1
) (* h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2)) (* 34624 (* h1 h1 h1) (* h2 h2) 
(* h3 h3) (* h5 h5) h6 j2) (* 6656 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) h6
) (* 35 (* h1 h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 689 (* h1 h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 5445 (* h1 h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 22879 (* h1 h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
56228 (* h1 h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 82844 
(* h1 h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 71840 (* h1 h1 h1
) (* h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2)) (* 33792 (* h1 h1 h1) (* h2 h2) 
(* h3 h3) h5 (* h6 h6) j2) (* 6656 (* h1 h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6)
) (* 12 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 228 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 1716 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 6844 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
16048 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 22864 
(* h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2)) (* 19456 (* h1 h1 h1
) (* h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2)) (* 9088 (* h1 h1 h1) (* h2 h2) (* 
h3 h3) (* h6 h6 h6) j2) (* 1792 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6)) 
(* 10 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 244 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 
1688 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 5196 
(* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 8326 (* h1 h1 
h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 7232 (* h1 h1 h1) (* h2 h2
) h3 (* h4 h4) (* h5 h5) (* j2 j2)) (* 3224 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) 
(* h5 h5) j2) (* 576 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5)) (* 36 (* h1 
h1 h1) (* h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 396 (* h1 h1 h1
) (* h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 1760 (* h1 h1 h1) (* h2
 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 4248 (* h1 h1 h1) (* h2 h2) h3 
(* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 6052 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) h5 
h6 (* j2 j2 j2)) (* 5084 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2)) 
(* 2328 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) h5 h6 j2) (* 448 (* h1 h1 h1) (* h2 
h2) h3 (* h4 h4) h5 h6) (* 4 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h6 h6) (* j2
 j2 j2 j2 j2 j2 j2)) (* 40 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 168 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 j2 
j2 j2 j2)) (* 384 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 j2 j2 j2))
 (* 516 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 408 (* h1
 h1 h1) (* h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 j2)) (* 176 (* h1 h1 h1) (* h2 h2
) h3 (* h4 h4) (* h6 h6) j2) (* 32 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h6 h6)
) (* (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
54 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 614 
(* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 3024 (* h1 
h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 7737 (* h1 h1 h1) (* 
h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 11058 (* h1 h1 h1) (* h2 h2) h3 h4
 (* h5 h5 h5) (* j2 j2 j2)) (* 8888 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) 
(* j2 j2)) (* 3744 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) j2) (* 640 (* h1 h1
 h1) (* h2 h2) h3 h4 (* h5 h5 h5)) (* 16 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 312 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6
 (* j2 j2 j2 j2 j2 j2 j2)) (* 2462 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2)) (* 10170 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 
j2 j2 j2)) (* 24050 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2)) 
(* 33550 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2)) (* 27224 (* h1 
h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2)) (* 11864 (* h1 h1 h1) (* h2 h2) 
h3 h4 (* h5 h5) h6 j2) (* 2144 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6) (* 15 
(* h1 h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 278 
(* h1 h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1966 (* 
h1 h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 7216 (* h1 h1 
h1) (* h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 15583 (* h1 h1 h1) (* h2
 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 20602 (* h1 h1 h1) (* h2 h2) h3 h4 
h5 (* h6 h6) (* j2 j2 j2)) (* 16396 (* h1 h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6) 
(* j2 j2)) (* 7208 (* h1 h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6) j2) (* 1344 (* h1 
h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6)) (* 2 (* h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 32 (* h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2)) (* 204 (* h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 696 (* h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2 j2
 j2 j2)) (* 1410 (* h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 
1752 (* h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2 j2)) (* 1312 (* h1 h1 h1
) (* h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2)) (* 544 (* h1 h1 h1) (* h2 h2) h3 h4 
(* h6 h6 h6) j2) (* 96 (* h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6 h6)) (* 10 (* h1 h1
 h1) (* h2 h2) h3 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 110 (* h1 h1 h1) 
(* h2 h2) h3 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 478 (* h1 h1 h1) (* h2 h2
) h3 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 1082 (* h1 h1 h1) (* h2 h2) h3 (* h5
 h5 h5 h5) (* j2 j2 j2 j2)) (* 1392 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) 
(* j2 j2 j2)) (* 1024 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) (* j2 j2)) (* 
400 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) j2) (* 64 (* h1 h1 h1) (* h2 h2) 
h3 (* h5 h5 h5 h5)) (* 9 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 164 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2
 j2 j2 j2)) (* 1226 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2)) (* 4868 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
11169 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 15184 (* h1 
h1 h1) (* h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 12020 (* h1 h1 h1) (* h2 h2
) h3 (* h5 h5 h5) h6 (* j2 j2)) (* 5104 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) 
h6 j2) (* 896 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) h6) (* 23 (* h1 h1 h1) (* 
h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 384 (* h1 h1 h1) 
(* h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2606 (* h1 h1 h1) 
(* h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 9492 (* h1 h1 h1) (* 
h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 20495 (* h1 h1 h1) (* h2 h2
) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 26980 (* h1 h1 h1) (* h2 h2) h3 (* 
h5 h5) (* h6 h6) (* j2 j2 j2)) (* 21220 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5) (* 
h6 h6) (* j2 j2)) (* 9152 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6) j2) (* 
1664 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6)) (* 15 (* h1 h1 h1) (* h2 h2)
 h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 242 (* h1 h1 h1) (* h2 h2) 
h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1570 (* h1 h1 h1) (* h2 h2) h3 
h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 5456 (* h1 h1 h1) (* h2 h2) h3 h5 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 11335 (* h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6)
 (* j2 j2 j2 j2)) (* 14550 (* h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2
)) (* 11312 (* h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2)) (* 4880 (* h1 
h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6) j2) (* 896 (* h1 h1 h1) (* h2 h2) h3 h5 (* 
h6 h6 h6)) (* 2 (* h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 28 (* h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 164 (* h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 528
 (* h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1026 (* h1 h1 
h1) (* h2 h2) h3 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 1236 (* h1 h1 h1) (* h2 h2)
 h3 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 904 (* h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6 
h6) (* j2 j2)) (* 368 (* h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6 h6) j2) (* 64 (* h1 
h1 h1) (* h2 h2) h3 (* h6 h6 h6 h6)) (* 8 (* h1 h1 h1) (* h2 h2) (* h4 h4) (* h5
 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 84 (* h1 h1 h1) (* h2 h2) (* h4 h4) (* h5 
h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 356 (* h1 h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) 
h6 (* j2 j2 j2 j2 j2)) (* 800 (* h1 h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) h6 (* 
j2 j2 j2 j2)) (* 1040 (* h1 h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)
) (* 788 (* h1 h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 324 (* h1 
h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) h6 j2) (* 56 (* h1 h1 h1) (* h2 h2) (* h4 
h4) (* h5 h5) h6) (* 2 (* h1 h1 h1) (* h2 h2) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2
 j2 j2 j2 j2)) (* 18 (* h1 h1 h1) (* h2 h2) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 68 (* h1 h1 h1) (* h2 h2) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2
)) (* 140 (* h1 h1 h1) (* h2 h2) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 170 
(* h1 h1 h1) (* h2 h2) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 122 (* h1 h1 h1) 
(* h2 h2) (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 48 (* h1 h1 h1) (* h2 h2) (* h4 
h4) h5 (* h6 h6) j2) (* 8 (* h1 h1 h1) (* h2 h2) (* h4 h4) h5 (* h6 h6)) (* 3 
(* h1 h1 h1) (* h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 45 (* 
h1 h1 h1) (* h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 276 (* h1 h1
 h1) (* h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 906 (* h1 h1 h1) (* 
h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 1755 (* h1 h1 h1) (* h2 h2) h4 
(* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 2073 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5 h5) 
h6 (* j2 j2 j2)) (* 1470 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2)) 
(* 576 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5 h5) h6 j2) (* 96 (* h1 h1 h1) (* h2 h2
) h4 (* h5 h5 h5) h6) (* 4 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 66 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6) (* j2
 j2 j2 j2 j2 j2 j2)) (* 430 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 1468 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2)) (* 2920 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)
) (* 3514 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 2526 
(* h1 h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 1000 (* h1 h1 h1) 
(* h2 h2) h4 (* h5 h5) (* h6 h6) j2) (* 168 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5) 
(* h6 h6)) (* (* h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 15 (* h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 88 (* h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 274 
(* h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 505 (* h1 h1 h1
) (* h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 571 (* h1 h1 h1) (* h2 h2) h4
 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 390 (* h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6 h6) 
(* j2 j2)) (* 148 (* h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6 h6) j2) (* 24 (* h1 h1 
h1) (* h2 h2) h4 h5 (* h6 h6 h6)) (* (* h1 h1 h1) (* h2 h2) (* h5 h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 13 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2)) (* 70 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2)) (* 206 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2
)) (* 365 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 401 (* 
h1 h1 h1) (* h2 h2) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 268 (* h1 h1 h1) (* h2 
h2) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 100 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5 h5) 
h6 j2) (* 16 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5 h5) h6) (* 4 (* h1 h1 h1) (* h2 
h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 58 (* h1 h1 h1) (* h2
 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 346 (* h1 h1 h1) (* h2 
h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1112 (* h1 h1 h1) (* h2 h2)
 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2120 (* h1 h1 h1) (* h2 h2) (* h5
 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 2474 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2)) (* 1738 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6) 
(* j2 j2)) (* 676 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6) j2) (* 112 (* h1
 h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6)) (* 4 (* h1 h1 h1) (* h2 h2) (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 58 (* h1 h1 h1) (* h2 h2) (* h5 h5)
 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 346 (* h1 h1 h1) (* h2 h2) (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1112 (* h1 h1 h1) (* h2 h2) (* h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2120 (* h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2)) (* 2474 (* h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6) (* j2
 j2 j2)) (* 1738 (* h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 676
 (* h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6) j2) (* 112 (* h1 h1 h1) (* h2 h2)
 (* h5 h5) (* h6 h6 h6)) (* (* h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 13 (* h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 70 (* h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 206 (* h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 365
 (* h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 401 (* h1 h1 h1) 
(* h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 268 (* h1 h1 h1) (* h2 h2) h5 (* 
h6 h6 h6 h6) (* j2 j2)) (* 100 (* h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6 h6) j2) (* 
16 (* h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6 h6)) (* 4 (* h1 h1 h1) h2 (* h3 h3 h3 
h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 208 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4
 h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 3084 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h5 (* 
j2 j2 j2 j2 j2 j2)) (* 18768 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 
j2 j2)) (* 57552 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2)) (* 96704
 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2)) (* 89856 (* h1 h1 h1) h2 
(* h3 h3 h3 h3) h4 h5 (* j2 j2)) (* 43008 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h5 
j2) (* 8192 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h5) (* 16 (* h1 h1 h1) h2 (* h3 
h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 352 (* h1 h1 h1) h2 (* h3 h3 h3 
h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2832 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 
h6 (* j2 j2 j2 j2 j2 j2)) (* 11840 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h6 (* j2 
j2 j2 j2 j2)) (* 29056 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2)) 
(* 43520 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2)) (* 39168 (* h1 h1 
h1) h2 (* h3 h3 h3 h3) h4 h6 (* j2 j2)) (* 19456 (* h1 h1 h1) h2 (* h3 h3 h3 h3)
 h4 h6 j2) (* 4096 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h6) (* 200 (* h1 h1 h1) h2
 (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 3840 (* h1 h1 h1) h2 (* 
h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 24320 (* h1 h1 h1) h2 (* h3 h3 
h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 73792 (* h1 h1 h1) h2 (* h3 h3 h3 h3) 
(* h5 h5) (* j2 j2 j2 j2)) (* 120064 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) 
(* j2 j2 j2)) (* 105984 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) (* j2 j2)) (* 
47104 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) j2) (* 8192 (* h1 h1 h1) h2 (* 
h3 h3 h3 h3) (* h5 h5)) (* 80 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 1792 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2
 j2 j2)) (* 14784 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2)) 
(* 63088 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 155232 (* 
h1 h1 h1) h2 (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 227072 (* h1 h1 h1) h2 
(* h3 h3 h3 h3) h5 h6 (* j2 j2 j2)) (* 193536 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h5
 h6 (* j2 j2)) (* 88064 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h5 h6 j2) (* 16384 (* h1
 h1 h1) h2 (* h3 h3 h3 h3) h5 h6) (* 8 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 208 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2120 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2)) (* 11584 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 38208 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6) (* j2 
j2 j2 j2 j2)) (* 79872 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2)
) (* 106624 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2)) (* 88064 (* 
h1 h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6) (* j2 j2)) (* 40960 (* h1 h1 h1) h2 (* h3
 h3 h3 h3) (* h6 h6) j2) (* 8192 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6)) (* 
14 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 530
 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 6102 (* 
h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 31870 (* h1 h1 
h1) h2 (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 88028 (* h1 h1 h1) h2 
(* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 136976 (* h1 h1 h1) h2 (* h3 h3 h3
) (* h4 h4) h5 (* j2 j2 j2)) (* 120160 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5
 (* j2 j2)) (* 55168 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 j2) (* 10240 (* 
h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5) (* 24 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4
 h4) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 408 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 
h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2776 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) 
h6 (* j2 j2 j2 j2 j2 j2)) (* 10152 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h6 (* 
j2 j2 j2 j2 j2)) (* 22128 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 
j2)) (* 29664 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2)) (* 24000 
(* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h6 (* j2 j2)) (* 10752 (* h1 h1 h1) h2 
(* h3 h3 h3) (* h4 h4) h6 j2) (* 2048 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h6)
 (* 34 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 1314 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
14594 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 72914 
(* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 193920 (* h1 h1
 h1) h2 (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 290864 (* h1 h1 h1) h2 (* 
h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 244096 (* h1 h1 h1) h2 (* h3 h3 h3) h4 
(* h5 h5) (* j2 j2)) (* 105984 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) j2) (* 
18432 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5)) (* 4 (* h1 h1 h1) h2 (* h3 h3 
h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 290 (* h1 h1 h1) h2 (* h3 h3 h3)
 h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4798 (* h1 h1 h1) h2 (* h3 h3 h3) h4 
h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 35514 (* h1 h1 h1) h2 (* h3 h3 h3) h4 h5 h6 
(* j2 j2 j2 j2 j2 j2)) (* 143694 (* h1 h1 h1) h2 (* h3 h3 h3) h4 h5 h6 (* j2 j2 
j2 j2 j2)) (* 341140 (* h1 h1 h1) h2 (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 
484384 (* h1 h1 h1) h2 (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 402112 (* h1 h1 h1
) h2 (* h3 h3 h3) h4 h5 h6 (* j2 j2)) (* 178944 (* h1 h1 h1) h2 (* h3 h3 h3) h4 
h5 h6 j2) (* 32768 (* h1 h1 h1) h2 (* h3 h3 h3) h4 h5 h6) (* 12 (* h1 h1 h1) h2 
(* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 276 (* h1 h1 h1) h2
 (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2612 (* h1 h1 h1) h2 
(* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 13404 (* h1 h1 h1) h2 (* 
h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 41520 (* h1 h1 h1) h2 (* h3 h3 
h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 81216 (* h1 h1 h1) h2 (* h3 h3 h3) h4 
(* h6 h6) (* j2 j2 j2 j2)) (* 100992 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6) 
(* j2 j2 j2)) (* 77376 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6) (* j2 j2)) (* 
33280 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6) j2) (* 6144 (* h1 h1 h1) h2 (* 
h3 h3 h3) h4 (* h6 h6)) (* 400 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) (* j2 
j2 j2 j2 j2 j2 j2)) (* 4880 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 
j2 j2 j2 j2)) (* 23680 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 
j2)) (* 59264 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 
82560 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2)) (* 64000 (* h1 h1 
h1) h2 (* h3 h3 h3) (* h5 h5 h5) (* j2 j2)) (* 25600 (* h1 h1 h1) h2 (* h3 h3 h3
) (* h5 h5 h5) j2) (* 4096 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5)) (* 220 (* 
h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3756 (* 
h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 27696 (* h1 
h1 h1) h2 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 112784 (* h1 h1 h1
) h2 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 271536 (* h1 h1 h1) h2 (* 
h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 389376 (* h1 h1 h1) h2 (* h3 h3 h3) 
(* h5 h5) h6 (* j2 j2 j2)) (* 321664 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) h6 
(* j2 j2)) (* 139776 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) h6 j2) (* 24576 (* 
h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) h6) (* 28 (* h1 h1 h1) h2 (* h3 h3 h3) h5 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 664 (* h1 h1 h1) h2 (* h3 h3 h3) h5
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6840 (* h1 h1 h1) h2 (* h3 h3 h3) h5 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 38936 (* h1 h1 h1) h2 (* h3 h3 h3) h5 (* 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 134108 (* h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6
) (* j2 j2 j2 j2 j2)) (* 288000 (* h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6) (* j2 
j2 j2 j2)) (* 384512 (* h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 
307968 (* h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2)) (* 134656 (* h1 h1 
h1) h2 (* h3 h3 h3) h5 (* h6 h6) j2) (* 24576 (* h1 h1 h1) h2 (* h3 h3 h3) h5 
(* h6 h6)) (* 12 (* h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 252 (* h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 2204 (* h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 10628 (* h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 31368 (* h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 59088 
(* h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 71328 (* h1 h1 h1)
 h2 (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2)) (* 53376 (* h1 h1 h1) h2 (* h3 h3 h3
) (* h6 h6 h6) (* j2 j2)) (* 22528 (* h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6) j2)
 (* 4096 (* h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6)) (* 36 (* h1 h1 h1) h2 (* h3 
h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 672 (* h1 h1 h1) h2 (* h3 h3) 
(* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 4176 (* h1 h1 h1) h2 (* h3 h3) (* h4 
h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 12184 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5
 (* j2 j2 j2 j2)) (* 18956 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2
)) (* 16200 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 (* j2 j2)) (* 7168 (* h1 
h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 j2) (* 1280 (* h1 h1 h1) h2 (* h3 h3) (* h4 
h4 h4) h5) (* 16 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 
j2)) (* 160 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 
672 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 1536 (* h1 
h1 h1) h2 (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2)) (* 2064 (* h1 h1 h1) h2 (* 
h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2)) (* 1632 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 
h4) h6 (* j2 j2)) (* 704 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h6 j2) (* 128 
(* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h6) (* 20 (* h1 h1 h1) h2 (* h3 h3) (* h4
 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 596 (* h1 h1 h1) h2 (* h3 h3) (* 
h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 5896 (* h1 h1 h1) h2 (* h3 h3) (* 
h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 26848 (* h1 h1 h1) h2 (* h3 h3) (* h4
 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 65388 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) 
(* h5 h5) (* j2 j2 j2 j2)) (* 90636 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5
) (* j2 j2 j2)) (* 71576 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)
) (* 29920 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) j2) (* 5120 (* h1 h1 h1
) h2 (* h3 h3) (* h4 h4) (* h5 h5)) (* 56 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5
 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1136 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 8940 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 h6 
(* j2 j2 j2 j2 j2 j2)) (* 36716 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 h6 (* j2 
j2 j2 j2 j2)) (* 85844 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)
) (* 117684 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 93336 (* 
h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 39552 (* h1 h1 h1) h2 (* h3
 h3) (* h4 h4) h5 h6 j2) (* 6912 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 h6) (* 
16 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 240 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 1472 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
4896 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 9744 
(* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 11952 (* h1 h1
 h1) h2 (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 8864 (* h1 h1 h1) h2 (* 
h3 h3) (* h4 h4) (* h6 h6) (* j2 j2)) (* 3648 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4
) (* h6 h6) j2) (* 640 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h6 h6)) (* 32 (* 
h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 912 (* h1
 h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 7972 (* h1 h1 
h1) h2 (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 33036 (* h1 h1 h1) h2
 (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 75228 (* h1 h1 h1) h2 (* h3 h3
) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 98452 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 
h5 h5) (* j2 j2 j2)) (* 73360 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) (* j2 j2
)) (* 28800 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) j2) (* 4608 (* h1 h1 h1) 
h2 (* h3 h3) h4 (* h5 h5 h5)) (* 6 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 358 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4950 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 31902 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2)) (* 114232 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2
 j2 j2 j2)) (* 242068 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2))
 (* 308804 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 231936 (* 
h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 94144 (* h1 h1 h1) h2 (* h3
 h3) h4 (* h5 h5) h6 j2) (* 15872 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) h6) (* 
24 (* h1 h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
532 (* h1 h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
5148 (* h1 h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
27596 (* h1 h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 89516 
(* h1 h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 180384 (* h1 h1
 h1) h2 (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 225072 (* h1 h1 h1) h2 (* 
h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 168208 (* h1 h1 h1) h2 (* h3 h3) h4 h5 
(* h6 h6) (* j2 j2)) (* 68736 (* h1 h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6) j2) (* 
11776 (* h1 h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6)) (* 4 (* h1 h1 h1) h2 (* h3 h3) 
h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 88 (* h1 h1 h1) h2 (* h3 h3) 
h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 776 (* h1 h1 h1) h2 (* h3 h3) h4
 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3680 (* h1 h1 h1) h2 (* h3 h3) h4 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 10500 (* h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6 
h6) (* j2 j2 j2 j2 j2)) (* 18888 (* h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6 h6) (* j2
 j2 j2 j2)) (* 21584 (* h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2)) (* 
15200 (* h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6 h6) (* j2 j2)) (* 6016 (* h1 h1 h1) 
h2 (* h3 h3) h4 (* h6 h6 h6) j2) (* 1024 (* h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6 
h6)) (* 100 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 1120 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 4900
 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 10936 (* h1 h1
 h1) h2 (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 13584 (* h1 h1 h1) h2 (* 
h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 9472 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 
h5 h5) (* j2 j2)) (* 3456 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) j2) (* 512 
(* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5)) (* 140 (* h1 h1 h1) h2 (* h3 h3) (* 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2116 (* h1 h1 h1) h2 (* h3 h3) (* 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 13668 (* h1 h1 h1) h2 (* h3 h3) (* h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 48804 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5)
 h6 (* j2 j2 j2 j2 j2)) (* 103408 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) h6 (* 
j2 j2 j2 j2)) (* 131064 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) 
(* 96640 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2)) (* 38016 (* h1 h1 
h1) h2 (* h3 h3) (* h5 h5 h5) h6 j2) (* 6144 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 
h5) h6) (* 28 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2 j2)) (* 628 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 5950 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 30954 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2
 j2 j2 j2)) (* 97102 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2)) (* 189530 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2))
 (* 229936 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 167712
 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 67072 (* h1 h1 h1) 
h2 (* h3 h3) (* h5 h5) (* h6 h6) j2) (* 11264 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5
) (* h6 h6)) (* 24 (* h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 476 (* h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 4048 (* h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 19328 (* h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)
) (* 56976 (* h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
106724 (* h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 126344 (* 
h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 91072 (* h1 h1 h1) h2 
(* h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 36352 (* h1 h1 h1) h2 (* h3 h3) h5 (* h6
 h6 h6) j2) (* 6144 (* h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6)) (* 4 (* h1 h1 h1)
 h2 (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 72 (* h1 h1 h1)
 h2 (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 552 (* h1 h1 h1) 
h2 (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2368 (* h1 h1 h1) h2 
(* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6276 (* h1 h1 h1) h2 (* h3 
h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 10680 (* h1 h1 h1) h2 (* h3 h3) (* h6
 h6 h6 h6) (* j2 j2 j2 j2)) (* 11696 (* h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6 h6) 
(* j2 j2 j2)) (* 7968 (* h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6 h6) (* j2 j2)) (* 
3072 (* h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6 h6) j2) (* 512 (* h1 h1 h1) h2 (* h3 
h3) (* h6 h6 h6 h6)) (* 20 (* h1 h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2
 j2 j2 j2 j2)) (* 332 (* h1 h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 
j2 j2)) (* 1792 (* h1 h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) 
(* 4568 (* h1 h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 6292 (* h1
 h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 4828 (* h1 h1 h1) h2 h3 
(* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 1944 (* h1 h1 h1) h2 h3 (* h4 h4 h4) (* h5 
h5) j2) (* 320 (* h1 h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5)) (* 20 (* h1 h1 h1) h2 
h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 156 (* h1 h1 h1) h2 h3 (* h4 
h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 544 (* h1 h1 h1) h2 h3 (* h4 h4 h4) h5 h6
 (* j2 j2 j2 j2 j2)) (* 1080 (* h1 h1 h1) h2 h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 
j2)) (* 1300 (* h1 h1 h1) h2 h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 940 (* h1 h1
 h1) h2 h3 (* h4 h4 h4) h5 h6 (* j2 j2)) (* 376 (* h1 h1 h1) h2 h3 (* h4 h4 h4) 
h5 h6 j2) (* 64 (* h1 h1 h1) h2 h3 (* h4 h4 h4) h5 h6) (* 8 (* h1 h1 h1) h2 h3 
(* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 192 (* h1 h1 h1) h2 h3 
(* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1536 (* h1 h1 h1) h2 h3 (* 
h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 5888 (* h1 h1 h1) h2 h3 (* h4 h4) 
(* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 12392 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5 
h5) (* j2 j2 j2 j2)) (* 15136 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) (* j2 j2
 j2)) (* 10704 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 4064 (* 
h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) j2) (* 640 (* h1 h1 h1) h2 h3 (* h4 h4) 
(* h5 h5 h5)) (* 32 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 568 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2
 j2)) (* 4032 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 14888 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 31200 
(* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 38472 (* h1 h1 h1)
 h2 h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 27648 (* h1 h1 h1) h2 h3 (* h4 h4
) (* h5 h5) h6 (* j2 j2)) (* 10712 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) h6 j2)
 (* 1728 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) h6) (* 18 (* h1 h1 h1) h2 h3 (* 
h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 242 (* h1 h1 h1) h2 h3 (* h4
 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1284 (* h1 h1 h1) h2 h3 (* h4 h4)
 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3740 (* h1 h1 h1) h2 h3 (* h4 h4) h5 (* 
h6 h6) (* j2 j2 j2 j2 j2)) (* 6650 (* h1 h1 h1) h2 h3 (* h4 h4) h5 (* h6 h6) (* 
j2 j2 j2 j2)) (* 7418 (* h1 h1 h1) h2 h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2)) 
(* 5072 (* h1 h1 h1) h2 h3 (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 1944 (* h1 h1 h1
) h2 h3 (* h4 h4) h5 (* h6 h6) j2) (* 320 (* h1 h1 h1) h2 h3 (* h4 h4) h5 (* h6 
h6)) (* 2 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
54 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 424 (* h1 
h1 h1) h2 h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1532 (* h1 h1 h1) h2 
h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 3026 (* h1 h1 h1) h2 h3 h4 (* h5 h5
 h5 h5) (* j2 j2 j2 j2)) (* 3486 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5 h5) (* j2 j2 
j2)) (* 2340 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5 h5) (* j2 j2)) (* 848 (* h1 h1 h1
) h2 h3 h4 (* h5 h5 h5 h5) j2) (* 128 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5 h5)) (* 
2 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 106 
(* h1 h1 h1) h2 h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1324 (* h1
 h1 h1) h2 h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 7632 (* h1 h1 h1) 
h2 h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 24314 (* h1 h1 h1) h2 h3 h4 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 45866 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5) 
h6 (* j2 j2 j2 j2)) (* 52392 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2))
 (* 35548 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5) h6 (* j2 j2)) (* 13168 (* h1 h1 h1)
 h2 h3 h4 (* h5 h5 h5) h6 j2) (* 2048 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5) h6) (* 
13 (* h1 h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
269 (* h1 h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
2398 (* h1 h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
11814 (* h1 h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 35017 
(* h1 h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 64145 (* h1 h1 
h1) h2 h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 72732 (* h1 h1 h1) h2 h3 h4
 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 49580 (* h1 h1 h1) h2 h3 h4 (* h5 h5) (* 
h6 h6) (* j2 j2)) (* 18592 (* h1 h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6) j2) (* 2944
 (* h1 h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6)) (* 4 (* h1 h1 h1) h2 h3 h4 h5 (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 86 (* h1 h1 h1) h2 h3 h4 h5 (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 702 (* h1 h1 h1) h2 h3 h4 h5 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 3000 (* h1 h1 h1) h2 h3 h4 h5 (* h6 h6 h6) (* j2 j2
 j2 j2 j2 j2)) (* 7712 (* h1 h1 h1) h2 h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2))
 (* 12614 (* h1 h1 h1) h2 h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 13246 (* h1 
h1 h1) h2 h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 8652 (* h1 h1 h1) h2 h3 h4 h5 
(* h6 h6 h6) (* j2 j2)) (* 3200 (* h1 h1 h1) h2 h3 h4 h5 (* h6 h6 h6) j2) (* 512
 (* h1 h1 h1) h2 h3 h4 h5 (* h6 h6 h6)) (* 20 (* h1 h1 h1) h2 h3 (* h5 h5 h5 h5)
 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 264 (* h1 h1 h1) h2 h3 (* h5 h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 1432 (* h1 h1 h1) h2 h3 (* h5 h5 h5 h5) h6 (* j2 j2
 j2 j2 j2 j2)) (* 4192 (* h1 h1 h1) h2 h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2))
 (* 7284 (* h1 h1 h1) h2 h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 7736 (* h1 h1
 h1) h2 h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 4928 (* h1 h1 h1) h2 h3 (* h5 h5 
h5 h5) h6 (* j2 j2)) (* 1728 (* h1 h1 h1) h2 h3 (* h5 h5 h5 h5) h6 j2) (* 256 
(* h1 h1 h1) h2 h3 (* h5 h5 h5 h5) h6) (* 10 (* h1 h1 h1) h2 h3 (* h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 200 (* h1 h1 h1) h2 h3 (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1682 (* h1 h1 h1) h2 h3 (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 7784 (* h1 h1 h1) h2 h3 (* h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 21742 (* h1 h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6)
 (* j2 j2 j2 j2 j2)) (* 37864 (* h1 h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2
 j2 j2)) (* 41206 (* h1 h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 
27176 (* h1 h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 9920 (* h1 h1 h1) 
h2 h3 (* h5 h5 h5) (* h6 h6) j2) (* 1536 (* h1 h1 h1) h2 h3 (* h5 h5 h5) (* h6 
h6)) (* 13 (* h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 237 (* h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 1850 (* h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 8114 (* h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
21921 (* h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 37513 (* 
h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 40552 (* h1 h1 h1) h2
 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 26760 (* h1 h1 h1) h2 h3 (* h5 h5) 
(* h6 h6 h6) (* j2 j2)) (* 9824 (* h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6) j2) 
(* 1536 (* h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6)) (* 4 (* h1 h1 h1) h2 h3 h5 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 68 (* h1 h1 h1) h2 h3 h5 (* 
h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 480 (* h1 h1 h1) h2 h3 h5 (* h6 h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1872 (* h1 h1 h1) h2 h3 h5 (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 4516 (* h1 h1 h1) h2 h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2
 j2 j2)) (* 7044 (* h1 h1 h1) h2 h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 7128 
(* h1 h1 h1) h2 h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 4520 (* h1 h1 h1) h2 h3 
h5 (* h6 h6 h6 h6) (* j2 j2)) (* 1632 (* h1 h1 h1) h2 h3 h5 (* h6 h6 h6 h6) j2) 
(* 256 (* h1 h1 h1) h2 h3 h5 (* h6 h6 h6 h6)) (* 4 (* h1 h1 h1) h2 (* h4 h4 h4) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 32 (* h1 h1 h1) h2 (* h4 h4 h4) (* h5 
h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 108 (* h1 h1 h1) h2 (* h4 h4 h4) (* h5 h5) h6 
(* j2 j2 j2 j2 j2)) (* 200 (* h1 h1 h1) h2 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2
 j2)) (* 220 (* h1 h1 h1) h2 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 144 (* 
h1 h1 h1) h2 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 52 (* h1 h1 h1) h2 (* h4 h4
 h4) (* h5 h5) h6 j2) (* 8 (* h1 h1 h1) h2 (* h4 h4 h4) (* h5 h5) h6) (* 4 (* h1
 h1 h1) h2 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 48 (* h1 h1
 h1) h2 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 236 (* h1 h1 h1) 
h2 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 632 (* h1 h1 h1) h2 (* h4
 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 1020 (* h1 h1 h1) h2 (* h4 h4) (* h5
 h5 h5) h6 (* j2 j2 j2 j2)) (* 1024 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5 h5) h6 
(* j2 j2 j2)) (* 628 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 216
 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5 h5) h6 j2) (* 32 (* h1 h1 h1) h2 (* h4 h4) 
(* h5 h5 h5) h6) (* 4 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 52 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2
 j2 j2 j2 j2)) (* 268 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 740 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 1220 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 
1244 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 772 (* h1 h1
 h1) h2 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 268 (* h1 h1 h1) h2 (* h4 h4
) (* h5 h5) (* h6 h6) j2) (* 40 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 h6)) 
(* 2 (* h1 h1 h1) h2 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 24 
(* h1 h1 h1) h2 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 118 (* h1 h1 
h1) h2 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 316 (* h1 h1 h1) h2 h4 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 510 (* h1 h1 h1) h2 h4 (* h5 h5 h5 h5)
 h6 (* j2 j2 j2 j2)) (* 512 (* h1 h1 h1) h2 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) 
(* 314 (* h1 h1 h1) h2 h4 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 108 (* h1 h1 h1) h2 
h4 (* h5 h5 h5 h5) h6 j2) (* 16 (* h1 h1 h1) h2 h4 (* h5 h5 h5 h5) h6) (* 2 (* 
h1 h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 36 (* 
h1 h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 262 (* h1
 h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1024 (* h1 h1 
h1) h2 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2406 (* h1 h1 h1) h2 
h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 3572 (* h1 h1 h1) h2 h4 (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 3386 (* h1 h1 h1) h2 h4 (* h5 h5 h5) (* h6 
h6) (* j2 j2 j2)) (* 1992 (* h1 h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) 
(* 664 (* h1 h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6) j2) (* 96 (* h1 h1 h1) h2 h4 
(* h5 h5 h5) (* h6 h6)) (* (* h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2
 j2 j2 j2 j2 j2 j2)) (* 20 (* h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 155 (* h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 630 (* h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2
 j2)) (* 1519 (* h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
2296 (* h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 2205 (* h1 h1
 h1) h2 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 1310 (* h1 h1 h1) h2 h4 (* h5
 h5) (* h6 h6 h6) (* j2 j2)) (* 440 (* h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6 h6) j2
) (* 64 (* h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6 h6)) (* (* h1 h1 h1) h2 (* h5 h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1 h1) h2 (* h5 h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 107 (* h1 h1 h1) h2 (* h5 h5 h5
 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 394 (* h1 h1 h1) h2 (* h5 h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 887 (* h1 h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6
) (* j2 j2 j2 j2 j2)) (* 1276 (* h1 h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2
 j2 j2)) (* 1181 (* h1 h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 682 
(* h1 h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 224 (* h1 h1 h1) h2 (* 
h5 h5 h5 h5) (* h6 h6) j2) (* 32 (* h1 h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6)) (* 2
 (* h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 32
 (* h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 214 
(* h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 788 (* h1
 h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1774 (* h1 h1 h1)
 h2 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2552 (* h1 h1 h1) h2 (* h5 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 2362 (* h1 h1 h1) h2 (* h5 h5 h5) (* h6 
h6 h6) (* j2 j2 j2)) (* 1364 (* h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)
) (* 448 (* h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6) j2) (* 64 (* h1 h1 h1) h2 (* 
h5 h5 h5) (* h6 h6 h6)) (* (* h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2
 j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 107 (* h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 394 (* h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2
 j2)) (* 887 (* h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
1276 (* h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 1181 (* h1 h1
 h1) h2 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 682 (* h1 h1 h1) h2 (* h5 h5)
 (* h6 h6 h6 h6) (* j2 j2)) (* 224 (* h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6 h6) j2)
 (* 32 (* h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6 h6)) (* 16 (* h1 h1 h1) (* h3 h3 h3
 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 400 (* h1 h1 h1) (* h3 h3 h3 
h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 3696 (* h1 h1 h1) (* h3 h3 h3 h3) 
(* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 16688 (* h1 h1 h1) (* h3 h3 h3 h3) (* h4 
h4) h5 (* j2 j2 j2 j2 j2)) (* 41728 (* h1 h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 
(* j2 j2 j2 j2)) (* 60608 (* h1 h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2)
) (* 50688 (* h1 h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2)) (* 22528 (* h1 
h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 j2) (* 4096 (* h1 h1 h1) (* h3 h3 h3 h3) (* 
h4 h4) h5) (* 40 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 1008 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 
j2)) (* 9400 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) 
(* 42672 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 105792
 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 149376 (* h1 h1 
h1) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 118784 (* h1 h1 h1) (* h3 h3 
h3 h3) h4 (* h5 h5) (* j2 j2)) (* 49152 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5
) j2) (* 8192 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5)) (* 8 (* h1 h1 h1) (* h3
 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 312 (* h1 h1 h1) (* h3 h3
 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4344 (* h1 h1 h1) (* h3 h3 h3 
h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 28552 (* h1 h1 h1) (* h3 h3 h3 h3) h4 
h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 103520 (* h1 h1 h1) (* h3 h3 h3 h3) h4 h5 h6 (* 
j2 j2 j2 j2 j2)) (* 222752 (* h1 h1 h1) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2)
) (* 290688 (* h1 h1 h1) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 224768 (* h1 
h1 h1) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2)) (* 94208 (* h1 h1 h1) (* h3 h3 h3 h3)
 h4 h5 h6 j2) (* 16384 (* h1 h1 h1) (* h3 h3 h3 h3) h4 h5 h6) (* 200 (* h1 h1 h1
) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4280 (* h1 h1 h1)
 (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 32688 (* h1 h1 h1) 
(* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 125888 (* h1 h1 h1) (* h3
 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 274944 (* h1 h1 h1) (* h3 h3 h3 
h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 352768 (* h1 h1 h1) (* h3 h3 h3 h3) (* h5 
h5) h6 (* j2 j2 j2)) (* 261120 (* h1 h1 h1) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 
j2)) (* 102400 (* h1 h1 h1) (* h3 h3 h3 h3) (* h5 h5) h6 j2) (* 16384 (* h1 h1 
h1) (* h3 h3 h3 h3) (* h5 h5) h6) (* 40 (* h1 h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1008 (* h1 h1 h1) (* h3 h3 h3 h3) h5 (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 9800 (* h1 h1 h1) (* h3 h3 h3 h3) h5 (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 50272 (* h1 h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6)
 (* j2 j2 j2 j2 j2 j2)) (* 153056 (* h1 h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6) (* 
j2 j2 j2 j2 j2)) (* 290048 (* h1 h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2
 j2)) (* 344320 (* h1 h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 
247808 (* h1 h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2)) (* 98304 (* h1 h1 h1
) (* h3 h3 h3 h3) h5 (* h6 h6) j2) (* 16384 (* h1 h1 h1) (* h3 h3 h3 h3) h5 (* 
h6 h6)) (* 24 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 480 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 3712 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 
14448 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 31656 (* 
h1 h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 40752 (* h1 h1 h1) 
(* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 30528 (* h1 h1 h1) (* h3 h3 h3) 
(* h4 h4 h4) h5 (* j2 j2)) (* 12288 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 j2
) (* 2048 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5) (* 2 (* h1 h1 h1) (* h3 h3 
h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 148 (* h1 h1 h1) (* 
h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2440 (* h1 h1 h1) 
(* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 17476 (* h1 h1 h1)
 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 65030 (* h1 h1 h1) 
(* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 136712 (* h1 h1 h1) (* 
h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 168144 (* h1 h1 h1) (* h3 h3 
h3) (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 119680 (* h1 h1 h1) (* h3 h3 h3) (* h4 
h4) (* h5 h5) (* j2 j2)) (* 45568 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) 
j2) (* 7168 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5)) (* 12 (* h1 h1 h1) 
(* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 432 (* h1 h1 h1)
 (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 5240 (* h1 h1 h1) 
(* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 30704 (* h1 h1 h1) (* 
h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 100460 (* h1 h1 h1) (* h3 h3
 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 196096 (* h1 h1 h1) (* h3 h3 h3) (* 
h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 232944 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 
h6 (* j2 j2 j2)) (* 164672 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2)) 
(* 63488 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 h6 j2) (* 10240 (* h1 h1 h1) (* 
h3 h3 h3) (* h4 h4) h5 h6) (* 80 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 1456 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 
j2 j2 j2 j2 j2 j2)) (* 10448 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 
j2 j2 j2 j2)) (* 38736 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 
j2)) (* 81504 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 
100224 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2)) (* 70912 (* h1 h1
 h1) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2)) (* 26624 (* h1 h1 h1) (* h3 h3 h3) 
h4 (* h5 h5 h5) j2) (* 4096 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5)) (* 32 (* 
h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1210 
(* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 14614 
(* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 84230 (* 
h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 269554 (* h1 h1
 h1) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 511176 (* h1 h1 h1) (* 
h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 585952 (* h1 h1 h1) (* h3 h3 h3) 
h4 (* h5 h5) h6 (* j2 j2 j2)) (* 397440 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) 
h6 (* j2 j2)) (* 146432 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) h6 j2) (* 22528 
(* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) h6) (* 72 (* h1 h1 h1) (* h3 h3 h3) h4 h5
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1620 (* h1 h1 h1) (* h3 h3 h3) h4 
h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 14820 (* h1 h1 h1) (* h3 h3 h3) h4 
h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 72324 (* h1 h1 h1) (* h3 h3 h3) h4 h5 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 208964 (* h1 h1 h1) (* h3 h3 h3) h4 h5 (* h6
 h6) (* j2 j2 j2 j2 j2)) (* 373656 (* h1 h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6) (* 
j2 j2 j2 j2)) (* 416512 (* h1 h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) 
(* 280832 (* h1 h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 104448 (* h1 
h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6) j2) (* 16384 (* h1 h1 h1) (* h3 h3 h3) h4 h5
 (* h6 h6)) (* 400 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 5760 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 34256 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)
) (* 109664 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
206208 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 232960 (* 
h1 h1 h1) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 154624 (* h1 h1 h1) (* 
h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2)) (* 55296 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5
 h5) h6 j2) (* 8192 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5 h5) h6) (* 110 (* h1 h1 
h1) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2122 (* 
h1 h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 17930
 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
84030 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
236896 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
414800 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 452096 
(* h1 h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 297216 (* h1 h1 
h1) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 107520 (* h1 h1 h1) (* h3 h3 
h3) (* h5 h5) (* h6 h6) j2) (* 16384 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 
h6)) (* 60 (* h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 1212 (* h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 10060 (* h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 45332 (* h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
122952 (* h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 209216 
(* h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 224320 (* h1 h1 h1
) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 146688 (* h1 h1 h1) (* h3 h3 h3)
 h5 (* h6 h6 h6) (* j2 j2)) (* 53248 (* h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6) 
j2) (* 8192 (* h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6)) (* 16 (* h1 h1 h1) (* h3 
h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 208 (* h1 h1 h1) (* h3 h3) 
(* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 960 (* h1 h1 h1) (* h3 h3) (* h4 h4
 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 2208 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4 h4) h5
 (* j2 j2 j2 j2)) (* 2832 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2)
) (* 2064 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2)) (* 800 (* h1 h1 
h1) (* h3 h3) (* h4 h4 h4 h4) h5 j2) (* 128 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4 
h4) h5) (* 24 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 456 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 
j2 j2)) (* 3280 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 
j2)) (* 11600 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) 
(* 22904 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 26600
 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 18080 (* h1 h1 
h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 6656 (* h1 h1 h1) (* h3 h3) 
(* h4 h4 h4) (* h5 h5) j2) (* 1024 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5)
) (* 16 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 368 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
2736 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 9792 
(* h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 19504 (* h1 h1 
h1) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 22832 (* h1 h1 h1) (* h3 h3
) (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 15632 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) 
h5 h6 (* j2 j2)) (* 5792 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 h6 j2) (* 896 
(* h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 h6) (* 2 (* h1 h1 h1) (* h3 h3) (* h4 h4)
 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 106 (* h1 h1 h1) (* h3 h3) (* 
h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1436 (* h1 h1 h1) (* h3 h3) 
(* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 8620 (* h1 h1 h1) (* h3 h3) 
(* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 27410 (* h1 h1 h1) (* h3 h3) 
(* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 50234 (* h1 h1 h1) (* h3 h3) (* h4
 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 54864 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* 
h5 h5 h5) (* j2 j2 j2)) (* 35248 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) 
(* j2 j2)) (* 12288 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) j2) (* 1792 
(* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5)) (* 16 (* h1 h1 h1) (* h3 h3) (* 
h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 480 (* h1 h1 h1) (* h3 h3
) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 5160 (* h1 h1 h1) (* h3
 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 27136 (* h1 h1 h1) (* 
h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 79808 (* h1 h1 h1) (* h3
 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 140288 (* h1 h1 h1) (* h3 h3)
 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 150728 (* h1 h1 h1) (* h3 h3) (* h4 
h4) (* h5 h5) h6 (* j2 j2 j2)) (* 96992 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 
h5) h6 (* j2 j2)) (* 34304 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) h6 j2) (* 
5120 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) h6) (* 4 (* h1 h1 h1) (* h3 h3) 
(* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 180 (* h1 h1 h1) (* h3
 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2128 (* h1 h1 h1) 
(* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 11560 (* h1 h1 h1)
 (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 34564 (* h1 h1 h1) 
(* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 61444 (* h1 h1 h1) (* h3
 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 66600 (* h1 h1 h1) (* h3 h3) (* 
h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 43168 (* h1 h1 h1) (* h3 h3) (* h4 h4) h5 
(* h6 h6) (* j2 j2)) (* 15360 (* h1 h1 h1) (* h3 h3) (* h4 h4) h5 (* h6 h6) j2) 
(* 2304 (* h1 h1 h1) (* h3 h3) (* h4 h4) h5 (* h6 h6)) (* 20 (* h1 h1 h1) (* h3 
h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 344 (* h1 h1 h1) (* h3 h3
) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 2288 (* h1 h1 h1) (* h3 h3) h4
 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 7720 (* h1 h1 h1) (* h3 h3) h4 (* h5 
h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 14620 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5)
 (* j2 j2 j2 j2)) (* 16192 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2
)) (* 10400 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2)) (* 3584 (* h1 
h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) j2) (* 512 (* h1 h1 h1) (* h3 h3) h4 (* h5 
h5 h5 h5)) (* 24 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 794 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 8076 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2)) (* 39728 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 110340 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
184534 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 189336 (* 
h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 116512 (* h1 h1 h1) (* 
h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2)) (* 39424 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5
 h5) h6 j2) (* 5632 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) h6) (* 96 (* h1 h1 h1
) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1832 (* h1
 h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 14656 
(* h1 h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 63536
 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 164416 
(* h1 h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 264872 (* 
h1 h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 267616 (* h1 h1 
h1) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 164672 (* h1 h1 h1) (* h3 
h3) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 56320 (* h1 h1 h1) (* h3 h3) h4 (* h5 
h5) (* h6 h6) j2) (* 8192 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6)) (* 24 
(* h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 508
 (* h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4264 
(* h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 18952 (* 
h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 49784 (* h1 h1 
h1) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 81020 (* h1 h1 h1) (* h3
 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 82472 (* h1 h1 h1) (* h3 h3) h4 h5 
(* h6 h6 h6) (* j2 j2 j2)) (* 51040 (* h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6) 
(* j2 j2)) (* 17536 (* h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6) j2) (* 2560 (* h1 
h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6)) (* 100 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1340 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 7324 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2)) (* 21332 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2)) (* 36304 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 
j2)) (* 37184 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 22528 
(* h1 h1 h1) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 7424 (* h1 h1 h1) (* h3 
h3) (* h5 h5 h5 h5) h6 j2) (* 1024 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5 h5) h6) 
(* 70 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 1244 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 9296 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 38196 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2
 j2)) (* 94906 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2))
 (* 147952 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 
145200 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 86912 (* 
h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 28928 (* h1 h1 h1) (* 
h3 h3) (* h5 h5 h5) (* h6 h6) j2) (* 4096 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) 
(* h6 h6)) (* 80 (* h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2 j2)) (* 1376 (* h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 9952 (* h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2
 j2 j2 j2 j2 j2)) (* 39680 (* h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 96208 (* h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2
 j2 j2 j2)) (* 147488 (* h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2)) (* 143488 (* h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 
85760 (* h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 28672 (* h1 h1
 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6) j2) (* 4096 (* h1 h1 h1) (* h3 h3) (* h5 
h5) (* h6 h6 h6)) (* 20 (* h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 344 (* h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 2488 (* h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 9920 (* h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 24052 (* h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 36872 (* h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 35872 (* 
h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 21440 (* h1 h1 h1) (* h3
 h3) h5 (* h6 h6 h6 h6) (* j2 j2)) (* 7168 (* h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6
 h6) j2) (* 1024 (* h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6 h6)) (* 8 (* h1 h1 h1) h3
 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 96 (* h1 h1 h1) h3 (* h4
 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 392 (* h1 h1 h1) h3 (* h4 h4 h4 
h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 800 (* h1 h1 h1) h3 (* h4 h4 h4 h4) (* h5 
h5) (* j2 j2 j2 j2)) (* 920 (* h1 h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 
j2)) (* 608 (* h1 h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2)) (* 216 (* h1 h1
 h1) h3 (* h4 h4 h4 h4) (* h5 h5) j2) (* 32 (* h1 h1 h1) h3 (* h4 h4 h4 h4) (* 
h5 h5)) (* 8 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 128 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 776 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2368 
(* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 4120 (* h1 h1 
h1) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 4288 (* h1 h1 h1) h3 (* h4 
h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 2648 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5 
h5) (* j2 j2)) (* 896 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) j2) (* 128 (* h1
 h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5)) (* 8 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5
) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 176 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1200 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 3864 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* 6920 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2))
 (* 7328 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 4576 (* h1 
h1 h1) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 1560 (* h1 h1 h1) h3 (* h4 h4 
h4) (* h5 h5) h6 j2) (* 224 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) h6) (* 4 (* 
h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 64 (* h1 
h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 388 (* h1 h1 h1
) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1184 (* h1 h1 h1) h3 
(* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 2060 (* h1 h1 h1) h3 (* h4 h4) 
(* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 2144 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5 
h5) (* j2 j2 j2)) (* 1324 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2)) 
(* 448 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) j2) (* 64 (* h1 h1 h1) h3 (* h4
 h4) (* h5 h5 h5 h5)) (* 4 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2
 j2 j2 j2 j2 j2 j2)) (* 128 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 1260 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2)) (* 5928 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2)) (* 15580 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)
) (* 24624 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 23988 
(* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 14120 (* h1 h1 h1) h3
 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 4608 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5
 h5) h6 j2) (* 640 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) h6) (* 2 (* h1 h1 h1) 
h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 88 (* h1 h1 
h1) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 978 (* h1 
h1 h1) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4888 (* h1 
h1 h1) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 13286 (* h1 h1
 h1) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 21432 (* h1 h1 h1) 
h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 21158 (* h1 h1 h1) h3 (* h4
 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 12568 (* h1 h1 h1) h3 (* h4 h4) (* h5 
h5) (* h6 h6) (* j2 j2)) (* 4128 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5) (* h6 h6) 
j2) (* 576 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5) (* h6 h6)) (* 2 (* h1 h1 h1) h3 
h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 60 (* h1 h1 h1) h3 h4 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 566 (* h1 h1 h1) h3 h4 (* h5 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2576 (* h1 h1 h1) h3 h4 (* h5 h5 h5 h5
) h6 (* j2 j2 j2 j2 j2 j2)) (* 6606 (* h1 h1 h1) h3 h4 (* h5 h5 h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* 10252 (* h1 h1 h1) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) 
(* 9850 (* h1 h1 h1) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 5736 (* h1 h1 h1)
 h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 1856 (* h1 h1 h1) h3 h4 (* h5 h5 h5 h5) 
h6 j2) (* 256 (* h1 h1 h1) h3 h4 (* h5 h5 h5 h5) h6) (* 24 (* h1 h1 h1) h3 h4 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 444 (* h1 h1 h1) h3 h4
 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3316 (* h1 h1 h1) h3 h4 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 13192 (* h1 h1 h1) h3 h4 (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 31104 (* h1 h1 h1) h3 h4 (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 45644 (* h1 h1 h1) h3 h4 (* h5 h5 h5) (* h6
 h6) (* j2 j2 j2 j2)) (* 42164 (* h1 h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 
j2 j2)) (* 23856 (* h1 h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 7552 
(* h1 h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6) j2) (* 1024 (* h1 h1 h1) h3 h4 (* h5 
h5 h5) (* h6 h6)) (* 12 (* h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 242 (* h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 1902 (* h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 7804 (* h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 18760 (* h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 27882 (* h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 25982 (* 
h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 14792 (* h1 h1 h1) h3 h4
 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 4704 (* h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6
 h6) j2) (* 640 (* h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6)) (* 10 (* h1 h1 h1) h3
 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 162 (* h1 h1 h1) 
h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1092 (* h1 h1 h1) 
h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4020 (* h1 h1 h1) h3 
(* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 8946 (* h1 h1 h1) h3 (* h5 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 12570 (* h1 h1 h1) h3 (* h5 h5 h5 h5)
 (* h6 h6) (* j2 j2 j2 j2)) (* 11232 (* h1 h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6) 
(* j2 j2 j2)) (* 6192 (* h1 h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 
1920 (* h1 h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6) j2) (* 256 (* h1 h1 h1) h3 (* h5 
h5 h5 h5) (* h6 h6)) (* 20 (* h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2
 j2 j2 j2 j2 j2 j2)) (* 324 (* h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 2184 (* h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 8040 (* h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 17892 (* h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)
) (* 25140 (* h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 22464 
(* h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 12384 (* h1 h1 h1) h3
 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 3840 (* h1 h1 h1) h3 (* h5 h5 h5) (* h6
 h6 h6) j2) (* 512 (* h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6)) (* 10 (* h1 h1 h1)
 h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 162 (* h1 h1 h1
) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1092 (* h1 h1 h1)
 h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4020 (* h1 h1 h1) h3 
(* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 8946 (* h1 h1 h1) h3 (* h5 
h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 12570 (* h1 h1 h1) h3 (* h5 h5) (* h6
 h6 h6 h6) (* j2 j2 j2 j2)) (* 11232 (* h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6 h6) 
(* j2 j2 j2)) (* 6192 (* h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 
1920 (* h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6 h6) j2) (* 256 (* h1 h1 h1) h3 (* h5 
h5) (* h6 h6 h6 h6)) (* 20 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2
 j2 j2)) (* 280 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2)) (* 
1056 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2)) (* 1632 (* h1 h1) 
(* h2 h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2)) (* 1088 (* h1 h1) (* h2 h2 h2 h2) (* 
h3 h3 h3) h5 j2) (* 256 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h5) (* 4 (* h1 h1
) (* h2 h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2 j2 j2 j2)) (* 68 (* h1 h1) (* h2 
h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2 j2 j2)) (* 384 (* h1 h1) (* h2 h2 h2 h2) 
(* h3 h3 h3) h6 (* j2 j2 j2 j2)) (* 1024 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) 
h6 (* j2 j2 j2)) (* 1408 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2)) 
(* 960 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h6 j2) (* 256 (* h1 h1) (* h2 h2 
h2 h2) (* h3 h3 h3) h6) (* (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2
 j2 j2 j2)) (* 50 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2 j2)) 
(* 405 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2)) (* 1160 (* h1 
h1) (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2)) (* 1492 (* h1 h1) (* h2 h2 h2 
h2) (* h3 h3) h4 h5 (* j2 j2)) (* 880 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h5 
j2) (* 192 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h5) (* 6 (* h1 h1) (* h2 h2 h2
 h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2)) (* 72 (* h1 h1) (* h2 h2 h2 h2) (* 
h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 326 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 
h6 (* j2 j2 j2 j2)) (* 732 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2
)) (* 872 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h6 (* j2 j2)) (* 528 (* h1 h1) 
(* h2 h2 h2 h2) (* h3 h3) h4 h6 j2) (* 128 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) 
h4 h6) (* 40 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) 
(* 280 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 752 (* 
h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2)) (* 960 (* h1 h1) (* h2 
h2 h2 h2) (* h3 h3) (* h5 h5) (* j2 j2)) (* 576 (* h1 h1) (* h2 h2 h2 h2) (* h3 
h3) (* h5 h5) j2) (* 128 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h5 h5)) (* 11 
(* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 122 (* h1 h1
) (* h2 h2 h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 615 (* h1 h1) (* h2 h2 
h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 1492 (* h1 h1) (* h2 h2 h2 h2) (* h3 
h3) h5 h6 (* j2 j2 j2)) (* 1820 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 h6 (* j2 
j2)) (* 1088 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 h6 j2) (* 256 (* h1 h1) (* 
h2 h2 h2 h2) (* h3 h3) h5 h6) (* 6 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h6 h6)
 (* j2 j2 j2 j2 j2 j2)) (* 72 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h6 h6) (* 
j2 j2 j2 j2 j2)) (* 326 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 
j2 j2)) (* 732 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2)) (* 
872 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2)) (* 528 (* h1 h1) 
(* h2 h2 h2 h2) (* h3 h3) (* h6 h6) j2) (* 128 (* h1 h1) (* h2 h2 h2 h2) (* h3 
h3) (* h6 h6)) (* (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2
)) (* 33 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 179 
(* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2)) (* 403 (* h1 h1) (* 
h2 h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2)) (* 444 (* h1 h1) (* h2 h2 h2 h2) h3 
h4 (* h5 h5) (* j2 j2)) (* 236 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h5 h5) j2) (* 
48 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h5 h5)) (* 8 (* h1 h1) (* h2 h2 h2 h2) h3 
h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 72 (* h1 h1) (* h2 h2 h2 h2) h3 h4 h5 h6 (* 
j2 j2 j2 j2 j2)) (* 264 (* h1 h1) (* h2 h2 h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2)) 
(* 504 (* h1 h1) (* h2 h2 h2 h2) h3 h4 h5 h6 (* j2 j2 j2)) (* 528 (* h1 h1) (* 
h2 h2 h2 h2) h3 h4 h5 h6 (* j2 j2)) (* 288 (* h1 h1) (* h2 h2 h2 h2) h3 h4 h5 h6
 j2) (* 64 (* h1 h1) (* h2 h2 h2 h2) h3 h4 h5 h6) (* 2 (* h1 h1) (* h2 h2 h2 h2)
 h3 h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 18 (* h1 h1) (* h2 h2 h2 h2) h3 h4 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 66 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h6 h6) 
(* j2 j2 j2 j2)) (* 126 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2)) 
(* 132 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h6 h6) (* j2 j2)) (* 72 (* h1 h1) (* 
h2 h2 h2 h2) h3 h4 (* h6 h6) j2) (* 16 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h6 h6)
) (* 10 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 60 (* 
h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 138 (* h1 h1) (* h2 
h2 h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2)) (* 152 (* h1 h1) (* h2 h2 h2 h2) h3 (* 
h5 h5 h5) (* j2 j2)) (* 80 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5 h5) j2) (* 16 
(* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5 h5)) (* 7 (* h1 h1) (* h2 h2 h2 h2) h3 (* 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 67 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) h6
 (* j2 j2 j2 j2 j2)) (* 257 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) h6 (* j2 j2 
j2 j2)) (* 505 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2)) (* 536 
(* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) h6 (* j2 j2)) (* 292 (* h1 h1) (* h2 h2 
h2 h2) h3 (* h5 h5) h6 j2) (* 64 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) h6) (* 8
 (* h1 h1) (* h2 h2 h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 72 (* h1 h1
) (* h2 h2 h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 264 (* h1 h1) (* h2 h2 
h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 504 (* h1 h1) (* h2 h2 h2 h2) h3 h5 
(* h6 h6) (* j2 j2 j2)) (* 528 (* h1 h1) (* h2 h2 h2 h2) h3 h5 (* h6 h6) (* j2 
j2)) (* 288 (* h1 h1) (* h2 h2 h2 h2) h3 h5 (* h6 h6) j2) (* 64 (* h1 h1) (* h2 
h2 h2 h2) h3 h5 (* h6 h6)) (* 2 (* h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 18 (* h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2 j2 
j2)) (* 66 (* h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 126 (* 
h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2)) (* 132 (* h1 h1) (* h2 h2 
h2 h2) h3 (* h6 h6 h6) (* j2 j2)) (* 72 (* h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6 h6
) j2) (* 16 (* h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6 h6)) (* 2 (* h1 h1) (* h2 h2 
h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1) (* h2 h2 h2 h2) h4
 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 52 (* h1 h1) (* h2 h2 h2 h2) h4 (* h5 h5) 
h6 (* j2 j2 j2 j2)) (* 88 (* h1 h1) (* h2 h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2)
) (* 82 (* h1 h1) (* h2 h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2)) (* 40 (* h1 h1) (* 
h2 h2 h2 h2) h4 (* h5 h5) h6 j2) (* 8 (* h1 h1) (* h2 h2 h2 h2) h4 (* h5 h5) h6)
 (* (* h1 h1) (* h2 h2 h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 8 (* h1 
h1) (* h2 h2 h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 26 (* h1 h1) (* h2 h2
 h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 44 (* h1 h1) (* h2 h2 h2 h2) h4 h5 
(* h6 h6) (* j2 j2 j2)) (* 41 (* h1 h1) (* h2 h2 h2 h2) h4 h5 (* h6 h6) (* j2 j2
)) (* 20 (* h1 h1) (* h2 h2 h2 h2) h4 h5 (* h6 h6) j2) (* 4 (* h1 h1) (* h2 h2 
h2 h2) h4 h5 (* h6 h6)) (* (* h1 h1) (* h2 h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2
 j2 j2 j2)) (* 8 (* h1 h1) (* h2 h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) 
(* 26 (* h1 h1) (* h2 h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 44 (* h1 h1)
 (* h2 h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 41 (* h1 h1) (* h2 h2 h2 h2) 
(* h5 h5 h5) h6 (* j2 j2)) (* 20 (* h1 h1) (* h2 h2 h2 h2) (* h5 h5 h5) h6 j2) 
(* 4 (* h1 h1) (* h2 h2 h2 h2) (* h5 h5 h5) h6) (* 2 (* h1 h1) (* h2 h2 h2 h2) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1) (* h2 h2 h2 h2) (* h5
 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 52 (* h1 h1) (* h2 h2 h2 h2) (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2)) (* 88 (* h1 h1) (* h2 h2 h2 h2) (* h5 h5) (* h6 h6) (* 
j2 j2 j2)) (* 82 (* h1 h1) (* h2 h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 j2)) (* 40 
(* h1 h1) (* h2 h2 h2 h2) (* h5 h5) (* h6 h6) j2) (* 8 (* h1 h1) (* h2 h2 h2 h2)
 (* h5 h5) (* h6 h6)) (* (* h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 8 (* h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 26 (* h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 44 (* h1 h1)
 (* h2 h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 41 (* h1 h1) (* h2 h2 h2 h2) 
h5 (* h6 h6 h6) (* j2 j2)) (* 20 (* h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6 h6) j2) 
(* 4 (* h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6 h6)) (* 40 (* h1 h1) (* h2 h2 h2) (* 
h3 h3 h3 h3) h5 (* j2 j2 j2 j2 j2 j2)) (* 640 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3
 h3) h5 (* j2 j2 j2 j2 j2)) (* 3232 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h5 
(* j2 j2 j2 j2)) (* 7488 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2 j2))
 (* 8704 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2)) (* 4864 (* h1 h1) 
(* h2 h2 h2) (* h3 h3 h3 h3) h5 j2) (* 1024 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 
h3) h5) (* 8 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2 j2 j2 j2 j2 j2))
 (* 152 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2 j2 j2 j2 j2)) (* 1040
 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2 j2 j2 j2)) (* 3584 (* h1 h1)
 (* h2 h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2 j2 j2)) (* 6912 (* h1 h1) (* h2 h2 h2)
 (* h3 h3 h3 h3) h6 (* j2 j2 j2)) (* 7552 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3)
 h6 (* j2 j2)) (* 4352 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h6 j2) (* 1024 (* 
h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h6) (* 4 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3)
 h4 h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 218 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 
h5 (* j2 j2 j2 j2 j2 j2)) (* 2424 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* 
j2 j2 j2 j2 j2)) (* 10782 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 
j2)) (* 23564 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2)) (* 26512 
(* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2)) (* 14592 (* h1 h1) (* h2 h2
 h2) (* h3 h3 h3) h4 h5 j2) (* 3072 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h5) 
(* 24 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 376
 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2)) (* 2296 (* h1 
h1) (* h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 7304 (* h1 h1) (* h2 
h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 13264 (* h1 h1) (* h2 h2 h2) (* h3
 h3 h3) h4 h6 (* j2 j2 j2)) (* 13856 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h6 
(* j2 j2)) (* 7744 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h6 j2) (* 1792 (* h1 
h1) (* h2 h2 h2) (* h3 h3 h3) h4 h6) (* 120 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) 
(* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1340 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* 
h5 h5) (* j2 j2 j2 j2 j2)) (* 6076 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h5 h5)
 (* j2 j2 j2 j2)) (* 13800 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 
j2 j2)) (* 15984 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2)) (* 
8768 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) j2) (* 1792 (* h1 h1) (* h2 
h2 h2) (* h3 h3 h3) (* h5 h5)) (* 32 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 506 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2
 j2 j2 j2 j2 j2)) (* 3628 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 
j2 j2)) (* 13470 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 
27196 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2)) (* 29744 (* h1 h1)
 (* h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2)) (* 16448 (* h1 h1) (* h2 h2 h2) (* 
h3 h3 h3) h5 h6 j2) (* 3584 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 h6) (* 24 (* 
h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 376 (* 
h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2296 (* h1 
h1) (* h2 h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 7304 (* h1 h1) 
(* h2 h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 13264 (* h1 h1) (* h2 h2
 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2)) (* 13856 (* h1 h1) (* h2 h2 h2) (* h3 
h3 h3) (* h6 h6) (* j2 j2)) (* 7744 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h6 h6
) j2) (* 1792 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h6 h6)) (* 4 (* h1 h1) (* 
h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 140 (* h1 h1) (* 
h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 1330 (* h1 h1) (* h2 
h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 5212 (* h1 h1) (* h2 h2 h2)
 (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 9998 (* h1 h1) (* h2 h2 h2) (* h3 h3
) (* h4 h4) h5 (* j2 j2 j2)) (* 9964 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h4 h4) 
h5 (* j2 j2)) (* 4944 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 j2) (* 960 
(* h1 h1) (* h2 h2 h2) (* h3 h3) (* h4 h4) h5) (* 10 (* h1 h1) (* h2 h2 h2) (* 
h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 146 (* h1 h1) (* h2 h2 h2) (* 
h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 818 (* h1 h1) (* h2 h2 h2) (* h3 
h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 2366 (* h1 h1) (* h2 h2 h2) (* h3 h3) 
(* h4 h4) h6 (* j2 j2 j2 j2)) (* 3884 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h4 h4)
 h6 (* j2 j2 j2)) (* 3656 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2
)) (* 1840 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h4 h4) h6 j2) (* 384 (* h1 h1) 
(* h2 h2 h2) (* h3 h3) (* h4 h4) h6) (* 7 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 
(* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 281 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 
(* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2393 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* 
h5 h5) (* j2 j2 j2 j2 j2)) (* 8679 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h5 h5)
 (* j2 j2 j2 j2)) (* 16068 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 
j2 j2)) (* 15844 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2)) (* 
7872 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) j2) (* 1536 (* h1 h1) (* h2 
h2 h2) (* h3 h3) h4 (* h5 h5)) (* 52 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 760 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2
 j2 j2 j2 j2 j2)) (* 4736 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 
j2 j2)) (* 15240 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 
26764 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 25888 (* h1 h1)
 (* h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2)) (* 12960 (* h1 h1) (* h2 h2 h2) (* 
h3 h3) h4 h5 h6 j2) (* 2624 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 h6) (* 24 (* 
h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 336 (* 
h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1840 (* h1 
h1) (* h2 h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 5248 (* h1 h1) 
(* h2 h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 8536 (* h1 h1) (* h2 h2 
h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2)) (* 7984 (* h1 h1) (* h2 h2 h2) (* h3 h3
) h4 (* h6 h6) (* j2 j2)) (* 4000 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h6 h6) 
j2) (* 832 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h6 h6)) (* 70 (* h1 h1) (* h2 
h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 640 (* h1 h1) (* h2 h2 
h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 2546 (* h1 h1) (* h2 h2 h2) 
(* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 5000 (* h1 h1) (* h2 h2 h2) (* h3 h3)
 (* h5 h5 h5) (* j2 j2 j2)) (* 4992 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5 h5
) (* j2 j2)) (* 2416 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) j2) (* 448 
(* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5 h5)) (* 33 (* h1 h1) (* h2 h2 h2) (* 
h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 481 (* h1 h1) (* h2 h2 h2) (* 
h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 2985 (* h1 h1) (* h2 h2 h2) (* h3 
h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 9523 (* h1 h1) (* h2 h2 h2) (* h3 h3) 
(* h5 h5) h6 (* j2 j2 j2 j2)) (* 16762 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5
) h6 (* j2 j2 j2)) (* 16352 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 
j2)) (* 8240 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) h6 j2) (* 1664 (* h1 h1)
 (* h2 h2 h2) (* h3 h3) (* h5 h5) h6) (* 48 (* h1 h1) (* h2 h2 h2) (* h3 h3) h5 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 624 (* h1 h1) (* h2 h2 h2) (* h3 h3) h5 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3434 (* h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* 
h6 h6) (* j2 j2 j2 j2 j2)) (* 10104 (* h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* h6 h6
) (* j2 j2 j2 j2)) (* 16866 (* h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 
j2 j2)) (* 15988 (* h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2)) (* 
8032 (* h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* h6 h6) j2) (* 1664 (* h1 h1) (* h2 
h2 h2) (* h3 h3) h5 (* h6 h6)) (* 14 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 190 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 1022 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6 h6)
 (* j2 j2 j2 j2 j2)) (* 2882 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6 h6) (* j2
 j2 j2 j2)) (* 4652 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2)) 
(* 4328 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2)) (* 2160 (* h1 
h1) (* h2 h2 h2) (* h3 h3) (* h6 h6 h6) j2) (* 448 (* h1 h1) (* h2 h2 h2) (* h3 
h3) (* h6 h6 h6)) (* 3 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2
 j2 j2 j2 j2)) (* 84 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 
j2 j2 j2)) (* 630 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 
j2)) (* 2028 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 
3339 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 2952 (* h1 
h1) (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2)) (* 1332 (* h1 h1) (* h2 h2 h2
) h3 (* h4 h4) (* h5 h5) j2) (* 240 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h5 h5
)) (* 13 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
154 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 710 (* 
h1 h1) (* h2 h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 1752 (* h1 h1) (* 
h2 h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 2533 (* h1 h1) (* h2 h2 h2) h3 
(* h4 h4) h5 h6 (* j2 j2 j2)) (* 2150 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) h5 h6 
(* j2 j2)) (* 992 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) h5 h6 j2) (* 192 (* h1 h1)
 (* h2 h2 h2) h3 (* h4 h4) h5 h6) (* 2 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h6
 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 20 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 84 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* 192 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 
j2 j2 j2)) (* 258 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 j2 j2)) 
(* 204 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 j2)) (* 88 (* h1 h1) 
(* h2 h2 h2) h3 (* h4 h4) (* h6 h6) j2) (* 16 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4
) (* h6 h6)) (* 2 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2
 j2)) (* 74 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 
556 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 1752 (* h1 
h1) (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 2822 (* h1 h1) (* h2 h2 
h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2)) (* 2446 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 
h5 h5) (* j2 j2)) (* 1084 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5 h5) j2) (* 192 
(* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5 h5)) (* 30 (* h1 h1) (* h2 h2 h2) h3 h4 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 396 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5
 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 2108 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) h6
 (* j2 j2 j2 j2 j2)) (* 5792 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 
j2 j2)) (* 8894 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2)) (* 7700 
(* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2)) (* 3512 (* h1 h1) (* h2 h2 
h2) h3 h4 (* h5 h5) h6 j2) (* 656 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) h6) (* 
30 (* h1 h1) (* h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 346 
(* h1 h1) (* h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1576 (* h1 
h1) (* h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 3860 (* h1 h1) (* h2 
h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 5550 (* h1 h1) (* h2 h2 h2) h3 h4 
h5 (* h6 h6) (* j2 j2 j2)) (* 4690 (* h1 h1) (* h2 h2 h2) h3 h4 h5 (* h6 h6) (* 
j2 j2)) (* 2156 (* h1 h1) (* h2 h2 h2) h3 h4 h5 (* h6 h6) j2) (* 416 (* h1 h1) 
(* h2 h2 h2) h3 h4 h5 (* h6 h6)) (* 4 (* h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 40 (* h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 168 (* h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2 j2 j2
 j2)) (* 384 (* h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 516 
(* h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2 j2)) (* 408 (* h1 h1) (* h2 
h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2)) (* 176 (* h1 h1) (* h2 h2 h2) h3 h4 (* h6 
h6 h6) j2) (* 32 (* h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6 h6)) (* 10 (* h1 h1) (* 
h2 h2 h2) h3 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 70 (* h1 h1) (* h2 h2 h2)
 h3 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 198 (* h1 h1) (* h2 h2 h2) h3 (* h5 
h5 h5 h5) (* j2 j2 j2 j2)) (* 290 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* 
j2 j2 j2)) (* 232 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* j2 j2)) (* 96 (* 
h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5 h5) j2) (* 16 (* h1 h1) (* h2 h2 h2) h3 (* h5
 h5 h5 h5)) (* 11 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2
 j2)) (* 140 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 742 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 2044 (* 
h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 3139 (* h1 h1) (* h2 
h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 2704 (* h1 h1) (* h2 h2 h2) h3 (* h5 
h5 h5) h6 (* j2 j2)) (* 1220 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) h6 j2) (* 
224 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) h6) (* 27 (* h1 h1) (* h2 h2 h2) h3 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 314 (* h1 h1) (* h2 h2 h2) h3 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1490 (* h1 h1) (* h2 h2 h2) h3 (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 3792 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5)
 (* h6 h6) (* j2 j2 j2 j2)) (* 5587 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* h6 h6
) (* j2 j2 j2)) (* 4766 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2))
 (* 2184 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* h6 h6) j2) (* 416 (* h1 h1) (* 
h2 h2 h2) h3 (* h5 h5) (* h6 h6)) (* 17 (* h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6 h6
) (* j2 j2 j2 j2 j2 j2 j2)) (* 192 (* h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 866 (* h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2
 j2 j2)) (* 2108 (* h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 
3017 (* h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 2540 (* h1 h1) 
(* h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2)) (* 1164 (* h1 h1) (* h2 h2 h2) h3 h5 
(* h6 h6 h6) j2) (* 224 (* h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6 h6)) (* 2 (* h1 h1
) (* h2 h2 h2) h3 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 20 (* h1 h1) (* 
h2 h2 h2) h3 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 84 (* h1 h1) (* h2 h2 h2)
 h3 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 192 (* h1 h1) (* h2 h2 h2) h3 (* h6 
h6 h6 h6) (* j2 j2 j2 j2)) (* 258 (* h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6 h6) (* 
j2 j2 j2)) (* 204 (* h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6 h6) (* j2 j2)) (* 88 (* 
h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6 h6) j2) (* 16 (* h1 h1) (* h2 h2 h2) h3 (* h6
 h6 h6 h6)) (* 3 (* h1 h1) (* h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2
 j2 j2)) (* 33 (* h1 h1) (* h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 
j2)) (* 144 (* h1 h1) (* h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) 
(* 330 (* h1 h1) (* h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 435 (* 
h1 h1) (* h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 333 (* h1 h1) (* h2 
h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 138 (* h1 h1) (* h2 h2 h2) (* h4 h4)
 (* h5 h5) h6 j2) (* 24 (* h1 h1) (* h2 h2 h2) (* h4 h4) (* h5 h5) h6) (* (* h1 
h1) (* h2 h2 h2) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 9 (* h1 h1)
 (* h2 h2 h2) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 34 (* h1 h1) (* 
h2 h2 h2) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 70 (* h1 h1) (* h2 h2 h2
) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 85 (* h1 h1) (* h2 h2 h2) (* h4 h4)
 h5 (* h6 h6) (* j2 j2 j2)) (* 61 (* h1 h1) (* h2 h2 h2) (* h4 h4) h5 (* h6 h6) 
(* j2 j2)) (* 24 (* h1 h1) (* h2 h2 h2) (* h4 h4) h5 (* h6 h6) j2) (* 4 (* h1 h1
) (* h2 h2 h2) (* h4 h4) h5 (* h6 h6)) (* 4 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 42 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5 h5) h6
 (* j2 j2 j2 j2 j2 j2)) (* 178 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* 400 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) 
(* 520 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 394 (* h1 h1) 
(* h2 h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2)) (* 162 (* h1 h1) (* h2 h2 h2) h4 (* 
h5 h5 h5) h6 j2) (* 28 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5 h5) h6) (* 7 (* h1 h1)
 (* h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 75 (* h1 h1) 
(* h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 322 (* h1 h1) (* 
h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 730 (* h1 h1) (* h2 h2 
h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 955 (* h1 h1) (* h2 h2 h2) h4 (* 
h5 h5) (* h6 h6) (* j2 j2 j2)) (* 727 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5) (* h6 
h6) (* j2 j2)) (* 300 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5) (* h6 h6) j2) (* 52 
(* h1 h1) (* h2 h2 h2) h4 (* h5 h5) (* h6 h6)) (* 2 (* h1 h1) (* h2 h2 h2) h4 h5
 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 18 (* h1 h1) (* h2 h2 h2) h4 h5 (* h6
 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 68 (* h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2)) (* 140 (* h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2
 j2)) (* 170 (* h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 122 (* 
h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2)) (* 48 (* h1 h1) (* h2 h2 h2) 
h4 h5 (* h6 h6 h6) j2) (* 8 (* h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6 h6)) (* (* h1 
h1) (* h2 h2 h2) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 9 (* h1 h1) (* 
h2 h2 h2) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 34 (* h1 h1) (* h2 h2 h2)
 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 70 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5
 h5) h6 (* j2 j2 j2 j2)) (* 85 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5 h5) h6 (* j2 
j2 j2)) (* 61 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 24 (* h1 
h1) (* h2 h2 h2) (* h5 h5 h5 h5) h6 j2) (* 4 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5 
h5) h6) (* 4 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 42 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 178 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 400 
(* h1 h1) (* h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 520 (* h1 h1) 
(* h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 394 (* h1 h1) (* h2 h2 h2) 
(* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 162 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5) (* 
h6 h6) j2) (* 28 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5) (* h6 h6)) (* 4 (* h1 h1) 
(* h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 42 (* h1 h1) 
(* h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 178 (* h1 h1) (* 
h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 400 (* h1 h1) (* h2 h2 
h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 520 (* h1 h1) (* h2 h2 h2) (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2)) (* 394 (* h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6 
h6) (* j2 j2)) (* 162 (* h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6 h6) j2) (* 28 
(* h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6 h6)) (* (* h1 h1) (* h2 h2 h2) h5 (* 
h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 9 (* h1 h1) (* h2 h2 h2) h5 (* h6 h6 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 34 (* h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2)) (* 70 (* h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2 j2 
j2)) (* 85 (* h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 61 (* h1 
h1) (* h2 h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2)) (* 24 (* h1 h1) (* h2 h2 h2) h5 
(* h6 h6 h6 h6) j2) (* 4 (* h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6 h6)) (* 2 (* h1 
h1) (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 152 (* h1 h1
) (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 2558 (* h1 h1) 
(* h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 16096 (* h1 h1) (* h2 
h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 49912 (* h1 h1) (* h2 h2) (* h3
 h3 h3 h3) h4 h5 (* j2 j2 j2 j2)) (* 84288 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) 
h4 h5 (* j2 j2 j2)) (* 78528 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2)
) (* 37632 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h5 j2) (* 7168 (* h1 h1) (* h2
 h2) (* h3 h3 h3 h3) h4 h5) (* 16 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 368 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2
 j2 j2 j2 j2 j2 j2)) (* 2992 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2 
j2 j2 j2 j2)) (* 12496 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2 
j2)) (* 30464 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 
45184 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2)) (* 40192 (* h1 h1)
 (* h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2)) (* 19712 (* h1 h1) (* h2 h2) (* h3 
h3 h3 h3) h4 h6 j2) (* 4096 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h6) (* 40 (* 
h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 880 (* 
h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 7272 (* h1 
h1) (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 26720 (* h1 h1) 
(* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 49472 (* h1 h1) (* h2 h2
) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2)) (* 47680 (* h1 h1) (* h2 h2) (* h3 h3 
h3 h3) (* h5 h5) (* j2 j2)) (* 22528 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h5 
h5) j2) (* 4096 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h5 h5)) (* 10 (* h1 h1) 
(* h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 304 (* h1 h1) 
(* h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 3582 (* h1 h1) (* 
h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 19728 (* h1 h1) (* h2 h2)
 (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 57720 (* h1 h1) (* h2 h2) (* h3 h3
 h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 94976 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 
h6 (* j2 j2 j2)) (* 87744 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2)) 
(* 42240 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 h6 j2) (* 8192 (* h1 h1) (* h2 
h2) (* h3 h3 h3 h3) h5 h6) (* 16 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 368 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h6 h6
) (* j2 j2 j2 j2 j2 j2 j2)) (* 2992 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h6 h6
) (* j2 j2 j2 j2 j2 j2)) (* 12496 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* 30464 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2
 j2 j2 j2)) (* 45184 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2))
 (* 40192 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2)) (* 19712 (* 
h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h6 h6) j2) (* 4096 (* h1 h1) (* h2 h2) (* h3
 h3 h3 h3) (* h6 h6)) (* 5 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 255 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* 
j2 j2 j2 j2 j2 j2 j2)) (* 3425 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* 
j2 j2 j2 j2 j2 j2)) (* 19161 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2
 j2 j2 j2 j2)) (* 54802 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 
j2 j2)) (* 86976 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 
77216 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2)) (* 35712 (* h1 h1
) (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 j2) (* 6656 (* h1 h1) (* h2 h2) (* h3 h3 
h3) (* h4 h4) h5) (* 16 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 312 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 
j2 j2 j2 j2 j2 j2)) (* 2264 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 
j2 j2 j2 j2 j2)) (* 8568 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 
j2 j2 j2)) (* 19032 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2
)) (* 25776 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2)) (* 20960
 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2)) (* 9408 (* h1 h1) (* 
h2 h2) (* h3 h3 h3) (* h4 h4) h6 j2) (* 1792 (* h1 h1) (* h2 h2) (* h3 h3 h3) 
(* h4 h4) h6) (* 7 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 415 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 
j2 j2 j2 j2)) (* 5273 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 
j2 j2 j2)) (* 28541 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2
 j2)) (* 81168 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) 
(* 129476 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 114800 
(* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2)) (* 52288 (* h1 h1) (* 
h2 h2) (* h3 h3 h3) h4 (* h5 h5) j2) (* 9472 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4
 (* h5 h5)) (* 62 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 1362 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 
j2)) (* 12158 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) 
(* 56134 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 146132
 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 221608 (* h1 h1) 
(* h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 193200 (* h1 h1) (* h2 h2) (* 
h3 h3 h3) h4 h5 h6 (* j2 j2)) (* 89344 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 h6
 j2) (* 16896 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 h6) (* 40 (* h1 h1) (* h2 
h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 728 (* h1 h1) (* 
h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 5112 (* h1 h1) (* 
h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 18984 (* h1 h1) (* h2
 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 41664 (* h1 h1) (* h2 h2) 
(* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 55968 (* h1 h1) (* h2 h2) (* h3 h3
 h3) h4 (* h6 h6) (* j2 j2 j2)) (* 45248 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* 
h6 h6) (* j2 j2)) (* 20224 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h6 h6) j2) (* 
3840 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h6 h6)) (* 70 (* h1 h1) (* h2 h2) 
(* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1120 (* h1 h1) (* h2 h2) 
(* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 7106 (* h1 h1) (* h2 h2) (* 
h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 21464 (* h1 h1) (* h2 h2) (* h3 h3
 h3) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 33952 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* 
h5 h5 h5) (* j2 j2 j2)) (* 28720 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) 
(* j2 j2)) (* 12224 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) j2) (* 2048 
(* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5 h5)) (* 25 (* h1 h1) (* h2 h2) (* h3 
h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 653 (* h1 h1) (* h2 h2) (* 
h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 6419 (* h1 h1) (* h2 h2) (* 
h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 31499 (* h1 h1) (* h2 h2) (* h3
 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 86244 (* h1 h1) (* h2 h2) (* h3 h3 
h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 136056 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* 
h5 h5) h6 (* j2 j2 j2)) (* 120896 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) h6 
(* j2 j2)) (* 55616 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) h6 j2) (* 10240 
(* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) h6) (* 61 (* h1 h1) (* h2 h2) (* h3 
h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1151 (* h1 h1) (* h2 h2) (* 
h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 8937 (* h1 h1) (* h2 h2) (* 
h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 37489 (* h1 h1) (* h2 h2) (* h3
 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 92098 (* h1 h1) (* h2 h2) (* h3 h3 
h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 135304 (* h1 h1) (* h2 h2) (* h3 h3 h3) h5 
(* h6 h6) (* j2 j2 j2)) (* 116304 (* h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* h6 h6) 
(* j2 j2)) (* 53696 (* h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* h6 h6) j2) (* 10240 
(* h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* h6 h6)) (* 24 (* h1 h1) (* h2 h2) (* h3 
h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 416 (* h1 h1) (* h2 h2) (* 
h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2848 (* h1 h1) (* h2 h2) (* 
h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 10416 (* h1 h1) (* h2 h2) (* h3
 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 22632 (* h1 h1) (* h2 h2) (* h3 h3 
h3) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 30192 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* 
h6 h6 h6) (* j2 j2 j2)) (* 24288 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6 h6) 
(* j2 j2)) (* 10816 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6 h6) j2) (* 2048 
(* h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6 h6)) (* 24 (* h1 h1) (* h2 h2) (* h3 
h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 488 (* h1 h1) (* h2 h2) (* h3 
h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 3120 (* h1 h1) (* h2 h2) (* h3 h3)
 (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 9184 (* h1 h1) (* h2 h2) (* h3 h3) (* h4
 h4 h4) h5 (* j2 j2 j2 j2)) (* 14312 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4 h4) 
h5 (* j2 j2 j2)) (* 12216 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2
)) (* 5392 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 j2) (* 960 (* h1 h1) 
(* h2 h2) (* h3 h3) (* h4 h4 h4) h5) (* 16 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 
h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 160 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 
h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 672 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4 
h4) h6 (* j2 j2 j2 j2 j2)) (* 1536 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4 h4) h6
 (* j2 j2 j2 j2)) (* 2064 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4 h4) h6 (* j2 j2
 j2)) (* 1632 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4 h4) h6 (* j2 j2)) (* 704 
(* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4 h4) h6 j2) (* 128 (* h1 h1) (* h2 h2) (* 
h3 h3) (* h4 h4 h4) h6) (* 8 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 316 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 3436 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4)
 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 16308 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 
h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 40692 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 
h4) (* h5 h5) (* j2 j2 j2 j2)) (* 57344 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) 
(* h5 h5) (* j2 j2 j2)) (* 45832 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h5 
h5) (* j2 j2)) (* 19328 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) j2) 
(* 3328 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5)) (* 34 (* h1 h1) (* h2
 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 642 (* h1 h1) (* 
h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 5006 (* h1 h1) (* 
h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 20994 (* h1 h1) (* h2
 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 50344 (* h1 h1) (* h2 h2) 
(* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 70564 (* h1 h1) (* h2 h2) (* h3 h3
) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 57008 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4)
 h5 h6 (* j2 j2)) (* 24544 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 h6 j2) (* 
4352 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 h6) (* 8 (* h1 h1) (* h2 h2) (* 
h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 144 (* h1 h1) (* h2 
h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 976 (* h1 h1) (* 
h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3456 (* h1 h1) 
(* h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 7176 (* h1 h1) 
(* h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 9072 (* h1 h1) (* h2
 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 6880 (* h1 h1) (* h2 h2) (* 
h3 h3) (* h4 h4) (* h6 h6) (* j2 j2)) (* 2880 (* h1 h1) (* h2 h2) (* h3 h3) (* 
h4 h4) (* h6 h6) j2) (* 512 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h6 h6)) 
(* 6 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 264 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 2744 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 
12716 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 31550
 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 44164 (* h1 
h1) (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2)) (* 34732 (* h1 h1) (* h2 
h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2)) (* 14256 (* h1 h1) (* h2 h2) (* h3 h3) 
h4 (* h5 h5 h5) j2) (* 2368 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5 h5)) (* 68
 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
1322 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
10476 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
43008 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
100128 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 136630 
(* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 107920 (* h1 h1) 
(* h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 45568 (* h1 h1) (* h2 h2) (* 
h3 h3) h4 (* h5 h5) h6 j2) (* 7936 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) h6
) (* 82 (* h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 1352 (* h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2
)) (* 9164 (* h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 34200 (* h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
75698 (* h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 100928 
(* h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 79232 (* h1 h1) 
(* h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 33648 (* h1 h1) (* h2 h2) (* 
h3 h3) h4 h5 (* h6 h6) j2) (* 5952 (* h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* h6 h6)
) (* 16 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 240 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 1472 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 4896 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
9744 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 11952 (* 
h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2)) (* 8864 (* h1 h1) (* h2
 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2)) (* 3648 (* h1 h1) (* h2 h2) (* h3 h3) 
h4 (* h6 h6 h6) j2) (* 640 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6 h6)) (* 20 
(* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 280 
(* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1536 (* 
h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 4032 (* h1 h1)
 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 5612 (* h1 h1) (* h2 h2
) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 4248 (* h1 h1) (* h2 h2) (* h3 h3) 
(* h5 h5 h5 h5) (* j2 j2)) (* 1648 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5 h5)
 j2) (* 256 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5 h5)) (* 17 (* h1 h1) (* h2
 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 384 (* h1 h1) (* 
h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 3212 (* h1 h1) (* 
h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 13698 (* h1 h1) (* h2
 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 33047 (* h1 h1) (* h2 h2) 
(* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 46062 (* h1 h1) (* h2 h2) (* h3 h3
) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 36460 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 
h5) h6 (* j2 j2)) (* 15152 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) h6 j2) (* 
2560 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) h6) (* 64 (* h1 h1) (* h2 h2) 
(* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1046 (* h1 h1) (* 
h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 7204 (* h1 h1)
 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 27068 (* h1 
h1) (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 59928 (* h1 
h1) (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 79678 (* h1 h1) 
(* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 62260 (* h1 h1) (* h2 
h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 26272 (* h1 h1) (* h2 h2) (* h3 
h3) (* h5 h5) (* h6 h6) j2) (* 4608 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* 
h6 h6)) (* 48 (* h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 734 (* h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 4646 (* h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 16326 (* h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 34538 (* h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 44676
 (* h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 34440 (* h1 h1) 
(* h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 14496 (* h1 h1) (* h2 h2) (* 
h3 h3) h5 (* h6 h6 h6) j2) (* 2560 (* h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6 h6)
) (* 8 (* h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 112 (* h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2))
 (* 656 (* h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
2112 (* h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 4104 
(* h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 4944 (* h1 h1)
 (* h2 h2) (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 3616 (* h1 h1) (* h2 h2) 
(* h3 h3) (* h6 h6 h6 h6) (* j2 j2)) (* 1472 (* h1 h1) (* h2 h2) (* h3 h3) (* h6
 h6 h6 h6) j2) (* 256 (* h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6 h6)) (* 14 (* h1
 h1) (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 246 (* h1 
h1) (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1344 (* h1 h1)
 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 3436 (* h1 h1) (* h2
 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 4734 (* h1 h1) (* h2 h2) h3 
(* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 3630 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4)
 (* h5 h5) (* j2 j2)) (* 1460 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) j2) 
(* 240 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) (* h5 h5)) (* 20 (* h1 h1) (* h2 h2) 
h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 156 (* h1 h1) (* h2 h2) h3 
(* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 544 (* h1 h1) (* h2 h2) h3 (* h4 h4
 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 1080 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) h5 h6
 (* j2 j2 j2 j2)) (* 1300 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2)
) (* 940 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2)) (* 376 (* h1 h1) 
(* h2 h2) h3 (* h4 h4 h4) h5 h6 j2) (* 64 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) h5
 h6) (* 3 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 95 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2
)) (* 862 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) 
(* 3522 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 
7679 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 9579 (* 
h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 6864 (* h1 h1) (* h2
 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 2628 (* h1 h1) (* h2 h2) h3 (* h4 
h4) (* h5 h5 h5) j2) (* 416 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5 h5)) (* 20
 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
326 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
2280 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
8552 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 18316 
(* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 23054 (* h1 h1
) (* h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 16872 (* h1 h1) (* h2 h2)
 h3 (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 6644 (* h1 h1) (* h2 h2) h3 (* h4 h4) 
(* h5 h5) h6 j2) (* 1088 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) h6) (* 9 (* 
h1 h1) (* h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 151 
(* h1 h1) (* h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 876 
(* h1 h1) (* h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2686 (* 
h1 h1) (* h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 4945 (* h1 h1)
 (* h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 5659 (* h1 h1) (* h2 h2
) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 3946 (* h1 h1) (* h2 h2) h3 (* h4 
h4) h5 (* h6 h6) (* j2 j2)) (* 1536 (* h1 h1) (* h2 h2) h3 (* h4 h4) h5 (* h6 h6
) j2) (* 256 (* h1 h1) (* h2 h2) h3 (* h4 h4) h5 (* h6 h6)) (* (* h1 h1) (* h2 
h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 39 (* h1 h1) (* h2 h2)
 h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 338 (* h1 h1) (* h2 h2) h3 
h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1274 (* h1 h1) (* h2 h2) h3 h4 (* 
h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 2573 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5 
h5) (* j2 j2 j2 j2)) (* 3003 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2 
j2)) (* 2032 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2)) (* 740 (* h1 
h1) (* h2 h2) h3 h4 (* h5 h5 h5 h5) j2) (* 112 (* h1 h1) (* h2 h2) h3 h4 (* h5 
h5 h5 h5)) (* 24 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 402 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2
)) (* 2738 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
9780 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 19996 (* 
h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 24218 (* h1 h1) (* h2
 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 17178 (* h1 h1) (* h2 h2) h3 h4 (* 
h5 h5 h5) h6 (* j2 j2)) (* 6592 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) h6 j2) 
(* 1056 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) h6) (* 47 (* h1 h1) (* h2 h2) h3 
h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 673 (* h1 h1) (* h2 h2) 
h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4074 (* h1 h1) (* h2 h2) 
h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 13662 (* h1 h1) (* h2 h2) h3
 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 27211 (* h1 h1) (* h2 h2) h3 h4 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 32781 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5
) (* h6 h6) (* j2 j2 j2)) (* 23404 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* h6 h6)
 (* j2 j2)) (* 9108 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* h6 h6) j2) (* 1488 
(* h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* h6 h6)) (* 18 (* h1 h1) (* h2 h2) h3 h4 
h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 242 (* h1 h1) (* h2 h2) h3 h4 h5
 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1284 (* h1 h1) (* h2 h2) h3 h4 h5 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3740 (* h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6 
h6) (* j2 j2 j2 j2 j2)) (* 6650 (* h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 
j2 j2 j2)) (* 7418 (* h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 
5072 (* h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2)) (* 1944 (* h1 h1) (* 
h2 h2) h3 h4 h5 (* h6 h6 h6) j2) (* 320 (* h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6 h6
)) (* 3 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 59 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 414
 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 1442 (* h1 
h1) (* h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 2831 (* h1 h1) (* h2 
h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 3287 (* h1 h1) (* h2 h2) h3 (* h5 
h5 h5 h5) h6 (* j2 j2 j2)) (* 2240 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) h6 (* 
j2 j2)) (* 828 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) h6 j2) (* 128 (* h1 h1) 
(* h2 h2) h3 (* h5 h5 h5 h5) h6) (* 22 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 316 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1910 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6328 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2)) (* 12402 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2)) (* 14700 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2
 j2)) (* 10338 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 3968 
(* h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* h6 h6) j2) (* 640 (* h1 h1) (* h2 h2) h3 
(* h5 h5 h5) (* h6 h6)) (* 27 (* h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 361 (* h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 2040 (* h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 6454 (* h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2)) (* 12331 (* h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2
 j2 j2)) (* 14461 (* h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) 
(* 10162 (* h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 3924 (* h1 
h1) (* h2 h2) h3 (* h5 h5) (* h6 h6 h6) j2) (* 640 (* h1 h1) (* h2 h2) h3 (* h5 
h5) (* h6 h6 h6)) (* 9 (* h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 111 (* h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2
 j2 j2)) (* 564 (* h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2))
 (* 1598 (* h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2785 
(* h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 3059 (* h1 h1) (* 
h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 2066 (* h1 h1) (* h2 h2) h3 h5 (* 
h6 h6 h6 h6) (* j2 j2)) (* 784 (* h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6 h6) j2) (* 
128 (* h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6 h6)) (* 4 (* h1 h1) (* h2 h2) (* h4 h4
 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 32 (* h1 h1) (* h2 h2) (* h4 h4 
h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 108 (* h1 h1) (* h2 h2) (* h4 h4 h4) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 200 (* h1 h1) (* h2 h2) (* h4 h4 h4) (* h5 
h5) h6 (* j2 j2 j2 j2)) (* 220 (* h1 h1) (* h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* 
j2 j2 j2)) (* 144 (* h1 h1) (* h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 52
 (* h1 h1) (* h2 h2) (* h4 h4 h4) (* h5 h5) h6 j2) (* 8 (* h1 h1) (* h2 h2) (* 
h4 h4 h4) (* h5 h5) h6) (* 3 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 38 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2)) (* 193 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2)) (* 528 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* 865 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 
j2)) (* 878 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 543 
(* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 188 (* h1 h1) (* h2 
h2) (* h4 h4) (* h5 h5 h5) h6 j2) (* 28 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5 
h5) h6) (* 2 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 32 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 182 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 532 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2)) (* 910 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2)) (* 952 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 
602 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 212 (* h1 h1
) (* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) j2) (* 32 (* h1 h1) (* h2 h2) (* h4 h4
) (* h5 h5) (* h6 h6)) (* 2 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 24 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2)) (* 118 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2
 j2)) (* 316 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
510 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 512 (* h1 h1) 
(* h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 314 (* h1 h1) (* h2 h2) h4 (* 
h5 h5 h5 h5) h6 (* j2 j2)) (* 108 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5 h5) h6 j2) 
(* 16 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5 h5) h6) (* 7 (* h1 h1) (* h2 h2) h4 (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 86 (* h1 h1) (* h2 h2) h4 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 429 (* h1 h1) (* h2 h2) h4 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1160 (* h1 h1) (* h2 h2) h4 (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1885 (* h1 h1) (* h2 h2) h4 (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2)) (* 1902 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5) (* h6
 h6) (* j2 j2 j2)) (* 1171 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 
j2)) (* 404 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5) (* h6 h6) j2) (* 60 (* h1 h1) 
(* h2 h2) h4 (* h5 h5 h5) (* h6 h6)) (* 4 (* h1 h1) (* h2 h2) h4 (* h5 h5) (* h6
 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 52 (* h1 h1) (* h2 h2) h4 (* h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 268 (* h1 h1) (* h2 h2) h4 (* h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 740 (* h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2)) (* 1220 (* h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6 h6)
 (* j2 j2 j2 j2)) (* 1244 (* h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2
 j2)) (* 772 (* h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 268 (* 
h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6 h6) j2) (* 40 (* h1 h1) (* h2 h2) h4 (* 
h5 h5) (* h6 h6 h6)) (* 2 (* h1 h1) (* h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2
 j2 j2 j2 j2 j2 j2)) (* 24 (* h1 h1) (* h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 118 (* h1 h1) (* h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 316 (* h1 h1) (* h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2)) (* 510 (* h1 h1) (* h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2))
 (* 512 (* h1 h1) (* h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 314 (* h1
 h1) (* h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 108 (* h1 h1) (* h2 h2) 
(* h5 h5 h5 h5) (* h6 h6) j2) (* 16 (* h1 h1) (* h2 h2) (* h5 h5 h5 h5) (* h6 h6
)) (* 4 (* h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 48 (* h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2))
 (* 236 (* h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
632 (* h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1020 
(* h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1024 (* h1 h1)
 (* h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 628 (* h1 h1) (* h2 h2) 
(* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 216 (* h1 h1) (* h2 h2) (* h5 h5 h5) (* 
h6 h6 h6) j2) (* 32 (* h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6 h6)) (* 2 (* h1 h1
) (* h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 24 (* h1 
h1) (* h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 118 (* h1 
h1) (* h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 316 (* h1 h1) 
(* h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 510 (* h1 h1) (* h2 
h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 512 (* h1 h1) (* h2 h2) (* h5 
h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 314 (* h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 
h6 h6) (* j2 j2)) (* 108 (* h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6 h6) j2) (* 16
 (* h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6 h6)) (* 24 (* h1 h1) h2 (* h3 h3 h3 
h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 776 (* h1 h1) h2 (* h3 h3 h3 h3
) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 7352 (* h1 h1) h2 (* h3 h3 h3 h3) 
(* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 32664 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 
h4) h5 (* j2 j2 j2 j2 j2)) (* 79728 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h5 
(* j2 j2 j2 j2)) (* 112992 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2
)) (* 92352 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2)) (* 40192 (* h1 
h1) h2 (* h3 h3 h3 h3) (* h4 h4) h5 j2) (* 7168 (* h1 h1) h2 (* h3 h3 h3 h3) (* 
h4 h4) h5) (* 32 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 416 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2
)) (* 2336 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 
7392 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 14400 (* 
h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2)) (* 17664 (* h1 h1) h2 
(* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2)) (* 13312 (* h1 h1) h2 (* h3 h3 h3 h3)
 (* h4 h4) h6 (* j2 j2)) (* 5632 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h6 j2) 
(* 1024 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h6) (* 48 (* h1 h1) h2 (* h3 h3 
h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1608 (* h1 h1) h2 (* h3 h3 
h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 15432 (* h1 h1) h2 (* h3 h3 h3 
h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 69304 (* h1 h1) h2 (* h3 h3 h3 h3) h4
 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 168888 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h5 
h5) (* j2 j2 j2 j2)) (* 234352 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 
j2 j2)) (* 183360 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2)) (* 74752 
(* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h5 h5) j2) (* 12288 (* h1 h1) h2 (* h3 h3 h3 
h3) h4 (* h5 h5)) (* 8 (* h1 h1) h2 (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 408 (* h1 h1) h2 (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 5576 (* h1 h1) h2 (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 36280 (* h1 h1) h2 (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 131856 
(* h1 h1) h2 (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 285712 (* h1 h1) h2
 (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 375616 (* h1 h1) h2 (* h3 h3 h3 h3
) h4 h5 h6 (* j2 j2 j2)) (* 292288 (* h1 h1) h2 (* h3 h3 h3 h3) h4 h5 h6 (* j2 
j2)) (* 123136 (* h1 h1) h2 (* h3 h3 h3 h3) h4 h5 h6 j2) (* 21504 (* h1 h1) h2 
(* h3 h3 h3 h3) h4 h5 h6) (* 16 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 304 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 2416 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 10704 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 29376 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 52032 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 
59648 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2)) (* 42752 (* h1 h1)
 h2 (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2)) (* 17408 (* h1 h1) h2 (* h3 h3 h3 h3
) h4 (* h6 h6) j2) (* 3072 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6)) (* 200 (* 
h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 2840 (* h1 
h1) h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 14720 (* h1 h1) h2
 (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 37312 (* h1 h1) h2 (* h3 h3
 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 50624 (* h1 h1) h2 (* h3 h3 h3 h3) (* 
h5 h5 h5) (* j2 j2 j2)) (* 37120 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* j2
 j2)) (* 13824 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5 h5) j2) (* 2048 (* h1 h1) 
h2 (* h3 h3 h3 h3) (* h5 h5 h5)) (* 120 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2400 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 19544 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 82432 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* 196016 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2
)) (* 269856 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 211200 
(* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2)) (* 86528 (* h1 h1) h2 (* h3
 h3 h3 h3) (* h5 h5) h6 j2) (* 14336 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) h6) 
(* 16 (* h1 h1) h2 (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 472 (* h1 h1) h2 (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 5208 (* h1 h1) h2 (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
29960 (* h1 h1) h2 (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 100728
 (* h1 h1) h2 (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 207328 (* h1 
h1) h2 (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 263264 (* h1 h1) h2 (* 
h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 200064 (* h1 h1) h2 (* h3 h3 h3 h3) 
h5 (* h6 h6) (* j2 j2)) (* 82944 (* h1 h1) h2 (* h3 h3 h3 h3) h5 (* h6 h6) j2) 
(* 14336 (* h1 h1) h2 (* h3 h3 h3 h3) h5 (* h6 h6)) (* 16 (* h1 h1) h2 (* h3 h3 
h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 272 (* h1 h1) h2 (* h3 h3
 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2000 (* h1 h1) h2 (* h3 h3 
h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 8368 (* h1 h1) h2 (* h3 h3 h3 
h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 21984 (* h1 h1) h2 (* h3 h3 h3 h3) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 37632 (* h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6 
h6) (* j2 j2 j2 j2)) (* 41984 (* h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2
 j2)) (* 29440 (* h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2)) (* 11776 (* 
h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6 h6) j2) (* 2048 (* h1 h1) h2 (* h3 h3 h3 h3) 
(* h6 h6 h6)) (* 28 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 680 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2
 j2)) (* 5584 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) 
(* 22120 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 48580 
(* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 62320 (* h1 h1) h2
 (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 46416 (* h1 h1) h2 (* h3 h3 h3) 
(* h4 h4 h4) h5 (* j2 j2)) (* 18560 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h5 j2
) (* 3072 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h5) (* 16 (* h1 h1) h2 (* h3 h3
 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 192 (* h1 h1) h2 (* h3 h3 
h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 992 (* h1 h1) h2 (* h3 h3 h3) 
(* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 2880 (* h1 h1) h2 (* h3 h3 h3) (* h4 
h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 5136 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h6 
(* j2 j2 j2 j2)) (* 5760 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2))
 (* 3968 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2)) (* 1536 (* h1 h1) 
h2 (* h3 h3 h3) (* h4 h4 h4) h6 j2) (* 256 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4
) h6) (* (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 146 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 3010 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 
j2 j2 j2)) (* 22644 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2
 j2 j2)) (* 84745 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 
j2)) (* 177962 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) 
(* 218980 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 156352 
(* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 59840 (* h1 h1) h2 
(* h3 h3 h3) (* h4 h4) (* h5 h5) j2) (* 9472 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4)
 (* h5 h5)) (* 12 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2
 j2 j2 j2)) (* 468 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 5720 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 34288 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)
) (* 115124 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 
229948 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 278472 (* 
h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 200096 (* h1 h1) h2 (* 
h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 78272 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4
) h5 h6 j2) (* 12800 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 h6) (* 8 (* h1 h1) 
h2 (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 160 (* h1
 h1) h2 (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1264 
(* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 5408 
(* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 14088 
(* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 23424 (* h1
 h1) h2 (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 25024 (* h1 h1) h2 
(* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 16640 (* h1 h1) h2 (* h3 h3 h3
) (* h4 h4) (* h6 h6) (* j2 j2)) (* 6272 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* 
h6 h6) j2) (* 1024 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h6 h6)) (* 94 (* h1 h1
) h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2116 (* h1 h1)
 h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 16116 (* h1 h1) h2
 (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 60664 (* h1 h1) h2 (* h3
 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 127406 (* h1 h1) h2 (* h3 h3 h3) 
h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 155364 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5
 h5) (* j2 j2 j2)) (* 108768 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2)
) (* 40384 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5 h5) j2) (* 6144 (* h1 h1) h2 
(* h3 h3 h3) h4 (* h5 h5 h5)) (* 22 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 886 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6
 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 11008 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6
 (* j2 j2 j2 j2 j2 j2 j2)) (* 66324 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 222942 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6 (* j2
 j2 j2 j2 j2)) (* 443558 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 
j2)) (* 531500 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 375280
 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 143360 (* h1 h1) h2 (* 
h3 h3 h3) h4 (* h5 h5) h6 j2) (* 22784 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6
) (* 56 (* h1 h1) h2 (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 1228 (* h1 h1) h2 (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2))
 (* 11352 (* h1 h1) h2 (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 57744 (* h1 h1) h2 (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
175552 (* h1 h1) h2 (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 329780 
(* h1 h1) h2 (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 384304 (* h1 h1) 
h2 (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 269616 (* h1 h1) h2 (* h3 h3 h3
) h4 h5 (* h6 h6) (* j2 j2)) (* 104000 (* h1 h1) h2 (* h3 h3 h3) h4 h5 (* h6 h6)
 j2) (* 16896 (* h1 h1) h2 (* h3 h3 h3) h4 h5 (* h6 h6)) (* 16 (* h1 h1) h2 (* 
h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 272 (* h1 h1) h2 
(* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1952 (* h1 h1) h2 
(* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 7840 (* h1 h1) h2 (* 
h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 19536 (* h1 h1) h2 (* h3 h3 
h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 31440 (* h1 h1) h2 (* h3 h3 h3) h4 
(* h6 h6 h6) (* j2 j2 j2 j2)) (* 32768 (* h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6 h6)
 (* j2 j2 j2)) (* 21376 (* h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2)) (* 
7936 (* h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6 h6) j2) (* 1280 (* h1 h1) h2 (* h3 h3
 h3) h4 (* h6 h6 h6)) (* 100 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 
j2 j2 j2 j2 j2)) (* 1320 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 
j2 j2 j2)) (* 6140 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2))
 (* 13736 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 16496 
(* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 10880 (* h1 h1) h2 
(* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2)) (* 3712 (* h1 h1) h2 (* h3 h3 h3) (* h5 
h5 h5 h5) j2) (* 512 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5 h5)) (* 160 (* h1 h1)
 h2 (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2760 (* h1 h1) 
h2 (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 19232 (* h1 h1) h2 
(* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 70128 (* h1 h1) h2 (* h3 
h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 145856 (* h1 h1) h2 (* h3 h3 h3) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 177800 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5
) h6 (* j2 j2 j2)) (* 124992 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2)
) (* 46720 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) h6 j2) (* 7168 (* h1 h1) h2 
(* h3 h3 h3) (* h5 h5 h5) h6) (* 33 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 856 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 8510 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 45008 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 140361 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 267816 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2)) (* 313896 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* h6 h6) 
(* j2 j2 j2)) (* 219392 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2))
 (* 83584 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* h6 h6) j2) (* 13312 (* h1 h1) 
h2 (* h3 h3 h3) (* h5 h5) (* h6 h6)) (* 44 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 788 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6312 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 29040 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 82548 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2)) (* 148412 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2
 j2 j2)) (* 168152 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 
115936 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 44288 (* h1 h1) 
h2 (* h3 h3 h3) h5 (* h6 h6 h6) j2) (* 7168 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 
h6 h6)) (* 8 (* h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 128 (* h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2
 j2)) (* 880 (* h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2))
 (* 3424 (* h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
8328 (* h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 13152 (* 
h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 13504 (* h1 h1) h2 
(* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 8704 (* h1 h1) h2 (* h3 h3 h3) (* 
h6 h6 h6 h6) (* j2 j2)) (* 3200 (* h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6 h6) j2) 
(* 512 (* h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6 h6)) (* 24 (* h1 h1) h2 (* h3 h3) 
(* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 312 (* h1 h1) h2 (* h3 h3) (* h4
 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 1440 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4 
h4) h5 (* j2 j2 j2 j2 j2)) (* 3312 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4 h4) h5 (* 
j2 j2 j2 j2)) (* 4248 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2)) 
(* 3096 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2)) (* 1200 (* h1 h1) 
h2 (* h3 h3) (* h4 h4 h4 h4) h5 j2) (* 192 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4 h4
) h5) (* 32 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 688 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 
j2 j2)) (* 5024 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 
j2)) (* 17728 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) 
(* 34848 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 40304
 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 27296 (* h1 h1) 
h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 10016 (* h1 h1) h2 (* h3 h3) 
(* h4 h4 h4) (* h5 h5) j2) (* 1536 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) (* h5 h5)
) (* 40 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 584 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
3760 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 12880 
(* h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 25416 (* h1 h1)
 h2 (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 29864 (* h1 h1) h2 (* h3 h3
) (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 20640 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) 
h5 h6 (* j2 j2)) (* 7744 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 h6 j2) (* 1216 
(* h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 h6) (* (* h1 h1) h2 (* h3 h3) (* h4 h4) 
(* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 99 (* h1 h1) h2 (* h3 h3) (* h4 
h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1684 (* h1 h1) h2 (* h3 h3) (* 
h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 10794 (* h1 h1) h2 (* h3 h3) 
(* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 35081 (* h1 h1) h2 (* h3 h3) 
(* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 64895 (* h1 h1) h2 (* h3 h3) (* h4
 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 71298 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* 
h5 h5 h5) (* j2 j2 j2)) (* 46052 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) 
(* j2 j2)) (* 16144 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) j2) (* 2368 
(* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5 h5)) (* 15 (* h1 h1) h2 (* h3 h3) (* 
h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 503 (* h1 h1) h2 (* h3 h3
) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 5466 (* h1 h1) h2 (* h3
 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 29410 (* h1 h1) h2 (* 
h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 88819 (* h1 h1) h2 (* h3
 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 160003 (* h1 h1) h2 (* h3 h3)
 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 175620 (* h1 h1) h2 (* h3 h3) (* h4 
h4) (* h5 h5) h6 (* j2 j2 j2)) (* 115124 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 
h5) h6 (* j2 j2)) (* 41392 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) h6 j2) (* 
6272 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) h6) (* 16 (* h1 h1) h2 (* h3 h3)
 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 320 (* h1 h1) h2 (* 
h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2724 (* h1 h1) h2 
(* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 13040 (* h1 h1) h2
 (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 37560 (* h1 h1) h2 
(* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 66768 (* h1 h1) h2 (* h3
 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 73508 (* h1 h1) h2 (* h3 h3) (* 
h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 48736 (* h1 h1) h2 (* h3 h3) (* h4 h4) h5 
(* h6 h6) (* j2 j2)) (* 17808 (* h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* h6 h6) j2) 
(* 2752 (* h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* h6 h6)) (* 24 (* h1 h1) h2 (* h3 
h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 512 (* h1 h1) h2 (* h3 h3
) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 3568 (* h1 h1) h2 (* h3 h3) h4
 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 12092 (* h1 h1) h2 (* h3 h3) h4 (* h5
 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 22748 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5 h5
) (* j2 j2 j2 j2)) (* 24964 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 
j2)) (* 15884 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2)) (* 5424 (* h1
 h1) h2 (* h3 h3) h4 (* h5 h5 h5 h5) j2) (* 768 (* h1 h1) h2 (* h3 h3) h4 (* h5 
h5 h5 h5)) (* 14 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 506 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 5668 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2)) (* 30364 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 90534 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 160402
 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 172552 (* h1 h1) 
h2 (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 110488 (* h1 h1) h2 (* h3 h3) 
h4 (* h5 h5 h5) h6 (* j2 j2)) (* 38688 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) h6
 j2) (* 5696 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) h6) (* 54 (* h1 h1) h2 (* h3
 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1148 (* h1 h1) h2
 (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 9922 (* h1 h1)
 h2 (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 46484 (* h1 h1
) h2 (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 129082 (* h1 h1)
 h2 (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 220836 (* h1 h1) h2 
(* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 234686 (* h1 h1) h2 (* h3 
h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 150764 (* h1 h1) h2 (* h3 h3) h4 (* 
h5 h5) (* h6 h6) (* j2 j2)) (* 53552 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* h6 
h6) j2) (* 8064 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* h6 h6)) (* 32 (* h1 h1) 
h2 (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 520 (* h1 h1)
 h2 (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3792 (* h1 h1) 
h2 (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 16048 (* h1 h1) h2 
(* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 42240 (* h1 h1) h2 (* h3 
h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 70536 (* h1 h1) h2 (* h3 h3) h4 h5
 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 74416 (* h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6
) (* j2 j2 j2)) (* 47936 (* h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2)) 
(* 17184 (* h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6) j2) (* 2624 (* h1 h1) h2 (* 
h3 h3) h4 h5 (* h6 h6 h6)) (* 40 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) h6 (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 648 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2)) (* 4168 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2)) (* 13800 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 
j2)) (* 25856 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 
28464 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 18224 (* h1 h1)
 h2 (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 6272 (* h1 h1) h2 (* h3 h3) (* h5
 h5 h5 h5) h6 j2) (* 896 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) h6) (* 19 (* h1 
h1) h2 (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 459 
(* h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
4194 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
20070 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
56199 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 96207
 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 101652 (* h1 
h1) h2 (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 64560 (* h1 h1) h2 (* 
h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 22560 (* h1 h1) h2 (* h3 h3) (* h5 
h5 h5) (* h6 h6) j2) (* 3328 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* h6 h6)) (* 
39 (* h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (* 677 (* h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 5144 (* h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2
)) (* 22098 (* h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2))
 (* 57991 (* h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
95681 (* h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 99370 
(* h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 62936 (* h1 h1) 
h2 (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 22176 (* h1 h1) h2 (* h3 h3) 
(* h5 h5) (* h6 h6 h6) j2) (* 3328 (* h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6 h6)
) (* 16 (* h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 240 (* h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 1628 (* h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
6456 (* h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 16120 
(* h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 25872 (* h1 h1)
 h2 (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 26524 (* h1 h1) h2 (* h3 h3
) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 16744 (* h1 h1) h2 (* h3 h3) h5 (* h6 h6 
h6 h6) (* j2 j2)) (* 5920 (* h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6 h6) j2) (* 896 
(* h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6 h6)) (* 12 (* h1 h1) h2 h3 (* h4 h4 h4 h4)
 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 144 (* h1 h1) h2 h3 (* h4 h4 h4 h4) (* 
h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 588 (* h1 h1) h2 h3 (* h4 h4 h4 h4) (* h5 h5) 
(* j2 j2 j2 j2 j2)) (* 1200 (* h1 h1) h2 h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 
j2 j2)) (* 1380 (* h1 h1) h2 h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 912 
(* h1 h1) h2 h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2)) (* 324 (* h1 h1) h2 h3 (* 
h4 h4 h4 h4) (* h5 h5) j2) (* 48 (* h1 h1) h2 h3 (* h4 h4 h4 h4) (* h5 h5)) (* 
10 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 184
 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1158 (* 
h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 3572 (* h1 h1) 
h2 h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 6230 (* h1 h1) h2 h3 (* 
h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 6480 (* h1 h1) h2 h3 (* h4 h4 h4) (* 
h5 h5 h5) (* j2 j2 j2)) (* 3994 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 
j2)) (* 1348 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5 h5) j2) (* 192 (* h1 h1) h2 
h3 (* h4 h4 h4) (* h5 h5 h5)) (* 20 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 272 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 1628 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2)) (* 5064 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 
j2 j2 j2)) (* 9020 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) 
(* 9600 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 6052 (* h1 h1
) h2 h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 2088 (* h1 h1) h2 h3 (* h4 h4 h4
) (* h5 h5) h6 j2) (* 304 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) h6) (* 6 (* h1 
h1) h2 h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 116 (* h1 h1
) h2 h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 722 (* h1 h1) h2 
h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2192 (* h1 h1) h2 h3 (* 
h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 3770 (* h1 h1) h2 h3 (* h4 h4) (* 
h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 3876 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5 h5) 
(* j2 j2 j2)) (* 2366 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 
792 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5 h5) j2) (* 112 (* h1 h1) h2 h3 (* h4 
h4) (* h5 h5 h5 h5)) (* 4 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 130 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 1328 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2)) (* 6506 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2)) (* 17680 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) 
(* 28694 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 28560 (* 
h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 17118 (* h1 h1) h2 h3 
(* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 5676 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 
h5) h6 j2) (* 800 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) h6) (* 8 (* h1 h1) h2 
h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 152 (* h1 h1
) h2 h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1218 (* h1
 h1) h2 h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 5446 (* h1
 h1) h2 h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 14408 (* h1 
h1) h2 h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 23348 (* h1 h1) 
h2 h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 23442 (* h1 h1) h2 h3 
(* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 14238 (* h1 h1) h2 h3 (* h4 h4) 
(* h5 h5) (* h6 h6) (* j2 j2)) (* 4796 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* h6
 h6) j2) (* 688 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* h6 h6)) (* 2 (* h1 h1) h2
 h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 64 (* h1 h1) h2 h3 
h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 642 (* h1 h1) h2 h3 h4 (* 
h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 3056 (* h1 h1) h2 h3 h4 (* h5 h5 h5
 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 8086 (* h1 h1) h2 h3 h4 (* h5 h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2)) (* 12832 (* h1 h1) h2 h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2))
 (* 12534 (* h1 h1) h2 h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 7392 (* h1 h1) 
h2 h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 2416 (* h1 h1) h2 h3 h4 (* h5 h5 h5 h5
) h6 j2) (* 336 (* h1 h1) h2 h3 h4 (* h5 h5 h5 h5) h6) (* 16 (* h1 h1) h2 h3 h4 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 308 (* h1 h1) h2 h3 h4
 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2444 (* h1 h1) h2 h3 h4 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 10416 (* h1 h1) h2 h3 h4 (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 26136 (* h1 h1) h2 h3 h4 (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 40436 (* h1 h1) h2 h3 h4 (* h5 h5 h5) (* h6
 h6) (* j2 j2 j2 j2)) (* 39068 (* h1 h1) h2 h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 
j2 j2)) (* 22984 (* h1 h1) h2 h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 7536 
(* h1 h1) h2 h3 h4 (* h5 h5 h5) (* h6 h6) j2) (* 1056 (* h1 h1) h2 h3 h4 (* h5 
h5 h5) (* h6 h6)) (* 16 (* h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 244 (* h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 1668 (* h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 6584 (* h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 15976 (* h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 24436 (* h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 23604 (* 
h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 13968 (* h1 h1) h2 h3 h4
 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 4624 (* h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6
 h6) j2) (* 656 (* h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6 h6)) (* 3 (* h1 h1) h2 h3 
(* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 66 (* h1 h1) h2 h3 
(* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 553 (* h1 h1) h2 h3 
(* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2384 (* h1 h1) h2 h3 (* 
h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 5949 (* h1 h1) h2 h3 (* h5 h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 9098 (* h1 h1) h2 h3 (* h5 h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2)) (* 8671 (* h1 h1) h2 h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 
j2 j2)) (* 5028 (* h1 h1) h2 h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 1624 (* 
h1 h1) h2 h3 (* h5 h5 h5 h5) (* h6 h6) j2) (* 224 (* h1 h1) h2 h3 (* h5 h5 h5 h5
) (* h6 h6)) (* 12 (* h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 188 (* h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 1300 (* h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 5068 (* h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2))
 (* 12028 (* h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 17972
 (* h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 16988 (* h1 h1) 
h2 h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 9860 (* h1 h1) h2 h3 (* h5 h5 
h5) (* h6 h6 h6) (* j2 j2)) (* 3208 (* h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6 h6) j2
) (* 448 (* h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6 h6)) (* 8 (* h1 h1) h2 h3 (* h5 
h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 112 (* h1 h1) h2 h3 (* h5
 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 710 (* h1 h1) h2 h3 (* h5 
h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2622 (* h1 h1) h2 h3 (* h5 h5) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6044 (* h1 h1) h2 h3 (* h5 h5) (* h6 
h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 8908 (* h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6 h6) 
(* j2 j2 j2 j2)) (* 8382 (* h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2))
 (* 4870 (* h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 1592 (* h1 h1) 
h2 h3 (* h5 h5) (* h6 h6 h6 h6) j2) (* 224 (* h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6
 h6)) (* 2 (* h1 h1) h2 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 18 (* h1 h1) h2 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
70 (* h1 h1) h2 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 154 (* h1
 h1) h2 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 210 (* h1 h1) h2 (* 
h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 182 (* h1 h1) h2 (* h4 h4 h4) (* 
h5 h5 h5) h6 (* j2 j2 j2)) (* 98 (* h1 h1) h2 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2
 j2)) (* 30 (* h1 h1) h2 (* h4 h4 h4) (* h5 h5 h5) h6 j2) (* 4 (* h1 h1) h2 (* 
h4 h4 h4) (* h5 h5 h5) h6) (* 2 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 18 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2)) (* 70 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2)) (* 154 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
210 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 182 (* h1 h1) 
h2 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 98 (* h1 h1) h2 (* h4 h4) (* h5
 h5 h5 h5) h6 (* j2 j2)) (* 30 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5 h5) h6 j2) (* 
4 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5 h5) h6) (* (* h1 h1) h2 (* h4 h4) (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 17 (* h1 h1) h2 (* h4 h4) (* h5
 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 107 (* h1 h1) h2 (* h4 h4) (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 357 (* h1 h1) h2 (* h4 h4) (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 721 (* h1 h1) h2 (* h4 h4) (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 931 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2)) (* 777 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2)) (* 407 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2)) 
(* 122 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5) (* h6 h6) j2) (* 16 (* h1 h1) h2 (* 
h4 h4) (* h5 h5 h5) (* h6 h6)) (* (* h1 h1) h2 h4 (* h5 h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 15 (* h1 h1) h2 h4 (* h5 h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 89 (* h1 h1) h2 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 287 (* h1 h1) h2 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2
 j2 j2 j2)) (* 567 (* h1 h1) h2 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2))
 (* 721 (* h1 h1) h2 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 595 (* h1 
h1) h2 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 309 (* h1 h1) h2 h4 (* h5 
h5 h5 h5) (* h6 h6) (* j2 j2)) (* 92 (* h1 h1) h2 h4 (* h5 h5 h5 h5) (* h6 h6) 
j2) (* 12 (* h1 h1) h2 h4 (* h5 h5 h5 h5) (* h6 h6)) (* 2 (* h1 h1) h2 h4 (* h5 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 28 (* h1 h1) h2 h4 (* h5 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 160 (* h1 h1) h2 h4 (* h5 h5
 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 504 (* h1 h1) h2 h4 (* h5 h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 980 (* h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6
 h6) (* j2 j2 j2 j2 j2)) (* 1232 (* h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2
 j2 j2 j2)) (* 1008 (* h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 
520 (* h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 154 (* h1 h1) h2 h4 
(* h5 h5 h5) (* h6 h6 h6) j2) (* 20 (* h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6 h6)) 
(* (* h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
13 (* h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 71 
(* h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 217 (* h1
 h1) h2 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 413 (* h1 h1) h2 
(* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 511 (* h1 h1) h2 (* h5 h5 h5
 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 413 (* h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6 
h6) (* j2 j2 j2)) (* 211 (* h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2)) 
(* 62 (* h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6 h6) j2) (* 8 (* h1 h1) h2 (* h5 h5 
h5 h5) (* h6 h6 h6)) (* (* h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 13 (* h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2
 j2 j2 j2 j2)) (* 71 (* h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2
 j2 j2)) (* 217 (* h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2))
 (* 413 (* h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 511 (* 
h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 413 (* h1 h1) h2 (* 
h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 211 (* h1 h1) h2 (* h5 h5 h5) (* h6 
h6 h6 h6) (* j2 j2)) (* 62 (* h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6 h6) j2) (* 8 
(* h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6 h6)) (* 32 (* h1 h1) (* h3 h3 h3 h3) (* h4
 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 512 (* h1 h1) (* h3 h3 h3 h3) (* h4 
h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 3200 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4 
h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 10560 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4 h4) h5
 (* j2 j2 j2 j2 j2)) (* 20448 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2
 j2 j2)) (* 24000 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 
16768 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2)) (* 6400 (* h1 h1) (* 
h3 h3 h3 h3) (* h4 h4 h4) h5 j2) (* 1024 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4 h4) 
h5) (* 4 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 200 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 2696 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 
j2 j2 j2)) (* 16416 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2
 j2 j2)) (* 53780 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 
j2)) (* 102424 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) 
(* 116320 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 77312 
(* h1 h1) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 27648 (* h1 h1) (* 
h3 h3 h3 h3) (* h4 h4) (* h5 h5) j2) (* 4096 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4)
 (* h5 h5)) (* 16 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2
 j2 j2 j2)) (* 512 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 5088 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 25024 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)
) (* 71184 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 
124608 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 136064 (* 
h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 90112 (* h1 h1) (* h3 h3
 h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 33024 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) 
h5 h6 j2) (* 5120 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 h6) (* 40 (* h1 h1) (* 
h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 808 (* h1 h1) (* h3
 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 6280 (* h1 h1) (* h3 h3 
h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 24216 (* h1 h1) (* h3 h3 h3 h3)
 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 51024 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5
 h5 h5) (* j2 j2 j2 j2)) (* 60864 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* 
j2 j2 j2)) (* 40832 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2)) (* 
14336 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5 h5) j2) (* 2048 (* h1 h1) (* h3 h3 
h3 h3) h4 (* h5 h5 h5)) (* 32 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2
 j2 j2 j2 j2 j2 j2 j2)) (* 1236 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 13436 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2)) (* 69876 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 
j2 j2 j2 j2)) (* 204580 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2
 j2)) (* 359544 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 
385280 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 245376 (* h1 
h1) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 84992 (* h1 h1) (* h3 h3 h3 h3
) h4 (* h5 h5) h6 j2) (* 12288 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) h6) (* 96 
(* h1 h1) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
1776 (* h1 h1) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
13552 (* h1 h1) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
56752 (* h1 h1) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 144816
 (* h1 h1) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 234528 (* h1 
h1) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 241728 (* h1 h1) (* h3 
h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 153216 (* h1 h1) (* h3 h3 h3 h3) h4 
h5 (* h6 h6) (* j2 j2)) (* 54272 (* h1 h1) (* h3 h3 h3 h3) h4 h5 (* h6 h6) j2) 
(* 8192 (* h1 h1) (* h3 h3 h3 h3) h4 h5 (* h6 h6)) (* 200 (* h1 h1) (* h3 h3 h3 
h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3280 (* h1 h1) (* h3 h3 h3 
h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 20888 (* h1 h1) (* h3 h3 h3 h3)
 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 68688 (* h1 h1) (* h3 h3 h3 h3) (* h5
 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 128448 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5 h5) 
h6 (* j2 j2 j2 j2)) (* 140544 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2
 j2)) (* 88576 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2)) (* 29696 (* 
h1 h1) (* h3 h3 h3 h3) (* h5 h5 h5) h6 j2) (* 4096 (* h1 h1) (* h3 h3 h3 h3) (* 
h5 h5 h5) h6) (* 60 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 1332 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2
 j2 j2 j2 j2 j2 j2)) (* 11884 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 55852 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 153720 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* 259200 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* 
j2 j2 j2 j2)) (* 269760 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 
j2)) (* 168192 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 57344
 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) j2) (* 8192 (* h1 h1) (* h3 h3 h3
 h3) (* h5 h5) (* h6 h6)) (* 80 (* h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 1296 (* h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 8976 (* h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 34928 (* h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 84192 (* h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 
j2 j2)) (* 130368 (* h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 
129664 (* h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 79872 (* h1 h1
) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 27648 (* h1 h1) (* h3 h3 h3 h3) 
h5 (* h6 h6 h6) j2) (* 4096 (* h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6 h6)) (* 16 (* 
h1 h1) (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 240 (* h1
 h1) (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 1376 (* h1 h1)
 (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 4128 (* h1 h1) (* h3 
h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 7248 (* h1 h1) (* h3 h3 h3) (* 
h4 h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 7728 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4 h4) 
h5 (* j2 j2 j2)) (* 4928 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2)) 
(* 1728 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4 h4) h5 j2) (* 256 (* h1 h1) (* h3 h3 
h3) (* h4 h4 h4 h4) h5) (* 6 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2
 j2 j2 j2 j2 j2 j2 j2 j2)) (* 222 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2516 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h5 
h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 13076 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h5
 h5) (* j2 j2 j2 j2 j2 j2)) (* 37014 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h5 
h5) (* j2 j2 j2 j2 j2)) (* 61902 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) 
(* j2 j2 j2 j2)) (* 62928 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2
 j2)) (* 38208 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 12736
 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) j2) (* 1792 (* h1 h1) (* h3 h3 h3
) (* h4 h4 h4) (* h5 h5)) (* 8 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 264 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 2544 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 
j2 j2 j2 j2 j2 j2)) (* 11824 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 
j2 j2 j2 j2)) (* 31336 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 
j2)) (* 50728 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 
51104 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 31264 (* h1 h1)
 (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2)) (* 10624 (* h1 h1) (* h3 h3 h3) (* 
h4 h4 h4) h5 h6 j2) (* 1536 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 h6) (* 8 (* 
h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
264 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 2912 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 15184 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) 
(* 43464 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 
73320 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 74704 
(* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 45120 (* h1 h1) 
(* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 14848 (* h1 h1) (* h3 h3 h3) 
(* h4 h4) (* h5 h5 h5) j2) (* 2048 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5)
) (* 66 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2
 j2)) (* 1784 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 15992 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2)) (* 71420 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2
 j2 j2)) (* 183222 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 
j2)) (* 286988 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) 
(* 278992 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 164224 
(* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 53568 (* h1 h1) (* 
h3 h3 h3) (* h4 h4) (* h5 h5) h6 j2) (* 7424 (* h1 h1) (* h3 h3 h3) (* h4 h4) 
(* h5 h5) h6) (* 56 (* h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 1088 (* h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2
 j2 j2 j2 j2 j2 j2)) (* 8288 (* h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2
 j2 j2 j2 j2 j2 j2)) (* 33632 (* h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 81624 (* h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2
 j2 j2 j2 j2)) (* 124320 (* h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 
j2 j2)) (* 119824 (* h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2)) 
(* 70912 (* h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 23488 (* h1
 h1) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) j2) (* 3328 (* h1 h1) (* h3 h3 h3) (* 
h4 h4) h5 (* h6 h6)) (* 20 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 384 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 
j2 j2 j2 j2)) (* 2776 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 
j2 j2)) (* 9696 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) 
(* 18228 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 19488 (* 
h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2)) (* 11872 (* h1 h1) (* h3 h3
 h3) h4 (* h5 h5 h5 h5) (* j2 j2)) (* 3840 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5
 h5) j2) (* 512 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5 h5)) (* 56 (* h1 h1) (* h3
 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1536 (* h1 h1) (* 
h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 13904 (* h1 h1) (* 
h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 62656 (* h1 h1) (* h3 
h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 161816 (* h1 h1) (* h3 h3 h3
) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 253824 (* h1 h1) (* h3 h3 h3) h4 (* 
h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 245408 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) 
h6 (* j2 j2 j2)) (* 142592 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2)) 
(* 45568 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) h6 j2) (* 6144 (* h1 h1) (* h3 
h3 h3) h4 (* h5 h5 h5) h6) (* 210 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3822 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 28292 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 112988 (* h1 h1) (* h3 h3 h3) h4 (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 270202 (* h1 h1) (* h3 h3 h3) h4 (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 404278 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2)) (* 381232 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* h6 
h6) (* j2 j2 j2)) (* 219904 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 
j2)) (* 70784 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) j2) (* 9728 (* h1 h1
) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6)) (* 88 (* h1 h1) (* h3 h3 h3) h4 h5 (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1448 (* h1 h1) (* h3 h3 h3) h4 h5 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 9904 (* h1 h1) (* h3 h3 h3) h4 h5 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 37296 (* h1 h1) (* h3 h3 h3) h4 h5 (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 85752 (* h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6 h6)
 (* j2 j2 j2 j2 j2)) (* 125448 (* h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 
j2 j2 j2)) (* 117248 (* h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 
67744 (* h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2)) (* 22016 (* h1 h1) 
(* h3 h3 h3) h4 h5 (* h6 h6 h6) j2) (* 3072 (* h1 h1) (* h3 h3 h3) h4 h5 (* h6 
h6 h6)) (* 100 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2
 j2)) (* 1540 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)
) (* 9004 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
26780 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 45008 (* 
h1 h1) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 44480 (* h1 h1) (* h3
 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 25600 (* h1 h1) (* h3 h3 h3) (* h5 
h5 h5 h5) h6 (* j2 j2)) (* 7936 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5 h5) h6 j2) 
(* 1024 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5 h5) h6) (* 80 (* h1 h1) (* h3 h3 h3) 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1536 (* h1 h1) (* h3 
h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 11904 (* h1 h1) 
(* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 49184 (* h1 h1)
 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 120240 (* h1 h1) 
(* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 181728 (* h1 h1) (* 
h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 171136 (* h1 h1) (* h3 h3 
h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 97536 (* h1 h1) (* h3 h3 h3) (* h5 
h5 h5) (* h6 h6) (* j2 j2)) (* 30720 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5) (* h6 
h6) j2) (* 4096 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6)) (* 150 (* h1 h1) 
(* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2260 (* 
h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 14816
 (* h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
54644 (* h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
123994 (* h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
179192 (* h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 165168 
(* h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 93888 (* h1 h1) 
(* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 29952 (* h1 h1) (* h3 h3 h3) 
(* h5 h5) (* h6 h6 h6) j2) (* 4096 (* h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6)
) (* 40 (* h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 608 (* h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 3920 (* h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
14112 (* h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 31336 
(* h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 44608 (* h1 h1)
 (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 40800 (* h1 h1) (* h3 h3 h3
) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 23168 (* h1 h1) (* h3 h3 h3) h5 (* h6 h6 
h6 h6) (* j2 j2)) (* 7424 (* h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6 h6) j2) (* 1024 
(* h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6 h6)) (* 16 (* h1 h1) (* h3 h3) (* h4 h4 h4
 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 224 (* h1 h1) (* h3 h3) (* h4 h4 
h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1168 (* h1 h1) (* h3 h3) (* h4 h4 
h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 3168 (* h1 h1) (* h3 h3) (* h4 h4 h4 
h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 5040 (* h1 h1) (* h3 h3) (* h4 h4 h4 h4) 
(* h5 h5) (* j2 j2 j2 j2)) (* 4896 (* h1 h1) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5)
 (* j2 j2 j2)) (* 2864 (* h1 h1) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2)) 
(* 928 (* h1 h1) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) j2) (* 128 (* h1 h1) (* h3 
h3) (* h4 h4 h4 h4) (* h5 h5)) (* 4 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5
) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 124 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1240 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* 
h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 5688 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* 
h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 14308 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5
 h5 h5) (* j2 j2 j2 j2 j2)) (* 21484 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5 
h5) (* j2 j2 j2 j2)) (* 19824 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* 
j2 j2 j2)) (* 11040 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2)) (* 
3408 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) j2) (* 448 (* h1 h1) (* h3 h3
) (* h4 h4 h4) (* h5 h5 h5)) (* 10 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6
 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 280 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2394 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 9976 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 23838 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5
 h5) h6 (* j2 j2 j2 j2 j2)) (* 35000 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) 
h6 (* j2 j2 j2 j2)) (* 32190 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2
 j2 j2)) (* 18104 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 
5696 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 j2) (* 768 (* h1 h1) (* h3 h3
) (* h4 h4 h4) (* h5 h5) h6) (* 2 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 64 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5 
h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 666 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 3192 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 
h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 8278 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5 
h5) (* j2 j2 j2 j2 j2)) (* 12640 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) 
(* j2 j2 j2 j2)) (* 11726 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2
 j2)) (* 6504 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 1984 
(* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) j2) (* 256 (* h1 h1) (* h3 h3) (* 
h4 h4) (* h5 h5 h5 h5)) (* 40 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 952 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 7596 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 30264 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5
 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 69632 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2)) (* 98584 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) 
h6 (* j2 j2 j2 j2)) (* 87388 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2
 j2 j2)) (* 47320 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 
14320 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 j2) (* 1856 (* h1 h1) (* h3 
h3) (* h4 h4) (* h5 h5 h5) h6) (* 70 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1162 (* h1 h1) (* h3 h3) (* h4 h4) (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 7784 (* h1 h1) (* h3 h3) (* h4 
h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 28196 (* h1 h1) (* h3 h3) 
(* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 61654 (* h1 h1) (* h3 h3
) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 85250 (* h1 h1) (* h3 h3)
 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 75132 (* h1 h1) (* h3 h3) (* 
h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 40944 (* h1 h1) (* h3 h3) (* h4 h4) 
(* h5 h5) (* h6 h6) (* j2 j2)) (* 12576 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) 
(* h6 h6) j2) (* 1664 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6)) (* 14 
(* h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 370
 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3120 
(* h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 12900 (* 
h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 30318 (* h1 h1)
 (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 43274 (* h1 h1) (* h3 h3
) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 38260 (* h1 h1) (* h3 h3) h4 (* h5 
h5 h5 h5) h6 (* j2 j2 j2)) (* 20480 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) h6 
(* j2 j2)) (* 6080 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) h6 j2) (* 768 (* h1 h1
) (* h3 h3) h4 (* h5 h5 h5 h5) h6) (* 116 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1944 (* h1 h1) (* h3 h3) h4 (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 13036 (* h1 h1) (* h3 h3) h4 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 46952 (* h1 h1) (* h3 h3) h4
 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 101452 (* h1 h1) (* h3 h3) h4 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 137896 (* h1 h1) (* h3 h3) h4 (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 118964 (* h1 h1) (* h3 h3) h4 (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2)) (* 63256 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* h6 
h6) (* j2 j2)) (* 18912 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) j2) (* 
2432 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6)) (* 110 (* h1 h1) (* h3 h3) 
h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1548 (* h1 h1) (* 
h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 9282 (* h1 h1) 
(* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 31136 (* h1 h1)
 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 64466 (* h1 h1) 
(* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 85660 (* h1 h1) (* h3
 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 73278 (* h1 h1) (* h3 h3) h4 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 39032 (* h1 h1) (* h3 h3) h4 (* h5 h5) 
(* h6 h6 h6) (* j2 j2)) (* 11776 (* h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) 
j2) (* 1536 (* h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6)) (* 20 (* h1 h1) (* h3
 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 364 (* h1 h1) 
(* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2632 (* h1 
h1) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 10008 (* h1
 h1) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 22340 (* h1 
h1) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 30812 (* h1 h1) 
(* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 26592 (* h1 h1) (* h3 h3
) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 13984 (* h1 h1) (* h3 h3) (* h5 h5 
h5 h5) (* h6 h6) (* j2 j2)) (* 4096 (* h1 h1) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6
) j2) (* 512 (* h1 h1) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6)) (* 80 (* h1 h1) (* 
h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1116 (* h1 
h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6680 (* 
h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 22376 
(* h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 46128 
(* h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 60796 (* h1
 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 51400 (* h1 h1) (* 
h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 26976 (* h1 h1) (* h3 h3) (* 
h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 8000 (* h1 h1) (* h3 h3) (* h5 h5 h5) (* h6
 h6 h6) j2) (* 1024 (* h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6)) (* 50 (* h1 
h1) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 650 
(* h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
3668 (* h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
11748 (* h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
23482 (* h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 30370
 (* h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 25440 (* h1 
h1) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 13328 (* h1 h1) (* h3 
h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 3968 (* h1 h1) (* h3 h3) (* h5 h5) 
(* h6 h6 h6 h6) j2) (* 512 (* h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6)) (* 4 
(* h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 52 (* 
h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 244 (* h1 h1
) h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 596 (* h1 h1) h3 (* 
h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 860 (* h1 h1) h3 (* h4 h4 h4 h4
) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 764 (* h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5 h5)
 (* j2 j2 j2)) (* 412 (* h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2)) (* 
124 (* h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5 h5) j2) (* 16 (* h1 h1) h3 (* h4 h4 h4
 h4) (* h5 h5 h5)) (* 4 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2
 j2 j2 j2 j2)) (* 52 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2
 j2 j2)) (* 244 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2))
 (* 596 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 860 (* 
h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 764 (* h1 h1) h3 (* 
h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 412 (* h1 h1) h3 (* h4 h4 h4) (* h5 
h5 h5 h5) (* j2 j2)) (* 124 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5 h5) j2) (* 16 
(* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5 h5)) (* 2 (* h1 h1) h3 (* h4 h4 h4) (* h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 62 (* h1 h1) h3 (* h4 h4 h4) (* h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 514 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5
 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1990 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5)
 h6 (* j2 j2 j2 j2 j2 j2)) (* 4366 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2)) (* 5882 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 
j2)) (* 4982 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 2594 (* 
h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 760 (* h1 h1) h3 (* h4 h4 
h4) (* h5 h5 h5) h6 j2) (* 96 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) h6) (* 2 
(* h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 58 
(* h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 462 
(* h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1746 (* 
h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 3770 (* h1 h1) 
h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 5022 (* h1 h1) h3 (* h4 
h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 4218 (* h1 h1) h3 (* h4 h4) (* h5 h5 
h5 h5) h6 (* j2 j2 j2)) (* 2182 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 
j2)) (* 636 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) h6 j2) (* 80 (* h1 h1) h3 (* 
h4 h4) (* h5 h5 h5 h5) h6) (* 14 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 244 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1598 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 5456 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 11078 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 14164 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* h6
 h6) (* j2 j2 j2 j2)) (* 11554 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2)) (* 5848 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 
1676 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) j2) (* 208 (* h1 h1) h3 (* h4
 h4) (* h5 h5 h5) (* h6 h6)) (* 12 (* h1 h1) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 186 (* h1 h1) h3 h4 (* h5 h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1136 (* h1 h1) h3 h4 (* h5 h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 3710 (* h1 h1) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 7308 (* h1 h1) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2)) (* 9142 (* h1 h1) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) 
(* 7336 (* h1 h1) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 3666 (* h1 h1
) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 1040 (* h1 h1) h3 h4 (* h5 h5 h5
 h5) (* h6 h6) j2) (* 128 (* h1 h1) h3 h4 (* h5 h5 h5 h5) (* h6 h6)) (* 22 (* h1
 h1) h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 318 (* 
h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1862 (* 
h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 5918 (* h1 
h1) h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 11442 (* h1 h1) h3
 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 14122 (* h1 h1) h3 h4 (* h5
 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 11218 (* h1 h1) h3 h4 (* h5 h5 h5) (* 
h6 h6 h6) (* j2 j2 j2)) (* 5562 (* h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 
j2)) (* 1568 (* h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6 h6) j2) (* 192 (* h1 h1) h3 
h4 (* h5 h5 h5) (* h6 h6 h6)) (* 10 (* h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 132 (* h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 726 (* h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 2208 (* h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 4134 (* h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2)) (* 4980 (* h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) 
(* 3882 (* h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 1896 (* h1 h1
) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 528 (* h1 h1) h3 (* h5 h5 h5 h5)
 (* h6 h6 h6) j2) (* 64 (* h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6 h6)) (* 10 (* h1 
h1) h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 132 (* h1
 h1) h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 726 (* h1 
h1) h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2208 (* h1 h1) 
h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4134 (* h1 h1) h3 (* 
h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 4980 (* h1 h1) h3 (* h5 h5 h5) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 3882 (* h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6 
h6) (* j2 j2 j2)) (* 1896 (* h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2)) 
(* 528 (* h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6 h6) j2) (* 64 (* h1 h1) h3 (* h5 h5
 h5) (* h6 h6 h6 h6)) (* 2 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 
j2 j2)) (* 80 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 550 
h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2)) (* 1504 h1 (* h2 h2 h2 h2
) (* h3 h3 h3) h4 h5 (* j2 j2 j2)) (* 1928 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5
 (* j2 j2)) (* 1152 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 j2) (* 256 h1 (* h2 h2
 h2 h2) (* h3 h3 h3) h4 h5) (* 8 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 
j2 j2 j2 j2)) (* 80 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) 
(* 328 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 704 h1 (* h2 h2
 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2)) (* 832 h1 (* h2 h2 h2 h2) (* h3 h3 h3) 
h4 h6 (* j2 j2)) (* 512 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h6 j2) (* 128 h1 (* 
h2 h2 h2 h2) (* h3 h3 h3) h4 h6) (* 20 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5)
 (* j2 j2 j2 j2 j2)) (* 220 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 
j2 j2)) (* 736 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2)) (* 1024 
h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2)) (* 608 h1 (* h2 h2 h2 h2) 
(* h3 h3 h3) (* h5 h5) j2) (* 128 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5)) (* 
6 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 96 h1 (* h2 h2
 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 554 h1 (* h2 h2 h2 h2) (* h3 
h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 1448 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h5 h6 (* 
j2 j2 j2)) (* 1848 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2)) (* 1120 h1 
(* h2 h2 h2 h2) (* h3 h3 h3) h5 h6 j2) (* 256 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h5
 h6) (* 8 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 80
 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 328 h1 (* h2 
h2 h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 704 h1 (* h2 h2 h2 h2) (* 
h3 h3 h3) (* h6 h6) (* j2 j2 j2)) (* 832 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h6 
h6) (* j2 j2)) (* 512 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h6 h6) j2) (* 128 h1 
(* h2 h2 h2 h2) (* h3 h3 h3) (* h6 h6)) (* 3 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 
h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 65 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 
(* j2 j2 j2 j2 j2)) (* 355 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2
 j2)) (* 807 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 890 h1 
(* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2)) (* 472 h1 (* h2 h2 h2 h2) (* 
h3 h3) (* h4 h4) h5 j2) (* 96 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5) (* 4 h1
 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 36 h1 (* h2 h2
 h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 132 h1 (* h2 h2 h2 h2) (* 
h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2)) (* 252 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 
h4) h6 (* j2 j2 j2)) (* 264 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2))
 (* 144 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h6 j2) (* 32 h1 (* h2 h2 h2 h2) 
(* h3 h3) (* h4 h4) h6) (* 4 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 
j2 j2 j2 j2)) (* 92 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)
) (* 476 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 1060 h1 
(* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 1168 h1 (* h2 h2 h2 h2) 
(* h3 h3) h4 (* h5 h5) (* j2 j2)) (* 624 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 
h5) j2) (* 128 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5)) (* 18 h1 (* h2 h2 h2 
h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 198 h1 (* h2 h2 h2 h2) (* h3 h3
) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 866 h1 (* h2 h2 h2 h2) (* h3 h3) h4 h5 h6 (* 
j2 j2 j2 j2)) (* 1818 h1 (* h2 h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 
1964 h1 (* h2 h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2)) (* 1056 h1 (* h2 h2 h2 h2)
 (* h3 h3) h4 h5 h6 j2) (* 224 h1 (* h2 h2 h2 h2) (* h3 h3) h4 h5 h6) (* 8 h1 
(* h2 h2 h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 72 h1 (* h2 h2 
h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 264 h1 (* h2 h2 h2 h2) (* 
h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 504 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* 
h6 h6) (* j2 j2 j2)) (* 528 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2))
 (* 288 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h6 h6) j2) (* 64 h1 (* h2 h2 h2 h2) 
(* h3 h3) h4 (* h6 h6)) (* 10 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2
 j2 j2 j2)) (* 100 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2)) 
(* 278 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2)) (* 324 h1 (* h2 
h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2)) (* 168 h1 (* h2 h2 h2 h2) (* h3 h3) 
(* h5 h5 h5) j2) (* 32 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5)) (* 8 h1 (* h2 
h2 h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 104 h1 (* h2 h2 h2 h2
) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 472 h1 (* h2 h2 h2 h2) (* h3 h3)
 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 1016 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) h6
 (* j2 j2 j2)) (* 1120 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2)) (* 
608 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) h6 j2) (* 128 h1 (* h2 h2 h2 h2) (* 
h3 h3) (* h5 h5) h6) (* 15 h1 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2
 j2 j2 j2)) (* 133 h1 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2))
 (* 511 h1 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 1011 h1 
(* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 1074 h1 (* h2 h2 h2 h2) 
(* h3 h3) h5 (* h6 h6) (* j2 j2)) (* 584 h1 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 
h6) j2) (* 128 h1 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6)) (* 4 h1 (* h2 h2 h2 h2
) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 36 h1 (* h2 h2 h2 h2) (* h3 
h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 132 h1 (* h2 h2 h2 h2) (* h3 h3) (* h6 
h6 h6) (* j2 j2 j2 j2)) (* 252 h1 (* h2 h2 h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 
j2 j2)) (* 264 h1 (* h2 h2 h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2)) (* 144 h1 
(* h2 h2 h2 h2) (* h3 h3) (* h6 h6 h6) j2) (* 32 h1 (* h2 h2 h2 h2) (* h3 h3) 
(* h6 h6 h6)) (* 2 h1 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 
j2)) (* 34 h1 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 146 
h1 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 278 h1 (* h2 h2 h2
 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 268 h1 (* h2 h2 h2 h2) h3 (* h4 h4)
 (* h5 h5) (* j2 j2)) (* 128 h1 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) j2) (* 24
 h1 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5)) (* 5 h1 (* h2 h2 h2 h2) h3 (* h4 h4)
 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 34 h1 (* h2 h2 h2 h2) h3 (* h4 h4) h5 h6 (* j2 
j2 j2 j2 j2)) (* 102 h1 (* h2 h2 h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 
168 h1 (* h2 h2 h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2)) (* 157 h1 (* h2 h2 h2 h2
) h3 (* h4 h4) h5 h6 (* j2 j2)) (* 78 h1 (* h2 h2 h2 h2) h3 (* h4 h4) h5 h6 j2) 
(* 16 h1 (* h2 h2 h2 h2) h3 (* h4 h4) h5 h6) (* h1 (* h2 h2 h2 h2) h3 h4 (* h5 
h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 22 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 
j2 j2 j2 j2)) (* 98 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 
188 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2)) (* 181 h1 (* h2 h2 h2 h2
) h3 h4 (* h5 h5 h5) (* j2 j2)) (* 86 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) j2) 
(* 16 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5)) (* 10 h1 (* h2 h2 h2 h2) h3 h4 (* 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 96 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5) h6 (* 
j2 j2 j2 j2 j2)) (* 348 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2)) 
(* 624 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2)) (* 594 h1 (* h2 h2 h2
 h2) h3 h4 (* h5 h5) h6 (* j2 j2)) (* 288 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5) h6 
j2) (* 56 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5) h6) (* 10 h1 (* h2 h2 h2 h2) h3 h4 
h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 68 h1 (* h2 h2 h2 h2) h3 h4 h5 (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* 204 h1 (* h2 h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2)
) (* 336 h1 (* h2 h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2)) (* 314 h1 (* h2 h2 
h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2)) (* 156 h1 (* h2 h2 h2 h2) h3 h4 h5 (* h6 h6
) j2) (* 32 h1 (* h2 h2 h2 h2) h3 h4 h5 (* h6 h6)) (* 2 h1 (* h2 h2 h2 h2) h3 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 24 h1 (* h2 h2 h2 h2) h3 (* h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2)) (* 96 h1 (* h2 h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 
j2)) (* 180 h1 (* h2 h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 174 h1 (* h2 
h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2)) (* 84 h1 (* h2 h2 h2 h2) h3 (* h5 h5 h5)
 h6 j2) (* 16 h1 (* h2 h2 h2 h2) h3 (* h5 h5 h5) h6) (* 8 h1 (* h2 h2 h2 h2) h3 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 62 h1 (* h2 h2 h2 h2) h3 (* h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 202 h1 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2)) (* 346 h1 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2)) 
(* 326 h1 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2)) (* 160 h1 (* h2 h2 
h2 h2) h3 (* h5 h5) (* h6 h6) j2) (* 32 h1 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6
)) (* 5 h1 (* h2 h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 34 h1 
(* h2 h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 102 h1 (* h2 h2 h2 h2)
 h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 168 h1 (* h2 h2 h2 h2) h3 h5 (* h6 h6 h6
) (* j2 j2 j2)) (* 157 h1 (* h2 h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2)) (* 78 h1
 (* h2 h2 h2 h2) h3 h5 (* h6 h6 h6) j2) (* 16 h1 (* h2 h2 h2 h2) h3 h5 (* h6 h6 
h6)) (* h1 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 7 h1
 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 20 h1 (* h2 h2 h2
 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 30 h1 (* h2 h2 h2 h2) (* h4 h4) 
(* h5 h5) h6 (* j2 j2 j2)) (* 25 h1 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2
 j2)) (* 11 h1 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5) h6 j2) (* 2 h1 (* h2 h2 h2 h2
) (* h4 h4) (* h5 h5) h6) (* h1 (* h2 h2 h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2)) (* 7 h1 (* h2 h2 h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 20 
h1 (* h2 h2 h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 30 h1 (* h2 h2 h2 h2) 
h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 25 h1 (* h2 h2 h2 h2) h4 (* h5 h5 h5) h6 (* 
j2 j2)) (* 11 h1 (* h2 h2 h2 h2) h4 (* h5 h5 h5) h6 j2) (* 2 h1 (* h2 h2 h2 h2) 
h4 (* h5 h5 h5) h6) (* 2 h1 (* h2 h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 14 h1 (* h2 h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 40 h1 (* h2 h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 60 h1 (* h2 
h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 50 h1 (* h2 h2 h2 h2) h4 (* h5
 h5) (* h6 h6) (* j2 j2)) (* 22 h1 (* h2 h2 h2 h2) h4 (* h5 h5) (* h6 h6) j2) 
(* 4 h1 (* h2 h2 h2 h2) h4 (* h5 h5) (* h6 h6)) (* h1 (* h2 h2 h2 h2) (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 7 h1 (* h2 h2 h2 h2) (* h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2)) (* 20 h1 (* h2 h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2
 j2 j2)) (* 30 h1 (* h2 h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 25 h1 
(* h2 h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 11 h1 (* h2 h2 h2 h2) (* h5
 h5 h5) (* h6 h6) j2) (* 2 h1 (* h2 h2 h2 h2) (* h5 h5 h5) (* h6 h6)) (* h1 (* 
h2 h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 7 h1 (* h2 h2 h2 
h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 20 h1 (* h2 h2 h2 h2) (* h5 h5
) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 30 h1 (* h2 h2 h2 h2) (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2)) (* 25 h1 (* h2 h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 11 
h1 (* h2 h2 h2 h2) (* h5 h5) (* h6 h6 h6) j2) (* 2 h1 (* h2 h2 h2 h2) (* h5 h5) 
(* h6 h6 h6)) (* 4 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2
)) (* 168 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 1420 
h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 5208 h1 (* h2 h2 h2
) (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2)) (* 9872 h1 (* h2 h2 h2) (* h3 h3 h3 h3)
 h4 h5 (* j2 j2 j2)) (* 10016 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2)) 
(* 5120 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 j2) (* 1024 h1 (* h2 h2 h2) (* h3 
h3 h3 h3) h4 h5) (* 16 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 192 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2)) (* 
976 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 2720 h1 (* h2 
h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 4480 h1 (* h2 h2 h2) (* h3 h3 
h3 h3) h4 h6 (* j2 j2 j2)) (* 4352 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 
j2)) (* 2304 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h6 j2) (* 512 h1 (* h2 h2 h2) 
(* h3 h3 h3 h3) h4 h6) (* 40 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 
j2 j2 j2 j2)) (* 520 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2
)) (* 2352 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 4992 h1
 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2)) (* 5312 h1 (* h2 h2 h2) 
(* h3 h3 h3 h3) (* h5 h5) (* j2 j2)) (* 2688 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* 
h5 h5) j2) (* 512 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5)) (* 12 h1 (* h2 h2 
h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 216 h1 (* h2 h2 h2) (* h3
 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 1492 h1 (* h2 h2 h2) (* h3 h3 h3 h3) 
h5 h6 (* j2 j2 j2 j2 j2)) (* 5112 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2
 j2 j2)) (* 9488 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2)) (* 9632 h1 
(* h2 h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2)) (* 4992 h1 (* h2 h2 h2) (* h3 h3 
h3 h3) h5 h6 j2) (* 1024 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h5 h6) (* 16 h1 (* h2 
h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 192 h1 (* h2 h2 h2
) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 976 h1 (* h2 h2 h2) (* h3 
h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2720 h1 (* h2 h2 h2) (* h3 h3 h3 h3) 
(* h6 h6) (* j2 j2 j2 j2)) (* 4480 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* 
j2 j2 j2)) (* 4352 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2)) (* 2304 
h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h6 h6) j2) (* 512 h1 (* h2 h2 h2) (* h3 h3 h3
 h3) (* h6 h6)) (* 12 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 
j2 j2 j2)) (* 312 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2
)) (* 2312 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 7808
 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 13868 h1 (* h2 h2
 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 13352 h1 (* h2 h2 h2) (* h3 h3 
h3) (* h4 h4) h5 (* j2 j2)) (* 6560 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 j2
) (* 1280 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5) (* 16 h1 (* h2 h2 h2) (* h3
 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 176 h1 (* h2 h2 h2) (* h3 h3 
h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 816 h1 (* h2 h2 h2) (* h3 h3 h3) (* 
h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 2064 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h6 
(* j2 j2 j2 j2)) (* 3072 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2))
 (* 2688 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2)) (* 1280 h1 (* h2 
h2 h2) (* h3 h3 h3) (* h4 h4) h6 j2) (* 256 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 
h4) h6) (* 12 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)
) (* 350 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 
2658 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 9274 h1 
(* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 17026 h1 (* h2 h2 h2)
 (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 16632 h1 (* h2 h2 h2) (* h3 h3 h3) 
h4 (* h5 h5) (* j2 j2)) (* 8096 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) j2) 
(* 1536 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5)) (* 60 h1 (* h2 h2 h2) (* h3 
h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 908 h1 (* h2 h2 h2) (* h3 h3 h3) h4
 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 5580 h1 (* h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* 
j2 j2 j2 j2 j2)) (* 17476 h1 (* h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2))
 (* 30120 h1 (* h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 28768 h1 (* h2 
h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2)) (* 14208 h1 (* h2 h2 h2) (* h3 h3 h3) h4
 h5 h6 j2) (* 2816 h1 (* h2 h2 h2) (* h3 h3 h3) h4 h5 h6) (* 32 h1 (* h2 h2 h2) 
(* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 352 h1 (* h2 h2 h2) (* h3
 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1632 h1 (* h2 h2 h2) (* h3 h3 h3)
 h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 4128 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h6 
h6) (* j2 j2 j2 j2)) (* 6144 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 
j2)) (* 5376 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2)) (* 2560 h1 (* 
h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6) j2) (* 512 h1 (* h2 h2 h2) (* h3 h3 h3) h4 
(* h6 h6)) (* 40 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)
) (* 480 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 1912 
h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 3520 h1 (* h2 h2 
h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2)) (* 3264 h1 (* h2 h2 h2) (* h3 h3 h3)
 (* h5 h5 h5) (* j2 j2)) (* 1472 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) j2) 
(* 256 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5)) (* 24 h1 (* h2 h2 h2) (* h3 h3
 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 406 h1 (* h2 h2 h2) (* h3 h3 h3) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 2674 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 
h5) h6 (* j2 j2 j2 j2 j2)) (* 8970 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* 
j2 j2 j2 j2)) (* 16406 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2)) 
(* 16160 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2)) (* 7968 h1 (* h2 
h2 h2) (* h3 h3 h3) (* h5 h5) h6 j2) (* 1536 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 
h5) h6) (* 48 h1 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 596 h1 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
3268 h1 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 9668 h1 
(* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 16252 h1 (* h2 h2 h2)
 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 15416 h1 (* h2 h2 h2) (* h3 h3 h3) 
h5 (* h6 h6) (* j2 j2)) (* 7648 h1 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) j2) 
(* 1536 h1 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6)) (* 16 h1 (* h2 h2 h2) (* h3 
h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 176 h1 (* h2 h2 h2) (* h3 h3 h3
) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 816 h1 (* h2 h2 h2) (* h3 h3 h3) (* h6 
h6 h6) (* j2 j2 j2 j2 j2)) (* 2064 h1 (* h2 h2 h2) (* h3 h3 h3) (* h6 h6 h6) (* 
j2 j2 j2 j2)) (* 3072 h1 (* h2 h2 h2) (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2)) 
(* 2688 h1 (* h2 h2 h2) (* h3 h3 h3) (* h6 h6 h6) (* j2 j2)) (* 1280 h1 (* h2 h2
 h2) (* h3 h3 h3) (* h6 h6 h6) j2) (* 256 h1 (* h2 h2 h2) (* h3 h3 h3) (* h6 h6 
h6)) (* 5 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 112 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 756 
h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 2302 h1 (* h2 
h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 3671 h1 (* h2 h2 h2) (* h3 
h3) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 3186 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4)
 h5 (* j2 j2)) (* 1424 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 j2) (* 256 h1 
(* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5) (* 4 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 
h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 40 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h6
 (* j2 j2 j2 j2 j2 j2)) (* 168 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h6 (* j2 
j2 j2 j2 j2)) (* 384 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2)) 
(* 516 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2)) (* 408 h1 (* h2 
h2 h2) (* h3 h3) (* h4 h4 h4) h6 (* j2 j2)) (* 176 h1 (* h2 h2 h2) (* h3 h3) (* 
h4 h4 h4) h6 j2) (* 32 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h6) (* 15 h1 (* h2
 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 324 h1 (* h2 
h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2048 h1 (* h2 h2 
h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 6006 h1 (* h2 h2 h2) 
(* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 9385 h1 (* h2 h2 h2) (* h3 h3)
 (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 8054 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) 
(* h5 h5) (* j2 j2)) (* 3576 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) j2) 
(* 640 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5)) (* 41 h1 (* h2 h2 h2) (* 
h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 540 h1 (* h2 h2 h2) (* h3 h3
) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 2976 h1 (* h2 h2 h2) (* h3 h3) (* h4
 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 8338 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6
 (* j2 j2 j2 j2)) (* 12839 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2
)) (* 11010 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 4928 h1 (* 
h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 j2) (* 896 h1 (* h2 h2 h2) (* h3 h3) (* h4 
h4) h5 h6) (* 12 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2)) (* 120 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 504 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 1152 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 1548 
h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 1224 h1 (* h2 h2 
h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2)) (* 528 h1 (* h2 h2 h2) (* h3 h3) 
(* h4 h4) (* h6 h6) j2) (* 96 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h6 h6)) (* 
7 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 178 h1 
(* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1188 h1 (* h2 
h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 3670 h1 (* h2 h2 h2) (* 
h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 5901 h1 (* h2 h2 h2) (* h3 h3) h4 (* 
h5 h5 h5) (* j2 j2 j2)) (* 5080 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 
j2)) (* 2216 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) j2) (* 384 h1 (* h2 h2 h2
) (* h3 h3) h4 (* h5 h5 h5)) (* 58 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2)) (* 818 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2
 j2 j2 j2 j2)) (* 4524 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 
j2)) (* 12628 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 
19394 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 16602 h1 (* h2 
h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 7416 h1 (* h2 h2 h2) (* h3 h3) h4
 (* h5 h5) h6 j2) (* 1344 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6) (* 67 h1 
(* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 744 h1 (* h2
 h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3684 h1 (* h2 h2 h2)
 (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 9770 h1 (* h2 h2 h2) (* h3 h3)
 h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 14665 h1 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6
 h6) (* j2 j2 j2)) (* 12462 h1 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2))
 (* 5584 h1 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) j2) (* 1024 h1 (* h2 h2 h2) 
(* h3 h3) h4 h5 (* h6 h6)) (* 12 h1 (* h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2 j2)) (* 120 h1 (* h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 504 h1 (* h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2
)) (* 1152 h1 (* h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1548 h1
 (* h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2)) (* 1224 h1 (* h2 h2 h2) 
(* h3 h3) h4 (* h6 h6 h6) (* j2 j2)) (* 528 h1 (* h2 h2 h2) (* h3 h3) h4 (* h6 
h6 h6) j2) (* 96 h1 (* h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6)) (* 10 h1 (* h2 h2 h2
) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 110 h1 (* h2 h2 h2) (* h3 
h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 378 h1 (* h2 h2 h2) (* h3 h3) (* h5 
h5 h5 h5) (* j2 j2 j2 j2)) (* 602 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* 
j2 j2 j2)) (* 492 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2)) (* 200 h1
 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) j2) (* 32 h1 (* h2 h2 h2) (* h3 h3) (* 
h5 h5 h5 h5)) (* 13 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 200 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 1180 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 3542 h1
 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 5695 h1 (* h2 h2 h2)
 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 4946 h1 (* h2 h2 h2) (* h3 h3) (* h5
 h5 h5) h6 (* j2 j2)) (* 2184 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 j2) (* 
384 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6) (* 43 h1 (* h2 h2 h2) (* h3 h3) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 494 h1 (* h2 h2 h2) (* h3 h3) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2476 h1 (* h2 h2 h2) (* h3 h3) (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 6622 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5)
 (* h6 h6) (* j2 j2 j2 j2)) (* 10009 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 
h6) (* j2 j2 j2)) (* 8548 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2
)) (* 3840 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) j2) (* 704 h1 (* h2 h2 
h2) (* h3 h3) (* h5 h5) (* h6 h6)) (* 31 h1 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 316 h1 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 1464 h1 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 
j2 j2 j2 j2)) (* 3734 h1 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2))
 (* 5497 h1 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 4638 h1 (* 
h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 2080 h1 (* h2 h2 h2) (* h3 h3)
 h5 (* h6 h6 h6) j2) (* 384 h1 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6)) (* 4 h1 
(* h2 h2 h2) (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 40 h1 (* h2 
h2 h2) (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 168 h1 (* h2 h2 h2) 
(* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 384 h1 (* h2 h2 h2) (* h3 h3) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 516 h1 (* h2 h2 h2) (* h3 h3) (* h6 h6 h6 h6
) (* j2 j2 j2)) (* 408 h1 (* h2 h2 h2) (* h3 h3) (* h6 h6 h6 h6) (* j2 j2)) (* 
176 h1 (* h2 h2 h2) (* h3 h3) (* h6 h6 h6 h6) j2) (* 32 h1 (* h2 h2 h2) (* h3 h3
) (* h6 h6 h6 h6)) (* 3 h1 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2
 j2 j2 j2)) (* 57 h1 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2
)) (* 328 h1 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 866 
h1 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 1219 h1 (* h2 h2 
h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 949 h1 (* h2 h2 h2) h3 (* h4 h4 
h4) (* h5 h5) (* j2 j2)) (* 386 h1 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) j2) 
(* 64 h1 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5)) (* 5 h1 (* h2 h2 h2) h3 (* h4 
h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 39 h1 (* h2 h2 h2) h3 (* h4 h4 h4) h5 
h6 (* j2 j2 j2 j2 j2 j2)) (* 136 h1 (* h2 h2 h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2 
j2 j2 j2)) (* 270 h1 (* h2 h2 h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 325 
h1 (* h2 h2 h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 235 h1 (* h2 h2 h2) h3 
(* h4 h4 h4) h5 h6 (* j2 j2)) (* 94 h1 (* h2 h2 h2) h3 (* h4 h4 h4) h5 h6 j2) 
(* 16 h1 (* h2 h2 h2) h3 (* h4 h4 h4) h5 h6) (* 4 h1 (* h2 h2 h2) h3 (* h4 h4) 
(* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 80 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 
h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 448 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) 
(* j2 j2 j2 j2 j2)) (* 1152 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 
j2 j2)) (* 1588 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 1216 
h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 488 h1 (* h2 h2 h2) h3 
(* h4 h4) (* h5 h5 h5) j2) (* 80 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5)) (* 
22 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 260 h1
 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 1262 h1 (* h2 
h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 3112 h1 (* h2 h2 h2) h3 
(* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 4258 h1 (* h2 h2 h2) h3 (* h4 h4) (* 
h5 h5) h6 (* j2 j2 j2)) (* 3284 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 
j2)) (* 1338 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 j2) (* 224 h1 (* h2 h2 h2
) h3 (* h4 h4) (* h5 h5) h6) (* 15 h1 (* h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 117 h1 (* h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2
 j2 j2 j2 j2)) (* 408 h1 (* h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 810 h1 (* h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 975 h1
 (* h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 705 h1 (* h2 h2 h2) h3 
(* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 282 h1 (* h2 h2 h2) h3 (* h4 h4) h5 (* h6 
h6) j2) (* 48 h1 (* h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6)) (* h1 (* h2 h2 h2) h3 
h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 23 h1 (* h2 h2 h2) h3 h4 (* h5 
h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 120 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) 
(* j2 j2 j2 j2 j2)) (* 286 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2)
) (* 369 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2)) (* 267 h1 (* h2 h2 
h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2)) (* 102 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5
) j2) (* 16 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5)) (* 17 h1 (* h2 h2 h2) h3 h4 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 213 h1 (* h2 h2 h2) h3 h4 (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 1038 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2)) (* 2538 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) 
(* 3437 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 2625 h1 (* h2 h2 
h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2)) (* 1060 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5) 
h6 j2) (* 176 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5) h6) (* 35 h1 (* h2 h2 h2) h3 h4
 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 349 h1 (* h2 h2 h2) h3 h4 (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1540 h1 (* h2 h2 h2) h3 h4 (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 3626 h1 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2)) (* 4859 h1 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2))
 (* 3721 h1 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 1518 h1 (* h2 
h2 h2) h3 h4 (* h5 h5) (* h6 h6) j2) (* 256 h1 (* h2 h2 h2) h3 h4 (* h5 h5) (* 
h6 h6)) (* 15 h1 (* h2 h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 117 h1 (* h2 h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 408 h1 
(* h2 h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 810 h1 (* h2 h2 h2) h3
 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 975 h1 (* h2 h2 h2) h3 h4 h5 (* h6 h6 h6
) (* j2 j2 j2)) (* 705 h1 (* h2 h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2)) (* 282 
h1 (* h2 h2 h2) h3 h4 h5 (* h6 h6 h6) j2) (* 48 h1 (* h2 h2 h2) h3 h4 h5 (* h6 
h6 h6)) (* 2 h1 (* h2 h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
26 h1 (* h2 h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 120 h1 (* h2 
h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 276 h1 (* h2 h2 h2) h3 (* h5
 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 354 h1 (* h2 h2 h2) h3 (* h5 h5 h5 h5) h6 (* 
j2 j2 j2)) (* 258 h1 (* h2 h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 100 h1 (* 
h2 h2 h2) h3 (* h5 h5 h5 h5) h6 j2) (* 16 h1 (* h2 h2 h2) h3 (* h5 h5 h5 h5) h6)
 (* 13 h1 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
133 h1 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 590 h1 
(* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1386 h1 (* h2 h2 
h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 1849 h1 (* h2 h2 h2) h3 (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2)) (* 1409 h1 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6)
 (* j2 j2)) (* 572 h1 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) j2) (* 96 h1 (* h2 
h2 h2) h3 (* h5 h5 h5) (* h6 h6)) (* 16 h1 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6
) (* j2 j2 j2 j2 j2 j2 j2)) (* 146 h1 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 606 h1 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2
 j2 j2)) (* 1380 h1 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 
1820 h1 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 1386 h1 (* h2 h2
 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 566 h1 (* h2 h2 h2) h3 (* h5 h5) 
(* h6 h6 h6) j2) (* 96 h1 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6)) (* 5 h1 (* h2 
h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 39 h1 (* h2 h2 h2) h3 
h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 136 h1 (* h2 h2 h2) h3 h5 (* h6 h6 
h6 h6) (* j2 j2 j2 j2 j2)) (* 270 h1 (* h2 h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2
 j2 j2)) (* 325 h1 (* h2 h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 235 h1 
(* h2 h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2)) (* 94 h1 (* h2 h2 h2) h3 h5 (* h6 
h6 h6 h6) j2) (* 16 h1 (* h2 h2 h2) h3 h5 (* h6 h6 h6 h6)) (* h1 (* h2 h2 h2) 
(* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 8 h1 (* h2 h2 h2) (* h4 
h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 27 h1 (* h2 h2 h2) (* h4 h4 h4) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 50 h1 (* h2 h2 h2) (* h4 h4 h4) (* h5 h5) h6
 (* j2 j2 j2 j2)) (* 55 h1 (* h2 h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) 
(* 36 h1 (* h2 h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 13 h1 (* h2 h2 h2)
 (* h4 h4 h4) (* h5 h5) h6 j2) (* 2 h1 (* h2 h2 h2) (* h4 h4 h4) (* h5 h5) h6) 
(* 2 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 16 
h1 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 54 h1 (* h2 
h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 100 h1 (* h2 h2 h2) (* 
h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 110 h1 (* h2 h2 h2) (* h4 h4) (* h5 
h5 h5) h6 (* j2 j2 j2)) (* 72 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2
)) (* 26 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5) h6 j2) (* 4 h1 (* h2 h2 h2) (* 
h4 h4) (* h5 h5 h5) h6) (* 3 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2
 j2 j2 j2 j2 j2 j2)) (* 24 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 81 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2
 j2 j2)) (* 150 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) 
(* 165 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 108 h1 (* 
h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 39 h1 (* h2 h2 h2) (* h4 
h4) (* h5 h5) (* h6 h6) j2) (* 6 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6)) 
(* h1 (* h2 h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 8 h1 (* h2
 h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 27 h1 (* h2 h2 h2) h4 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 50 h1 (* h2 h2 h2) h4 (* h5 h5 h5 h5) 
h6 (* j2 j2 j2 j2)) (* 55 h1 (* h2 h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) 
(* 36 h1 (* h2 h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 13 h1 (* h2 h2 h2) h4 
(* h5 h5 h5 h5) h6 j2) (* 2 h1 (* h2 h2 h2) h4 (* h5 h5 h5 h5) h6) (* 4 h1 (* h2
 h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 32 h1 (* h2 h2 h2
) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 108 h1 (* h2 h2 h2) h4 (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 200 h1 (* h2 h2 h2) h4 (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2)) (* 220 h1 (* h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2)) (* 144 h1 (* h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 52 h1 
(* h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6) j2) (* 8 h1 (* h2 h2 h2) h4 (* h5 h5 h5) 
(* h6 h6)) (* 3 h1 (* h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 24 h1 (* h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
81 h1 (* h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 150 h1 (* h2
 h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 165 h1 (* h2 h2 h2) h4 (* 
h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 108 h1 (* h2 h2 h2) h4 (* h5 h5) (* h6 h6 
h6) (* j2 j2)) (* 39 h1 (* h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6) j2) (* 6 h1 (* h2
 h2 h2) h4 (* h5 h5) (* h6 h6 h6)) (* h1 (* h2 h2 h2) (* h5 h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 8 h1 (* h2 h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 27 h1 (* h2 h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 50 h1 (* h2 h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 55 h1 
(* h2 h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 36 h1 (* h2 h2 h2) (* h5
 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 13 h1 (* h2 h2 h2) (* h5 h5 h5 h5) (* h6 h6) 
j2) (* 2 h1 (* h2 h2 h2) (* h5 h5 h5 h5) (* h6 h6)) (* 2 h1 (* h2 h2 h2) (* h5 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 16 h1 (* h2 h2 h2) (* h5 h5 h5)
 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 54 h1 (* h2 h2 h2) (* h5 h5 h5) (* h6 h6
 h6) (* j2 j2 j2 j2 j2)) (* 100 h1 (* h2 h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2)) (* 110 h1 (* h2 h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 72 
h1 (* h2 h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 26 h1 (* h2 h2 h2) (* h5
 h5 h5) (* h6 h6 h6) j2) (* 4 h1 (* h2 h2 h2) (* h5 h5 h5) (* h6 h6 h6)) (* h1 
(* h2 h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 8 h1 (* h2 
h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 27 h1 (* h2 h2 h2) 
(* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 50 h1 (* h2 h2 h2) (* h5 h5) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 55 h1 (* h2 h2 h2) (* h5 h5) (* h6 h6 h6 h6)
 (* j2 j2 j2)) (* 36 h1 (* h2 h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 13 
h1 (* h2 h2 h2) (* h5 h5) (* h6 h6 h6 h6) j2) (* 2 h1 (* h2 h2 h2) (* h5 h5) (* 
h6 h6 h6 h6)) (* 8 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 304 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2
 j2)) (* 2992 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) 
(* 13520 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 33352 
h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 47648 h1 (* h2 h2)
 (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 39200 h1 (* h2 h2) (* h3 h3 h3 h3
) (* h4 h4) h5 (* j2 j2)) (* 17152 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 j2)
 (* 3072 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5) (* 16 h1 (* h2 h2) (* h3 h3 
h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 208 h1 (* h2 h2) (* h3 h3 h3
 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1168 h1 (* h2 h2) (* h3 h3 h3 h3)
 (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 3696 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 
h4) h6 (* j2 j2 j2 j2 j2)) (* 7200 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h6 (* 
j2 j2 j2 j2)) (* 8832 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2)) 
(* 6656 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2)) (* 2816 h1 (* h2 h2
) (* h3 h3 h3 h3) (* h4 h4) h6 j2) (* 512 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4)
 h6) (* 4 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2))
 (* 200 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
2520 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 13712 
h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 38244 h1 (* h2 
h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 58408 h1 (* h2 h2) (* h3 h3
 h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 48960 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* 
h5 h5) (* j2 j2)) (* 20992 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) j2) (* 3584
 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5)) (* 32 h1 (* h2 h2) (* h3 h3 h3 h3) 
h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 784 h1 (* h2 h2) (* h3 h3 h3 h3) h4 h5 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 6880 h1 (* h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2
 j2 j2 j2 j2 j2)) (* 29808 h1 (* h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 
j2)) (* 72288 h1 (* h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 102624 
h1 (* h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 84352 h1 (* h2 h2) (* h3 
h3 h3 h3) h4 h5 h6 (* j2 j2)) (* 36992 h1 (* h2 h2) (* h3 h3 h3 h3) h4 h5 h6 j2)
 (* 6656 h1 (* h2 h2) (* h3 h3 h3 h3) h4 h5 h6) (* 32 h1 (* h2 h2) (* h3 h3 h3 
h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 416 h1 (* h2 h2) (* h3 h3 h3 h3
) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2336 h1 (* h2 h2) (* h3 h3 h3 h3) h4
 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 7392 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 
h6) (* j2 j2 j2 j2 j2)) (* 14400 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6) (* j2
 j2 j2 j2)) (* 17664 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2)) (* 
13312 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2)) (* 5632 h1 (* h2 h2) 
(* h3 h3 h3 h3) h4 (* h6 h6) j2) (* 1024 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 
h6)) (* 20 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 360 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2356 
h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 7056 h1 (* h2 
h2) (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 10720 h1 (* h2 h2) (* h3 h3
 h3 h3) (* h5 h5 h5) (* j2 j2 j2)) (* 8480 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5
 h5) (* j2 j2)) (* 3328 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) j2) (* 512 h1 
(* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5)) (* 8 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 236 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5
) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2548 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6
 (* j2 j2 j2 j2 j2 j2)) (* 13276 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2
 j2 j2 j2 j2)) (* 36772 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2
)) (* 56472 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 47808 h1 
(* h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2)) (* 20736 h1 (* h2 h2) (* h3 h3
 h3 h3) (* h5 h5) h6 j2) (* 3584 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6) (* 
24 h1 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 480
 h1 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3888 h1 
(* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 16288 h1 (* h2 
h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 38936 h1 (* h2 h2) (* h3
 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 54976 h1 (* h2 h2) (* h3 h3 h3 h3) 
h5 (* h6 h6) (* j2 j2 j2)) (* 45152 h1 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) 
(* j2 j2)) (* 19840 h1 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) j2) (* 3584 h1 (* 
h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6)) (* 16 h1 (* h2 h2) (* h3 h3 h3 h3) (* h6 h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 208 h1 (* h2 h2) (* h3 h3 h3 h3) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1168 h1 (* h2 h2) (* h3 h3 h3 h3) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 3696 h1 (* h2 h2) (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 
j2 j2 j2 j2)) (* 7200 h1 (* h2 h2) (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2))
 (* 8832 h1 (* h2 h2) (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2)) (* 6656 h1 (* 
h2 h2) (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2)) (* 2816 h1 (* h2 h2) (* h3 h3 h3 
h3) (* h6 h6 h6) j2) (* 512 h1 (* h2 h2) (* h3 h3 h3 h3) (* h6 h6 h6)) (* 8 h1 
(* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 236 h1 
(* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 2088 h1 (* 
h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 8600 h1 (* h2 h2) 
(* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 19352 h1 (* h2 h2) (* h3 h3 
h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 25244 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4
 h4) h5 (* j2 j2 j2)) (* 19032 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 
j2)) (* 7680 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 j2) (* 1280 h1 (* h2 h2) 
(* h3 h3 h3) (* h4 h4 h4) h5) (* 8 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 96 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 
j2 j2 j2 j2 j2 j2)) (* 496 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2
 j2 j2 j2)) (* 1440 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2)
) (* 2568 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2)) (* 2880 h1 
(* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2)) (* 1984 h1 (* h2 h2) (* h3 
h3 h3) (* h4 h4 h4) h6 (* j2 j2)) (* 768 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) 
h6 j2) (* 128 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h6) (* 21 h1 (* h2 h2) (* 
h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 598 h1 (* h2 h2) 
(* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 5174 h1 (* h2 h2) 
(* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 21244 h1 (* h2 h2) 
(* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 47933 h1 (* h2 h2) (* h3
 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 62542 h1 (* h2 h2) (* h3 h3 h3) 
(* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 46904 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) 
(* h5 h5) (* j2 j2)) (* 18720 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) j2) 
(* 3072 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5)) (* 64 h1 (* h2 h2) (* h3 
h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1124 h1 (* h2 h2) (* h3 
h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 8200 h1 (* h2 h2) (* h3 h3 
h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 31080 h1 (* h2 h2) (* h3 h3 h3) 
(* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 67248 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4)
 h5 h6 (* j2 j2 j2 j2)) (* 86100 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2
 j2 j2)) (* 64424 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 25984 
h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 j2) (* 4352 h1 (* h2 h2) (* h3 h3 h3) 
(* h4 h4) h5 h6) (* 24 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 288 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 1488 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 4320 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 
j2 j2)) (* 7704 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2)) 
(* 8640 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 5952 h1 
(* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2)) (* 2304 h1 (* h2 h2) (* h3
 h3 h3) (* h4 h4) (* h6 h6) j2) (* 384 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6
 h6)) (* 7 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 242 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
2554 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 11956 
h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 28991 h1 (* h2 
h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 38938 h1 (* h2 h2) (* h3 h3
 h3) h4 (* h5 h5 h5) (* j2 j2 j2)) (* 29152 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 
h5 h5) (* j2 j2)) (* 11360 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) j2) (* 1792
 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5)) (* 68 h1 (* h2 h2) (* h3 h3 h3) h4 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1440 h1 (* h2 h2) (* h3 h3 h3) h4 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 11312 h1 (* h2 h2) (* h3 h3 h3) h4 (* 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 44712 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5)
 h6 (* j2 j2 j2 j2 j2)) (* 99372 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2
 j2 j2 j2)) (* 129048 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) 
(* 96832 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 38784 h1 (* h2 
h2) (* h3 h3 h3) h4 (* h5 h5) h6 j2) (* 6400 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 
h5) h6) (* 104 h1 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2
 j2)) (* 1540 h1 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 10136 h1 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
36360 h1 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 76440 h1 
(* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 96468 h1 (* h2 h2) 
(* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 71752 h1 (* h2 h2) (* h3 h3 h3) h4
 h5 (* h6 h6) (* j2 j2)) (* 28928 h1 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) j2) 
(* 4864 h1 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6)) (* 24 h1 (* h2 h2) (* h3 h3 
h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 288 h1 (* h2 h2) (* h3 h3 h3
) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1488 h1 (* h2 h2) (* h3 h3 h3) h4
 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4320 h1 (* h2 h2) (* h3 h3 h3) h4 (* h6 
h6 h6) (* j2 j2 j2 j2 j2)) (* 7704 h1 (* h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6) (* 
j2 j2 j2 j2)) (* 8640 h1 (* h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2)) 
(* 5952 h1 (* h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2)) (* 2304 h1 (* h2 h2
) (* h3 h3 h3) h4 (* h6 h6 h6) j2) (* 384 h1 (* h2 h2) (* h3 h3 h3) h4 (* h6 h6 
h6)) (* 10 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 170 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1018 
h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 2670 h1 (* h2 
h2) (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 3548 h1 (* h2 h2) (* h3 h3 
h3) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 2504 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 
h5) (* j2 j2)) (* 896 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) j2) (* 128 h1 
(* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5)) (* 11 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5
 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 274 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2554 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2)) (* 11548 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2)) (* 27899 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 
j2)) (* 37714 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 28512 
h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2)) (* 11232 h1 (* h2 h2) (* h3
 h3 h3) (* h5 h5 h5) h6 j2) (* 1792 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6) 
(* 47 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2))
 (* 842 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 6138 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
23468 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 51439
 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 66506 h1 (* 
h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 49928 h1 (* h2 h2) (* 
h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 20064 h1 (* h2 h2) (* h3 h3 h3) (* 
h5 h5) (* h6 h6) j2) (* 3328 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6)) (* 
48 h1 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 652
 h1 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4024 h1 
(* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 13880 h1 (* h2 
h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 28544 h1 (* h2 h2) (* h3
 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 35612 h1 (* h2 h2) (* h3 h3 h3) h5 
(* h6 h6 h6) (* j2 j2 j2)) (* 26360 h1 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) 
(* j2 j2)) (* 10624 h1 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) j2) (* 1792 h1 (* 
h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6)) (* 8 h1 (* h2 h2) (* h3 h3 h3) (* h6 h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 96 h1 (* h2 h2) (* h3 h3 h3) (* h6 h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2)) (* 496 h1 (* h2 h2) (* h3 h3 h3) (* h6 h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 1440 h1 (* h2 h2) (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 
j2 j2 j2)) (* 2568 h1 (* h2 h2) (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) 
(* 2880 h1 (* h2 h2) (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 1984 h1 (* h2
 h2) (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2)) (* 768 h1 (* h2 h2) (* h3 h3 h3) 
(* h6 h6 h6 h6) j2) (* 128 h1 (* h2 h2) (* h3 h3 h3) (* h6 h6 h6 h6)) (* 12 h1 
(* h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 156 h1 (* h2
 h2) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 720 h1 (* h2 h2) (* 
h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 1656 h1 (* h2 h2) (* h3 h3) (* 
h4 h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 2124 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) 
h5 (* j2 j2 j2)) (* 1548 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2)) 
(* 600 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 j2) (* 96 h1 (* h2 h2) (* h3 h3
) (* h4 h4 h4 h4) h5) (* 10 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 246 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 1900 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* 
j2 j2 j2 j2 j2 j2)) (* 6924 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 
j2 j2 j2 j2)) (* 13906 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2
 j2)) (* 16334 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 
11192 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 4144 h1 (* h2 
h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) j2) (* 640 h1 (* h2 h2) (* h3 h3) (* h4 h4 
h4) (* h5 h5)) (* 16 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 216 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 1404 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2))
 (* 4952 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 10040 
h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 12056 h1 (* h2 h2)
 (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 8476 h1 (* h2 h2) (* h3 h3) (* h4
 h4 h4) h5 h6 (* j2 j2)) (* 3224 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 j2) 
(* 512 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6) (* 13 h1 (* h2 h2) (* h3 h3) 
(* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 317 h1 (* h2 h2) (* h3 h3
) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 2414 h1 (* h2 h2) (* h3 h3
) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 8774 h1 (* h2 h2) (* h3 h3) 
(* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 17573 h1 (* h2 h2) (* h3 h3) (* h4
 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 20501 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* 
h5 h5 h5) (* j2 j2 j2)) (* 13888 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) 
(* j2 j2)) (* 5064 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) j2) (* 768 h1 
(* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5)) (* 63 h1 (* h2 h2) (* h3 h3) (* h4 
h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1039 h1 (* h2 h2) (* h3 h3) (* 
h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 6944 h1 (* h2 h2) (* h3 h3) (* 
h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 23822 h1 (* h2 h2) (* h3 h3) (* h4
 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 46535 h1 (* h2 h2) (* h3 h3) (* h4 h4) 
(* h5 h5) h6 (* j2 j2 j2 j2)) (* 53963 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5
) h6 (* j2 j2 j2)) (* 36794 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 
j2)) (* 13624 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 j2) (* 2112 h1 (* h2
 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6) (* 48 h1 (* h2 h2) (* h3 h3) (* h4 h4) h5
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 576 h1 (* h2 h2) (* h3 h3) (* h4 h4) 
h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3276 h1 (* h2 h2) (* h3 h3) (* h4 h4) 
h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 10536 h1 (* h2 h2) (* h3 h3) (* h4 h4) h5
 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 20184 h1 (* h2 h2) (* h3 h3) (* h4 h4) h5 (* 
h6 h6) (* j2 j2 j2 j2)) (* 23424 h1 (* h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6) 
(* j2 j2 j2)) (* 16140 h1 (* h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2)) 
(* 6072 h1 (* h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6) j2) (* 960 h1 (* h2 h2) 
(* h3 h3) (* h4 h4) h5 (* h6 h6)) (* 2 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5)
 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 62 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 592 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2
 j2 j2 j2 j2 j2)) (* 2460 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 
j2 j2)) (* 5274 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 
6318 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2)) (* 4276 h1 (* h2 h2
) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2)) (* 1528 h1 (* h2 h2) (* h3 h3) h4 (* 
h5 h5 h5 h5) j2) (* 224 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5)) (* 39 h1 (* 
h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 743 h1 (* h2
 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 5214 h1 (* h2 h2)
 (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 18370 h1 (* h2 h2) (* h3
 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 36367 h1 (* h2 h2) (* h3 h3) h4 
(* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 42295 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5)
 h6 (* j2 j2 j2)) (* 28684 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2)) 
(* 10496 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 j2) (* 1600 h1 (* h2 h2) (* 
h3 h3) h4 (* h5 h5 h5) h6) (* 96 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1340 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 8188 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 26872 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6
) (* j2 j2 j2 j2 j2)) (* 51352 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* 
j2 j2 j2 j2)) (* 58924 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2
)) (* 40012 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 14816 h1
 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) j2) (* 2304 h1 (* h2 h2) (* h3 h3) 
h4 (* h5 h5) (* h6 h6)) (* 48 h1 (* h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2
 j2 j2 j2 j2 j2 j2)) (* 552 h1 (* h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 2964 h1 (* h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 9096 h1 (* h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2))
 (* 16872 h1 (* h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 19176 h1
 (* h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 13044 h1 (* h2 h2) (* 
h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2)) (* 4872 h1 (* h2 h2) (* h3 h3) h4 h5 (* h6 
h6 h6) j2) (* 768 h1 (* h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6)) (* 3 h1 (* h2 h2) 
(* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 69 h1 (* h2 h2) (* 
h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 586 h1 (* h2 h2) (* h3 h3
) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 2370 h1 (* h2 h2) (* h3 h3) (* h5
 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 5079 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5)
 h6 (* j2 j2 j2 j2)) (* 6129 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 
j2)) (* 4188 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 1512 h1 (* 
h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 j2) (* 224 h1 (* h2 h2) (* h3 h3) (* h5 h5 
h5 h5) h6) (* 26 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 426 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 2800 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 9596 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)
) (* 18794 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 
21794 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 14796 h1 
(* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 5432 h1 (* h2 h2) (* h3
 h3) (* h5 h5 h5) (* h6 h6) j2) (* 832 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6
 h6)) (* 43 h1 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 547 h1 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 3144 h1 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 9974 h1 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 18723 h1 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 21295
 h1 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 14410 h1 (* h2 
h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 5336 h1 (* h2 h2) (* h3 h3) 
(* h5 h5) (* h6 h6 h6) j2) (* 832 h1 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6))
 (* 16 h1 (* h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 180 h1 (* h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
936 h1 (* h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2792 h1 
(* h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 5072 h1 (* h2 h2) 
(* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 5684 h1 (* h2 h2) (* h3 h3) h5 
(* h6 h6 h6 h6) (* j2 j2 j2)) (* 3832 h1 (* h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) 
(* j2 j2)) (* 1424 h1 (* h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) j2) (* 224 h1 (* h2
 h2) (* h3 h3) h5 (* h6 h6 h6 h6)) (* 6 h1 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5
) (* j2 j2 j2 j2 j2 j2 j2)) (* 72 h1 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* 
j2 j2 j2 j2 j2 j2)) (* 294 h1 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2
 j2 j2)) (* 600 h1 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 
690 h1 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 456 h1 (* h2 h2) 
h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2)) (* 162 h1 (* h2 h2) h3 (* h4 h4 h4 h4) 
(* h5 h5) j2) (* 24 h1 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5)) (* 3 h1 (* h2 h2)
 h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 64 h1 (* h2 h2) h3
 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 433 h1 (* h2 h2) h3 (* 
h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1390 h1 (* h2 h2) h3 (* h4 h4 
h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 2485 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 
h5 h5) (* j2 j2 j2 j2)) (* 2628 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 
j2 j2)) (* 1639 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2)) (* 558 h1 
(* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) j2) (* 80 h1 (* h2 h2) h3 (* h4 h4 h4) 
(* h5 h5 h5)) (* 8 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 100 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2
 j2)) (* 610 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 1958 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 3580 h1
 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 3888 h1 (* h2 h2) h3
 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 2490 h1 (* h2 h2) h3 (* h4 h4 h4) 
(* h5 h5) h6 (* j2 j2)) (* 870 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 j2) (* 
128 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6) (* 2 h1 (* h2 h2) h3 (* h4 h4) 
(* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 44 h1 (* h2 h2) h3 (* h4 h4) (* 
h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 288 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5
 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 898 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) 
(* j2 j2 j2 j2 j2)) (* 1570 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 
j2 j2)) (* 1632 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 1004 
h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 338 h1 (* h2 h2) h3 (* 
h4 h4) (* h5 h5 h5 h5) j2) (* 48 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5)) (* 
19 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 276
 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1625 h1 
(* h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 4922 h1 (* h2 
h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 8565 h1 (* h2 h2) h3 (* 
h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 8944 h1 (* h2 h2) h3 (* h4 h4) (* h5 
h5 h5) h6 (* j2 j2 j2)) (* 5551 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 
j2)) (* 1890 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 j2) (* 272 h1 (* h2 h2) 
h3 (* h4 h4) (* h5 h5 h5) h6) (* 24 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 264 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1398 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 4110 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6)
 (* j2 j2 j2 j2 j2)) (* 7140 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2
 j2 j2 j2)) (* 7524 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) 
(* 4734 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 1638 h1 (* 
h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) j2) (* 240 h1 (* h2 h2) h3 (* h4 h4) (* 
h5 h5) (* h6 h6)) (* 6 h1 (* h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 104 h1 (* h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)
) (* 640 h1 (* h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 1954 h1
 (* h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 3390 h1 (* h2 h2) h3 
h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 3516 h1 (* h2 h2) h3 h4 (* h5 h5 h5 h5
) h6 (* j2 j2 j2)) (* 2164 h1 (* h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 
730 h1 (* h2 h2) h3 h4 (* h5 h5 h5 h5) h6 j2) (* 104 h1 (* h2 h2) h3 h4 (* h5 h5
 h5 h5) h6) (* 29 h1 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 360 h1 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 1951 h1 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 5674 h1 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 9675 h1
 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 10004 h1 (* h2 h2) 
h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 6185 h1 (* h2 h2) h3 h4 (* h5 h5 
h5) (* h6 h6) (* j2 j2)) (* 2106 h1 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) j2) 
(* 304 h1 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6)) (* 24 h1 (* h2 h2) h3 h4 (* h5
 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 252 h1 (* h2 h2) h3 h4 (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1254 h1 (* h2 h2) h3 h4 (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3522 h1 (* h2 h2) h3 h4 (* h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2)) (* 5940 h1 (* h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2)) (* 6144 h1 (* h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) 
(* 3822 h1 (* h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 1314 h1 (* h2 h2
) h3 h4 (* h5 h5) (* h6 h6 h6) j2) (* 192 h1 (* h2 h2) h3 h4 (* h5 h5) (* h6 h6 
h6)) (* 4 h1 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2))
 (* 60 h1 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
352 h1 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1056 h1 
(* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1820 h1 (* h2 h2) 
h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 1884 h1 (* h2 h2) h3 (* h5 h5 
h5 h5) (* h6 h6) (* j2 j2 j2)) (* 1160 h1 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6)
 (* j2 j2)) (* 392 h1 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) j2) (* 56 h1 (* h2 
h2) h3 (* h5 h5 h5 h5) (* h6 h6)) (* 13 h1 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 148 h1 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 759 h1 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2)) (* 2142 h1 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2)) (* 3595 h1 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 
3688 h1 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 2273 h1 (* h2 h2
) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 774 h1 (* h2 h2) h3 (* h5 h5 h5) 
(* h6 h6 h6) j2) (* 112 h1 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6)) (* 8 h1 (* h2
 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 82 h1 (* h2 h2
) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 394 h1 (* h2 h2) h3 
(* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1076 h1 (* h2 h2) h3 (* h5 
h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1780 h1 (* h2 h2) h3 (* h5 h5) (* h6 
h6 h6 h6) (* j2 j2 j2 j2)) (* 1818 h1 (* h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* 
j2 j2 j2)) (* 1122 h1 (* h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 384 
h1 (* h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) j2) (* 56 h1 (* h2 h2) h3 (* h5 h5) 
(* h6 h6 h6 h6)) (* h1 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 9 h1 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2)) (* 35 h1 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
77 h1 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 105 h1 (* h2
 h2) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 91 h1 (* h2 h2) (* h4 h4 
h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 49 h1 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5) 
h6 (* j2 j2)) (* 15 h1 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5) h6 j2) (* 2 h1 (* h2 
h2) (* h4 h4 h4) (* h5 h5 h5) h6) (* h1 (* h2 h2) (* h4 h4) (* h5 h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 9 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2)) (* 35 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2)) (* 77 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)
) (* 105 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 91 h1 (* 
h2 h2) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 49 h1 (* h2 h2) (* h4 h4) 
(* h5 h5 h5 h5) h6 (* j2 j2)) (* 15 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5 h5) h6 j2
) (* 2 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5 h5) h6) (* 3 h1 (* h2 h2) (* h4 h4) 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 27 h1 (* h2 h2) (* h4 h4)
 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 105 h1 (* h2 h2) (* h4 h4) 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 231 h1 (* h2 h2) (* h4 h4) (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 315 h1 (* h2 h2) (* h4 h4) (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2)) (* 273 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 
h6) (* j2 j2 j2)) (* 147 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2)
) (* 45 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6) j2) (* 6 h1 (* h2 h2) (* 
h4 h4) (* h5 h5 h5) (* h6 h6)) (* 2 h1 (* h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 18 h1 (* h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 70 h1 (* h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 154 h1 (* h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2
)) (* 210 h1 (* h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 182 h1 
(* h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 98 h1 (* h2 h2) h4 (* h5
 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 30 h1 (* h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6) 
j2) (* 4 h1 (* h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6)) (* 3 h1 (* h2 h2) h4 (* h5 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 27 h1 (* h2 h2) h4 (* h5 h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 105 h1 (* h2 h2) h4 (* h5 h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 231 h1 (* h2 h2) h4 (* h5 h5 h5) (* h6 h6
 h6) (* j2 j2 j2 j2 j2)) (* 315 h1 (* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2)) (* 273 h1 (* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 147
 h1 (* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 45 h1 (* h2 h2) h4 (* 
h5 h5 h5) (* h6 h6 h6) j2) (* 6 h1 (* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6)) (* h1
 (* h2 h2) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 9 h1 (* 
h2 h2) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 35 h1 (* h2 h2)
 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 77 h1 (* h2 h2) (* h5 h5
 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 105 h1 (* h2 h2) (* h5 h5 h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2)) (* 91 h1 (* h2 h2) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2
 j2 j2)) (* 49 h1 (* h2 h2) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 15 h1 (* 
h2 h2) (* h5 h5 h5 h5) (* h6 h6 h6) j2) (* 2 h1 (* h2 h2) (* h5 h5 h5 h5) (* h6 
h6 h6)) (* h1 (* h2 h2) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 9 h1 (* h2 h2) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 35
 h1 (* h2 h2) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 77 h1 (* h2
 h2) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 105 h1 (* h2 h2) (* h5 
h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 91 h1 (* h2 h2) (* h5 h5 h5) (* h6 h6
 h6 h6) (* j2 j2 j2)) (* 49 h1 (* h2 h2) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2))
 (* 15 h1 (* h2 h2) (* h5 h5 h5) (* h6 h6 h6 h6) j2) (* 2 h1 (* h2 h2) (* h5 h5 
h5) (* h6 h6 h6 h6)) (* 32 h1 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 512 h1 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 
j2)) (* 3200 h1 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 
10560 h1 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 20448 h1 h2 
(* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 24000 h1 h2 (* h3 h3 h3 h3) 
(* h4 h4 h4) h5 (* j2 j2 j2)) (* 16768 h1 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* 
j2 j2)) (* 6400 h1 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h5 j2) (* 1024 h1 h2 (* h3 h3
 h3 h3) (* h4 h4 h4) h5) (* 2 h1 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2
 j2 j2 j2 j2 j2 j2 j2)) (* 156 h1 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 2268 h1 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 
j2 j2 j2 j2 j2 j2)) (* 14104 h1 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 
j2 j2 j2 j2)) (* 46578 h1 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 
j2)) (* 89100 h1 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 
101488 h1 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 67584 h1 h2 
(* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 24192 h1 h2 (* h3 h3 h3 h3) 
(* h4 h4) (* h5 h5) j2) (* 3584 h1 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5)) (* 16
 h1 h2 (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 368 h1
 h2 (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3488 h1 h2 
(* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 17408 h1 h2 (* h3 
h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 50928 h1 h2 (* h3 h3 h3 h3) 
(* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 91728 h1 h2 (* h3 h3 h3 h3) (* h4 h4) h5 
h6 (* j2 j2 j2 j2)) (* 102752 h1 h2 (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)
) (* 69568 h1 h2 (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 25984 h1 h2 (* h3
 h3 h3 h3) (* h4 h4) h5 h6 j2) (* 4096 h1 h2 (* h3 h3 h3 h3) (* h4 h4) h5 h6) 
(* 44 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 880 
h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 6752 h1 h2 
(* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 25640 h1 h2 (* h3 h3 
h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 53236 h1 h2 (* h3 h3 h3 h3) h4 (* 
h5 h5 h5) (* j2 j2 j2 j2)) (* 62696 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 
j2 j2)) (* 41600 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2)) (* 14464 h1 h2
 (* h3 h3 h3 h3) h4 (* h5 h5 h5) j2) (* 2048 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5 
h5)) (* 12 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (* 440 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
5376 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 31400 h1
 h2 (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 101044 h1 h2 (* h3
 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 191168 h1 h2 (* h3 h3 h3 h3) 
h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 216832 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5) h6
 (* j2 j2 j2)) (* 144288 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 
51712 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5) h6 j2) (* 7680 h1 h2 (* h3 h3 h3 h3) h4
 (* h5 h5) h6) (* 32 h1 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 640 h1 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 5440 h1 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
25216 h1 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 70176 h1 
h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 122112 h1 h2 (* h3 h3 
h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 133504 h1 h2 (* h3 h3 h3 h3) h4 h5 
(* h6 h6) (* j2 j2 j2)) (* 88832 h1 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2)
) (* 32768 h1 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6) j2) (* 5120 h1 h2 (* h3 h3 h3 
h3) h4 h5 (* h6 h6)) (* 40 h1 h2 (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 808 h1 h2 (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2)) (* 6280 h1 h2 (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
24216 h1 h2 (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 51024 h1 h2 
(* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 60864 h1 h2 (* h3 h3 h3 h3) 
(* h5 h5 h5) h6 (* j2 j2 j2)) (* 40832 h1 h2 (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* 
j2 j2)) (* 14336 h1 h2 (* h3 h3 h3 h3) (* h5 h5 h5) h6 j2) (* 2048 h1 h2 (* h3 
h3 h3 h3) (* h5 h5 h5) h6) (* 10 h1 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2 j2)) (* 284 h1 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 3108 h1 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 17296 h1 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 54466 h1 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2)) (* 102068 h1 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 
115344 h1 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 76704 h1 h2 
(* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 27520 h1 h2 (* h3 h3 h3 h3) 
(* h5 h5) (* h6 h6) j2) (* 4096 h1 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6)) (* 16
 h1 h2 (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 304 h1
 h2 (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2464 h1 h2 
(* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 11008 h1 h2 (* h3 
h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 29808 h1 h2 (* h3 h3 h3 h3) 
h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 50832 h1 h2 (* h3 h3 h3 h3) h5 (* h6 h6 
h6) (* j2 j2 j2 j2)) (* 54752 h1 h2 (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)
) (* 36032 h1 h2 (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 13184 h1 h2 (* h3
 h3 h3 h3) h5 (* h6 h6 h6) j2) (* 2048 h1 h2 (* h3 h3 h3 h3) h5 (* h6 h6 h6)) 
(* 16 h1 h2 (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 240 
h1 h2 (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 1376 h1 h2 
(* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 4128 h1 h2 (* h3 h3 h3
) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 7248 h1 h2 (* h3 h3 h3) (* h4 h4 h4 
h4) h5 (* j2 j2 j2 j2)) (* 7728 h1 h2 (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 
j2)) (* 4928 h1 h2 (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2)) (* 1728 h1 h2 (* 
h3 h3 h3) (* h4 h4 h4 h4) h5 j2) (* 256 h1 h2 (* h3 h3 h3) (* h4 h4 h4 h4) h5) 
(* 3 h1 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 159 h1 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 1974 h1 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
10602 h1 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 30507 
h1 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 51567 h1 h2 (* 
h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 52860 h1 h2 (* h3 h3 h3) 
(* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 32328 h1 h2 (* h3 h3 h3) (* h4 h4 h4) 
(* h5 h5) (* j2 j2)) (* 10848 h1 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) j2) (* 
1536 h1 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5)) (* 8 h1 h2 (* h3 h3 h3) (* h4 h4
 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 192 h1 h2 (* h3 h3 h3) (* h4 h4 h4
) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1816 h1 h2 (* h3 h3 h3) (* h4 h4 h4) h5 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 8672 h1 h2 (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2
 j2 j2 j2 j2 j2)) (* 23704 h1 h2 (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 
j2)) (* 39424 h1 h2 (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 40616 h1
 h2 (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 25312 h1 h2 (* h3 h3 h3) 
(* h4 h4 h4) h5 h6 (* j2 j2)) (* 8736 h1 h2 (* h3 h3 h3) (* h4 h4 h4) h5 h6 j2) 
(* 1280 h1 h2 (* h3 h3 h3) (* h4 h4 h4) h5 h6) (* 4 h1 h2 (* h3 h3 h3) (* h4 h4)
 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 188 h1 h2 (* h3 h3 h3) (* h4 h4
) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2320 h1 h2 (* h3 h3 h3) (* h4 h4)
 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 12680 h1 h2 (* h3 h3 h3) (* h4 h4) 
(* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 37140 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 
h5 h5) (* j2 j2 j2 j2 j2)) (* 63420 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) 
(* j2 j2 j2 j2)) (* 65048 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)
) (* 39424 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 12992 h1 h2 
(* h3 h3 h3) (* h4 h4) (* h5 h5 h5) j2) (* 1792 h1 h2 (* h3 h3 h3) (* h4 h4) (* 
h5 h5 h5)) (* 33 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 825 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 7982 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2)) (* 38638 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 105825 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
174489 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 176688 h1 
h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 107520 h1 h2 (* h3 h3 h3
) (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 36064 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 
h5) h6 j2) (* 5120 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) h6) (* 24 h1 h2 (* h3 
h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 480 h1 h2 (* h3
 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4008 h1 h2 (* h3 
h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 17760 h1 h2 (* h3 h3 
h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 46344 h1 h2 (* h3 h3 h3) 
(* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 74784 h1 h2 (* h3 h3 h3) (* h4 h4)
 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 75480 h1 h2 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6
) (* j2 j2 j2)) (* 46368 h1 h2 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2)) 
(* 15840 h1 h2 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) j2) (* 2304 h1 h2 (* h3 h3 h3
) (* h4 h4) h5 (* h6 h6)) (* 22 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 418 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 
j2 j2 j2)) (* 2980 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) 
(* 10236 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 18966 h1 
h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 20034 h1 h2 (* h3 h3 h3) 
h4 (* h5 h5 h5 h5) (* j2 j2 j2)) (* 12080 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) 
(* j2 j2)) (* 3872 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) j2) (* 512 h1 h2 (* h3 
h3 h3) h4 (* h5 h5 h5 h5)) (* 16 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 496 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 5368 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2
 j2 j2)) (* 27936 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 80208 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 135840 h1 
h2 (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 138920 h1 h2 (* h3 h3 h3)
 h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 84176 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5) h6
 (* j2 j2)) (* 27776 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5) h6 j2) (* 3840 h1 h2 (* 
h3 h3 h3) h4 (* h5 h5 h5) h6) (* 57 h1 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1173 h1 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 10042 h1 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6
) (* j2 j2 j2 j2 j2 j2 j2)) (* 45470 h1 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 120129 h1 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2
 j2 j2 j2 j2)) (* 194277 h1 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2)) (* 194796 h1 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 118056
 h1 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 39584 h1 h2 (* h3 h3 h3
) h4 (* h5 h5) (* h6 h6) j2) (* 5632 h1 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6)) 
(* 24 h1 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
448 h1 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3528 
h1 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 15008 h1 h2 
(* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 38088 h1 h2 (* h3 h3 
h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 60288 h1 h2 (* h3 h3 h3) h4 h5 (* 
h6 h6 h6) (* j2 j2 j2 j2)) (* 60024 h1 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 
j2 j2)) (* 36512 h1 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2)) (* 12384 h1 h2
 (* h3 h3 h3) h4 h5 (* h6 h6 h6) j2) (* 1792 h1 h2 (* h3 h3 h3) h4 h5 (* h6 h6 
h6)) (* 20 h1 h2 (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 384 h1 h2 (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2776 
h1 h2 (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 9696 h1 h2 (* h3
 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 18228 h1 h2 (* h3 h3 h3) (* h5
 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 19488 h1 h2 (* h3 h3 h3) (* h5 h5 h5 h5) h6 
(* j2 j2 j2)) (* 11872 h1 h2 (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 3840 
h1 h2 (* h3 h3 h3) (* h5 h5 h5 h5) h6 j2) (* 512 h1 h2 (* h3 h3 h3) (* h5 h5 h5 
h5) h6) (* 12 h1 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 308 h1 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2
 j2)) (* 3048 h1 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 15256 h1 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
43068 h1 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 72420 h1 
h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 73872 h1 h2 (* h3 h3 
h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 44752 h1 h2 (* h3 h3 h3) (* h5 h5 h5
) (* h6 h6) (* j2 j2)) (* 14784 h1 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) j2) 
(* 2048 h1 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6)) (* 27 h1 h2 (* h3 h3 h3) (* 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 507 h1 h2 (* h3 h3 h3) 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4034 h1 h2 (* h3 h3 h3) 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 17434 h1 h2 (* h3 h3 h3) (* 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 44811 h1 h2 (* h3 h3 h3) (* h5 h5)
 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 71355 h1 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6
 h6) (* j2 j2 j2 j2)) (* 70968 h1 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 
j2 j2)) (* 42864 h1 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 14368 
h1 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) j2) (* 2048 h1 h2 (* h3 h3 h3) (* h5 
h5) (* h6 h6 h6)) (* 8 h1 h2 (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 144 h1 h2 (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 1096 h1 h2 (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 4544 h1 h2 (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 11320 h1
 h2 (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 17680 h1 h2 (* h3 h3 
h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 17432 h1 h2 (* h3 h3 h3) h5 (* h6 h6 
h6 h6) (* j2 j2 j2)) (* 10528 h1 h2 (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2)) 
(* 3552 h1 h2 (* h3 h3 h3) h5 (* h6 h6 h6 h6) j2) (* 512 h1 h2 (* h3 h3 h3) h5 
(* h6 h6 h6 h6)) (* 16 h1 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 224 h1 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2
 j2 j2)) (* 1168 h1 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)
) (* 3168 h1 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 5040 
h1 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 4896 h1 h2 (* h3 
h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 2864 h1 h2 (* h3 h3) (* h4 h4 h4 
h4) (* h5 h5) (* j2 j2)) (* 928 h1 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) j2) 
(* 128 h1 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5)) (* 2 h1 h2 (* h3 h3) (* h4 h4 
h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 86 h1 h2 (* h3 h3) (* h4 h4 
h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 954 h1 h2 (* h3 h3) (* h4 h4 h4
) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 4566 h1 h2 (* h3 h3) (* h4 h4 h4) 
(* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 11742 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 
h5 h5) (* j2 j2 j2 j2 j2)) (* 17874 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) 
(* j2 j2 j2 j2)) (* 16654 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2)
) (* 9346 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2)) (* 2904 h1 h2 (* 
h3 h3) (* h4 h4 h4) (* h5 h5 h5) j2) (* 384 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 
h5 h5)) (* 9 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 196 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2
 j2)) (* 1689 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)
) (* 7308 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
18075 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 27284 h1 
h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 25651 h1 h2 (* h3 h3)
 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 14684 h1 h2 (* h3 h3) (* h4 h4 h4) 
(* h5 h5) h6 (* j2 j2)) (* 4688 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 j2) 
(* 640 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) h6) (* h1 h2 (* h3 h3) (* h4 h4) 
(* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 46 h1 h2 (* h3 h3) (* h4 h4) 
(* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 535 h1 h2 (* h3 h3) (* h4 h4) 
(* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 2680 h1 h2 (* h3 h3) (* h4 h4) (* 
h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 7095 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 
h5 h5) (* j2 j2 j2 j2 j2)) (* 10950 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) 
(* j2 j2 j2 j2)) (* 10217 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)
) (* 5684 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 1736 h1 h2 (* 
h3 h3) (* h4 h4) (* h5 h5 h5 h5) j2) (* 224 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 
h5 h5)) (* 18 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 420 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2
 j2)) (* 3742 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)
) (* 16384 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
40422 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 60276 h1 
h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 55602 h1 h2 (* h3 h3)
 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 31080 h1 h2 (* h3 h3) (* h4 h4) (* 
h5 h5 h5) h6 (* j2 j2)) (* 9656 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 j2) 
(* 1280 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) h6) (* 27 h1 h2 (* h3 h3) (* h4 
h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 492 h1 h2 (* h3 h3) 
(* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3723 h1 h2 (* h3 
h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 14916 h1 h2 (* h3
 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 35217 h1 h2 (* h3 
h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 51612 h1 h2 (* h3 h3) 
(* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 47577 h1 h2 (* h3 h3) (* h4 h4
) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 26868 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5)
 (* h6 h6) (* j2 j2)) (* 8496 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) j2) 
(* 1152 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6)) (* 4 h1 h2 (* h3 h3) h4 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 120 h1 h2 (* h3 h3) h4 (* 
h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1226 h1 h2 (* h3 h3) h4 (* h5 h5
 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 5874 h1 h2 (* h3 h3) h4 (* h5 h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2)) (* 15288 h1 h2 (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* 23436 h1 h2 (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) 
(* 21818 h1 h2 (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 12138 h1 h2 (* 
h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 3712 h1 h2 (* h3 h3) h4 (* h5 h5 h5 
h5) h6 j2) (* 480 h1 h2 (* h3 h3) h4 (* h5 h5 h5 h5) h6) (* 30 h1 h2 (* h3 h3) 
h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 582 h1 h2 (* h3 h3)
 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4622 h1 h2 (* h3 h3) 
h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 19070 h1 h2 (* h3 h3) h4 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 45618 h1 h2 (* h3 h3) h4 (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 66930 h1 h2 (* h3 h3) h4 (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2)) (* 61242 h1 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2)) (* 34122 h1 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 
10600 h1 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) j2) (* 1408 h1 h2 (* h3 h3) h4 
(* h5 h5 h5) (* h6 h6)) (* 27 h1 h2 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2
 j2 j2 j2 j2 j2 j2 j2)) (* 460 h1 h2 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 3275 h1 h2 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 12580 h1 h2 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 28881 h1 h2 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2)) (* 41532 h1 h2 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 
37785 h1 h2 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 21140 h1 h2 (* 
h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 6640 h1 h2 (* h3 h3) h4 (* h5 h5)
 (* h6 h6 h6) j2) (* 896 h1 h2 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6)) (* 3 h1 h2 
(* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 74 h1 h2 
(* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 691 h1 h2 
(* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3194 h1 h2 (* 
h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 8193 h1 h2 (* h3 h3) 
(* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 12486 h1 h2 (* h3 h3) (* h5 h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 11601 h1 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6
 h6) (* j2 j2 j2)) (* 6454 h1 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) 
(* 1976 h1 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) j2) (* 256 h1 h2 (* h3 h3) (* 
h5 h5 h5 h5) (* h6 h6)) (* 14 h1 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2
 j2 j2 j2 j2 j2 j2 j2)) (* 248 h1 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 1834 h1 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 7252 h1 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 16938 h1 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2)) (* 24528 h1 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 
22294 h1 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 12388 h1 h2 (* 
h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 3848 h1 h2 (* h3 h3) (* h5 h5 h5)
 (* h6 h6 h6) j2) (* 512 h1 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6)) (* 9 h1 h2 
(* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 148 h1 h2
 (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1017 h1 h2 
(* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3804 h1 h2 (* 
h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 8571 h1 h2 (* h3 h3) 
(* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 12164 h1 h2 (* h3 h3) (* h5 h5)
 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 10963 h1 h2 (* h3 h3) (* h5 h5) (* h6 h6 h6
 h6) (* j2 j2 j2)) (* 6092 h1 h2 (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) 
(* 1904 h1 h2 (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) j2) (* 256 h1 h2 (* h3 h3) (* 
h5 h5) (* h6 h6 h6 h6)) (* 4 h1 h2 h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 52 h1 h2 h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 
j2 j2)) (* 244 h1 h2 h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 
596 h1 h2 h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 860 h1 h2 h3 
(* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 764 h1 h2 h3 (* h4 h4 h4 h4) 
(* h5 h5 h5) (* j2 j2 j2)) (* 412 h1 h2 h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2
)) (* 124 h1 h2 h3 (* h4 h4 h4 h4) (* h5 h5 h5) j2) (* 16 h1 h2 h3 (* h4 h4 h4 
h4) (* h5 h5 h5)) (* 4 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 52 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2))
 (* 244 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 596 h1 
h2 h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 860 h1 h2 h3 (* h4 h4 
h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 764 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5 h5
) (* j2 j2 j2)) (* 412 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 124 
h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5 h5) j2) (* 16 h1 h2 h3 (* h4 h4 h4) (* h5 h5 
h5 h5)) (* 2 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2
)) (* 44 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
368 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1476 h1 
h2 h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 3340 h1 h2 h3 (* h4
 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 4612 h1 h2 h3 (* h4 h4 h4) (* h5 
h5 h5) h6 (* j2 j2 j2 j2)) (* 3984 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 
j2 j2)) (* 2108 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 626 h1 h2 h3
 (* h4 h4 h4) (* h5 h5 h5) h6 j2) (* 80 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5) h6) 
(* 2 h1 h2 h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 40
 h1 h2 h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 316 h1 h2
 h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1232 h1 h2 h3 (* 
h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 2744 h1 h2 h3 (* h4 h4) (* 
h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 3752 h1 h2 h3 (* h4 h4) (* h5 h5 h5 h5) 
h6 (* j2 j2 j2 j2)) (* 3220 h1 h2 h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) 
(* 1696 h1 h2 h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 502 h1 h2 h3 (* h4 
h4) (* h5 h5 h5 h5) h6 j2) (* 64 h1 h2 h3 (* h4 h4) (* h5 h5 h5 h5) h6) (* 6 h1 
h2 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 108 h1
 h2 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 792 h1 
h2 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2964 h1 h2 
h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6444 h1 h2 h3 (* 
h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 8676 h1 h2 h3 (* h4 h4) (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 7368 h1 h2 h3 (* h4 h4) (* h5 h5 h5) (* 
h6 h6) (* j2 j2 j2)) (* 3852 h1 h2 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2)
) (* 1134 h1 h2 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) j2) (* 144 h1 h2 h3 (* h4 h4
) (* h5 h5 h5) (* h6 h6)) (* 4 h1 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2
 j2 j2 j2 j2 j2 j2)) (* 68 h1 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 476 h1 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 1732 h1 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
3700 h1 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 4924 h1 h2 h3 
h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 4148 h1 h2 h3 h4 (* h5 h5 h5 h5
) (* h6 h6) (* j2 j2 j2)) (* 2156 h1 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2
)) (* 632 h1 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6) j2) (* 80 h1 h2 h3 h4 (* h5 h5 
h5 h5) (* h6 h6)) (* 6 h1 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 100 h1 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 688 h1 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 2476 h1 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 5252 h1 
h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 6956 h1 h2 h3 h4 (* h5
 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 5840 h1 h2 h3 h4 (* h5 h5 h5) (* h6 h6 
h6) (* j2 j2 j2)) (* 3028 h1 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 
886 h1 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6) j2) (* 112 h1 h2 h3 h4 (* h5 h5 h5) 
(* h6 h6 h6)) (* 2 h1 h2 h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2
 j2 j2)) (* 32 h1 h2 h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 212 h1 h2 h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 744 
h1 h2 h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1552 h1 h2 h3 
(* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2032 h1 h2 h3 (* h5 h5 h5 h5
) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1692 h1 h2 h3 (* h5 h5 h5 h5) (* h6 h6 h6) 
(* j2 j2 j2)) (* 872 h1 h2 h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 254 h1 
h2 h3 (* h5 h5 h5 h5) (* h6 h6 h6) j2) (* 32 h1 h2 h3 (* h5 h5 h5 h5) (* h6 h6 
h6)) (* 2 h1 h2 h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 32 h1 h2 h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 212 
h1 h2 h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 744 h1 h2 h3 
(* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1552 h1 h2 h3 (* h5 h5 h5
) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2032 h1 h2 h3 (* h5 h5 h5) (* h6 h6 h6 
h6) (* j2 j2 j2 j2)) (* 1692 h1 h2 h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2))
 (* 872 h1 h2 h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 254 h1 h2 h3 (* h5 
h5 h5) (* h6 h6 h6 h6) j2) (* 32 h1 h2 h3 (* h5 h5 h5) (* h6 h6 h6 h6)) (* 8 h1 
(* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 168 h1
 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1392 h1 
(* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 5968 h1 (* 
h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 14856 h1 (* h3 h3 
h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 22632 h1 (* h3 h3 h3 h3) 
(* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 21376 h1 (* h3 h3 h3 h3) (* h4 h4 h4)
 (* h5 h5) (* j2 j2 j2)) (* 12192 h1 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* 
j2 j2)) (* 3840 h1 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) j2) (* 512 h1 (* h3 h3
 h3 h3) (* h4 h4 h4) (* h5 h5)) (* 4 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 100 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5)
 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 992 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 5016 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* 
j2 j2 j2 j2 j2 j2)) (* 14068 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 
j2 j2 j2)) (* 23012 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) 
(* 22440 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 12832 h1 (* 
h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 3968 h1 (* h3 h3 h3 h3) (* h4 
h4) (* h5 h5 h5) j2) (* 512 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5)) (* 56 h1 
(* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1024 
h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 7520 
h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 29488 h1 
(* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 68808 h1 (* h3 
h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 99984 h1 (* h3 h3 h3 h3)
 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 91168 h1 (* h3 h3 h3 h3) (* h4 h4) 
(* h5 h5) h6 (* j2 j2 j2)) (* 50624 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 
(* j2 j2)) (* 15616 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 j2) (* 2048 h1 (* 
h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6) (* 24 h1 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6
 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 524 h1 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4536 h1 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2
 j2 j2 j2 j2 j2 j2)) (* 20264 h1 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2)) (* 51688 h1 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) 
(* 78956 h1 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 73288 h1 (* 
h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 40416 h1 (* h3 h3 h3 h3) h4 (* 
h5 h5 h5) h6 (* j2 j2)) (* 12160 h1 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 j2) (* 
1536 h1 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6) (* 88 h1 (* h3 h3 h3 h3) h4 (* h5 h5
) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1544 h1 (* h3 h3 h3 h3) h4 (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 10864 h1 (* h3 h3 h3 h3) h4 (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 41072 h1 (* h3 h3 h3 h3) h4 (* h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 93048 h1 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6
 h6) (* j2 j2 j2 j2 j2)) (* 132072 h1 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* 
j2 j2 j2 j2)) (* 118208 h1 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) 
(* 64672 h1 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 19712 h1 (* h3 
h3 h3 h3) h4 (* h5 h5) (* h6 h6) j2) (* 2560 h1 (* h3 h3 h3 h3) h4 (* h5 h5) (* 
h6 h6)) (* 20 h1 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 424 h1 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2
 j2)) (* 3544 h1 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 15248 h1 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
37620 h1 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 55944 h1 
(* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 50848 h1 (* h3 h3 h3 
h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 27584 h1 (* h3 h3 h3 h3) (* h5 h5 h5
) (* h6 h6) (* j2 j2)) (* 8192 h1 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) j2) (* 
1024 h1 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6)) (* 40 h1 (* h3 h3 h3 h3) (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 688 h1 (* h3 h3 h3 h3) (* h5
 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4736 h1 (* h3 h3 h3 h3) (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 17552 h1 (* h3 h3 h3 h3) (* h5 h5)
 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 39096 h1 (* h3 h3 h3 h3) (* h5 h5) (* h6
 h6 h6) (* j2 j2 j2 j2 j2)) (* 54720 h1 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2)) (* 48416 h1 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)
) (* 26240 h1 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 7936 h1 (* h3
 h3 h3 h3) (* h5 h5) (* h6 h6 h6) j2) (* 1024 h1 (* h3 h3 h3 h3) (* h5 h5) (* h6
 h6 h6)) (* 4 h1 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 80 h1 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 620 h1 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 2440 h1 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 5532
 h1 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 7680 h1 (* h3 
h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 6644 h1 (* h3 h3 h3) (* h4 
h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 3496 h1 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 
h5) (* j2 j2)) (* 1024 h1 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) j2) (* 128 h1 
(* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5)) (* 8 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 160 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5
 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1240 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 4880 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 
h5) (* j2 j2 j2 j2 j2 j2)) (* 11064 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) 
(* j2 j2 j2 j2 j2)) (* 15360 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 
j2 j2)) (* 13288 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 6992
 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2)) (* 2048 h1 (* h3 h3 h3) 
(* h4 h4 h4) (* h5 h5 h5) j2) (* 256 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5)) 
(* 32 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 564 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 3924 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
14336 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 30888 
h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 41364 h1 (* h3 
h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 34852 h1 (* h3 h3 h3) (* h4
 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 17976 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 
h5) h6 (* j2 j2)) (* 5184 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 j2) (* 640 
h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6) (* 2 h1 (* h3 h3 h3) (* h4 h4) (* h5 
h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 48 h1 (* h3 h3 h3) (* h4 h4) (* h5 
h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 450 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5
 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 2104 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 
h5) (* j2 j2 j2 j2 j2 j2)) (* 5334 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* 
j2 j2 j2 j2 j2)) (* 7872 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 
j2)) (* 6982 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 3672 h1 
(* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 1056 h1 (* h3 h3 h3) (* h4 
h4) (* h5 h5 h5 h5) j2) (* 128 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5)) (* 56 
h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 968
 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6608 
h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 23792 h1 
(* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 50712 h1 (* h3 
h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 67368 h1 (* h3 h3 h3) 
(* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 56416 h1 (* h3 h3 h3) (* h4 h4) 
(* h5 h5 h5) h6 (* j2 j2 j2)) (* 28960 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6
 (* j2 j2)) (* 8320 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 j2) (* 1024 h1 (* 
h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6) (* 72 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1212 h1 (* h3 h3 h3) (* h4 h4) (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 8052 h1 (* h3 h3 h3) (* h4 h4) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 28368 h1 (* h3 h3 h3) (* h4 h4)
 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 59472 h1 (* h3 h3 h3) (* h4 h4) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 78012 h1 (* h3 h3 h3) (* h4 h4) (* h5
 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 64692 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* 
h6 h6) (* j2 j2 j2)) (* 32952 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* 
j2 j2)) (* 9408 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) j2) (* 1152 h1 (* 
h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6)) (* 12 h1 (* h3 h3 h3) h4 (* h5 h5 h5 h5
) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 250 h1 (* h3 h3 h3) h4 (* h5 h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2030 h1 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 8340 h1 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2
 j2 j2 j2 j2)) (* 19296 h1 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)
) (* 26730 h1 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 22662 h1 
(* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 11528 h1 (* h3 h3 h3) h4 (* 
h5 h5 h5 h5) h6 (* j2 j2)) (* 3232 h1 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 j2) (* 
384 h1 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6) (* 88 h1 (* h3 h3 h3) h4 (* h5 h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1456 h1 (* h3 h3 h3) h4 (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 9496 h1 (* h3 h3 h3) h4 (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 32944 h1 (* h3 h3 h3) h4 (* h5 h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 68232 h1 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6
 h6) (* j2 j2 j2 j2 j2)) (* 88656 h1 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2)) (* 72968 h1 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) 
(* 36944 h1 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 10496 h1 (* h3 
h3 h3) h4 (* h5 h5 h5) (* h6 h6) j2) (* 1280 h1 (* h3 h3 h3) h4 (* h5 h5 h5) (* 
h6 h6)) (* 64 h1 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 1052 h1 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 6812 h1 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 23488 h1 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 48408 h1 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 62652 
h1 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 51404 h1 (* h3 h3 
h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 25960 h1 (* h3 h3 h3) h4 (* h5 h5
) (* h6 h6 h6) (* j2 j2)) (* 7360 h1 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) j2) 
(* 896 h1 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6)) (* 10 h1 (* h3 h3 h3) (* h5 h5
 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 202 h1 (* h3 h3 h3) (* h5 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1580 h1 (* h3 h3 h3) (* h5 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 6236 h1 (* h3 h3 h3) (* h5 h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 13962 h1 (* h3 h3 h3) (* h5 h5 h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 18858 h1 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6
) (* j2 j2 j2 j2)) (* 15680 h1 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 
j2)) (* 7856 h1 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 2176 h1 (* 
h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) j2) (* 256 h1 (* h3 h3 h3) (* h5 h5 h5 h5) 
(* h6 h6)) (* 40 h1 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 648 h1 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 4128 h1 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 14032 h1 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 28584 h1 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 36648 
h1 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 29840 h1 (* h3 h3 
h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 14976 h1 (* h3 h3 h3) (* h5 h5 h5
) (* h6 h6 h6) (* j2 j2)) (* 4224 h1 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) j2) 
(* 512 h1 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6)) (* 20 h1 (* h3 h3 h3) (* h5 h5
) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 324 h1 (* h3 h3 h3) (* h5 
h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2064 h1 (* h3 h3 h3) (* h5 
h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 7016 h1 (* h3 h3 h3) (* h5 h5) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 14292 h1 (* h3 h3 h3) (* h5 h5) (* h6 
h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 18324 h1 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6)
 (* j2 j2 j2 j2)) (* 14920 h1 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2
)) (* 7488 h1 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 2112 h1 (* h3
 h3 h3) (* h5 h5) (* h6 h6 h6 h6) j2) (* 256 h1 (* h3 h3 h3) (* h5 h5) (* h6 h6 
h6 h6)) (* 2 h1 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 38 h1 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 274 h1 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 982 h1 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2022 
h1 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 2562 h1 (* h3 
h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 2038 h1 (* h3 h3) (* h4 h4 
h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 994 h1 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 
h5) (* j2 j2)) (* 272 h1 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) j2) (* 32 h1 (* 
h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5)) (* 2 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 
h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 38 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 
h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 274 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5
) (* j2 j2 j2 j2 j2 j2 j2)) (* 982 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* 
j2 j2 j2 j2 j2 j2)) (* 2022 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 
j2 j2 j2)) (* 2562 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) 
(* 2038 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 994 h1 (* h3 
h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 272 h1 (* h3 h3) (* h4 h4 h4) (* 
h5 h5 h5 h5) j2) (* 32 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5)) (* 16 h1 (* h3
 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 266 h1 (* 
h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1712 h1 (* 
h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 5706 h1 (* h3 
h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 11200 h1 (* h3 h3) 
(* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 13726 h1 (* h3 h3) (* h4 h4 
h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 10656 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5
 h5) h6 (* j2 j2 j2)) (* 5102 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2
)) (* 1376 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 j2) (* 160 h1 (* h3 h3) (* 
h4 h4 h4) (* h5 h5 h5) h6) (* 14 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2
 j2 j2 j2 j2 j2 j2 j2 j2)) (* 228 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 1438 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2)) (* 4724 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2)) (* 9178 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 
j2 j2)) (* 11164 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 
8618 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 4108 h1 (* h3 h3
) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 1104 h1 (* h3 h3) (* h4 h4) (* h5 
h5 h5 h5) h6 j2) (* 128 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6) (* 36 h1 (* 
h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 570 
h1 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
3492 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
11226 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
21468 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 25806
 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 19740 h1 (* 
h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 9342 h1 (* h3 h3) (* h4
 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 2496 h1 (* h3 h3) (* h4 h4) (* h5 h5 
h5) (* h6 h6) j2) (* 288 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6)) (* 22 h1
 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 342 
h1 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2054 
h1 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 6502 h1 
(* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 12290 h1 (* h3 
h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 14642 h1 (* h3 h3) h4 
(* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 11122 h1 (* h3 h3) h4 (* h5 h5 h5 
h5) (* h6 h6) (* j2 j2 j2)) (* 5234 h1 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) 
(* j2 j2)) (* 1392 h1 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) j2) (* 160 h1 (* h3
 h3) h4 (* h5 h5 h5 h5) (* h6 h6)) (* 32 h1 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 494 h1 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2944 h1 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 9262 h1 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 17424 h1 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2)) (* 20682 h1 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)
) (* 15664 h1 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 7354 h1 
(* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 1952 h1 (* h3 h3) h4 (* h5 
h5 h5) (* h6 h6 h6) j2) (* 224 h1 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6)) (* 10 
h1 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 152
 h1 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 890 
h1 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2760 h1 
(* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 5134 h1 (* h3 
h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 6040 h1 (* h3 h3) (* h5 
h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 4542 h1 (* h3 h3) (* h5 h5 h5 h5) (* 
h6 h6 h6) (* j2 j2 j2)) (* 2120 h1 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 
j2)) (* 560 h1 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) j2) (* 64 h1 (* h3 h3) (* 
h5 h5 h5 h5) (* h6 h6 h6)) (* 10 h1 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2 j2)) (* 152 h1 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 890 h1 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2
 j2 j2 j2 j2 j2 j2)) (* 2760 h1 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 5134 h1 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 
j2)) (* 6040 h1 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 4542 
h1 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 2120 h1 (* h3 h3) (* 
h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 560 h1 (* h3 h3) (* h5 h5 h5) (* h6 h6 
h6 h6) j2) (* 64 h1 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6)) (* 4 (* h2 h2 h2 h2)
 (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 52 (* h2 h2 h2 h2) (* h3 h3
 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 236 (* h2 h2 h2 h2) (* h3 h3 h3) (* h4 
h4) h5 (* j2 j2 j2 j2)) (* 508 (* h2 h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 
j2 j2)) (* 560 (* h2 h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2)) (* 304 (* h2
 h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 j2) (* 64 (* h2 h2 h2 h2) (* h3 h3 h3) (* 
h4 h4) h5) (* 2 (* h2 h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2))
 (* 34 (* h2 h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 202 (* 
h2 h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 510 (* h2 h2 h2 h2) 
(* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 596 (* h2 h2 h2 h2) (* h3 h3 h3) h4 
(* h5 h5) (* j2 j2)) (* 320 (* h2 h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) j2) (* 64 
(* h2 h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5)) (* 8 (* h2 h2 h2 h2) (* h3 h3 h3) h4 
h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 104 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 
j2 j2 j2 j2)) (* 472 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 
1016 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 1120 (* h2 h2 h2 h2)
 (* h3 h3 h3) h4 h5 h6 (* j2 j2)) (* 608 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 h6 
j2) (* 128 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 h6) (* 2 (* h2 h2 h2 h2) (* h3 h3 
h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 34 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5
 h5) h6 (* j2 j2 j2 j2 j2)) (* 202 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* 
j2 j2 j2 j2)) (* 510 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 
596 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2)) (* 320 (* h2 h2 h2 h2) 
(* h3 h3 h3) (* h5 h5) h6 j2) (* 64 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6) 
(* 4 (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 52 (* 
h2 h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 236 (* h2 h2 h2 h2
) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 508 (* h2 h2 h2 h2) (* h3 h3 h3)
 h5 (* h6 h6) (* j2 j2 j2)) (* 560 (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* 
j2 j2)) (* 304 (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) j2) (* 64 (* h2 h2 h2 
h2) (* h3 h3 h3) h5 (* h6 h6)) (* 2 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 
(* j2 j2 j2 j2 j2 j2)) (* 24 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 
j2 j2 j2)) (* 96 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 
180 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 174 (* h2 h2 h2 
h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2)) (* 84 (* h2 h2 h2 h2) (* h3 h3) (* h4 
h4 h4) h5 j2) (* 16 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5) (* 4 (* h2 h2 h2 
h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 48 (* h2 h2 h2 h2) 
(* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 192 (* h2 h2 h2 h2) (* h3 
h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 360 (* h2 h2 h2 h2) (* h3 h3) (* h4 
h4) (* h5 h5) (* j2 j2 j2)) (* 348 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5)
 (* j2 j2)) (* 168 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) j2) (* 32 (* h2
 h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5)) (* 6 (* h2 h2 h2 h2) (* h3 h3) (* h4 
h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 72 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6
 (* j2 j2 j2 j2 j2)) (* 288 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 
j2 j2)) (* 540 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 522 
(* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 252 (* h2 h2 h2 h2) (* 
h3 h3) (* h4 h4) h5 h6 j2) (* 48 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6) (* 
(* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 16 (* h2 h2 
h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 86 (* h2 h2 h2 h2) (* h3
 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 184 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 
h5 h5) (* j2 j2 j2)) (* 185 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2))
 (* 88 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) j2) (* 16 (* h2 h2 h2 h2) (* h3
 h3) h4 (* h5 h5 h5)) (* 8 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2
 j2 j2 j2)) (* 96 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) 
(* 384 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 720 (* h2 
h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 696 (* h2 h2 h2 h2) (* h3 
h3) h4 (* h5 h5) h6 (* j2 j2)) (* 336 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 
j2) (* 64 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6) (* 6 (* h2 h2 h2 h2) (* h3 
h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 72 (* h2 h2 h2 h2) (* h3 h3) h4 h5
 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 288 (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) 
(* j2 j2 j2 j2)) (* 540 (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) 
(* 522 (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 252 (* h2 h2 h2 
h2) (* h3 h3) h4 h5 (* h6 h6) j2) (* 48 (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6
)) (* (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 16 (* 
h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 86 (* h2 h2 h2 h2)
 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 184 (* h2 h2 h2 h2) (* h3 h3) (* 
h5 h5 h5) h6 (* j2 j2 j2)) (* 185 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* 
j2 j2)) (* 88 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 j2) (* 16 (* h2 h2 h2 h2
) (* h3 h3) (* h5 h5 h5) h6) (* 4 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 48 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2
 j2 j2 j2 j2)) (* 192 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2)) (* 360 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 348 
(* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 168 (* h2 h2 h2 h2) 
(* h3 h3) (* h5 h5) (* h6 h6) j2) (* 32 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* 
h6 h6)) (* 2 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 24 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 96 (* h2 
h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 180 (* h2 h2 h2 h2) (* 
h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 174 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 
h6 h6) (* j2 j2)) (* 84 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) j2) (* 16 (* 
h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6)) (* (* h2 h2 h2 h2) h3 (* h4 h4 h4) (* h5
 h5) (* j2 j2 j2 j2 j2 j2)) (* 11 (* h2 h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* 
j2 j2 j2 j2 j2)) (* 38 (* h2 h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)
) (* 62 (* h2 h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 53 (* h2 h2 
h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 23 (* h2 h2 h2 h2) h3 (* h4 h4 h4
) (* h5 h5) j2) (* 4 (* h2 h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5)) (* (* h2 h2 h2 
h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 11 (* h2 h2 h2 h2) h3 
(* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 38 (* h2 h2 h2 h2) h3 (* h4 h4) 
(* h5 h5 h5) (* j2 j2 j2 j2)) (* 62 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) 
(* j2 j2 j2)) (* 53 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 23 
(* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) j2) (* 4 (* h2 h2 h2 h2) h3 (* h4 h4) 
(* h5 h5 h5)) (* 3 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 
j2)) (* 33 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 114 
(* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 186 (* h2 h2 h2 h2
) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 159 (* h2 h2 h2 h2) h3 (* h4 h4) 
(* h5 h5) h6 (* j2 j2)) (* 69 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 j2) (* 
12 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6) (* 2 (* h2 h2 h2 h2) h3 h4 (* h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 22 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2)) (* 76 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) 
(* 124 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 106 (* h2 h2 h2 h2
) h3 h4 (* h5 h5 h5) h6 (* j2 j2)) (* 46 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) h6 
j2) (* 8 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) h6) (* 3 (* h2 h2 h2 h2) h3 h4 (* h5
 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 33 (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2)) (* 114 (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* 
j2 j2 j2 j2)) (* 186 (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 
159 (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 69 (* h2 h2 h2 h2) 
h3 h4 (* h5 h5) (* h6 h6) j2) (* 12 (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6)) 
(* (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 11 (* h2 
h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 38 (* h2 h2 h2 h2) h3
 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 62 (* h2 h2 h2 h2) h3 (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2)) (* 53 (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2
)) (* 23 (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) j2) (* 4 (* h2 h2 h2 h2) h3 
(* h5 h5 h5) (* h6 h6)) (* (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2
 j2 j2 j2)) (* 11 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 38 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 62 (* h2 h2 
h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 53 (* h2 h2 h2 h2) h3 (* h5 h5
) (* h6 h6 h6) (* j2 j2)) (* 23 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) j2) 
(* 4 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6)) (* 8 (* h2 h2 h2) (* h3 h3 h3 h3
) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 120 (* h2 h2 h2) (* h3 h3 h3 h3) (* 
h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 680 (* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4) 
h5 (* j2 j2 j2 j2 j2)) (* 1960 (* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 
j2 j2 j2)) (* 3152 (* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 
2848 (* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2)) (* 1344 (* h2 h2 h2) 
(* h3 h3 h3 h3) (* h4 h4) h5 j2) (* 256 (* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4) 
h5) (* 4 (* h2 h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
76 (* h2 h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 540 (* h2
 h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 1828 (* h2 h2 h2) 
(* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 3232 (* h2 h2 h2) (* h3 h3 h3 
h3) h4 (* h5 h5) (* j2 j2 j2)) (* 3024 (* h2 h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5)
 (* j2 j2)) (* 1408 (* h2 h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) j2) (* 256 (* h2 
h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5)) (* 16 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 h6
 (* j2 j2 j2 j2 j2 j2 j2)) (* 240 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2
 j2 j2 j2 j2)) (* 1360 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2))
 (* 3920 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 6304 (* h2 h2
 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 5696 (* h2 h2 h2) (* h3 h3 h3 h3)
 h4 h5 h6 (* j2 j2)) (* 2688 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 h6 j2) (* 512 
(* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 h6) (* 4 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 76 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6
 (* j2 j2 j2 j2 j2 j2)) (* 540 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* 1828 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2))
 (* 3232 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 3024 (* h2 
h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2)) (* 1408 (* h2 h2 h2) (* h3 h3 h3 
h3) (* h5 h5) h6 j2) (* 256 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6) (* 8 (* 
h2 h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 120 (* h2 h2
 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 680 (* h2 h2 h2) (* 
h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1960 (* h2 h2 h2) (* h3 h3 h3 
h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 3152 (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* h6 
h6) (* j2 j2 j2)) (* 2848 (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2)) 
(* 1344 (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) j2) (* 256 (* h2 h2 h2) (* h3 
h3 h3 h3) h5 (* h6 h6)) (* 8 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 
j2 j2 j2 j2 j2)) (* 112 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2
 j2 j2)) (* 576 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) 
(* 1488 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 2136 (* h2
 h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 1728 (* h2 h2 h2) (* h3 h3
 h3) (* h4 h4 h4) h5 (* j2 j2)) (* 736 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5
 j2) (* 128 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5) (* 14 (* h2 h2 h2) (* h3 
h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 204 (* h2 h2 h2) (* h3 
h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1100 (* h2 h2 h2) (* h3 h3 
h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 2944 (* h2 h2 h2) (* h3 h3 h3) 
(* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 4310 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4)
 (* h5 h5) (* j2 j2 j2)) (* 3508 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) 
(* j2 j2)) (* 1488 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) j2) (* 256 (* 
h2 h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5)) (* 24 (* h2 h2 h2) (* h3 h3 h3) (* 
h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 336 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4
) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 1728 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6
 (* j2 j2 j2 j2 j2)) (* 4464 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 
j2 j2)) (* 6408 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 5184 
(* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 2208 (* h2 h2 h2) (* h3 
h3 h3) (* h4 h4) h5 h6 j2) (* 384 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6) (* 
4 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 72 (* 
h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 472 (* h2 h2 h2
) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 1424 (* h2 h2 h2) (* h3 h3
 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 2212 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5
 h5 h5) (* j2 j2 j2)) (* 1832 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2
)) (* 768 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) j2) (* 128 (* h2 h2 h2) (* 
h3 h3 h3) h4 (* h5 h5 h5)) (* 28 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2
 j2 j2 j2 j2 j2 j2)) (* 408 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 
j2 j2 j2 j2)) (* 2200 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 
j2)) (* 5888 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 8620 
(* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 7016 (* h2 h2 h2) (* 
h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 2976 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 
h5) h6 j2) (* 512 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6) (* 24 (* h2 h2 h2) 
(* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 336 (* h2 h2 h2) (* h3
 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1728 (* h2 h2 h2) (* h3 h3 h3)
 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 4464 (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* 
h6 h6) (* j2 j2 j2 j2)) (* 6408 (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 
j2 j2)) (* 5184 (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 2208 (* 
h2 h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) j2) (* 384 (* h2 h2 h2) (* h3 h3 h3) h4 
h5 (* h6 h6)) (* 4 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 72 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 472 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 1424 (* 
h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 2212 (* h2 h2 h2) (* 
h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 1832 (* h2 h2 h2) (* h3 h3 h3) (* h5 
h5 h5) h6 (* j2 j2)) (* 768 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 j2) (* 128
 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6) (* 14 (* h2 h2 h2) (* h3 h3 h3) (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 204 (* h2 h2 h2) (* h3 h3 h3) (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1100 (* h2 h2 h2) (* h3 h3 h3) (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2944 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2)) (* 4310 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6)
 (* j2 j2 j2)) (* 3508 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) 
(* 1488 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) j2) (* 256 (* h2 h2 h2) 
(* h3 h3 h3) (* h5 h5) (* h6 h6)) (* 8 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2)) (* 112 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 576 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2
 j2 j2)) (* 1488 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 
2136 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 1728 (* h2 h2 h2
) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 736 (* h2 h2 h2) (* h3 h3 h3) h5 
(* h6 h6 h6) j2) (* 128 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6)) (* 2 (* h2 h2
 h2) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 26 (* h2 h2 h2) 
(* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 120 (* h2 h2 h2) (* h3 h3
) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 276 (* h2 h2 h2) (* h3 h3) (* h4 h4 
h4 h4) h5 (* j2 j2 j2 j2)) (* 354 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 (* 
j2 j2 j2)) (* 258 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2)) (* 100 
(* h2 h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 j2) (* 16 (* h2 h2 h2) (* h3 h3) (* h4
 h4 h4 h4) h5) (* 8 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2
 j2 j2 j2)) (* 104 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 
j2 j2)) (* 480 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2))
 (* 1104 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 1416 
(* h2 h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 1032 (* h2 h2 h2)
 (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 400 (* h2 h2 h2) (* h3 h3) (* h4
 h4 h4) (* h5 h5) j2) (* 64 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5)) (* 8 
(* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 104 (* h2
 h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 480 (* h2 h2 h2) 
(* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 1104 (* h2 h2 h2) (* h3 h3) 
(* h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 1416 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) 
h5 h6 (* j2 j2 j2)) (* 1032 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2))
 (* 400 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 j2) (* 64 (* h2 h2 h2) (* h3 
h3) (* h4 h4 h4) h5 h6) (* 7 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2
 j2 j2 j2 j2 j2 j2)) (* 95 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 
j2 j2 j2 j2 j2)) (* 462 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 
j2 j2 j2)) (* 1098 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)
) (* 1431 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 1047 
(* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 404 (* h2 h2 h2) (* 
h3 h3) (* h4 h4) (* h5 h5 h5) j2) (* 64 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 
h5 h5)) (* 24 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2
 j2)) (* 312 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)
) (* 1440 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
3312 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 4248 (* 
h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 3096 (* h2 h2 h2) 
(* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 1200 (* h2 h2 h2) (* h3 h3) (* h4
 h4) (* h5 h5) h6 j2) (* 192 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6) (* 
12 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
156 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 720 
(* h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1656 (* h2 
h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 2124 (* h2 h2 h2) 
(* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 1548 (* h2 h2 h2) (* h3 h3) 
(* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 600 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* 
h6 h6) j2) (* 96 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6)) (* (* h2 h2 h2) 
(* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 17 (* h2 h2 h2) (* h3 
h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 102 (* h2 h2 h2) (* h3 h3) h4 
(* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 270 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5
 h5) (* j2 j2 j2 j2)) (* 369 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 
j2)) (* 273 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2)) (* 104 (* h2 h2
 h2) (* h3 h3) h4 (* h5 h5 h5 h5) j2) (* 16 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 
h5 h5)) (* 14 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)
) (* 190 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 924
 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 2196 (* h2 h2 
h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 2862 (* h2 h2 h2) (* h3 h3)
 h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 2094 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5)
 h6 (* j2 j2)) (* 808 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 j2) (* 128 (* h2
 h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6) (* 24 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 312 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1440 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2)) (* 3312 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6)
 (* j2 j2 j2 j2)) (* 4248 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2
 j2)) (* 3096 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 1200 
(* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) j2) (* 192 (* h2 h2 h2) (* h3 h3) 
h4 (* h5 h5) (* h6 h6)) (* 8 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 104 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2
 j2 j2)) (* 480 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 1104 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1416 (* h2
 h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 1032 (* h2 h2 h2) (* h3 h3
) h4 h5 (* h6 h6 h6) (* j2 j2)) (* 400 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6)
 j2) (* 64 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6)) (* (* h2 h2 h2) (* h3 h3) 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 17 (* h2 h2 h2) (* h3 h3) (* h5 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 102 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5
) h6 (* j2 j2 j2 j2 j2)) (* 270 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 
j2 j2 j2)) (* 369 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 273
 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 104 (* h2 h2 h2) (* h3 
h3) (* h5 h5 h5 h5) h6 j2) (* 16 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6) (* 7
 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 95 
(* h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 462 (* 
h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1098 (* h2 h2 
h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 1431 (* h2 h2 h2) (* h3
 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 1047 (* h2 h2 h2) (* h3 h3) (* h5 
h5 h5) (* h6 h6) (* j2 j2)) (* 404 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6)
 j2) (* 64 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6)) (* 8 (* h2 h2 h2) (* 
h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 104 (* h2 h2 h2) (* 
h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 480 (* h2 h2 h2) (* h3 
h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1104 (* h2 h2 h2) (* h3 h3) 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1416 (* h2 h2 h2) (* h3 h3) (* h5 h5)
 (* h6 h6 h6) (* j2 j2 j2)) (* 1032 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6
) (* j2 j2)) (* 400 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) j2) (* 64 (* 
h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6)) (* 2 (* h2 h2 h2) (* h3 h3) h5 (* h6
 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 26 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6
 h6) (* j2 j2 j2 j2 j2 j2)) (* 120 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* 
j2 j2 j2 j2 j2)) (* 276 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2
)) (* 354 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 258 (* h2 
h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2)) (* 100 (* h2 h2 h2) (* h3 h3) h5 
(* h6 h6 h6 h6) j2) (* 16 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6)) (* (* h2 h2
 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 12 (* h2 h2 h2) 
h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 49 (* h2 h2 h2) h3 (* h4 
h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 100 (* h2 h2 h2) h3 (* h4 h4 h4 h4) 
(* h5 h5) (* j2 j2 j2 j2)) (* 115 (* h2 h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* 
j2 j2 j2)) (* 76 (* h2 h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2)) (* 27 (* 
h2 h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) j2) (* 4 (* h2 h2 h2) h3 (* h4 h4 h4 h4) 
(* h5 h5)) (* 2 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 
j2)) (* 24 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 
98 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 200 (* h2 h2
 h2) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 230 (* h2 h2 h2) h3 (* h4 
h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 152 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5 
h5) (* j2 j2)) (* 54 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) j2) (* 8 (* h2 h2
 h2) h3 (* h4 h4 h4) (* h5 h5 h5)) (* 4 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 48 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2)) (* 196 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2
 j2 j2)) (* 400 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 
460 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 304 (* h2 h2 h2) 
h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 108 (* h2 h2 h2) h3 (* h4 h4 h4) (* 
h5 h5) h6 j2) (* 16 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6) (* (* h2 h2 h2) 
h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 12 (* h2 h2 h2) h3 (* 
h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 49 (* h2 h2 h2) h3 (* h4 h4) 
(* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 100 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5
 h5) (* j2 j2 j2 j2)) (* 115 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 
j2)) (* 76 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 27 (* h2 h2 
h2) h3 (* h4 h4) (* h5 h5 h5 h5) j2) (* 4 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5 
h5)) (* 6 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 72 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 294 
(* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 600 (* h2 h2 h2
) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 690 (* h2 h2 h2) h3 (* h4 h4)
 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 456 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 
(* j2 j2)) (* 162 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 j2) (* 24 (* h2 h2 
h2) h3 (* h4 h4) (* h5 h5 h5) h6) (* 6 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* h6
 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 72 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 294 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* 600 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 
j2 j2 j2)) (* 690 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) 
(* 456 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 162 (* h2 h2 
h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) j2) (* 24 (* h2 h2 h2) h3 (* h4 h4) (* h5 
h5) (* h6 h6)) (* 2 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2)) (* 24 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 98 
(* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 200 (* h2 h2 h2) h3
 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 230 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5
) h6 (* j2 j2 j2)) (* 152 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 54
 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) h6 j2) (* 8 (* h2 h2 h2) h3 h4 (* h5 h5 h5 
h5) h6) (* 6 (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2))
 (* 72 (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 294 
(* h2 h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 600 (* h2 h2 h2
) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 690 (* h2 h2 h2) h3 h4 (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2)) (* 456 (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) 
(* j2 j2)) (* 162 (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) j2) (* 24 (* h2 h2 
h2) h3 h4 (* h5 h5 h5) (* h6 h6)) (* 4 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2)) (* 48 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2)) (* 196 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2)) (* 400 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 460
 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 304 (* h2 h2 h2) h3 
h4 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 108 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 
h6 h6) j2) (* 16 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6)) (* (* h2 h2 h2) h3 
(* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 12 (* h2 h2 h2) h3 (* h5 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 49 (* h2 h2 h2) h3 (* h5 h5 h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 100 (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2)) (* 115 (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) 
(* 76 (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 27 (* h2 h2 h2) h3
 (* h5 h5 h5 h5) (* h6 h6) j2) (* 4 (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6)) 
(* 2 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 24 
(* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 98 (* h2 h2 
h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 200 (* h2 h2 h2) h3 (* 
h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 230 (* h2 h2 h2) h3 (* h5 h5 h5) (* 
h6 h6 h6) (* j2 j2 j2)) (* 152 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 
j2)) (* 54 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) j2) (* 8 (* h2 h2 h2) h3 
(* h5 h5 h5) (* h6 h6 h6)) (* (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2
 j2 j2 j2 j2 j2)) (* 12 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2
 j2 j2)) (* 49 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
100 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 115 (* h2 h2 
h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 76 (* h2 h2 h2) h3 (* h5 h5) 
(* h6 h6 h6 h6) (* j2 j2)) (* 27 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) j2) 
(* 4 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6)) (* 8 (* h2 h2) (* h3 h3 h3 h3) 
(* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 128 (* h2 h2) (* h3 h3 h3 h3) 
(* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 800 (* h2 h2) (* h3 h3 h3 h3) (* h4
 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 2640 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4 h4)
 h5 (* j2 j2 j2 j2 j2)) (* 5112 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 
j2 j2 j2)) (* 6000 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 
4192 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2)) (* 1600 (* h2 h2) (* 
h3 h3 h3 h3) (* h4 h4 h4) h5 j2) (* 256 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4 h4) 
h5) (* 8 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 160 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 
j2)) (* 1232 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)
) (* 4736 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 
10120 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 12512 
(* h2 h2) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 8864 (* h2 h2) 
(* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 3328 (* h2 h2) (* h3 h3 h3 h3)
 (* h4 h4) (* h5 h5) j2) (* 512 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5)) 
(* 24 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
384 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2400 
(* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 7920 (* h2 
h2) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 15336 (* h2 h2) (* h3
 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 18000 (* h2 h2) (* h3 h3 h3 h3) 
(* h4 h4) h5 h6 (* j2 j2 j2)) (* 12576 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 h6
 (* j2 j2)) (* 4800 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 h6 j2) (* 768 (* h2 
h2) (* h3 h3 h3 h3) (* h4 h4) h5 h6) (* 2 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5 
h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 48 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5 h5)
 (* j2 j2 j2 j2 j2 j2 j2)) (* 448 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* 
j2 j2 j2 j2 j2 j2)) (* 2060 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 
j2 j2 j2)) (* 4974 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) 
(* 6532 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2)) (* 4688 (* h2 h2
) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2)) (* 1728 (* h2 h2) (* h3 h3 h3 h3) 
h4 (* h5 h5 h5) j2) (* 256 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5 h5)) (* 16 (* 
h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 320 (* h2
 h2) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2464 (* h2 h2)
 (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 9472 (* h2 h2) (* h3 
h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 20240 (* h2 h2) (* h3 h3 h3 h3)
 h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 25024 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5
) h6 (* j2 j2 j2)) (* 17728 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2))
 (* 6656 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) h6 j2) (* 1024 (* h2 h2) (* h3 
h3 h3 h3) h4 (* h5 h5) h6) (* 24 (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 384 (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 2400 (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 7920 (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 15336 (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 
18000 (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 12576 (* h2 h2)
 (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 4800 (* h2 h2) (* h3 h3 h3 h3) h4
 h5 (* h6 h6) j2) (* 768 (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* h6 h6)) (* 2 (* h2 
h2) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 48 (* h2 h2)
 (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 448 (* h2 h2) (* 
h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 2060 (* h2 h2) (* h3 h3 
h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 4974 (* h2 h2) (* h3 h3 h3 h3) (* 
h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 6532 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) h6 
(* j2 j2 j2)) (* 4688 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2)) (* 
1728 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) h6 j2) (* 256 (* h2 h2) (* h3 h3 h3 
h3) (* h5 h5 h5) h6) (* 8 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2
 j2 j2 j2 j2 j2 j2)) (* 160 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 1232 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 4736 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2)) (* 10120 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2
)) (* 12512 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 8864 
(* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 3328 (* h2 h2) (* h3
 h3 h3 h3) (* h5 h5) (* h6 h6) j2) (* 512 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) 
(* h6 h6)) (* 8 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 128 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2
)) (* 800 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
2640 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 5112 (* h2
 h2) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 6000 (* h2 h2) (* h3 h3
 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 4192 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6
 h6 h6) (* j2 j2)) (* 1600 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6 h6) j2) (* 256 
(* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6 h6)) (* 4 (* h2 h2) (* h3 h3 h3) (* h4 h4 
h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 60 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4 
h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 344 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4 h4) 
h5 (* j2 j2 j2 j2 j2 j2)) (* 1032 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* 
j2 j2 j2 j2 j2)) (* 1812 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 
j2)) (* 1932 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2)) (* 1232 (* 
h2 h2) (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2)) (* 432 (* h2 h2) (* h3 h3 h3) 
(* h4 h4 h4 h4) h5 j2) (* 64 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4 h4) h5) (* 14 
(* h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
218 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
1304 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 
4044 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 7254 
(* h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 7818 (* h2 h2)
 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 4996 (* h2 h2) (* h3 h3 h3
) (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 1744 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) 
(* h5 h5) j2) (* 256 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5)) (* 16 (* h2 
h2) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 240 (* h2 h2
) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1376 (* h2 h2) 
(* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 4128 (* h2 h2) (* h3 
h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 7248 (* h2 h2) (* h3 h3 h3) (* 
h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 7728 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 
h6 (* j2 j2 j2)) (* 4928 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2)) 
(* 1728 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 h6 j2) (* 256 (* h2 h2) (* h3 h3 
h3) (* h4 h4 h4) h5 h6) (* 8 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 152 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 1088 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* 
j2 j2 j2 j2 j2 j2)) (* 3792 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 
j2 j2 j2 j2)) (* 7272 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 
j2)) (* 8088 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 5200
 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 1792 (* h2 h2) (* 
h3 h3 h3) (* h4 h4) (* h5 h5 h5) j2) (* 256 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* 
h5 h5 h5)) (* 42 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 654 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2)) (* 3912 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 
j2 j2)) (* 12132 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2
)) (* 21762 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 
23454 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 14988 (* h2
 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 5232 (* h2 h2) (* h3 h3 
h3) (* h4 h4) (* h5 h5) h6 j2) (* 768 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5)
 h6) (* 24 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2
 j2)) (* 360 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 2064 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)
) (* 6192 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
10872 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 11592 
(* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 7392 (* h2 h2) 
(* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 2592 (* h2 h2) (* h3 h3 h3) 
(* h4 h4) h5 (* h6 h6) j2) (* 384 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6))
 (* (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 23
 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 202 (* 
h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 850 (* h2 h2) 
(* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 1817 (* h2 h2) (* h3 h3 
h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 2119 (* h2 h2) (* h3 h3 h3) h4 (* h5 
h5 h5 h5) (* j2 j2 j2)) (* 1372 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 
j2)) (* 464 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5 h5) j2) (* 64 (* h2 h2) (* h3 
h3 h3) h4 (* h5 h5 h5 h5)) (* 16 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 304 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2)) (* 2176 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2)) (* 7584 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2)) (* 14544 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 
16176 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 10400 (* h2 h2)
 (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2)) (* 3584 (* h2 h2) (* h3 h3 h3) h4 
(* h5 h5 h5) h6 j2) (* 512 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) h6) (* 42 (* 
h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 654 
(* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3912 
(* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 12132 
(* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 21762 (* h2
 h2) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 23454 (* h2 h2) (* 
h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 14988 (* h2 h2) (* h3 h3 h3) 
h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 5232 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) 
(* h6 h6) j2) (* 768 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6)) (* 16 (* h2 
h2) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 240 (* h2 h2
) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1376 (* h2 h2) 
(* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4128 (* h2 h2) (* h3 
h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 7248 (* h2 h2) (* h3 h3 h3) h4 
h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 7728 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6 
h6) (* j2 j2 j2)) (* 4928 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2)) 
(* 1728 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6 h6) j2) (* 256 (* h2 h2) (* h3 h3 
h3) h4 h5 (* h6 h6 h6)) (* (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 23 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2
 j2 j2 j2)) (* 202 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2)) (* 850 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
1817 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 2119 (* h2 h2
) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 1372 (* h2 h2) (* h3 h3 h3) 
(* h5 h5 h5 h5) h6 (* j2 j2)) (* 464 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) h6 
j2) (* 64 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) h6) (* 8 (* h2 h2) (* h3 h3 h3)
 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 152 (* h2 h2) (* h3 h3 
h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1088 (* h2 h2) (* h3 h3 
h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3792 (* h2 h2) (* h3 h3 h3)
 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 7272 (* h2 h2) (* h3 h3 h3) (* h5
 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 8088 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2)) (* 5200 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) 
(* j2 j2)) (* 1792 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) j2) (* 256 (* 
h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6)) (* 14 (* h2 h2) (* h3 h3 h3) (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 218 (* h2 h2) (* h3 h3 h3) (* 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1304 (* h2 h2) (* h3 h3 h3) (* 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4044 (* h2 h2) (* h3 h3 h3) (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 7254 (* h2 h2) (* h3 h3 h3) (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2)) (* 7818 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2)) (* 4996 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2
)) (* 1744 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) j2) (* 256 (* h2 h2) 
(* h3 h3 h3) (* h5 h5) (* h6 h6 h6)) (* 4 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 60 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2)) (* 344 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 1032 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 
j2 j2 j2)) (* 1812 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) 
(* 1932 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 1232 (* h2 h2
) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2)) (* 432 (* h2 h2) (* h3 h3 h3) h5 
(* h6 h6 h6 h6) j2) (* 64 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6 h6)) (* 4 (* h2 
h2) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 56 (* h2
 h2) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 292 (* h2 
h2) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 792 (* h2 h2) 
(* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 1260 (* h2 h2) (* h3 
h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 1224 (* h2 h2) (* h3 h3) (* h4
 h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 716 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) 
(* h5 h5) (* j2 j2)) (* 232 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) j2) 
(* 32 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5)) (* 7 (* h2 h2) (* h3 h3) 
(* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 102 (* h2 h2) (* h3 h3
) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 557 (* h2 h2) (* h3 h3)
 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1560 (* h2 h2) (* h3 h3) 
(* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 2529 (* h2 h2) (* h3 h3) (* h4 
h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 2478 (* h2 h2) (* h3 h3) (* h4 h4 h4) 
(* h5 h5 h5) (* j2 j2 j2)) (* 1451 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5)
 (* j2 j2)) (* 468 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) j2) (* 64 (* h2
 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5)) (* 16 (* h2 h2) (* h3 h3) (* h4 h4 h4)
 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 224 (* h2 h2) (* h3 h3) (* h4 h4 
h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1168 (* h2 h2) (* h3 h3) (* h4 h4 
h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 3168 (* h2 h2) (* h3 h3) (* h4 h4 h4)
 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 5040 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5
 h5) h6 (* j2 j2 j2 j2)) (* 4896 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 
(* j2 j2 j2)) (* 2864 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) 
(* 928 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 j2) (* 128 (* h2 h2) (* h3 
h3) (* h4 h4 h4) (* h5 h5) h6) (* 2 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5
) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 36 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5 
h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 238 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5 
h5) (* j2 j2 j2 j2 j2 j2)) (* 744 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) 
(* j2 j2 j2 j2 j2)) (* 1278 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 
j2 j2 j2)) (* 1284 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) 
(* 754 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 240 (* h2 h2)
 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) j2) (* 32 (* h2 h2) (* h3 h3) (* h4 h4) (* 
h5 h5 h5 h5)) (* 21 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2
 j2 j2 j2 j2)) (* 306 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2)) (* 1671 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2)) (* 4680 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2)) (* 7587 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 
7434 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 4353 (* h2 
h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 1404 (* h2 h2) (* h3 h3) 
(* h4 h4) (* h5 h5 h5) h6 j2) (* 192 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) 
h6) (* 24 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 336 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2
 j2 j2 j2)) (* 1752 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 4752 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2
 j2 j2 j2)) (* 7560 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2)) (* 7344 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) 
(* 4296 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 1392 (* 
h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) j2) (* 192 (* h2 h2) (* h3 h3) 
(* h4 h4) (* h5 h5) (* h6 h6)) (* 4 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 72 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2)) (* 476 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2
 j2 j2 j2 j2)) (* 1488 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 
j2)) (* 2556 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 2568 
(* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 1508 (* h2 h2) (* h3 
h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 480 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 
h5) h6 j2) (* 64 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) h6) (* 21 (* h2 h2) (* 
h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 306 (* h2 h2) 
(* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1671 (* h2 h2) 
(* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4680 (* h2 h2) (* 
h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 7587 (* h2 h2) (* h3 h3)
 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 7434 (* h2 h2) (* h3 h3) h4 (* h5
 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 4353 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* 
h6 h6) (* j2 j2)) (* 1404 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) j2) (* 
192 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6)) (* 16 (* h2 h2) (* h3 h3) h4 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 224 (* h2 h2) (* h3 h3) 
h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1168 (* h2 h2) (* h3 h3) 
h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3168 (* h2 h2) (* h3 h3) h4 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 5040 (* h2 h2) (* h3 h3) h4 (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 4896 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6
 h6 h6) (* j2 j2 j2)) (* 2864 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* 
j2 j2)) (* 928 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) j2) (* 128 (* h2 h2
) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6)) (* 2 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 36 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 238 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 744 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2)) (* 1278 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6)
 (* j2 j2 j2 j2)) (* 1284 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2
 j2)) (* 754 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 240 (* 
h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) j2) (* 32 (* h2 h2) (* h3 h3) (* h5 
h5 h5 h5) (* h6 h6)) (* 7 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2
 j2 j2 j2 j2 j2 j2)) (* 102 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 557 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 1560 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2)) (* 2529 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)
) (* 2478 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 1451 
(* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 468 (* h2 h2) (* h3 
h3) (* h5 h5 h5) (* h6 h6 h6) j2) (* 64 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 
h6 h6)) (* 4 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 56 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2
 j2)) (* 292 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)
) (* 792 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
1260 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 1224 (* 
h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 716 (* h2 h2) (* h3 
h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 232 (* h2 h2) (* h3 h3) (* h5 h5) 
(* h6 h6 h6 h6) j2) (* 32 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6)) (* (* 
h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 13 (* h2 
h2) h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 61 (* h2 h2) h3
 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 149 (* h2 h2) h3 (* h4 
h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 215 (* h2 h2) h3 (* h4 h4 h4 h4) 
(* h5 h5 h5) (* j2 j2 j2 j2)) (* 191 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5 h5) 
(* j2 j2 j2)) (* 103 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2)) (* 31 
(* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5 h5) j2) (* 4 (* h2 h2) h3 (* h4 h4 h4 h4) 
(* h5 h5 h5)) (* (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 13 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)
) (* 61 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 149 
(* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 215 (* h2 h2) 
h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 191 (* h2 h2) h3 (* h4 h4 h4
) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 103 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5 h5)
 (* j2 j2)) (* 31 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5 h5) j2) (* 4 (* h2 h2) 
h3 (* h4 h4 h4) (* h5 h5 h5 h5)) (* 4 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 52 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2)) (* 244 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2
 j2 j2 j2 j2)) (* 596 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2)) (* 860 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 764 
(* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 412 (* h2 h2) h3 (* 
h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 124 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 
h5) h6 j2) (* 16 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) h6) (* 3 (* h2 h2) h3 
(* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 39 (* h2 h2) h3 (* 
h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 183 (* h2 h2) h3 (* h4 h4
) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 447 (* h2 h2) h3 (* h4 h4) (* h5 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 645 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) 
h6 (* j2 j2 j2 j2)) (* 573 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2
)) (* 309 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 93 (* h2 h2) 
h3 (* h4 h4) (* h5 h5 h5 h5) h6 j2) (* 12 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5)
 h6) (* 6 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 78 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2
)) (* 366 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 894 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1290
 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 1146 (* h2 h2
) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 618 (* h2 h2) h3 (* h4 h4
) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 186 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) 
(* h6 h6) j2) (* 24 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6)) (* 3 (* h2 h2
) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 39 (* h2 h2) 
h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 183 (* h2 h2) h3 h4
 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 447 (* h2 h2) h3 h4 (* h5 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 645 (* h2 h2) h3 h4 (* h5 h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2)) (* 573 (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* 
j2 j2 j2)) (* 309 (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 93 (* 
h2 h2) h3 h4 (* h5 h5 h5 h5) (* h6 h6) j2) (* 12 (* h2 h2) h3 h4 (* h5 h5 h5 h5)
 (* h6 h6)) (* 4 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 52 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 244 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 596
 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 860 (* h2 h2) 
h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 764 (* h2 h2) h3 h4 (* h5 h5
 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 412 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6 h6)
 (* j2 j2)) (* 124 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6 h6) j2) (* 16 (* h2 h2)
 h3 h4 (* h5 h5 h5) (* h6 h6 h6)) (* (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 13 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 61 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 149 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2
)) (* 215 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 191 (* 
h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 103 (* h2 h2) h3 (* h5 
h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 31 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6 h6
) j2) (* 4 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6 h6)) (* (* h2 h2) h3 (* h5 h5 
h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 13 (* h2 h2) h3 (* h5 h5 h5)
 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 61 (* h2 h2) h3 (* h5 h5 h5) (* h6
 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 149 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6 
h6) (* j2 j2 j2 j2 j2)) (* 215 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 
j2 j2 j2)) (* 191 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 103
 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 31 (* h2 h2) h3 (* h5 
h5 h5) (* h6 h6 h6 h6) j2) (* 4 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6 h6)) (* 4 
h2 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 84 
h2 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 696 h2
 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 2984 h2 (* 
h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 7428 h2 (* h3 h3 
h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 11316 h2 (* h3 h3 h3 h3) 
(* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 10688 h2 (* h3 h3 h3 h3) (* h4 h4 h4)
 (* h5 h5) (* j2 j2 j2)) (* 6096 h2 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2
 j2)) (* 1920 h2 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) j2) (* 256 h2 (* h3 h3 
h3 h3) (* h4 h4 h4) (* h5 h5)) (* 2 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 50 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 496 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 2508 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* 
j2 j2 j2 j2 j2 j2)) (* 7034 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 
j2 j2 j2)) (* 11506 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) 
(* 11220 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 6416 h2 (* 
h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 1984 h2 (* h3 h3 h3 h3) (* h4 
h4) (* h5 h5 h5) j2) (* 256 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5)) (* 12 h2 
(* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 252 h2
 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2088 h2 
(* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 8952 h2 (* 
h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 22284 h2 (* h3 h3 
h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 33948 h2 (* h3 h3 h3 h3) 
(* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 32064 h2 (* h3 h3 h3 h3) (* h4 h4) 
(* h5 h5) h6 (* j2 j2 j2)) (* 18288 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 
(* j2 j2)) (* 5760 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 j2) (* 768 h2 (* h3
 h3 h3 h3) (* h4 h4) (* h5 h5) h6) (* 4 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 100 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 992 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2)) (* 5016 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2
 j2)) (* 14068 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
23012 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 22440 h2 (* h3 
h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 12832 h2 (* h3 h3 h3 h3) h4 (* h5 
h5 h5) h6 (* j2 j2)) (* 3968 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 j2) (* 512 h2
 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6) (* 12 h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 252 h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2088 h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 8952 h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 22284 h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* 33948 h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2)) (* 32064 h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 
18288 h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 5760 h2 (* h3 h3 
h3 h3) h4 (* h5 h5) (* h6 h6) j2) (* 768 h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 
h6)) (* 2 h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 50 h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 496 h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
2508 h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 7034 h2
 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 11506 h2 (* h3 h3
 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 11220 h2 (* h3 h3 h3 h3) (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 6416 h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 
h6) (* j2 j2)) (* 1984 h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) j2) (* 256 h2 
(* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6)) (* 4 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 84 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 696 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6
 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2984 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2)) (* 7428 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2)) (* 11316 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)
) (* 10688 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 6096 h2 
(* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 1920 h2 (* h3 h3 h3 h3) (* 
h5 h5) (* h6 h6 h6) j2) (* 256 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6)) (* 2 
h2 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 40 
h2 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 310 h2
 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1220 h2 (* 
h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2766 h2 (* h3 h3 
h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 3840 h2 (* h3 h3 h3) (* h4 
h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 3322 h2 (* h3 h3 h3) (* h4 h4 h4 h4) (* 
h5 h5) (* j2 j2 j2)) (* 1748 h2 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2)
) (* 512 h2 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) j2) (* 64 h2 (* h3 h3 h3) (* 
h4 h4 h4 h4) (* h5 h5)) (* 4 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 80 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 620 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2
 j2 j2 j2 j2)) (* 2440 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 
j2 j2)) (* 5532 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) 
(* 7680 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 6644 h2 
(* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 3496 h2 (* h3 h3 h3) (* 
h4 h4 h4) (* h5 h5 h5) (* j2 j2)) (* 1024 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 
h5) j2) (* 128 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5)) (* 8 h2 (* h3 h3 h3) 
(* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 160 h2 (* h3 h3 h3)
 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1240 h2 (* h3 h3 h3) 
(* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 4880 h2 (* h3 h3 h3) (* 
h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 11064 h2 (* h3 h3 h3) (* h4 h4 
h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 15360 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5
 h5) h6 (* j2 j2 j2 j2)) (* 13288 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* 
j2 j2 j2)) (* 6992 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 2048 
h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 j2) (* 256 h2 (* h3 h3 h3) (* h4 h4 h4
) (* h5 h5) h6) (* h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 24 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 225 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2
 j2)) (* 1052 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) 
(* 2667 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 3936 h2
 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 3491 h2 (* h3 h3 h3)
 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 1836 h2 (* h3 h3 h3) (* h4 h4) (* h5
 h5 h5 h5) (* j2 j2)) (* 528 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) j2) (* 64
 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5)) (* 12 h2 (* h3 h3 h3) (* h4 h4) (* 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 240 h2 (* h3 h3 h3) (* h4 h4) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1860 h2 (* h3 h3 h3) (* h4 h4) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 7320 h2 (* h3 h3 h3) (* h4 h4) (* 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 16596 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2)) (* 23040 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 
(* j2 j2 j2 j2)) (* 19932 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)
) (* 10488 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 3072 h2 (* h3
 h3 h3) (* h4 h4) (* h5 h5 h5) h6 j2) (* 384 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 
h5) h6) (* 12 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2 j2)) (* 240 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 1860 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 7320 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 16596 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2
 j2)) (* 23040 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) 
(* 19932 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 10488 h2
 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 3072 h2 (* h3 h3 h3) 
(* h4 h4) (* h5 h5) (* h6 h6) j2) (* 384 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* 
h6 h6)) (* 2 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2
)) (* 48 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
450 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2104 h2 
(* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 5334 h2 (* h3 h3 h3
) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 7872 h2 (* h3 h3 h3) h4 (* h5 h5 
h5 h5) h6 (* j2 j2 j2 j2)) (* 6982 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 
j2 j2)) (* 3672 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 1056 h2 (* 
h3 h3 h3) h4 (* h5 h5 h5 h5) h6 j2) (* 128 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6
) (* 12 h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 240 h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 1860 h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
7320 h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 16596 
h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 23040 h2 (* h3 
h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 19932 h2 (* h3 h3 h3) h4 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 10488 h2 (* h3 h3 h3) h4 (* h5 h5 h5) 
(* h6 h6) (* j2 j2)) (* 3072 h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) j2) (* 
384 h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6)) (* 8 h2 (* h3 h3 h3) h4 (* h5 h5)
 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 160 h2 (* h3 h3 h3) h4 (* h5 h5
) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1240 h2 (* h3 h3 h3) h4 (* h5 h5)
 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4880 h2 (* h3 h3 h3) h4 (* h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 11064 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2)) (* 15360 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2
 j2 j2 j2)) (* 13288 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 
6992 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 2048 h2 (* h3 h3 h3
) h4 (* h5 h5) (* h6 h6 h6) j2) (* 256 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6)
) (* h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 24 h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
225 h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1052 
h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2667 h2 (* 
h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 3936 h2 (* h3 h3 h3) 
(* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 3491 h2 (* h3 h3 h3) (* h5 h5 h5 
h5) (* h6 h6) (* j2 j2 j2)) (* 1836 h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) 
(* j2 j2)) (* 528 h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) j2) (* 64 h2 (* h3 
h3 h3) (* h5 h5 h5 h5) (* h6 h6)) (* 4 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 80 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 620 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 2440 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 5532 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2)) (* 7680 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) 
(* 6644 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 3496 h2 (* h3
 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 1024 h2 (* h3 h3 h3) (* h5 h5 h5
) (* h6 h6 h6) j2) (* 128 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6)) (* 2 h2 (* 
h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 40 h2 (* 
h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 310 h2 (* h3
 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1220 h2 (* h3 h3 
h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2766 h2 (* h3 h3 h3) (* 
h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 3840 h2 (* h3 h3 h3) (* h5 h5) (* 
h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 3322 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) 
(* j2 j2 j2)) (* 1748 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 
512 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) j2) (* 64 h2 (* h3 h3 h3) (* h5 h5
) (* h6 h6 h6 h6)) (* h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 19 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 137 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2
 j2 j2)) (* 491 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2))
 (* 1011 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 1281 
h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 1019 h2 (* h3 h3) 
(* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 497 h2 (* h3 h3) (* h4 h4 h4 h4) 
(* h5 h5 h5) (* j2 j2)) (* 136 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) j2) (* 
16 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5)) (* h2 (* h3 h3) (* h4 h4 h4) (* h5
 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 19 h2 (* h3 h3) (* h4 h4 h4) (* h5
 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 137 h2 (* h3 h3) (* h4 h4 h4) (* h5 
h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 491 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5
 h5) (* j2 j2 j2 j2 j2 j2)) (* 1011 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) 
(* j2 j2 j2 j2 j2)) (* 1281 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 
j2 j2)) (* 1019 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 497 
h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 136 h2 (* h3 h3) (* h4 
h4 h4) (* h5 h5 h5 h5) j2) (* 16 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5)) (* 4
 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 76
 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 548 
h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1964 h2 
(* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 4044 h2 (* h3 
h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 5124 h2 (* h3 h3) (* h4 
h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 4076 h2 (* h3 h3) (* h4 h4 h4) (* h5 
h5 h5) h6 (* j2 j2 j2)) (* 1988 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 
j2)) (* 544 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 j2) (* 64 h2 (* h3 h3) (* 
h4 h4 h4) (* h5 h5 h5) h6) (* 3 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 57 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 411 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2
 j2 j2 j2 j2 j2)) (* 1473 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2)) (* 3033 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2))
 (* 3843 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 3057 h2 
(* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 1491 h2 (* h3 h3) (* h4 
h4) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 408 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) 
h6 j2) (* 48 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6) (* 6 h2 (* h3 h3) (* h4 
h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 114 h2 (* h3 h3) 
(* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 822 h2 (* h3 h3
) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2946 h2 (* h3 h3
) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6066 h2 (* h3 h3) 
(* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 7686 h2 (* h3 h3) (* h4 
h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 6114 h2 (* h3 h3) (* h4 h4) (* h5
 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 2982 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* 
h6 h6) (* j2 j2)) (* 816 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) j2) (* 96
 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6)) (* 3 h2 (* h3 h3) h4 (* h5 h5 h5
 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 57 h2 (* h3 h3) h4 (* h5 h5 h5
 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 411 h2 (* h3 h3) h4 (* h5 h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1473 h2 (* h3 h3) h4 (* h5 h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3033 h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2)) (* 3843 h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2)) (* 3057 h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 
1491 h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 408 h2 (* h3 h3) h4
 (* h5 h5 h5 h5) (* h6 h6) j2) (* 48 h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6)) 
(* 4 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 76 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
548 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1964 
h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4044 h2 (* 
h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 5124 h2 (* h3 h3) h4 
(* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 4076 h2 (* h3 h3) h4 (* h5 h5 h5) 
(* h6 h6 h6) (* j2 j2 j2)) (* 1988 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* 
j2 j2)) (* 544 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) j2) (* 64 h2 (* h3 h3) 
h4 (* h5 h5 h5) (* h6 h6 h6)) (* h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2 j2)) (* 19 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 137 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 491 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2
 j2 j2 j2)) (* 1011 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)
) (* 1281 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1019 h2 
(* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 497 h2 (* h3 h3) (* h5 
h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 136 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 
h6) j2) (* 16 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6)) (* h2 (* h3 h3) (* h5 
h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 19 h2 (* h3 h3) (* h5 
h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 137 h2 (* h3 h3) (* h5 h5
 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 491 h2 (* h3 h3) (* h5 h5 h5) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1011 h2 (* h3 h3) (* h5 h5 h5) (* h6 
h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1281 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) 
(* j2 j2 j2 j2)) (* 1019 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2))
 (* 497 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 136 h2 (* h3 h3)
 (* h5 h5 h5) (* h6 h6 h6 h6) j2) (* 16 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6
))) 0)))
(check-sat)
(exit)

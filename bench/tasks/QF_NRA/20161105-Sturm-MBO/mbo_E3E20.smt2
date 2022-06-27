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
(set-info :instance |E3E20|)
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
(+ (* 6 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2 j2 j2)) (* 88 
(* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2 j2)) (* 512 (* h1 h1 h1
 h1) (* h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2)) (* 1504 (* h1 h1 h1 h1) (* h2 h2
 h2) (* h3 h3) h5 (* j2 j2 j2)) (* 2336 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) 
h5 (* j2 j2)) (* 1792 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 j2) (* 512 (* h1
 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5) (* 4 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3
) h6 (* j2 j2 j2 j2 j2 j2)) (* 60 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h6 (* 
j2 j2 j2 j2 j2)) (* 360 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h6 (* j2 j2 j2 j2
)) (* 1104 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h6 (* j2 j2 j2)) (* 1824 (* h1
 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h6 (* j2 j2)) (* 1536 (* h1 h1 h1 h1) (* h2 h2
 h2) (* h3 h3) h6 j2) (* 512 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h6) (* 6 (* 
h1 h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 70 (* h1 h1 h1 
h1) (* h2 h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 320 (* h1 h1 h1 h1) (* h2 
h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2)) (* 736 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* 
h5 h5) (* j2 j2 j2)) (* 896 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* j2 j2))
 (* 544 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) j2) (* 128 (* h1 h1 h1 h1) (* 
h2 h2 h2) h3 (* h5 h5)) (* (* h1 h1 h1 h1) (* h2 h2 h2) h3 h5 h6 (* j2 j2 j2 j2 
j2 j2 j2)) (* 20 (* h1 h1 h1 h1) (* h2 h2 h2) h3 h5 h6 (* j2 j2 j2 j2 j2 j2)) 
(* 153 (* h1 h1 h1 h1) (* h2 h2 h2) h3 h5 h6 (* j2 j2 j2 j2 j2)) (* 594 (* h1 h1
 h1 h1) (* h2 h2 h2) h3 h5 h6 (* j2 j2 j2 j2)) (* 1284 (* h1 h1 h1 h1) (* h2 h2 
h2) h3 h5 h6 (* j2 j2 j2)) (* 1560 (* h1 h1 h1 h1) (* h2 h2 h2) h3 h5 h6 (* j2 
j2)) (* 992 (* h1 h1 h1 h1) (* h2 h2 h2) h3 h5 h6 j2) (* 256 (* h1 h1 h1 h1) (* 
h2 h2 h2) h3 h5 h6) (* 4 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 48 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 228 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6) (* j2 j2 j2 j2)) (* 552 (* h1 
h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6) (* j2 j2 j2)) (* 720 (* h1 h1 h1 h1) (* h2 
h2 h2) h3 (* h6 h6) (* j2 j2)) (* 480 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6) 
j2) (* 128 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6)) (* (* h1 h1 h1 h1) (* h2 
h2 h2) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 13 (* h1 h1 h1 h1) (* h2 h2 h2)
 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 69 (* h1 h1 h1 h1) (* h2 h2 h2) (* h5 h5
) h6 (* j2 j2 j2 j2 j2)) (* 195 (* h1 h1 h1 h1) (* h2 h2 h2) (* h5 h5) h6 (* j2 
j2 j2 j2)) (* 318 (* h1 h1 h1 h1) (* h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2)) (* 300
 (* h1 h1 h1 h1) (* h2 h2 h2) (* h5 h5) h6 (* j2 j2)) (* 152 (* h1 h1 h1 h1) (* 
h2 h2 h2) (* h5 h5) h6 j2) (* 32 (* h1 h1 h1 h1) (* h2 h2 h2) (* h5 h5) h6) (* 
(* h1 h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 13 (* h1 
h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 69 (* h1 h1 h1 h1)
 (* h2 h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 195 (* h1 h1 h1 h1) (* h2 h2 
h2) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 318 (* h1 h1 h1 h1) (* h2 h2 h2) h5 (* h6 
h6) (* j2 j2 j2)) (* 300 (* h1 h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6) (* j2 j2)) 
(* 152 (* h1 h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6) j2) (* 32 (* h1 h1 h1 h1) (* h2
 h2 h2) h5 (* h6 h6)) (* 6 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2
 j2 j2 j2 j2)) (* 124 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2 
j2 j2)) (* 1064 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2 j2)) 
(* 4880 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2)) (* 12800 (* 
h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2)) (* 18944 (* h1 h1 h1 h1) 
(* h2 h2) (* h3 h3 h3) h5 (* j2 j2)) (* 14336 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3
 h3) h5 j2) (* 4096 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5) (* 4 (* h1 h1 h1 
h1) (* h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 84 (* h1 h1 h1 h1) 
(* h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2 j2 j2 j2)) (* 736 (* h1 h1 h1 h1) (* h2 h2
) (* h3 h3 h3) h6 (* j2 j2 j2 j2 j2)) (* 3472 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3
 h3) h6 (* j2 j2 j2 j2)) (* 9472 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h6 (* j2
 j2 j2)) (* 14848 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h6 (* j2 j2)) (* 12288 
(* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h6 j2) (* 4096 (* h1 h1 h1 h1) (* h2 h2) 
(* h3 h3 h3) h6) (* 36 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2 
j2 j2)) (* 492 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 
2616 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2)) (* 6864 (* h1 h1
 h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2)) (* 9312 (* h1 h1 h1 h1) (* h2 h2
) (* h3 h3) h4 h5 (* j2 j2)) (* 6144 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 
j2) (* 1536 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5) (* 16 (* h1 h1 h1 h1) (* 
h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2)) (* 224 (* h1 h1 h1 h1) (* h2 h2) 
(* h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 1232 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) 
h4 h6 (* j2 j2 j2 j2)) (* 3392 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h6 (* j2 
j2 j2)) (* 4928 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h6 (* j2 j2)) (* 3584 (* 
h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h6 j2) (* 1024 (* h1 h1 h1 h1) (* h2 h2) (* 
h3 h3) h4 h6) (* 12 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2
 j2 j2 j2)) (* 212 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2 
j2 j2)) (* 1528 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)
) (* 5776 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 
12256 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2)) (* 14464 (* h1
 h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* j2 j2)) (* 8704 (* h1 h1 h1 h1) (* 
h2 h2) (* h3 h3) (* h5 h5) j2) (* 2048 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h5
 h5)) (* (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 36 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 479
 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 3112 (* h1 
h1 h1 h1) (* h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 11100 (* h1 h1 h1 h1)
 (* h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 22768 (* h1 h1 h1 h1) (* h2 h2) 
(* h3 h3) h5 h6 (* j2 j2 j2)) (* 26624 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h5 h6
 (* j2 j2)) (* 16384 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h5 h6 j2) (* 4096 (* h1
 h1 h1 h1) (* h2 h2) (* h3 h3) h5 h6) (* 8 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 160 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1224 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* 
h6 h6) (* j2 j2 j2 j2 j2)) (* 4752 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6)
 (* j2 j2 j2 j2)) (* 10272 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6) (* j2 
j2 j2)) (* 12480 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6) (* j2 j2)) (* 
7936 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6) j2) (* 2048 (* h1 h1 h1 h1) 
(* h2 h2) (* h3 h3) (* h6 h6)) (* 36 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) 
(* j2 j2 j2 j2 j2 j2)) (* 384 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* j2 j2
 j2 j2 j2)) (* 1572 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2)) 
(* 3192 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2)) (* 3408 (* h1 h1
 h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* j2 j2)) (* 1824 (* h1 h1 h1 h1) (* h2 h2) 
h3 h4 (* h5 h5) j2) (* 384 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5)) (* 4 (* h1
 h1 h1 h1) (* h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 76 (* h1 h1 h1 h1)
 (* h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 540 (* h1 h1 h1 h1) (* h2 h2) 
h3 h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 1908 (* h1 h1 h1 h1) (* h2 h2) h3 h4 h5 h6 
(* j2 j2 j2 j2)) (* 3696 (* h1 h1 h1 h1) (* h2 h2) h3 h4 h5 h6 (* j2 j2 j2)) (* 
3984 (* h1 h1 h1 h1) (* h2 h2) h3 h4 h5 h6 (* j2 j2)) (* 2240 (* h1 h1 h1 h1) 
(* h2 h2) h3 h4 h5 h6 j2) (* 512 (* h1 h1 h1 h1) (* h2 h2) h3 h4 h5 h6) (* 8 (* 
h1 h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 88 (* h1 h1 h1 
h1) (* h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 376 (* h1 h1 h1 h1) (* h2 
h2) h3 h4 (* h6 h6) (* j2 j2 j2 j2)) (* 808 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* 
h6 h6) (* j2 j2 j2)) (* 928 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6) (* j2 j2))
 (* 544 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6) j2) (* 128 (* h1 h1 h1 h1) (* 
h2 h2) h3 h4 (* h6 h6)) (* 6 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* j2 j2 
j2 j2 j2 j2 j2)) (* 88 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2 
j2 j2)) (* 518 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 
1580 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 2696 (* h1 h1
 h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2)) (* 2576 (* h1 h1 h1 h1) (* h2 h2
) h3 (* h5 h5 h5) (* j2 j2)) (* 1280 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) 
j2) (* 256 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5)) (* 2 (* h1 h1 h1 h1) (* h2
 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 48 (* h1 h1 h1 h1) (* h2 h2
) h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 450 (* h1 h1 h1 h1) (* h2 h2) h3 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 2188 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 
h5) h6 (* j2 j2 j2 j2 j2)) (* 6088 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5) h6 (* 
j2 j2 j2 j2)) (* 10000 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2)) 
(* 9536 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5) h6 (* j2 j2)) (* 4864 (* h1 h1 h1
 h1) (* h2 h2) h3 (* h5 h5) h6 j2) (* 1024 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5
) h6) (* 2 (* h1 h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 50 (* h1 h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
466 (* h1 h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2222 (* 
h1 h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 6068 (* h1 h1 h1 
h1) (* h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 9848 (* h1 h1 h1 h1) (* h2 h2)
 h3 h5 (* h6 h6) (* j2 j2 j2)) (* 9360 (* h1 h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6)
 (* j2 j2)) (* 4800 (* h1 h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6) j2) (* 1024 (* h1 
h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6)) (* 4 (* h1 h1 h1 h1) (* h2 h2) h3 (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 60 (* h1 h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 364 (* h1 h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6) (* j2 j2
 j2 j2 j2)) (* 1156 (* h1 h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2 j2)) 
(* 2080 (* h1 h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2)) (* 2128 (* h1 h1
 h1 h1) (* h2 h2) h3 (* h6 h6 h6) (* j2 j2)) (* 1152 (* h1 h1 h1 h1) (* h2 h2) 
h3 (* h6 h6 h6) j2) (* 256 (* h1 h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6)) (* 4 (* h1
 h1 h1 h1) (* h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 48 (* h1 h1 h1
 h1) (* h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 232 (* h1 h1 h1 h1) (* 
h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 592 (* h1 h1 h1 h1) (* h2 h2) h4 
(* h5 h5) h6 (* j2 j2 j2 j2)) (* 868 (* h1 h1 h1 h1) (* h2 h2) h4 (* h5 h5) h6 
(* j2 j2 j2)) (* 736 (* h1 h1 h1 h1) (* h2 h2) h4 (* h5 h5) h6 (* j2 j2)) (* 336
 (* h1 h1 h1 h1) (* h2 h2) h4 (* h5 h5) h6 j2) (* 64 (* h1 h1 h1 h1) (* h2 h2) 
h4 (* h5 h5) h6) (* 2 (* h1 h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 24 (* h1 h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)
) (* 116 (* h1 h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 296 
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
(* 24 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 472 (* 
h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 3808 (* h1 h1 h1 h1
) h2 (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 16160 (* h1 h1 h1 h1) h2 (* h3 h3
 h3) h4 h5 (* j2 j2 j2 j2)) (* 38400 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h5 (* j2
 j2 j2)) (* 50176 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h5 (* j2 j2)) (* 32768 (* 
h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h5 j2) (* 8192 (* h1 h1 h1 h1) h2 (* h3 h3 h3) 
h4 h5) (* 8 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
160 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2)) (* 1320 (* h1 
h1 h1 h1) h2 (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 5776 (* h1 h1 h1 h1) h2 
(* h3 h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 14336 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 
h6 (* j2 j2 j2)) (* 19968 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h6 (* j2 j2)) (* 
14336 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h6 j2) (* 4096 (* h1 h1 h1 h1) h2 (* h3
 h3 h3) h4 h6) (* 36 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2
 j2 j2)) (* 696 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2))
 (* 5488 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 22560 
(* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 51200 (* h1 h1 h1 
h1) h2 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2)) (* 62464 (* h1 h1 h1 h1) h2 (* h3 h3
 h3) (* h5 h5) (* j2 j2)) (* 36864 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) j2)
 (* 8192 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5)) (* 72 (* h1 h1 h1 h1) h2 (* 
h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1320 (* h1 h1 h1 h1) h2 (* h3 h3 h3
) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 9920 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h5 h6 (* 
j2 j2 j2 j2 j2)) (* 39264 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2))
 (* 87424 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h5 h6 (* j2 j2 j2)) (* 108032 (* h1 h1
 h1 h1) h2 (* h3 h3 h3) h5 h6 (* j2 j2)) (* 67584 (* h1 h1 h1 h1) h2 (* h3 h3 h3
) h5 h6 j2) (* 16384 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h5 h6) (* 32 (* h1 h1 h1 h1
) h2 (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 576 (* h1 h1 h1 h1) h2 
(* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4256 (* h1 h1 h1 h1) h2 (* h3 
h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 16640 (* h1 h1 h1 h1) h2 (* h3 h3 h3) 
(* h6 h6) (* j2 j2 j2 j2)) (* 36992 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6) 
(* j2 j2 j2)) (* 46592 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6) (* j2 j2)) (* 
30720 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6) j2) (* 8192 (* h1 h1 h1 h1) h2 
(* h3 h3 h3) (* h6 h6)) (* 72 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* j2 j2
 j2 j2 j2 j2)) (* 912 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 
j2)) (* 4392 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 10176
 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 12000 (* h1 h1 h1 h1
) h2 (* h3 h3) (* h4 h4) h5 (* j2 j2)) (* 6912 (* h1 h1 h1 h1) h2 (* h3 h3) (* 
h4 h4) h5 j2) (* 1536 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5) (* 16 (* h1 h1 
h1 h1) h2 (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 208 (* h1 h1 h1 h1) 
h2 (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 1040 (* h1 h1 h1 h1) h2 (* h3 
h3) (* h4 h4) h6 (* j2 j2 j2 j2)) (* 2544 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4)
 h6 (* j2 j2 j2)) (* 3232 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h6 (* j2 j2)) 
(* 2048 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h6 j2) (* 512 (* h1 h1 h1 h1) h2 
(* h3 h3) (* h4 h4) h6) (* 48 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* j2 j2
 j2 j2 j2 j2 j2)) (* 800 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 
j2 j2 j2)) (* 5360 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2))
 (* 18496 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 35136 
(* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 36608 (* h1 h1 h1 h1)
 h2 (* h3 h3) h4 (* h5 h5) (* j2 j2)) (* 19456 (* h1 h1 h1 h1) h2 (* h3 h3) h4 
(* h5 h5) j2) (* 4096 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5)) (* 2 (* h1 h1 
h1 h1) h2 (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 94 (* h1 h1 h1 h1) 
h2 (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1386 (* h1 h1 h1 h1) h2 (* h3
 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 9106 (* h1 h1 h1 h1) h2 (* h3 h3) h4 h5 
h6 (* j2 j2 j2 j2 j2)) (* 31060 (* h1 h1 h1 h1) h2 (* h3 h3) h4 h5 h6 (* j2 j2 
j2 j2)) (* 58576 (* h1 h1 h1 h1) h2 (* h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 61184 
(* h1 h1 h1 h1) h2 (* h3 h3) h4 h5 h6 (* j2 j2)) (* 33024 (* h1 h1 h1 h1) h2 (* 
h3 h3) h4 h5 h6 j2) (* 7168 (* h1 h1 h1 h1) h2 (* h3 h3) h4 h5 h6) (* 8 (* h1 h1
 h1 h1) h2 (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 200 (* h1 h1 h1 
h1) h2 (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1640 (* h1 h1 h1 h1) h2 
(* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 6360 (* h1 h1 h1 h1) h2 (* h3 h3) 
h4 (* h6 h6) (* j2 j2 j2 j2)) (* 13168 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6)
 (* j2 j2 j2)) (* 14912 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6) (* j2 j2)) (* 
8704 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6) j2) (* 2048 (* h1 h1 h1 h1) h2 
(* h3 h3) h4 (* h6 h6)) (* 36 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* j2 j2
 j2 j2 j2 j2 j2)) (* 588 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 
j2 j2 j2)) (* 3832 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2))
 (* 12720 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 22880 
(* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* j2 j2 j2)) (* 22144 (* h1 h1 h1 h1)
 h2 (* h3 h3) (* h5 h5 h5) (* j2 j2)) (* 10752 (* h1 h1 h1 h1) h2 (* h3 h3) (* 
h5 h5 h5) j2) (* 2048 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5)) (* 12 (* h1 h1 
h1 h1) h2 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 320 (* h1 h1 h1
 h1) h2 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 3244 (* h1 h1 h1 h1)
 h2 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 16808 (* h1 h1 h1 h1) h2 
(* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 49168 (* h1 h1 h1 h1) h2 (* h3 h3)
 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 83424 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5) 
h6 (* j2 j2 j2)) (* 80384 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5) h6 (* j2 j2)) 
(* 40448 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5) h6 j2) (* 8192 (* h1 h1 h1 h1) 
h2 (* h3 h3) (* h5 h5) h6) (* 12 (* h1 h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 340 (* h1 h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 3436 (* h1 h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 17292 (* h1 h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 48744 (* h1 h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 
80256 (* h1 h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 76416 (* h1 h1 
h1 h1) h2 (* h3 h3) h5 (* h6 h6) (* j2 j2)) (* 38912 (* h1 h1 h1 h1) h2 (* h3 h3
) h5 (* h6 h6) j2) (* 8192 (* h1 h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6)) (* 32 (* 
h1 h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 480 (* h1 h1
 h1 h1) h2 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2912 (* h1 h1 h1 h1)
 h2 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 9248 (* h1 h1 h1 h1) h2 (* h3 
h3) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 16640 (* h1 h1 h1 h1) h2 (* h3 h3) (* h6 h6
 h6) (* j2 j2 j2)) (* 17024 (* h1 h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6) (* j2 j2))
 (* 9216 (* h1 h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6) j2) (* 2048 (* h1 h1 h1 h1) 
h2 (* h3 h3) (* h6 h6 h6)) (* 72 (* h1 h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* j2
 j2 j2 j2 j2 j2)) (* 696 (* h1 h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 
j2 j2)) (* 2520 (* h1 h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 
4488 (* h1 h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 4224 (* h1 h1 h1
 h1) h2 h3 (* h4 h4) (* h5 h5) (* j2 j2)) (* 2016 (* h1 h1 h1 h1) h2 h3 (* h4 h4
) (* h5 h5) j2) (* 384 (* h1 h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5)) (* 4 (* h1 h1 
h1 h1) h2 h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 72 (* h1 h1 h1 h1) h2 
h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 472 (* h1 h1 h1 h1) h2 h3 (* h4 h4)
 h5 h6 (* j2 j2 j2 j2 j2)) (* 1504 (* h1 h1 h1 h1) h2 h3 (* h4 h4) h5 h6 (* j2 
j2 j2 j2)) (* 2596 (* h1 h1 h1 h1) h2 h3 (* h4 h4) h5 h6 (* j2 j2 j2)) (* 2488 
(* h1 h1 h1 h1) h2 h3 (* h4 h4) h5 h6 (* j2 j2)) (* 1248 (* h1 h1 h1 h1) h2 h3 
(* h4 h4) h5 h6 j2) (* 256 (* h1 h1 h1 h1) h2 h3 (* h4 h4) h5 h6) (* 24 (* h1 h1
 h1 h1) h2 h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 328 (* h1 h1 h1 h1) 
h2 h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1768 (* h1 h1 h1 h1) h2 h3 h4 
(* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 4856 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5 h5) 
(* j2 j2 j2 j2)) (* 7392 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5 h5) (* j2 j2 j2)) (* 
6304 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5 h5) (* j2 j2)) (* 2816 (* h1 h1 h1 h1) h2
 h3 h4 (* h5 h5 h5) j2) (* 512 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5 h5)) (* 4 (* h1
 h1 h1 h1) h2 h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 128 (* h1 h1 h1
 h1) h2 h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1304 (* h1 h1 h1 h1) h2 
h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 6304 (* h1 h1 h1 h1) h2 h3 h4 (* h5
 h5) h6 (* j2 j2 j2 j2 j2)) (* 16532 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5) h6 (* j2
 j2 j2 j2)) (* 24768 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5) h6 (* j2 j2 j2)) (* 
21168 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5) h6 (* j2 j2)) (* 9600 (* h1 h1 h1 h1) 
h2 h3 h4 (* h5 h5) h6 j2) (* 1792 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5) h6) (* 2 
(* h1 h1 h1 h1) h2 h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 68 (* h1 
h1 h1 h1) h2 h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 684 (* h1 h1 h1 h1)
 h2 h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3248 (* h1 h1 h1 h1) h2 h3 h4 
h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 8466 (* h1 h1 h1 h1) h2 h3 h4 h5 (* h6 h6) 
(* j2 j2 j2 j2)) (* 12796 (* h1 h1 h1 h1) h2 h3 h4 h5 (* h6 h6) (* j2 j2 j2)) 
(* 11184 (* h1 h1 h1 h1) h2 h3 h4 h5 (* h6 h6) (* j2 j2)) (* 5248 (* h1 h1 h1 h1
) h2 h3 h4 h5 (* h6 h6) j2) (* 1024 (* h1 h1 h1 h1) h2 h3 h4 h5 (* h6 h6)) (* 12
 (* h1 h1 h1 h1) h2 h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 212 (* h1
 h1 h1 h1) h2 h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1540 (* h1 h1 h1 
h1) h2 h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 5964 (* h1 h1 h1 h1) h2 h3 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 13408 (* h1 h1 h1 h1) h2 h3 (* h5 h5 h5) 
h6 (* j2 j2 j2 j2)) (* 17936 (* h1 h1 h1 h1) h2 h3 (* h5 h5 h5) h6 (* j2 j2 j2))
 (* 14016 (* h1 h1 h1 h1) h2 h3 (* h5 h5 h5) h6 (* j2 j2)) (* 5888 (* h1 h1 h1 
h1) h2 h3 (* h5 h5 h5) h6 j2) (* 1024 (* h1 h1 h1 h1) h2 h3 (* h5 h5 h5) h6) (* 
(* h1 h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 40 
(* h1 h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 512 
(* h1 h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3226 (* 
h1 h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 11567 (* h1 h1 
h1 h1) h2 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 25006 (* h1 h1 h1 h1) h2
 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 33056 (* h1 h1 h1 h1) h2 h3 (* h5 h5
) (* h6 h6) (* j2 j2 j2)) (* 26080 (* h1 h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6) (* 
j2 j2)) (* 11264 (* h1 h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6) j2) (* 2048 (* h1 h1 
h1 h1) h2 h3 (* h5 h5) (* h6 h6)) (* 12 (* h1 h1 h1 h1) h2 h3 h5 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 200 (* h1 h1 h1 h1) h2 h3 h5 (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 1384 (* h1 h1 h1 h1) h2 h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2
 j2 j2)) (* 5184 (* h1 h1 h1 h1) h2 h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
11500 (* h1 h1 h1 h1) h2 h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 15512 (* h1 h1 
h1 h1) h2 h3 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 12480 (* h1 h1 h1 h1) h2 h3 h5 (* 
h6 h6 h6) (* j2 j2)) (* 5504 (* h1 h1 h1 h1) h2 h3 h5 (* h6 h6 h6) j2) (* 1024 
(* h1 h1 h1 h1) h2 h3 h5 (* h6 h6 h6)) (* 4 (* h1 h1 h1 h1) h2 (* h4 h4) (* h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 44 (* h1 h1 h1 h1) h2 (* h4 h4) (* h5 h5) h6
 (* j2 j2 j2 j2 j2 j2)) (* 192 (* h1 h1 h1 h1) h2 (* h4 h4) (* h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* 440 (* h1 h1 h1 h1) h2 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) 
(* 580 (* h1 h1 h1 h1) h2 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 444 (* h1 h1 
h1 h1) h2 (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 184 (* h1 h1 h1 h1) h2 (* h4 h4) 
(* h5 h5) h6 j2) (* 32 (* h1 h1 h1 h1) h2 (* h4 h4) (* h5 h5) h6) (* 2 (* h1 h1 
h1 h1) h2 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 30 (* h1 h1 h1 h1) 
h2 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 184 (* h1 h1 h1 h1) h2 h4 (* 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 604 (* h1 h1 h1 h1) h2 h4 (* h5 h5 h5) h6
 (* j2 j2 j2 j2 j2)) (* 1170 (* h1 h1 h1 h1) h2 h4 (* h5 h5 h5) h6 (* j2 j2 j2 
j2)) (* 1382 (* h1 h1 h1 h1) h2 h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 980 (* h1 h1
 h1 h1) h2 h4 (* h5 h5 h5) h6 (* j2 j2)) (* 384 (* h1 h1 h1 h1) h2 h4 (* h5 h5 
h5) h6 j2) (* 64 (* h1 h1 h1 h1) h2 h4 (* h5 h5 h5) h6) (* 4 (* h1 h1 h1 h1) h2 
h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 60 (* h1 h1 h1 h1) h2 h4 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 368 (* h1 h1 h1 h1) h2 h4 (* h5
 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1208 (* h1 h1 h1 h1) h2 h4 (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 2340 (* h1 h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2)) (* 2764 (* h1 h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2))
 (* 1960 (* h1 h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 768 (* h1 h1 h1
 h1) h2 h4 (* h5 h5) (* h6 h6) j2) (* 128 (* h1 h1 h1 h1) h2 h4 (* h5 h5) (* h6 
h6)) (* (* h1 h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 19 (* h1 h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 152 (* h1 h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
670 (* h1 h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1793 (* 
h1 h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 3031 (* h1 h1 h1 
h1) h2 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 3254 (* h1 h1 h1 h1) h2 (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2)) (* 2152 (* h1 h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6)
 (* j2 j2)) (* 800 (* h1 h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6) j2) (* 128 (* h1 h1
 h1 h1) h2 (* h5 h5 h5) (* h6 h6)) (* (* h1 h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 19 (* h1 h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 152 (* h1 h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 670 (* h1 h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2)) (* 1793 (* h1 h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2)) (* 3031 (* h1 h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 
3254 (* h1 h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 2152 (* h1 h1 h1
 h1) h2 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 800 (* h1 h1 h1 h1) h2 (* h5 h5) 
(* h6 h6 h6) j2) (* 128 (* h1 h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6)) (* 24 (* h1 
h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 448 (* h1 h1 h1
 h1) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 3384 (* h1 h1 h1 h1) 
(* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 13200 (* h1 h1 h1 h1) (* h3 h3 
h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 28160 (* h1 h1 h1 h1) (* h3 h3 h3) (* h4 h4
) h5 (* j2 j2 j2)) (* 32256 (* h1 h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2))
 (* 18432 (* h1 h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 j2) (* 4096 (* h1 h1 h1 h1) 
(* h3 h3 h3) (* h4 h4) h5) (* 72 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* j2
 j2 j2 j2 j2 j2 j2)) (* 1320 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 
j2 j2 j2 j2)) (* 9728 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 
j2)) (* 36640 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 
74240 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 78848 (* h1 h1 
h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2)) (* 40960 (* h1 h1 h1 h1) (* h3 h3 h3
) h4 (* h5 h5) j2) (* 8192 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5)) (* 12 (* 
h1 h1 h1 h1) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 368 (* h1 h1 
h1 h1) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 4188 (* h1 h1 h1 h1) 
(* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 24088 (* h1 h1 h1 h1) (* h3 h3 
h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 77472 (* h1 h1 h1 h1) (* h3 h3 h3) h4 h5 h6 
(* j2 j2 j2 j2)) (* 142720 (* h1 h1 h1 h1) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2)) 
(* 146944 (* h1 h1 h1 h1) (* h3 h3 h3) h4 h5 h6 (* j2 j2)) (* 77824 (* h1 h1 h1 
h1) (* h3 h3 h3) h4 h5 h6 j2) (* 16384 (* h1 h1 h1 h1) (* h3 h3 h3) h4 h5 h6) 
(* 36 (* h1 h1 h1 h1) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
804 (* h1 h1 h1 h1) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 7504 
(* h1 h1 h1 h1) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 37776 (* h1 
h1 h1 h1) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 110400 (* h1 h1 h1 h1
) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 187904 (* h1 h1 h1 h1) (* h3 h3 
h3) (* h5 h5) h6 (* j2 j2 j2)) (* 178176 (* h1 h1 h1 h1) (* h3 h3 h3) (* h5 h5) 
h6 (* j2 j2)) (* 86016 (* h1 h1 h1 h1) (* h3 h3 h3) (* h5 h5) h6 j2) (* 16384 
(* h1 h1 h1 h1) (* h3 h3 h3) (* h5 h5) h6) (* 48 (* h1 h1 h1 h1) (* h3 h3 h3) h5
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 992 (* h1 h1 h1 h1) (* h3 h3 h3) h5 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 8560 (* h1 h1 h1 h1) (* h3 h3 h3) h5 (* 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 39936 (* h1 h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6)
 (* j2 j2 j2 j2 j2)) (* 109120 (* h1 h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6) (* j2 
j2 j2 j2)) (* 177152 (* h1 h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 
165888 (* h1 h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2)) (* 81920 (* h1 h1 h1
 h1) (* h3 h3 h3) h5 (* h6 h6) j2) (* 16384 (* h1 h1 h1 h1) (* h3 h3 h3) h5 (* 
h6 h6)) (* 48 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) 
(* 560 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 2416 (* 
h1 h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 4880 (* h1 h1 h1 h1) 
(* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 5024 (* h1 h1 h1 h1) (* h3 h3) (* h4 
h4 h4) h5 (* j2 j2)) (* 2560 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 j2) (* 
512 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5) (* 48 (* h1 h1 h1 h1) (* h3 h3) 
(* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 752 (* h1 h1 h1 h1) (* h3 h3) 
(* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 4656 (* h1 h1 h1 h1) (* h3 h3) (* 
h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 14544 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4
) (* h5 h5) (* j2 j2 j2 j2)) (* 24544 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 
h5) (* j2 j2 j2)) (* 22656 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 
j2)) (* 10752 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) j2) (* 2048 (* h1 h1
 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5)) (* 48 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4)
 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 944 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) h5 
h6 (* j2 j2 j2 j2 j2 j2)) (* 6512 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) h5 h6 (* 
j2 j2 j2 j2 j2)) (* 21264 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 
j2)) (* 36512 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 33920 
(* h1 h1 h1 h1) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 16128 (* h1 h1 h1 h1) 
(* h3 h3) (* h4 h4) h5 h6 j2) (* 3072 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) h5 h6)
 (* 72 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
1104 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 6632 
(* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 19840 (* h1 h1 
h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 31520 (* h1 h1 h1 h1) (* h3
 h3) h4 (* h5 h5 h5) (* j2 j2 j2)) (* 27008 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 
h5 h5) (* j2 j2)) (* 11776 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) j2) (* 2048
 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5)) (* 36 (* h1 h1 h1 h1) (* h3 h3) h4 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 804 (* h1 h1 h1 h1) (* h3 h3) h4 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 7060 (* h1 h1 h1 h1) (* h3 h3) h4 (* 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 31948 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5)
 h6 (* j2 j2 j2 j2 j2)) (* 81464 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5) h6 (* j2
 j2 j2 j2)) (* 120192 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) 
(* 101248 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 45056 (* h1 h1
 h1 h1) (* h3 h3) h4 (* h5 h5) h6 j2) (* 8192 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5
 h5) h6) (* 12 (* h1 h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2
 j2)) (* 428 (* h1 h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2))
 (* 4540 (* h1 h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
22436 (* h1 h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 59528 (* 
h1 h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 89344 (* h1 h1 h1 h1)
 (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 75776 (* h1 h1 h1 h1) (* h3 h3) h4 
h5 (* h6 h6) (* j2 j2)) (* 33792 (* h1 h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6) j2) 
(* 6144 (* h1 h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6)) (* 36 (* h1 h1 h1 h1) (* h3 
h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 696 (* h1 h1 h1 h1) (* h3 h3
) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 5524 (* h1 h1 h1 h1) (* h3 h3) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 23184 (* h1 h1 h1 h1) (* h3 h3) (* h5 
h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 55440 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5 h5) h6
 (* j2 j2 j2 j2)) (* 76544 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2
)) (* 59904 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2)) (* 24576 (* h1 
h1 h1 h1) (* h3 h3) (* h5 h5 h5) h6 j2) (* 4096 (* h1 h1 h1 h1) (* h3 h3) (* h5 
h5 h5) h6) (* 6 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 190 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 2278 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 14138 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2
 j2 j2 j2 j2)) (* 50780 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2)) (* 110096 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2)) (* 144832 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 
112384 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 47104 (* h1 
h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6) j2) (* 8192 (* h1 h1 h1 h1) (* h3 h3) 
(* h5 h5) (* h6 h6)) (* 48 (* h1 h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 848 (* h1 h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 6160 (* h1 h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 23856 (* h1 h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 53632 (* h1 h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 71744 (* 
h1 h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 56064 (* h1 h1 h1 h1) 
(* h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 23552 (* h1 h1 h1 h1) (* h3 h3) h5 (* h6
 h6 h6) j2) (* 4096 (* h1 h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6)) (* 48 (* h1 h1 h1
 h1) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 416 (* h1 h1 h1 h1) h3 
(* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 1312 (* h1 h1 h1 h1) h3 (* h4 h4 
h4) (* h5 h5) (* j2 j2 j2 j2)) (* 2048 (* h1 h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5)
 (* j2 j2 j2)) (* 1712 (* h1 h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 
736 (* h1 h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) j2) (* 128 (* h1 h1 h1 h1) h3 (* 
h4 h4 h4) (* h5 h5)) (* 24 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2
 j2 j2 j2 j2)) (* 304 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 
j2 j2)) (* 1488 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) 
(* 3648 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 4952 (* h1
 h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 3792 (* h1 h1 h1 h1) h3 
(* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 1536 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5 
h5) j2) (* 256 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5)) (* 72 (* h1 h1 h1 h1) 
h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 912 (* h1 h1 h1 h1) h3 
(* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 4464 (* h1 h1 h1 h1) h3 (* h4 
h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 10944 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5
 h5) h6 (* j2 j2 j2 j2)) (* 14856 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5) h6 (* 
j2 j2 j2)) (* 11376 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 4608
 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5) h6 j2) (* 768 (* h1 h1 h1 h1) h3 (* h4 
h4) (* h5 h5) h6) (* 24 (* h1 h1 h1 h1) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 400 (* h1 h1 h1 h1) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)
) (* 2704 (* h1 h1 h1 h1) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 9600 
(* h1 h1 h1 h1) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 19544 (* h1 h1 h1 
h1) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 23600 (* h1 h1 h1 h1) h3 h4 (* h5 
h5 h5) h6 (* j2 j2 j2)) (* 16704 (* h1 h1 h1 h1) h3 h4 (* h5 h5 h5) h6 (* j2 j2)
) (* 6400 (* h1 h1 h1 h1) h3 h4 (* h5 h5 h5) h6 j2) (* 1024 (* h1 h1 h1 h1) h3 
h4 (* h5 h5 h5) h6) (* 36 (* h1 h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 600 (* h1 h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2
 j2 j2 j2)) (* 4056 (* h1 h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 14400 (* h1 h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
29316 (* h1 h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 35400 (* h1 
h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 25056 (* h1 h1 h1 h1) h3 h4
 (* h5 h5) (* h6 h6) (* j2 j2)) (* 9600 (* h1 h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6
) j2) (* 1536 (* h1 h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6)) (* 6 (* h1 h1 h1 h1) h3
 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 124 (* h1 h1 h1 h1) 
h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1076 (* h1 h1 h1 h1) 
h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 5104 (* h1 h1 h1 h1) h3 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 14486 (* h1 h1 h1 h1) h3 (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 25444 (* h1 h1 h1 h1) h3 (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2)) (* 27776 (* h1 h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2)) (* 18304 (* h1 h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 
6656 (* h1 h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6) j2) (* 1024 (* h1 h1 h1 h1) h3 
(* h5 h5 h5) (* h6 h6)) (* 6 (* h1 h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 124 (* h1 h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2
 j2 j2 j2 j2 j2 j2)) (* 1076 (* h1 h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 5104 (* h1 h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 14486 (* h1 h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)
) (* 25444 (* h1 h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 27776 
(* h1 h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 18304 (* h1 h1 h1 h1)
 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 6656 (* h1 h1 h1 h1) h3 (* h5 h5) (* h6
 h6 h6) j2) (* 1024 (* h1 h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6)) (* 6 (* h1 h1 h1)
 (* h2 h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2 j2)) (* 64 (* h1 h1 h1) (* h2 h2 h2
 h2) (* h3 h3) h5 (* j2 j2 j2 j2)) (* 256 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3)
 h5 (* j2 j2 j2)) (* 480 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 (* j2 j2)) 
(* 416 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 j2) (* 128 (* h1 h1 h1) (* h2 
h2 h2 h2) (* h3 h3) h5) (* 4 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h6 (* j2 j2 
j2 j2 j2)) (* 44 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h6 (* j2 j2 j2 j2)) (* 
184 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h6 (* j2 j2 j2)) (* 368 (* h1 h1 h1) 
(* h2 h2 h2 h2) (* h3 h3) h6 (* j2 j2)) (* 352 (* h1 h1 h1) (* h2 h2 h2 h2) (* 
h3 h3) h6 j2) (* 128 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h6) (* 6 (* h1 h1 h1
) (* h2 h2 h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 46 (* h1 h1 h1) (* h2 h2 
h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2)) (* 136 (* h1 h1 h1) (* h2 h2 h2 h2) h3 (* 
h5 h5) (* j2 j2 j2)) (* 192 (* h1 h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) (* j2 j2))
 (* 128 (* h1 h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) j2) (* 32 (* h1 h1 h1) (* h2 
h2 h2 h2) h3 (* h5 h5)) (* (* h1 h1 h1) (* h2 h2 h2 h2) h3 h5 h6 (* j2 j2 j2 j2 
j2 j2)) (* 16 (* h1 h1 h1) (* h2 h2 h2 h2) h3 h5 h6 (* j2 j2 j2 j2 j2)) (* 89 
(* h1 h1 h1) (* h2 h2 h2 h2) h3 h5 h6 (* j2 j2 j2 j2)) (* 238 (* h1 h1 h1) (* h2
 h2 h2 h2) h3 h5 h6 (* j2 j2 j2)) (* 332 (* h1 h1 h1) (* h2 h2 h2 h2) h3 h5 h6 
(* j2 j2)) (* 232 (* h1 h1 h1) (* h2 h2 h2 h2) h3 h5 h6 j2) (* 64 (* h1 h1 h1) 
(* h2 h2 h2 h2) h3 h5 h6) (* 4 (* h1 h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6) (* j2 
j2 j2 j2 j2)) (* 32 (* h1 h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6) (* j2 j2 j2 j2)) 
(* 100 (* h1 h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6) (* j2 j2 j2)) (* 152 (* h1 h1 
h1) (* h2 h2 h2 h2) h3 (* h6 h6) (* j2 j2)) (* 112 (* h1 h1 h1) (* h2 h2 h2 h2) 
h3 (* h6 h6) j2) (* 32 (* h1 h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6)) (* (* h1 h1 h1
) (* h2 h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 9 (* h1 h1 h1) (* h2 h2
 h2 h2) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 33 (* h1 h1 h1) (* h2 h2 h2 h2) (* 
h5 h5) h6 (* j2 j2 j2 j2)) (* 63 (* h1 h1 h1) (* h2 h2 h2 h2) (* h5 h5) h6 (* j2
 j2 j2)) (* 66 (* h1 h1 h1) (* h2 h2 h2 h2) (* h5 h5) h6 (* j2 j2)) (* 36 (* h1 
h1 h1) (* h2 h2 h2 h2) (* h5 h5) h6 j2) (* 8 (* h1 h1 h1) (* h2 h2 h2 h2) (* h5 
h5) h6) (* (* h1 h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 9
 (* h1 h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 33 (* h1 h1 h1
) (* h2 h2 h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 63 (* h1 h1 h1) (* h2 h2 h2 
h2) h5 (* h6 h6) (* j2 j2 j2)) (* 66 (* h1 h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6) 
(* j2 j2)) (* 36 (* h1 h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6) j2) (* 8 (* h1 h1 h1)
 (* h2 h2 h2 h2) h5 (* h6 h6)) (* 12 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 
(* j2 j2 j2 j2 j2 j2)) (* 200 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2
 j2 j2 j2)) (* 1328 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2)) 
(* 4448 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2)) (* 7808 (* h1 h1
 h1) (* h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2)) (* 6656 (* h1 h1 h1) (* h2 h2 h2) 
(* h3 h3 h3) h5 j2) (* 2048 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5) (* 8 (* 
h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2 j2 j2 j2)) (* 136 (* h1 h1 h1
) (* h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2 j2 j2)) (* 928 (* h1 h1 h1) (* h2 h2 
h2) (* h3 h3 h3) h6 (* j2 j2 j2 j2)) (* 3232 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 
h3) h6 (* j2 j2 j2)) (* 6016 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2)
) (* 5632 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h6 j2) (* 2048 (* h1 h1 h1) (* 
h2 h2 h2) (* h3 h3 h3) h6) (* 24 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 (* j2
 j2 j2 j2 j2 j2)) (* 352 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2 
j2 j2)) (* 1976 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2)) (* 
5392 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2)) (* 7520 (* h1 h1 h1
) (* h2 h2 h2) (* h3 h3) h4 h5 (* j2 j2)) (* 5056 (* h1 h1 h1) (* h2 h2 h2) (* 
h3 h3) h4 h5 j2) (* 1280 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5) (* 12 (* h1 
h1 h1) (* h2 h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2)) (* 176 (* h1 h1 h1) 
(* h2 h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 1004 (* h1 h1 h1) (* h2 h2 
h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 2840 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3)
 h4 h6 (* j2 j2 j2)) (* 4208 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h6 (* j2 j2)
) (* 3104 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h6 j2) (* 896 (* h1 h1 h1) (* 
h2 h2 h2) (* h3 h3) h4 h6) (* 24 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) 
(* j2 j2 j2 j2 j2 j2)) (* 328 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) (* 
j2 j2 j2 j2 j2)) (* 1744 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 
j2 j2)) (* 4576 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2)) (* 
6208 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) (* j2 j2)) (* 4096 (* h1 h1 
h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) j2) (* 1024 (* h1 h1 h1) (* h2 h2 h2) (* h3
 h3) (* h5 h5)) (* 2 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2
 j2 j2)) (* 70 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2)) 
(* 736 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 3484 (* 
h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 8592 (* h1 h1 h1) (* 
h2 h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2)) (* 11408 (* h1 h1 h1) (* h2 h2 h2) (* h3
 h3) h5 h6 (* j2 j2)) (* 7680 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 h6 j2) (* 
2048 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 h6) (* 20 (* h1 h1 h1) (* h2 h2 h2) 
(* h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 280 (* h1 h1 h1) (* h2 h2 h2) (* 
h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1476 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3)
 (* h6 h6) (* j2 j2 j2 j2)) (* 3856 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6
) (* j2 j2 j2)) (* 5328 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2))
 (* 3712 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6) j2) (* 1024 (* h1 h1 h1) 
(* h2 h2 h2) (* h3 h3) (* h6 h6)) (* 24 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5
) (* j2 j2 j2 j2 j2 j2)) (* 280 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) (* j2 
j2 j2 j2 j2)) (* 1208 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2))
 (* 2536 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2)) (* 2768 (* h1 
h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2)) (* 1504 (* h1 h1 h1) (* h2 h2 h2)
 h3 h4 (* h5 h5) j2) (* 320 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5)) (* 3 (* 
h1 h1 h1) (* h2 h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 59 (* h1 h1 h1) 
(* h2 h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 435 (* h1 h1 h1) (* h2 h2 h2)
 h3 h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 1581 (* h1 h1 h1) (* h2 h2 h2) h3 h4 h5 h6 
(* j2 j2 j2 j2)) (* 3126 (* h1 h1 h1) (* h2 h2 h2) h3 h4 h5 h6 (* j2 j2 j2)) (* 
3420 (* h1 h1 h1) (* h2 h2 h2) h3 h4 h5 h6 (* j2 j2)) (* 1944 (* h1 h1 h1) (* h2
 h2 h2) h3 h4 h5 h6 j2) (* 448 (* h1 h1 h1) (* h2 h2 h2) h3 h4 h5 h6) (* 8 (* h1
 h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 88 (* h1 h1 h1) 
(* h2 h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 376 (* h1 h1 h1) (* h2 h2 h2
) h3 h4 (* h6 h6) (* j2 j2 j2 j2)) (* 808 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h6 
h6) (* j2 j2 j2)) (* 928 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6) (* j2 j2)) 
(* 544 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6) j2) (* 128 (* h1 h1 h1) (* h2 
h2 h2) h3 h4 (* h6 h6)) (* 12 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) (* j2 j2
 j2 j2 j2 j2)) (* 128 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2 
j2)) (* 524 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 1064 
(* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2)) (* 1136 (* h1 h1 h1) (* 
h2 h2 h2) h3 (* h5 h5 h5) (* j2 j2)) (* 608 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 
h5 h5) j2) (* 128 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5)) (* 4 (* h1 h1 h1) 
(* h2 h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 80 (* h1 h1 h1) (* h2 
h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 580 (* h1 h1 h1) (* h2 h2 h2) 
h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 2056 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 
h5) h6 (* j2 j2 j2 j2)) (* 3952 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) h6 (* j2 
j2 j2)) (* 4192 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) h6 (* j2 j2)) (* 2304 (* 
h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) h6 j2) (* 512 (* h1 h1 h1) (* h2 h2 h2) h3 
(* h5 h5) h6) (* 5 (* h1 h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 91 (* h1 h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 615 (* h1 h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2085 (* 
h1 h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 3912 (* h1 h1 h1) (* 
h2 h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2)) (* 4116 (* h1 h1 h1) (* h2 h2 h2) h3 h5 
(* h6 h6) (* j2 j2)) (* 2272 (* h1 h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6) j2) (* 
512 (* h1 h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6)) (* 8 (* h1 h1 h1) (* h2 h2 h2) h3
 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 88 (* h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6
 h6) (* j2 j2 j2 j2 j2)) (* 376 (* h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6) (* j2 
j2 j2 j2)) (* 808 (* h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2)) (* 928
 (* h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6) (* j2 j2)) (* 544 (* h1 h1 h1) (* h2 
h2 h2) h3 (* h6 h6 h6) j2) (* 128 (* h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6)) (* 
3 (* h1 h1 h1) (* h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 38 (* 
h1 h1 h1) (* h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 190 (* h1 h1 h1
) (* h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 496 (* h1 h1 h1) (* h2 h2 
h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 739 (* h1 h1 h1) (* h2 h2 h2) h4 (* h5 
h5) h6 (* j2 j2 j2)) (* 634 (* h1 h1 h1) (* h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2))
 (* 292 (* h1 h1 h1) (* h2 h2 h2) h4 (* h5 h5) h6 j2) (* 56 (* h1 h1 h1) (* h2 
h2 h2) h4 (* h5 h5) h6) (* 2 (* h1 h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 24 (* h1 h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 116 (* h1 h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
296 (* h1 h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 434 (* h1 h1 
h1) (* h2 h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 368 (* h1 h1 h1) (* h2 h2 h2) 
h4 h5 (* h6 h6) (* j2 j2)) (* 168 (* h1 h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6) j2) 
(* 32 (* h1 h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6)) (* 2 (* h1 h1 h1) (* h2 h2 h2) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 24 (* h1 h1 h1) (* h2 h2 h2) (* h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 116 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2)) (* 296 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2
 j2 j2)) (* 434 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 368 
(* h1 h1 h1) (* h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2)) (* 168 (* h1 h1 h1) (* h2 
h2 h2) (* h5 h5 h5) h6 j2) (* 32 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5 h5) h6) (* 4
 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 48 
(* h1 h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 232 (* 
h1 h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 592 (* h1 h1 
h1) (* h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 868 (* h1 h1 h1) (* h2 
h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 736 (* h1 h1 h1) (* h2 h2 h2) (* h5 
h5) (* h6 h6) (* j2 j2)) (* 336 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6) j2
) (* 64 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6)) (* 2 (* h1 h1 h1) (* h2 
h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 24 (* h1 h1 h1) (* h2 h2 h2)
 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 116 (* h1 h1 h1) (* h2 h2 h2) h5 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 296 (* h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6) 
(* j2 j2 j2 j2)) (* 434 (* h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2)) 
(* 368 (* h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2)) (* 168 (* h1 h1 h1) 
(* h2 h2 h2) h5 (* h6 h6 h6) j2) (* 32 (* h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6)
) (* 6 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 
124 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2 j2 j2 j2 j2)) (* 1064 (* 
h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2 j2 j2 j2)) (* 4880 (* h1 h1 h1) 
(* h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2 j2 j2)) (* 12800 (* h1 h1 h1) (* h2 h2) 
(* h3 h3 h3 h3) h5 (* j2 j2 j2)) (* 18944 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3)
 h5 (* j2 j2)) (* 14336 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 j2) (* 4096 
(* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5) (* 4 (* h1 h1 h1) (* h2 h2) (* h3 h3 
h3 h3) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 84 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3)
 h6 (* j2 j2 j2 j2 j2 j2)) (* 736 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h6 (* 
j2 j2 j2 j2 j2)) (* 3472 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2 j2 
j2)) (* 9472 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2 j2)) (* 14848 
(* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2)) (* 12288 (* h1 h1 h1) (* h2
 h2) (* h3 h3 h3 h3) h6 j2) (* 4096 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h6) 
(* 24 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 496
 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 4184 (* h1 
h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 18464 (* h1 h1 h1) 
(* h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2)) (* 45344 (* h1 h1 h1) (* h2 h2) 
(* h3 h3 h3) h4 h5 (* j2 j2 j2)) (* 60800 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4
 h5 (* j2 j2)) (* 40448 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 j2) (* 10240 
(* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5) (* 12 (* h1 h1 h1) (* h2 h2) (* h3 h3
 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 240 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) 
h4 h6 (* j2 j2 j2 j2 j2 j2)) (* 1980 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h6 
(* j2 j2 j2 j2 j2)) (* 8664 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 
j2 j2)) (* 21504 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2)) (* 
29952 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2)) (* 21504 (* h1 h1 h1)
 (* h2 h2) (* h3 h3 h3) h4 h6 j2) (* 6144 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4
 h6) (* 18 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2
)) (* 354 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) 
(* 2988 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 
13576 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 34416 
(* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2)) (* 46528 (* h1 h1 h1
) (* h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2)) (* 29952 (* h1 h1 h1) (* h2 h2) 
(* h3 h3 h3) (* h5 h5) j2) (* 7168 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5)
) (* (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
58 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 881 
(* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 6460 (* h1 
h1 h1) (* h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 26532 (* h1 h1 h1) 
(* h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 62880 (* h1 h1 h1) (* h2 h2) 
(* h3 h3 h3) h5 h6 (* j2 j2 j2)) (* 83200 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5
 h6 (* j2 j2)) (* 55552 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 h6 j2) (* 14336 
(* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 h6) (* 20 (* h1 h1 h1) (* h2 h2) (* h3 h3
 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 368 (* h1 h1 h1) (* h2 h2) (* h3 h3 
h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2852 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3)
 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 11848 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* 
h6 h6) (* j2 j2 j2 j2)) (* 28032 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6) 
(* j2 j2 j2)) (* 37376 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2)) 
(* 25856 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6) j2) (* 7168 (* h1 h1 h1) 
(* h2 h2) (* h3 h3 h3) (* h6 h6)) (* 108 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 
h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 1368 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4)
 h5 (* j2 j2 j2 j2 j2)) (* 6588 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 
(* j2 j2 j2 j2)) (* 15264 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2
 j2)) (* 18000 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2)) (* 10368
 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 j2) (* 2304 (* h1 h1 h1) (* h2 h2
) (* h3 h3) (* h4 h4) h5) (* 32 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h6 
(* j2 j2 j2 j2 j2 j2)) (* 400 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h6 (* 
j2 j2 j2 j2 j2)) (* 1936 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2 
j2 j2)) (* 4624 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2 j2)) (* 
5776 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2)) (* 3616 (* h1 h1 
h1) (* h2 h2) (* h3 h3) (* h4 h4) h6 j2) (* 896 (* h1 h1 h1) (* h2 h2) (* h3 h3)
 (* h4 h4) h6) (* 48 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 
j2 j2 j2 j2)) (* 848 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 
j2 j2 j2)) (* 5968 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 
j2)) (* 21424 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 
41920 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 44608 (* h1
 h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2)) (* 24064 (* h1 h1 h1) (* h2 
h2) (* h3 h3) h4 (* h5 h5) j2) (* 5120 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h5
 h5)) (* 3 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 105 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
1443 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 9543 
(* h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 33450 (* h1 h1 
h1) (* h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 65008 (* h1 h1 h1) (* h2 h2
) (* h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 69808 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 
h5 h6 (* j2 j2)) (* 38624 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6 j2) (* 8576 
(* h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6) (* 16 (* h1 h1 h1) (* h2 h2) (* h3 h3
) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 312 (* h1 h1 h1) (* h2 h2) (* h3 h3)
 h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2312 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4
 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 8584 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h6
 h6) (* j2 j2 j2 j2)) (* 17448 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6) (* 
j2 j2 j2)) (* 19616 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2)) (* 
11424 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6) j2) (* 2688 (* h1 h1 h1) (* 
h2 h2) (* h3 h3) h4 (* h6 h6)) (* 18 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 
h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 300 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 
h5) (* j2 j2 j2 j2 j2 j2)) (* 2142 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5)
 (* j2 j2 j2 j2 j2)) (* 7996 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) (* j2
 j2 j2 j2)) (* 16008 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2))
 (* 16912 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2)) (* 8832 (* h1
 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) j2) (* 1792 (* h1 h1 h1) (* h2 h2) (* 
h3 h3) (* h5 h5 h5)) (* 3 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2
 j2 j2 j2 j2 j2 j2)) (* 117 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2)) (* 1445 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 
j2 j2 j2 j2 j2)) (* 8755 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 
j2 j2 j2)) (* 29196 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2
)) (* 55068 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 57680
 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2)) (* 31040 (* h1 h1 h1) 
(* h2 h2) (* h3 h3) (* h5 h5) h6 j2) (* 6656 (* h1 h1 h1) (* h2 h2) (* h3 h3) 
(* h5 h5) h6) (* 5 (* h1 h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 145 (* h1 h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 1673 (* h1 h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 9651 (* h1 h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 30470 (* h1 h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 
54880 (* h1 h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 56080 (* h1
 h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2)) (* 30208 (* h1 h1 h1) (* h2 
h2) (* h3 h3) h5 (* h6 h6) j2) (* 6656 (* h1 h1 h1) (* h2 h2) (* h3 h3) h5 (* h6
 h6)) (* 20 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 308 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2))
 (* 1988 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
6748 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 12888 (* 
h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2)) (* 13856 (* h1 h1 h1) 
(* h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2)) (* 7808 (* h1 h1 h1) (* h2 h2) (* h3
 h3) (* h6 h6 h6) j2) (* 1792 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6)) (* 
108 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1044
 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 3780 (* h1
 h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 6732 (* h1 h1 h1) 
(* h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 6336 (* h1 h1 h1) (* h2 h2) h3
 (* h4 h4) (* h5 h5) (* j2 j2)) (* 3024 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* 
h5 h5) j2) (* 576 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5)) (* 8 (* h1 h1 
h1) (* h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 140 (* h1 h1 h1) 
(* h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 888 (* h1 h1 h1) (* h2 h2
) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 2760 (* h1 h1 h1) (* h2 h2) h3 (* h4
 h4) h5 h6 (* j2 j2 j2 j2)) (* 4680 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) h5 h6 
(* j2 j2 j2)) (* 4428 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2)) (* 
2200 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) h5 h6 j2) (* 448 (* h1 h1 h1) (* h2 h2)
 h3 (* h4 h4) h5 h6) (* 8 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 j2
 j2 j2 j2 j2)) (* 64 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 j2 j2 
j2 j2)) (* 208 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 j2 j2 j2)) 
(* 352 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 328 (* h1 
h1 h1) (* h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 j2)) (* 160 (* h1 h1 h1) (* h2 h2)
 h3 (* h4 h4) (* h6 h6) j2) (* 32 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h6 h6))
 (* 24 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
352 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2000 (* 
h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 5696 (* h1 h1 h1) 
(* h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 8888 (* h1 h1 h1) (* h2 h2) h3 
h4 (* h5 h5 h5) (* j2 j2 j2)) (* 7712 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) 
(* j2 j2)) (* 3488 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) j2) (* 640 (* h1 h1
 h1) (* h2 h2) h3 h4 (* h5 h5 h5)) (* 6 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 138 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6
 (* j2 j2 j2 j2 j2 j2 j2)) (* 1338 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2)) (* 6614 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 
j2 j2 j2)) (* 17936 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2)) 
(* 27704 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2)) (* 24296 (* h1 
h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2)) (* 11264 (* h1 h1 h1) (* h2 h2) 
h3 h4 (* h5 h5) h6 j2) (* 2144 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6) (* 4 
(* h1 h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 98 (* 
h1 h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 904 (* h1 h1
 h1) (* h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4196 (* h1 h1 h1) 
(* h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 10908 (* h1 h1 h1) (* h2 h2)
 h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 16546 (* h1 h1 h1) (* h2 h2) h3 h4 h5 
(* h6 h6) (* j2 j2 j2)) (* 14536 (* h1 h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6) (* j2
 j2)) (* 6856 (* h1 h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6) j2) (* 1344 (* h1 h1 h1)
 (* h2 h2) h3 h4 h5 (* h6 h6)) (* 4 (* h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 56 (* h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 296 (* h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2 j2 j2
 j2)) (* 800 (* h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1220 
(* h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2 j2)) (* 1064 (* h1 h1 h1) (* 
h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2)) (* 496 (* h1 h1 h1) (* h2 h2) h3 h4 (* h6 
h6 h6) j2) (* 96 (* h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6 h6)) (* 6 (* h1 h1 h1) 
(* h2 h2) h3 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 70 (* h1 h1 h1) (* h2 
h2) h3 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 326 (* h1 h1 h1) (* h2 h2) h3 
(* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 794 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5
 h5) (* j2 j2 j2 j2)) (* 1100 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) (* j2 j2
 j2)) (* 872 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) (* j2 j2)) (* 368 (* h1 
h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) j2) (* 64 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5
 h5 h5)) (* 3 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 76 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 718 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 3372 
(* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 8715 (* h1 h1 
h1) (* h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 12912 (* h1 h1 h1) (* h2 h2
) h3 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 10908 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 
h5) h6 (* j2 j2)) (* 4880 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) h6 j2) (* 896 
(* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) h6) (* 9 (* h1 h1 h1) (* h2 h2) h3 (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 180 (* h1 h1 h1) (* h2 h2) h3 (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1474 (* h1 h1 h1) (* h2 h2) h3 (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6340 (* h1 h1 h1) (* h2 h2) h3 (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 15617 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2)) (* 22704 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6
) (* j2 j2 j2)) (* 19228 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2)
) (* 8768 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6) j2) (* 1664 (* h1 h1 h1)
 (* h2 h2) h3 (* h5 h5) (* h6 h6)) (* 5 (* h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 98 (* h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 790 (* h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2)) (* 3352 (* h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 
j2 j2)) (* 8189 (* h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 
11886 (* h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 10112 (* h1 h1 
h1) (* h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2)) (* 4656 (* h1 h1 h1) (* h2 h2) h3 h5
 (* h6 h6 h6) j2) (* 896 (* h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6)) (* 4 (* h1 
h1 h1) (* h2 h2) h3 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 48 (* h1 h1 h1)
 (* h2 h2) h3 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 232 (* h1 h1 h1) (* h2 
h2) h3 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 592 (* h1 h1 h1) (* h2 h2) h3 (* 
h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 868 (* h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6 h6) 
(* j2 j2 j2)) (* 736 (* h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6 h6) (* j2 j2)) (* 336
 (* h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6 h6) j2) (* 64 (* h1 h1 h1) (* h2 h2) h3 
(* h6 h6 h6 h6)) (* 8 (* h1 h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2)) (* 84 (* h1 h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2
 j2 j2)) (* 356 (* h1 h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)
) (* 800 (* h1 h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 1040 
(* h1 h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 788 (* h1 h1 h1) 
(* h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 324 (* h1 h1 h1) (* h2 h2) (* h4 
h4) (* h5 h5) h6 j2) (* 56 (* h1 h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) h6) (* 2 
(* h1 h1 h1) (* h2 h2) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 18 
(* h1 h1 h1) (* h2 h2) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 68 (* h1
 h1 h1) (* h2 h2) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 140 (* h1 h1 h1)
 (* h2 h2) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 170 (* h1 h1 h1) (* h2 h2)
 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 122 (* h1 h1 h1) (* h2 h2) (* h4 h4) h5
 (* h6 h6) (* j2 j2)) (* 48 (* h1 h1 h1) (* h2 h2) (* h4 h4) h5 (* h6 h6) j2) 
(* 8 (* h1 h1 h1) (* h2 h2) (* h4 h4) h5 (* h6 h6)) (* 3 (* h1 h1 h1) (* h2 h2) 
h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 45 (* h1 h1 h1) (* h2 h2) h4 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 276 (* h1 h1 h1) (* h2 h2) h4 (* h5
 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 906 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2)) (* 1755 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5 h5) h6 (* j2 
j2 j2 j2)) (* 2073 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 
1470 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2)) (* 576 (* h1 h1 h1) 
(* h2 h2) h4 (* h5 h5 h5) h6 j2) (* 96 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5 h5) h6
) (* 4 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 66 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 430 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
1468 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2920 
(* h1 h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 3514 (* h1 h1 
h1) (* h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 2526 (* h1 h1 h1) (* h2 h2
) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 1000 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5) 
(* h6 h6) j2) (* 168 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6)) (* (* h1 h1 
h1) (* h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 15 (* h1 h1 h1)
 (* h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 88 (* h1 h1 h1) (* h2
 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 274 (* h1 h1 h1) (* h2 h2) h4 
h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 505 (* h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6
 h6) (* j2 j2 j2 j2)) (* 571 (* h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 
j2)) (* 390 (* h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2)) (* 148 (* h1 h1
 h1) (* h2 h2) h4 h5 (* h6 h6 h6) j2) (* 24 (* h1 h1 h1) (* h2 h2) h4 h5 (* h6 
h6 h6)) (* (* h1 h1 h1) (* h2 h2) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 13 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
70 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 206 (* h1
 h1 h1) (* h2 h2) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 365 (* h1 h1 h1) (* 
h2 h2) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 401 (* h1 h1 h1) (* h2 h2) (* h5 
h5 h5 h5) h6 (* j2 j2 j2)) (* 268 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5 h5) h6 (* 
j2 j2)) (* 100 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5 h5) h6 j2) (* 16 (* h1 h1 h1) 
(* h2 h2) (* h5 h5 h5 h5) h6) (* 4 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 58 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6
) (* j2 j2 j2 j2 j2 j2 j2)) (* 346 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6)
 (* j2 j2 j2 j2 j2 j2)) (* 1112 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* 2120 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2)) (* 2474 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) 
(* 1738 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 676 (* h1 h1
 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6) j2) (* 112 (* h1 h1 h1) (* h2 h2) (* h5 h5
 h5) (* h6 h6)) (* 4 (* h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 58 (* h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2
 j2 j2 j2 j2)) (* 346 (* h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 1112 (* h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2)) (* 2120 (* h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 
2474 (* h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 1738 (* h1 
h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 676 (* h1 h1 h1) (* h2 h2)
 (* h5 h5) (* h6 h6 h6) j2) (* 112 (* h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6)
) (* (* h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
13 (* h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 70 (* 
h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 206 (* h1 h1 h1
) (* h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 365 (* h1 h1 h1) (* h2 h2)
 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 401 (* h1 h1 h1) (* h2 h2) h5 (* h6 h6 
h6 h6) (* j2 j2 j2)) (* 268 (* h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2))
 (* 100 (* h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6 h6) j2) (* 16 (* h1 h1 h1) (* h2 
h2) h5 (* h6 h6 h6 h6)) (* 24 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 
j2 j2 j2 j2)) (* 472 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2)
) (* 3808 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 16160 (* 
h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2)) (* 38400 (* h1 h1 h1) h2 (* 
h3 h3 h3 h3) h4 h5 (* j2 j2 j2)) (* 50176 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h5 
(* j2 j2)) (* 32768 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h5 j2) (* 8192 (* h1 h1 
h1) h2 (* h3 h3 h3 h3) h4 h5) (* 8 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h6 (* j2 
j2 j2 j2 j2 j2 j2)) (* 160 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2 
j2 j2)) (* 1320 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 
5776 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 14336 (* h1 h1 h1
) h2 (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2)) (* 19968 (* h1 h1 h1) h2 (* h3 h3 h3 h3
) h4 h6 (* j2 j2)) (* 14336 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h6 j2) (* 4096 
(* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h6) (* 36 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 696 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5
) (* j2 j2 j2 j2 j2 j2)) (* 5488 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) (* j2
 j2 j2 j2 j2)) (* 22560 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2
)) (* 51200 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2)) (* 62464 (* 
h1 h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) (* j2 j2)) (* 36864 (* h1 h1 h1) h2 (* h3
 h3 h3 h3) (* h5 h5) j2) (* 8192 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5)) (* 
72 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1320 (* h1
 h1 h1) h2 (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 9920 (* h1 h1 h1) h2 
(* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 39264 (* h1 h1 h1) h2 (* h3 h3 h3 
h3) h5 h6 (* j2 j2 j2 j2)) (* 87424 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h5 h6 (* j2 
j2 j2)) (* 108032 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h5 h6 (* j2 j2)) (* 67584 (* 
h1 h1 h1) h2 (* h3 h3 h3 h3) h5 h6 j2) (* 16384 (* h1 h1 h1) h2 (* h3 h3 h3 h3) 
h5 h6) (* 32 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2))
 (* 576 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4256
 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 16640 (* h1 h1
 h1) h2 (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 36992 (* h1 h1 h1) h2 (* 
h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2)) (* 46592 (* h1 h1 h1) h2 (* h3 h3 h3 h3) 
(* h6 h6) (* j2 j2)) (* 30720 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6) j2) (* 
8192 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6)) (* 72 (* h1 h1 h1) h2 (* h3 h3 
h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 1296 (* h1 h1 h1) h2 (* h3 h3 h3) 
(* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 9448 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 
h4) h5 (* j2 j2 j2 j2 j2)) (* 35648 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 
(* j2 j2 j2 j2)) (* 73888 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2)
) (* 82816 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 (* j2 j2)) (* 46592 (* h1 
h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 j2) (* 10240 (* h1 h1 h1) h2 (* h3 h3 h3) 
(* h4 h4) h5) (* 16 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 272 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 1872 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 6704 
(* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2)) (* 13408 (* h1 h1 h1)
 h2 (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2)) (* 14976 (* h1 h1 h1) h2 (* h3 h3 h3
) (* h4 h4) h6 (* j2 j2)) (* 8704 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h6 j2) 
(* 2048 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h6) (* 216 (* h1 h1 h1) h2 (* h3 
h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 3552 (* h1 h1 h1) h2 (* h3 h3 
h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 23944 (* h1 h1 h1) h2 (* h3 h3 h3) h4
 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 84576 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5
) (* j2 j2 j2 j2)) (* 165216 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 
j2)) (* 173440 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) (* j2 j2)) (* 90624 (* 
h1 h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) j2) (* 18432 (* h1 h1 h1) h2 (* h3 h3 h3)
 h4 (* h5 h5)) (* 2 (* h1 h1 h1) h2 (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 414 (* h1 h1 h1) h2 (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 6314 (* h1 h1 h1) h2 (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 40722 
(* h1 h1 h1) h2 (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 138964 (* h1 h1 h1)
 h2 (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 265744 (* h1 h1 h1) h2 (* h3 h3 h3
) h4 h5 h6 (* j2 j2 j2)) (* 281152 (* h1 h1 h1) h2 (* h3 h3 h3) h4 h5 h6 (* j2 
j2)) (* 152320 (* h1 h1 h1) h2 (* h3 h3 h3) h4 h5 h6 j2) (* 32768 (* h1 h1 h1) 
h2 (* h3 h3 h3) h4 h5 h6) (* 88 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 1304 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 7928 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 25544 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 
46928 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2)) (* 49088 (* h1 h1 
h1) h2 (* h3 h3 h3) h4 (* h6 h6) (* j2 j2)) (* 27136 (* h1 h1 h1) h2 (* h3 h3 h3
) h4 (* h6 h6) j2) (* 6144 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6)) (* 72 (* 
h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1176 (* h1 
h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 7664 (* h1 h1 h1) 
h2 (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 25440 (* h1 h1 h1) h2 (* h3 
h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 45760 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5
 h5 h5) (* j2 j2 j2)) (* 44288 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) (* j2 
j2)) (* 21504 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) j2) (* 4096 (* h1 h1 h1)
 h2 (* h3 h3 h3) (* h5 h5 h5)) (* 12 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 500 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 6112 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2)) (* 36280 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 
j2 j2 j2)) (* 119968 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) 
(* 225888 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 232832 (* 
h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2)) (* 120832 (* h1 h1 h1) h2 (* 
h3 h3 h3) (* h5 h5) h6 j2) (* 24576 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) h6) 
(* 12 (* h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
600 (* h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 7068 
(* h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 39424 (* h1 
h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 121936 (* h1 h1 h1) 
h2 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 217504 (* h1 h1 h1) h2 (* h3 h3
 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 219648 (* h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6 
h6) (* j2 j2)) (* 115712 (* h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6) j2) (* 24576 
(* h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6)) (* 96 (* h1 h1 h1) h2 (* h3 h3 h3) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1184 (* h1 h1 h1) h2 (* h3 h3 h3) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6432 (* h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6 
h6) (* j2 j2 j2 j2 j2)) (* 19296 (* h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6) (* j2
 j2 j2 j2)) (* 33792 (* h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2)) (* 
34176 (* h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6) (* j2 j2)) (* 18432 (* h1 h1 h1)
 h2 (* h3 h3 h3) (* h6 h6 h6) j2) (* 4096 (* h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6 
h6)) (* 144 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 
1584 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 6512 (* h1
 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 12752 (* h1 h1 h1) h2 
(* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 12864 (* h1 h1 h1) h2 (* h3 h3) (* h4
 h4 h4) h5 (* j2 j2)) (* 6464 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 j2) (* 
1280 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5) (* 16 (* h1 h1 h1) h2 (* h3 h3) 
(* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 160 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4
 h4) h6 (* j2 j2 j2 j2 j2)) (* 608 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h6 (* 
j2 j2 j2 j2)) (* 1152 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2)) 
(* 1168 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h6 (* j2 j2)) (* 608 (* h1 h1 h1)
 h2 (* h3 h3) (* h4 h4 h4) h6 j2) (* 128 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) 
h6) (* 144 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2
)) (* 2160 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) 
(* 12848 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 
38800 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 63872 
(* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 57920 (* h1 h1 h1
) h2 (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 27136 (* h1 h1 h1) h2 (* h3 h3)
 (* h4 h4) (* h5 h5) j2) (* 5120 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5)) 
(* 4 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
176 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2520 
(* h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 15520 (* h1 
h1 h1) h2 (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 48308 (* h1 h1 h1) h2
 (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 81360 (* h1 h1 h1) h2 (* h3 h3) 
(* h4 h4) h5 h6 (* j2 j2 j2)) (* 75216 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 h6
 (* j2 j2)) (* 35904 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 h6 j2) (* 6912 (* h1
 h1 h1) h2 (* h3 h3) (* h4 h4) h5 h6) (* 8 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 192 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1296 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* 
h6 h6) (* j2 j2 j2 j2 j2)) (* 4064 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h6 h6)
 (* j2 j2 j2 j2)) (* 6856 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2
 j2)) (* 6432 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2)) (* 3168 
(* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h6 h6) j2) (* 640 (* h1 h1 h1) h2 (* h3 
h3) (* h4 h4) (* h6 h6)) (* 216 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) (* j2 
j2 j2 j2 j2 j2 j2)) (* 2904 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 
j2 j2 j2 j2)) (* 15880 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 
j2)) (* 45000 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 
69792 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2)) (* 59488 (* h1 h1 
h1) h2 (* h3 h3) h4 (* h5 h5 h5) (* j2 j2)) (* 26112 (* h1 h1 h1) h2 (* h3 h3) 
h4 (* h5 h5 h5) j2) (* 4608 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5)) (* 42 (* 
h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1212 (* 
h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 11756 (* h1 
h1 h1) h2 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 56000 (* h1 h1 h1)
 h2 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 147418 (* h1 h1 h1) h2 (* 
h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 222388 (* h1 h1 h1) h2 (* h3 h3) h4 
(* h5 h5) h6 (* j2 j2 j2)) (* 190592 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) h6 
(* j2 j2)) (* 86080 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) h6 j2) (* 15872 (* h1
 h1 h1) h2 (* h3 h3) h4 (* h5 h5) h6) (* 30 (* h1 h1 h1) h2 (* h3 h3) h4 h5 (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 824 (* h1 h1 h1) h2 (* h3 h3) h4 h5 (* h6
 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 8096 (* h1 h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6)
 (* j2 j2 j2 j2 j2 j2)) (* 39116 (* h1 h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6) (* j2
 j2 j2 j2 j2)) (* 103954 (* h1 h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 
j2)) (* 158172 (* h1 h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 136976
 (* h1 h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 62720 (* h1 h1 h1) h2 
(* h3 h3) h4 h5 (* h6 h6) j2) (* 11776 (* h1 h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6)
) (* 40 (* h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
560 (* h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2992 (* 
h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 8192 (* h1 h1 h1) 
h2 (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 12648 (* h1 h1 h1) h2 (* h3 h3)
 h4 (* h6 h6 h6) (* j2 j2 j2)) (* 11152 (* h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6 h6
) (* j2 j2)) (* 5248 (* h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6 h6) j2) (* 1024 (* h1
 h1 h1) h2 (* h3 h3) h4 (* h6 h6 h6)) (* 36 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 480 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5
) (* j2 j2 j2 j2 j2 j2)) (* 2500 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) (* j2
 j2 j2 j2 j2)) (* 6552 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2)
) (* 9392 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 7456 (* h1 
h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) (* j2 j2)) (* 3072 (* h1 h1 h1) h2 (* h3 h3)
 (* h5 h5 h5 h5) j2) (* 512 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5)) (* 24 (* 
h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 568 (* h1
 h1 h1) h2 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 5216 (* h1 h1 
h1) h2 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 24568 (* h1 h1 h1) h2
 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 64600 (* h1 h1 h1) h2 (* h3 h3
) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 96320 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 
h5) h6 (* j2 j2 j2)) (* 80416 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2
)) (* 34944 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) h6 j2) (* 6144 (* h1 h1 h1) 
h2 (* h3 h3) (* h5 h5 h5) h6) (* (* h1 h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 82 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1454 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 11424 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 48177 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 117222 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2)) (* 167992 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6) 
(* j2 j2 j2)) (* 139328 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2))
 (* 61696 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6) j2) (* 11264 (* h1 h1 h1
) h2 (* h3 h3) (* h5 h5) (* h6 h6)) (* 36 (* h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 724 (* h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6
) (* j2 j2 j2 j2 j2 j2 j2)) (* 5956 (* h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 25564 (* h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6) (* j2 
j2 j2 j2 j2)) (* 62504 (* h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)
) (* 89728 (* h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 74656 (* 
h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 33280 (* h1 h1 h1) h2 (* h3
 h3) h5 (* h6 h6 h6) j2) (* 6144 (* h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6)) (* 
32 (* h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 384 
(* h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1856 (* h1 
h1 h1) h2 (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 4736 (* h1 h1 h1) h2 
(* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 6944 (* h1 h1 h1) h2 (* h3 h3) (* 
h6 h6 h6 h6) (* j2 j2 j2)) (* 5888 (* h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6 h6) (* 
j2 j2)) (* 2688 (* h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6 h6) j2) (* 512 (* h1 h1 h1
) h2 (* h3 h3) (* h6 h6 h6 h6)) (* 144 (* h1 h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5)
 (* j2 j2 j2 j2 j2 j2)) (* 1152 (* h1 h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) (* j2 
j2 j2 j2 j2)) (* 3488 (* h1 h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2))
 (* 5312 (* h1 h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 4368 (* h1 
h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 1856 (* h1 h1 h1) h2 h3 (* h4 
h4 h4) (* h5 h5) j2) (* 320 (* h1 h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5)) (* 4 (* 
h1 h1 h1) h2 h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 60 (* h1 h1 h1) 
h2 h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 304 (* h1 h1 h1) h2 h3 (* h4 
h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 760 (* h1 h1 h1) h2 h3 (* h4 h4 h4) h5 h6 
(* j2 j2 j2 j2)) (* 1060 (* h1 h1 h1) h2 h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 
844 (* h1 h1 h1) h2 h3 (* h4 h4 h4) h5 h6 (* j2 j2)) (* 360 (* h1 h1 h1) h2 h3 
(* h4 h4 h4) h5 h6 j2) (* 64 (* h1 h1 h1) h2 h3 (* h4 h4 h4) h5 h6) (* 72 (* h1 
h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 864 (* h1 h1 h1
) h2 h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 4048 (* h1 h1 h1) h2 h3
 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 9632 (* h1 h1 h1) h2 h3 (* h4 h4)
 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 12808 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5
) (* j2 j2 j2)) (* 9664 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 
3872 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) j2) (* 640 (* h1 h1 h1) h2 h3 (* 
h4 h4) (* h5 h5 h5)) (* 8 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 232 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2
 j2 j2 j2)) (* 2272 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 
j2)) (* 10288 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
24520 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 32968 (* h1 
h1 h1) h2 h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 25232 (* h1 h1 h1) h2 h3 
(* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 10272 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5
) h6 j2) (* 1728 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) h6) (* 2 (* h1 h1 h1) h2
 h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 66 (* h1 h1 h1) h2 h3
 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 564 (* h1 h1 h1) h2 h3 (* 
h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2220 (* h1 h1 h1) h2 h3 (* h4 h4) 
h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 4810 (* h1 h1 h1) h2 h3 (* h4 h4) h5 (* h6 
h6) (* j2 j2 j2 j2)) (* 6122 (* h1 h1 h1) h2 h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 
j2)) (* 4576 (* h1 h1 h1) h2 h3 (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 1864 (* h1 
h1 h1) h2 h3 (* h4 h4) h5 (* h6 h6) j2) (* 320 (* h1 h1 h1) h2 h3 (* h4 h4) h5 
(* h6 h6)) (* 24 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2))
 (* 256 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1072 (* 
h1 h1 h1) h2 h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 2336 (* h1 h1 h1) h2 
h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 2904 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5
 h5) (* j2 j2 j2)) (* 2080 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5 h5) (* j2 j2)) (* 
800 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5 h5) j2) (* 128 (* h1 h1 h1) h2 h3 h4 (* h5
 h5 h5 h5)) (* 42 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 722 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
5000 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 18084 (* h1
 h1 h1) h2 h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 37354 (* h1 h1 h1) h2 h3
 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 45658 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5)
 h6 (* j2 j2 j2)) (* 32676 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5) h6 (* j2 j2)) (* 
12656 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5) h6 j2) (* 2048 (* h1 h1 h1) h2 h3 h4 
(* h5 h5 h5) h6) (* 2 (* h1 h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 84 (* h1 h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 1102 (* h1 h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 7020 (* h1 h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 24782 (* h1 h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
51084 (* h1 h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 62882 (* h1 
h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 45524 (* h1 h1 h1) h2 h3 h4
 (* h5 h5) (* h6 h6) (* j2 j2)) (* 17888 (* h1 h1 h1) h2 h3 h4 (* h5 h5) (* h6 
h6) j2) (* 2944 (* h1 h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6)) (* 14 (* h1 h1 h1) h2
 h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 226 (* h1 h1 h1) h2 h3 h4
 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1432 (* h1 h1 h1) h2 h3 h4 h5 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4772 (* h1 h1 h1) h2 h3 h4 h5 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2)) (* 9310 (* h1 h1 h1) h2 h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2
)) (* 11034 (* h1 h1 h1) h2 h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 7836 (* h1 h1
 h1) h2 h3 h4 h5 (* h6 h6 h6) (* j2 j2)) (* 3072 (* h1 h1 h1) h2 h3 h4 h5 (* h6 
h6 h6) j2) (* 512 (* h1 h1 h1) h2 h3 h4 h5 (* h6 h6 h6)) (* 12 (* h1 h1 h1) h2 
h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 176 (* h1 h1 h1) h2 h3 (* 
h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1048 (* h1 h1 h1) h2 h3 (* h5 h5 h5
 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 3312 (* h1 h1 h1) h2 h3 (* h5 h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2)) (* 6124 (* h1 h1 h1) h2 h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) 
(* 6848 (* h1 h1 h1) h2 h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 4560 (* h1 h1 h1)
 h2 h3 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 1664 (* h1 h1 h1) h2 h3 (* h5 h5 h5 h5) 
h6 j2) (* 256 (* h1 h1 h1) h2 h3 (* h5 h5 h5 h5) h6) (* 2 (* h1 h1 h1) h2 h3 (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 74 (* h1 h1 h1) h2 h3 (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 868 (* h1 h1 h1) h2 h3 (* h5
 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4972 (* h1 h1 h1) h2 h3 (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 16042 (* h1 h1 h1) h2 h3 (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 30866 (* h1 h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6)
 (* j2 j2 j2 j2)) (* 36080 (* h1 h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2
)) (* 25112 (* h1 h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 9568 (* h1 
h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6) j2) (* 1536 (* h1 h1 h1) h2 h3 (* h5 h5 h5) 
(* h6 h6)) (* 3 (* h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 85 (* h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 904 (* h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2
)) (* 4962 (* h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
15731 (* h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 30113 (* 
h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 35250 (* h1 h1 h1) h2
 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 24664 (* h1 h1 h1) h2 h3 (* h5 h5) 
(* h6 h6 h6) (* j2 j2)) (* 9472 (* h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6) j2) 
(* 1536 (* h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6)) (* 12 (* h1 h1 h1) h2 h3 h5 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 164 (* h1 h1 h1) h2 h3 h5 (* h6 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 928 (* h1 h1 h1) h2 h3 h5 (* h6 h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2)) (* 2856 (* h1 h1 h1) h2 h3 h5 (* h6 h6 h6 h6) (* j2 j2 
j2 j2 j2)) (* 5260 (* h1 h1 h1) h2 h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 
5972 (* h1 h1 h1) h2 h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 4104 (* h1 h1 h1) h2
 h3 h5 (* h6 h6 h6 h6) (* j2 j2)) (* 1568 (* h1 h1 h1) h2 h3 h5 (* h6 h6 h6 h6) 
j2) (* 256 (* h1 h1 h1) h2 h3 h5 (* h6 h6 h6 h6)) (* 4 (* h1 h1 h1) h2 (* h4 h4 
h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 32 (* h1 h1 h1) h2 (* h4 h4 h4) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 108 (* h1 h1 h1) h2 (* h4 h4 h4) (* h5 h5
) h6 (* j2 j2 j2 j2 j2)) (* 200 (* h1 h1 h1) h2 (* h4 h4 h4) (* h5 h5) h6 (* j2 
j2 j2 j2)) (* 220 (* h1 h1 h1) h2 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 144
 (* h1 h1 h1) h2 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 52 (* h1 h1 h1) h2 (* 
h4 h4 h4) (* h5 h5) h6 j2) (* 8 (* h1 h1 h1) h2 (* h4 h4 h4) (* h5 h5) h6) (* 4 
(* h1 h1 h1) h2 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 48 (* 
h1 h1 h1) h2 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 236 (* h1 h1
 h1) h2 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 632 (* h1 h1 h1) h2 
(* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 1020 (* h1 h1 h1) h2 (* h4 h4) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 1024 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5 h5) 
h6 (* j2 j2 j2)) (* 628 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 
216 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5 h5) h6 j2) (* 32 (* h1 h1 h1) h2 (* h4 h4
) (* h5 h5 h5) h6) (* 4 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 52 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2
 j2 j2 j2 j2 j2)) (* 268 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 740 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2)) (* 1220 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) 
(* 1244 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 772 (* h1
 h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 268 (* h1 h1 h1) h2 (* h4
 h4) (* h5 h5) (* h6 h6) j2) (* 40 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 h6)
) (* 2 (* h1 h1 h1) h2 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 24 
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
 (* 32 (* h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6 h6)) (* 24 (* h1 h1 h1) (* h3 h3 h3
 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 448 (* h1 h1 h1) (* h3 h3 h3 h3) 
(* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 3384 (* h1 h1 h1) (* h3 h3 h3 h3) (* h4 
h4) h5 (* j2 j2 j2 j2 j2)) (* 13200 (* h1 h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 
(* j2 j2 j2 j2)) (* 28160 (* h1 h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2)
) (* 32256 (* h1 h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2)) (* 18432 (* h1 
h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 j2) (* 4096 (* h1 h1 h1) (* h3 h3 h3 h3) (* 
h4 h4) h5) (* 72 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 
j2)) (* 1320 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) 
(* 9728 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 36640 
(* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 74240 (* h1 h1 h1)
 (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 78848 (* h1 h1 h1) (* h3 h3 h3 h3
) h4 (* h5 h5) (* j2 j2)) (* 40960 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) j2)
 (* 8192 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5)) (* 12 (* h1 h1 h1) (* h3 h3 
h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 368 (* h1 h1 h1) (* h3 h3 h3 h3)
 h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 4188 (* h1 h1 h1) (* h3 h3 h3 h3) h4 h5 
h6 (* j2 j2 j2 j2 j2 j2)) (* 24088 (* h1 h1 h1) (* h3 h3 h3 h3) h4 h5 h6 (* j2 
j2 j2 j2 j2)) (* 77472 (* h1 h1 h1) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) 
(* 142720 (* h1 h1 h1) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 146944 (* h1 h1
 h1) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2)) (* 77824 (* h1 h1 h1) (* h3 h3 h3 h3) 
h4 h5 h6 j2) (* 16384 (* h1 h1 h1) (* h3 h3 h3 h3) h4 h5 h6) (* 36 (* h1 h1 h1) 
(* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 804 (* h1 h1 h1) 
(* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 7504 (* h1 h1 h1) (* 
h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 37776 (* h1 h1 h1) (* h3 h3 
h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 110400 (* h1 h1 h1) (* h3 h3 h3 h3) 
(* h5 h5) h6 (* j2 j2 j2 j2)) (* 187904 (* h1 h1 h1) (* h3 h3 h3 h3) (* h5 h5) 
h6 (* j2 j2 j2)) (* 178176 (* h1 h1 h1) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2)) 
(* 86016 (* h1 h1 h1) (* h3 h3 h3 h3) (* h5 h5) h6 j2) (* 16384 (* h1 h1 h1) (* 
h3 h3 h3 h3) (* h5 h5) h6) (* 48 (* h1 h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 992 (* h1 h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 8560 (* h1 h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 39936 (* h1 h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 109120 (* h1 h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 
177152 (* h1 h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 165888 (* h1 
h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2)) (* 81920 (* h1 h1 h1) (* h3 h3 h3
 h3) h5 (* h6 h6) j2) (* 16384 (* h1 h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6)) (* 48 
(* h1 h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 752 (* h1
 h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 4656 (* h1 h1 h1)
 (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 14544 (* h1 h1 h1) (* h3 h3
 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 24544 (* h1 h1 h1) (* h3 h3 h3) (* h4 
h4 h4) h5 (* j2 j2 j2)) (* 22656 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2
 j2)) (* 10752 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 j2) (* 2048 (* h1 h1 h1
) (* h3 h3 h3) (* h4 h4 h4) h5) (* 288 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) (* h5
 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 4152 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) (* h5
 h5) (* j2 j2 j2 j2 j2 j2)) (* 23616 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 
h5) (* j2 j2 j2 j2 j2)) (* 67864 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) 
(* j2 j2 j2 j2)) (* 105904 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 
j2 j2)) (* 90816 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 
40192 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) j2) (* 7168 (* h1 h1 h1) (* 
h3 h3 h3) (* h4 h4) (* h5 h5)) (* 24 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 h6 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 736 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 7392 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 h6 (* 
j2 j2 j2 j2 j2 j2)) (* 35856 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 
j2 j2 j2)) (* 95304 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) 
(* 144400 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 123840 (* 
h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 55808 (* h1 h1 h1) (* h3 h3
 h3) (* h4 h4) h5 h6 j2) (* 10240 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 h6) (* 
144 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 2208 
(* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 13264 (* h1 
h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 39680 (* h1 h1 h1) 
(* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 63040 (* h1 h1 h1) (* h3 h3 h3)
 h4 (* h5 h5 h5) (* j2 j2 j2)) (* 54016 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5
) (* j2 j2)) (* 23552 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) j2) (* 4096 (* 
h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5)) (* 156 (* h1 h1 h1) (* h3 h3 h3) h4 (* 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3224 (* h1 h1 h1) (* h3 h3 h3) h4 (* 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 26284 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 
h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 111488 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) 
h6 (* j2 j2 j2 j2 j2)) (* 269392 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2
 j2 j2 j2)) (* 378752 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) 
(* 304640 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 129536 (* h1 
h1 h1) (* h3 h3 h3) h4 (* h5 h5) h6 j2) (* 22528 (* h1 h1 h1) (* h3 h3 h3) h4 
(* h5 h5) h6) (* 132 (* h1 h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 2596 (* h1 h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 19924 (* h1 h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)
) (* 80844 (* h1 h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
189976 (* h1 h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 264320 (* 
h1 h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 213504 (* h1 h1 h1) (* 
h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 92160 (* h1 h1 h1) (* h3 h3 h3) h4 h5 
(* h6 h6) j2) (* 16384 (* h1 h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6)) (* 72 (* h1 h1
 h1) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1392 (* h1 h1 
h1) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 11048 (* h1 h1 h1)
 (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 46368 (* h1 h1 h1) (* h3
 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 110880 (* h1 h1 h1) (* h3 h3 h3) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 153088 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5 h5
) h6 (* j2 j2 j2)) (* 119808 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2)
) (* 49152 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5 h5) h6 j2) (* 8192 (* h1 h1 h1) 
(* h3 h3 h3) (* h5 h5 h5) h6) (* 6 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 310 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4230 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 27506 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 101004 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 222192 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2)) (* 294528 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6) 
(* j2 j2 j2)) (* 228608 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2))
 (* 95232 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6) j2) (* 16384 (* h1 h1 h1
) (* h3 h3 h3) (* h5 h5) (* h6 h6)) (* 144 (* h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2160 (* h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 14000 (* h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2)) (* 50704 (* h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2
 j2 j2 j2 j2)) (* 110080 (* h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 
j2)) (* 144832 (* h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 112384
 (* h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 47104 (* h1 h1 h1) (* 
h3 h3 h3) h5 (* h6 h6 h6) j2) (* 8192 (* h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6))
 (* 48 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 416 
(* h1 h1 h1) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 1312 (* h1 h1 
h1) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 2048 (* h1 h1 h1) (* h3 h3)
 (* h4 h4 h4 h4) h5 (* j2 j2 j2)) (* 1712 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4 h4)
 h5 (* j2 j2)) (* 736 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4 h4) h5 j2) (* 128 (* h1
 h1 h1) (* h3 h3) (* h4 h4 h4 h4) h5) (* 96 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) 
(* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1216 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) 
(* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 5952 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) (* 
h5 h5) (* j2 j2 j2 j2 j2)) (* 14592 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5
) (* j2 j2 j2 j2)) (* 19808 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 
j2 j2)) (* 15168 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 
6144 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) j2) (* 1024 (* h1 h1 h1) (* 
h3 h3) (* h4 h4 h4) (* h5 h5)) (* 48 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 848 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2
 j2 j2 j2 j2 j2)) (* 4672 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 
j2 j2)) (* 12064 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 
16816 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 13072 (* h1 h1 
h1) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2)) (* 5344 (* h1 h1 h1) (* h3 h3) (* h4
 h4 h4) h5 h6 j2) (* 896 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 h6) (* 288 (* h1
 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 3288 (* h1
 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 14616 (* h1 
h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 33016 (* h1 h1 h1
) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 41704 (* h1 h1 h1) (* h3 
h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 29904 (* h1 h1 h1) (* h3 h3) (* h4 
h4) (* h5 h5 h5) (* j2 j2)) (* 11392 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 
h5) j2) (* 1792 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5)) (* 72 (* h1 h1 h1
) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1512 (* h1 h1
 h1) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 11488 (* h1 
h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 43536 (* h1 h1
 h1) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 92104 (* h1 h1 h1) 
(* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 113928 (* h1 h1 h1) (* h3 
h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 81936 (* h1 h1 h1) (* h3 h3) (* h4 
h4) (* h5 h5) h6 (* j2 j2)) (* 31744 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) 
h6 j2) (* 5120 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) h6) (* 12 (* h1 h1 h1)
 (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 440 (* h1 h1 
h1) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4200 (* h1 h1 
h1) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 17632 (* h1 h1 h1
) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 39212 (* h1 h1 h1) (* 
h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 49800 (* h1 h1 h1) (* h3 h3) 
(* h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 36352 (* h1 h1 h1) (* h3 h3) (* h4 h4) 
h5 (* h6 h6) (* j2 j2)) (* 14208 (* h1 h1 h1) (* h3 h3) (* h4 h4) h5 (* h6 h6) 
j2) (* 2304 (* h1 h1 h1) (* h3 h3) (* h4 h4) h5 (* h6 h6)) (* 72 (* h1 h1 h1) 
(* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 888 (* h1 h1 h1) (* h3
 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 4184 (* h1 h1 h1) (* h3 h3) h4
 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 9736 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 
h5 h5) (* j2 j2 j2 j2)) (* 12416 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2
 j2 j2)) (* 8864 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2)) (* 3328 
(* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) j2) (* 512 (* h1 h1 h1) (* h3 h3) h4 
(* h5 h5 h5 h5)) (* 168 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2
 j2 j2 j2 j2)) (* 2788 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2)) (* 18500 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2)) (* 63812 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
125508 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 145992 (* 
h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 99392 (* h1 h1 h1) (* h3
 h3) h4 (* h5 h5 h5) h6 (* j2 j2)) (* 36608 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 
h5) h6 j2) (* 5632 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) h6) (* 12 (* h1 h1 h1)
 (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 440 (* h1 
h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 5160 (* 
h1 h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 29408 
(* h1 h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 93868 
(* h1 h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 178056 (* 
h1 h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 204736 (* h1 h1 
h1) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 139904 (* h1 h1 h1) (* h3 
h3) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 52224 (* h1 h1 h1) (* h3 h3) h4 (* h5 
h5) (* h6 h6) j2) (* 8192 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6)) (* 60 
(* h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1096 
(* h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 7592 (* 
h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 26624 (* h1 h1 
h1) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 52956 (* h1 h1 h1) (* h3
 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 62424 (* h1 h1 h1) (* h3 h3) h4 h5 
(* h6 h6 h6) (* j2 j2 j2)) (* 43232 (* h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6) 
(* j2 j2)) (* 16256 (* h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6) j2) (* 2560 (* h1 
h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6)) (* 36 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5 h5
) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 588 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 3868 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 13236 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* 25680 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)
) (* 29264 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 19392 (* 
h1 h1 h1) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 6912 (* h1 h1 h1) (* h3 h3)
 (* h5 h5 h5 h5) h6 j2) (* 1024 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5 h5) h6) (* 12
 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 332 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 3444 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 18268 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 55456 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
101064 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 112208 
(* h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 74240 (* h1 h1 h1
) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 26880 (* h1 h1 h1) (* h3 h3) 
(* h5 h5 h5) (* h6 h6) j2) (* 4096 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6)
) (* 18 (* h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
 j2)) (* 420 (* h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 3932 (* h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 19504 (* h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2
 j2)) (* 56706 (* h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2))
 (* 100828 (* h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 
110720 (* h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 73152 (* 
h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 26624 (* h1 h1 h1) (* 
h3 h3) (* h5 h5) (* h6 h6 h6) j2) (* 4096 (* h1 h1 h1) (* h3 h3) (* h5 h5) (* h6
 h6 h6)) (* 48 (* h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2
 j2)) (* 704 (* h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2))
 (* 4192 (* h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
13248 (* h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 24496 (* 
h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 27392 (* h1 h1 h1) 
(* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 18240 (* h1 h1 h1) (* h3 h3) h5 
(* h6 h6 h6 h6) (* j2 j2)) (* 6656 (* h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6 h6) j2)
 (* 1024 (* h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6 h6)) (* 48 (* h1 h1 h1) h3 (* h4 
h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 272 (* h1 h1 h1) h3 (* h4 h4 h4 h4
) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 640 (* h1 h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5)
 (* j2 j2 j2 j2)) (* 800 (* h1 h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2))
 (* 560 (* h1 h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2)) (* 208 (* h1 h1 h1)
 h3 (* h4 h4 h4 h4) (* h5 h5) j2) (* 32 (* h1 h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5
)) (* 48 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
464 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1728 (* 
h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 3360 (* h1 h1 h1) 
h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 3760 (* h1 h1 h1) h3 (* h4 h4 
h4) (* h5 h5 h5) (* j2 j2 j2)) (* 2448 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5)
 (* j2 j2)) (* 864 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) j2) (* 128 (* h1 h1
 h1) h3 (* h4 h4 h4) (* h5 h5 h5)) (* 72 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 744 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 2864 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* 5680 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2))
 (* 6440 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 4232 (* h1 
h1 h1) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 1504 (* h1 h1 h1) h3 (* h4 h4 
h4) (* h5 h5) h6 j2) (* 224 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) h6) (* 24 (* 
h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 232 (* h1 h1
 h1) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 864 (* h1 h1 h1) h3 
(* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 1680 (* h1 h1 h1) h3 (* h4 h4) 
(* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 1880 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5 
h5) (* j2 j2 j2)) (* 1224 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2)) 
(* 432 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) j2) (* 64 (* h1 h1 h1) h3 (* h4
 h4) (* h5 h5 h5 h5)) (* 48 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 704 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2
 j2 j2 j2 j2)) (* 4048 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2)) (* 12000 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) 
(* 20560 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 21248 (* 
h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 13104 (* h1 h1 h1) h3 
(* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 4448 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 
h5) h6 j2) (* 640 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) h6) (* 36 (* h1 h1 h1) 
h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 564 (* h1 h1 h1
) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3384 (* h1 h1 h1
) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 10296 (* h1 h1 h1) 
h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 17940 (* h1 h1 h1) h3 
(* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 18756 (* h1 h1 h1) h3 (* h4 h4
) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 11664 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5)
 (* h6 h6) (* j2 j2)) (* 3984 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5) (* h6 h6) j2) 
(* 576 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5) (* h6 h6)) (* 24 (* h1 h1 h1) h3 h4 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 328 (* h1 h1 h1) h3 h4 (* h5 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1792 (* h1 h1 h1) h3 h4 (* h5 h5 h5 h5
) h6 (* j2 j2 j2 j2 j2 j2)) (* 5136 (* h1 h1 h1) h3 h4 (* h5 h5 h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* 8600 (* h1 h1 h1) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 
8744 (* h1 h1 h1) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 5328 (* h1 h1 h1) h3
 h4 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 1792 (* h1 h1 h1) h3 h4 (* h5 h5 h5 h5) h6 
j2) (* 256 (* h1 h1 h1) h3 h4 (* h5 h5 h5 h5) h6) (* 12 (* h1 h1 h1) h3 h4 (* h5
 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 260 (* h1 h1 h1) h3 h4 (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2208 (* h1 h1 h1) h3 h4 (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 9736 (* h1 h1 h1) h3 h4 (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 24844 (* h1 h1 h1) h3 h4 (* h5 h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 38772 (* h1 h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6
) (* j2 j2 j2 j2)) (* 37640 (* h1 h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 
j2)) (* 22208 (* h1 h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 7296 (* h1
 h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6) j2) (* 1024 (* h1 h1 h1) h3 h4 (* h5 h5 h5)
 (* h6 h6)) (* 6 (* h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 142 (* h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 1268 (* h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 5764 (* h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 14990 (* h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 23686 
(* h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 23192 (* h1 h1 h1)
 h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 13768 (* h1 h1 h1) h3 h4 (* h5 h5
) (* h6 h6 h6) (* j2 j2)) (* 4544 (* h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6) j2) 
(* 640 (* h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6)) (* 6 (* h1 h1 h1) h3 (* h5 h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 106 (* h1 h1 h1) h3 (* h5 h5
 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 776 (* h1 h1 h1) h3 (* h5 h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3076 (* h1 h1 h1) h3 (* h5 h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 7286 (* h1 h1 h1) h3 (* h5 h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2)) (* 10786 (* h1 h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2)) (* 10076 (* h1 h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)
) (* 5776 (* h1 h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 1856 (* h1 h1 
h1) h3 (* h5 h5 h5 h5) (* h6 h6) j2) (* 256 (* h1 h1 h1) h3 (* h5 h5 h5 h5) (* 
h6 h6)) (* 12 (* h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 212 (* h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2
 j2)) (* 1552 (* h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 6152 (* h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
14572 (* h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 21572 (* 
h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 20152 (* h1 h1 h1) h3
 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 11552 (* h1 h1 h1) h3 (* h5 h5 h5) 
(* h6 h6 h6) (* j2 j2)) (* 3712 (* h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6) j2) 
(* 512 (* h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6)) (* 6 (* h1 h1 h1) h3 (* h5 h5)
 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 106 (* h1 h1 h1) h3 (* h5 h5
) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 776 (* h1 h1 h1) h3 (* h5 h5) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3076 (* h1 h1 h1) h3 (* h5 h5) (* 
h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 7286 (* h1 h1 h1) h3 (* h5 h5) (* h6 h6 
h6 h6) (* j2 j2 j2 j2 j2)) (* 10786 (* h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6 h6) 
(* j2 j2 j2 j2)) (* 10076 (* h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)
) (* 5776 (* h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 1856 (* h1 h1 
h1) h3 (* h5 h5) (* h6 h6 h6 h6) j2) (* 256 (* h1 h1 h1) h3 (* h5 h5) (* h6 h6 
h6 h6)) (* 6 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2 j2)) (* 76
 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2)) (* 360 (* h1 h1) (* 
h2 h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2)) (* 784 (* h1 h1) (* h2 h2 h2 h2) (* 
h3 h3 h3) h5 (* j2 j2)) (* 768 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h5 j2) (* 
256 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h5) (* 4 (* h1 h1) (* h2 h2 h2 h2) 
(* h3 h3 h3) h6 (* j2 j2 j2 j2 j2)) (* 52 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3)
 h6 (* j2 j2 j2 j2)) (* 256 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2 
j2)) (* 592 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2)) (* 640 (* h1 h1
) (* h2 h2 h2 h2) (* h3 h3 h3) h6 j2) (* 256 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 
h3) h6) (* 18 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 
174 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2)) (* 612 (* h1 h1) 
(* h2 h2 h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2)) (* 984 (* h1 h1) (* h2 h2 h2 h2) 
(* h3 h3) h4 h5 (* j2 j2)) (* 720 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h5 j2) 
(* 192 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h5) (* 8 (* h1 h1) (* h2 h2 h2 h2)
 (* h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 80 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) 
h4 h6 (* j2 j2 j2 j2)) (* 296 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h6 (* j2 j2
 j2)) (* 512 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h6 (* j2 j2)) (* 416 (* h1 
h1) (* h2 h2 h2 h2) (* h3 h3) h4 h6 j2) (* 128 (* h1 h1) (* h2 h2 h2 h2) (* h3 
h3) h4 h6) (* 12 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2
)) (* 116 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 408 
(* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2)) (* 656 (* h1 h1) (* 
h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* j2 j2)) (* 480 (* h1 h1) (* h2 h2 h2 h2) (* 
h3 h3) (* h5 h5) j2) (* 128 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h5 h5)) (* 
(* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 34 (* h1 h1)
 (* h2 h2 h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 249 (* h1 h1) (* h2 h2 
h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 780 (* h1 h1) (* h2 h2 h2 h2) (* h3 
h3) h5 h6 (* j2 j2 j2)) (* 1204 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 h6 (* j2 
j2)) (* 896 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 h6 j2) (* 256 (* h1 h1) (* h2
 h2 h2 h2) (* h3 h3) h5 h6) (* 12 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* 104 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 
j2 j2 j2)) (* 348 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2)) 
(* 560 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2)) (* 432 (* h1 h1)
 (* h2 h2 h2 h2) (* h3 h3) (* h6 h6) j2) (* 128 (* h1 h1) (* h2 h2 h2 h2) (* h3 
h3) (* h6 h6)) (* 18 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2
)) (* 120 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2)) (* 306 (* 
h1 h1) (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2)) (* 372 (* h1 h1) (* h2 h2 
h2 h2) h3 h4 (* h5 h5) (* j2 j2)) (* 216 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h5 
h5) j2) (* 48 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h5 h5)) (* 2 (* h1 h1) (* h2 h2
 h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 30 (* h1 h1) (* h2 h2 h2 h2) h3 h4
 h5 h6 (* j2 j2 j2 j2 j2)) (* 150 (* h1 h1) (* h2 h2 h2 h2) h3 h4 h5 h6 (* j2 j2
 j2 j2)) (* 354 (* h1 h1) (* h2 h2 h2 h2) h3 h4 h5 h6 (* j2 j2 j2)) (* 432 (* h1
 h1) (* h2 h2 h2 h2) h3 h4 h5 h6 (* j2 j2)) (* 264 (* h1 h1) (* h2 h2 h2 h2) h3 
h4 h5 h6 j2) (* 64 (* h1 h1) (* h2 h2 h2 h2) h3 h4 h5 h6) (* 4 (* h1 h1) (* h2 
h2 h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 28 (* h1 h1) (* h2 h2 h2 h2) h3
 h4 (* h6 h6) (* j2 j2 j2 j2)) (* 76 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h6 h6) 
(* j2 j2 j2)) (* 100 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h6 h6) (* j2 j2)) (* 64 
(* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h6 h6) j2) (* 16 (* h1 h1) (* h2 h2 h2 h2) h3
 h4 (* h6 h6)) (* 6 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2)
) (* 40 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 102 (* h1 
h1) (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2)) (* 124 (* h1 h1) (* h2 h2 h2 
h2) h3 (* h5 h5 h5) (* j2 j2)) (* 72 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5 h5) 
j2) (* 16 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5 h5)) (* 2 (* h1 h1) (* h2 h2 h2 
h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 32 (* h1 h1) (* h2 h2 h2 h2) h3 
(* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 162 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) 
h6 (* j2 j2 j2 j2)) (* 380 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2
)) (* 456 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) h6 (* j2 j2)) (* 272 (* h1 h1) 
(* h2 h2 h2 h2) h3 (* h5 h5) h6 j2) (* 64 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5)
 h6) (* 3 (* h1 h1) (* h2 h2 h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 37
 (* h1 h1) (* h2 h2 h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 169 (* h1 h1) 
(* h2 h2 h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 379 (* h1 h1) (* h2 h2 h2 h2
) h3 h5 (* h6 h6) (* j2 j2 j2)) (* 448 (* h1 h1) (* h2 h2 h2 h2) h3 h5 (* h6 h6)
 (* j2 j2)) (* 268 (* h1 h1) (* h2 h2 h2 h2) h3 h5 (* h6 h6) j2) (* 64 (* h1 h1)
 (* h2 h2 h2 h2) h3 h5 (* h6 h6)) (* 4 (* h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6 h6)
 (* j2 j2 j2 j2 j2)) (* 28 (* h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2
 j2)) (* 76 (* h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2)) (* 100 (* h1
 h1) (* h2 h2 h2 h2) h3 (* h6 h6 h6) (* j2 j2)) (* 64 (* h1 h1) (* h2 h2 h2 h2) 
h3 (* h6 h6 h6) j2) (* 16 (* h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6 h6)) (* 2 (* h1 
h1) (* h2 h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1) (* h2
 h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 52 (* h1 h1) (* h2 h2 h2 h2) 
h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 88 (* h1 h1) (* h2 h2 h2 h2) h4 (* h5 h5) h6
 (* j2 j2 j2)) (* 82 (* h1 h1) (* h2 h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2)) (* 40 
(* h1 h1) (* h2 h2 h2 h2) h4 (* h5 h5) h6 j2) (* 8 (* h1 h1) (* h2 h2 h2 h2) h4 
(* h5 h5) h6) (* (* h1 h1) (* h2 h2 h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)
) (* 8 (* h1 h1) (* h2 h2 h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 26 (* h1
 h1) (* h2 h2 h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 44 (* h1 h1) (* h2 h2 
h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 41 (* h1 h1) (* h2 h2 h2 h2) h4 h5 (* h6
 h6) (* j2 j2)) (* 20 (* h1 h1) (* h2 h2 h2 h2) h4 h5 (* h6 h6) j2) (* 4 (* h1 
h1) (* h2 h2 h2 h2) h4 h5 (* h6 h6)) (* (* h1 h1) (* h2 h2 h2 h2) (* h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2)) (* 8 (* h1 h1) (* h2 h2 h2 h2) (* h5 h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* 26 (* h1 h1) (* h2 h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) 
(* 44 (* h1 h1) (* h2 h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 41 (* h1 h1) 
(* h2 h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2)) (* 20 (* h1 h1) (* h2 h2 h2 h2) (* h5
 h5 h5) h6 j2) (* 4 (* h1 h1) (* h2 h2 h2 h2) (* h5 h5 h5) h6) (* 2 (* h1 h1) 
(* h2 h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1) (* h2
 h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 52 (* h1 h1) (* h2 h2 h2 
h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 88 (* h1 h1) (* h2 h2 h2 h2) (* h5 
h5) (* h6 h6) (* j2 j2 j2)) (* 82 (* h1 h1) (* h2 h2 h2 h2) (* h5 h5) (* h6 h6) 
(* j2 j2)) (* 40 (* h1 h1) (* h2 h2 h2 h2) (* h5 h5) (* h6 h6) j2) (* 8 (* h1 h1
) (* h2 h2 h2 h2) (* h5 h5) (* h6 h6)) (* (* h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 8 (* h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6 h6) (* j2 
j2 j2 j2 j2)) (* 26 (* h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) 
(* 44 (* h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 41 (* h1 h1) 
(* h2 h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2)) (* 20 (* h1 h1) (* h2 h2 h2 h2) h5 
(* h6 h6 h6) j2) (* 4 (* h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6 h6)) (* 6 (* h1 h1) 
(* h2 h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2 j2 j2 j2 j2)) (* 100 (* h1 h1) (* h2 h2
 h2) (* h3 h3 h3 h3) h5 (* j2 j2 j2 j2 j2)) (* 664 (* h1 h1) (* h2 h2 h2) (* h3 
h3 h3 h3) h5 (* j2 j2 j2 j2)) (* 2224 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h5 
(* j2 j2 j2)) (* 3904 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2)) (* 
3328 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h5 j2) (* 1024 (* h1 h1) (* h2 h2 h2
) (* h3 h3 h3 h3) h5) (* 4 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2 j2
 j2 j2 j2)) (* 68 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2 j2 j2 j2)) 
(* 464 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2 j2 j2)) (* 1616 (* h1 
h1) (* h2 h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2 j2)) (* 3008 (* h1 h1) (* h2 h2 h2)
 (* h3 h3 h3 h3) h6 (* j2 j2)) (* 2816 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h6
 j2) (* 1024 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h6) (* 36 (* h1 h1) (* h2 h2
 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 564 (* h1 h1) (* h2 h2 h2) (* 
h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 3456 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) 
h4 h5 (* j2 j2 j2 j2)) (* 10416 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 
j2 j2)) (* 15936 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2)) (* 11520 
(* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h5 j2) (* 3072 (* h1 h1) (* h2 h2 h2) (* 
h3 h3 h3) h4 h5) (* 16 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 
j2 j2)) (* 248 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 
1520 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 4664 (* h1 h1
) (* h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2)) (* 7472 (* h1 h1) (* h2 h2 h2) 
(* h3 h3 h3) h4 h6 (* j2 j2)) (* 5888 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h6 
j2) (* 1792 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h6) (* 18 (* h1 h1) (* h2 h2 
h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 282 (* h1 h1) (* h2 h2 h2) 
(* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 1860 (* h1 h1) (* h2 h2 h2) (* h3 
h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 6136 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) 
(* h5 h5) (* j2 j2 j2)) (* 9872 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) 
(* j2 j2)) (* 7040 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) j2) (* 1792 (* 
h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h5 h5)) (* (* h1 h1) (* h2 h2 h2) (* h3 h3 
h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 54 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5
 h6 (* j2 j2 j2 j2 j2 j2)) (* 677 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 h6 (* 
j2 j2 j2 j2 j2)) (* 3844 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 
j2)) (* 11380 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2)) (* 17568 
(* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2)) (* 12992 (* h1 h1) (* h2 h2
 h2) (* h3 h3 h3) h5 h6 j2) (* 3584 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 h6) 
(* 20 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
296 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1732 
(* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 5088 (* h1 h1)
 (* h2 h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2)) (* 7856 (* h1 h1) (* h2 h2 h2
) (* h3 h3 h3) (* h6 h6) (* j2 j2)) (* 6016 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) 
(* h6 h6) j2) (* 1792 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h6 h6)) (* 36 (* h1
 h1) (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 492 (* h1 h1)
 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 2508 (* h1 h1) (* h2
 h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 6036 (* h1 h1) (* h2 h2 h2) 
(* h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 7296 (* h1 h1) (* h2 h2 h2) (* h3 h3) 
(* h4 h4) h5 (* j2 j2)) (* 4272 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 j2
) (* 960 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h4 h4) h5) (* 12 (* h1 h1) (* h2 h2
 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 156 (* h1 h1) (* h2 h2 h2)
 (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 780 (* h1 h1) (* h2 h2 h2) (* h3 
h3) (* h4 h4) h6 (* j2 j2 j2 j2)) (* 1908 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h4
 h4) h6 (* j2 j2 j2)) (* 2424 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h4 h4) h6 (* 
j2 j2)) (* 1536 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h4 h4) h6 j2) (* 384 (* h1 
h1) (* h2 h2 h2) (* h3 h3) (* h4 h4) h6) (* 72 (* h1 h1) (* h2 h2 h2) (* h3 h3) 
h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 912 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 
(* h5 h5) (* j2 j2 j2 j2 j2)) (* 4392 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h5 
h5) (* j2 j2 j2 j2)) (* 10176 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* 
j2 j2 j2)) (* 12000 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2)) (* 
6912 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) j2) (* 1536 (* h1 h1) (* h2 
h2 h2) (* h3 h3) h4 (* h5 h5)) (* 4 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 158 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2
 j2 j2 j2 j2 j2)) (* 1638 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 
j2 j2)) (* 7310 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 
16414 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 19308 (* h1 h1)
 (* h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2)) (* 11344 (* h1 h1) (* h2 h2 h2) (* 
h3 h3) h4 h5 h6 j2) (* 2624 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 h6) (* 32 (* 
h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 392 (* h1 
h1) (* h2 h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1864 (* h1 h1) 
(* h2 h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 4392 (* h1 h1) (* h2 h2 
h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2)) (* 5432 (* h1 h1) (* h2 h2 h2) (* h3 h3
) h4 (* h6 h6) (* j2 j2)) (* 3376 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h6 h6) 
j2) (* 832 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h6 h6)) (* 18 (* h1 h1) (* h2 
h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 228 (* h1 h1) (* h2 h2 
h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 1230 (* h1 h1) (* h2 h2 h2) 
(* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 3076 (* h1 h1) (* h2 h2 h2) (* h3 h3)
 (* h5 h5 h5) (* j2 j2 j2)) (* 3704 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5 h5
) (* j2 j2)) (* 2096 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) j2) (* 448 
(* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5 h5)) (* 3 (* h1 h1) (* h2 h2 h2) (* h3
 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 105 (* h1 h1) (* h2 h2 h2) (* h3 
h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 1037 (* h1 h1) (* h2 h2 h2) (* h3 h3)
 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 4663 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5
 h5) h6 (* j2 j2 j2 j2)) (* 10636 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) h6 
(* j2 j2 j2)) (* 12588 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2)) 
(* 7344 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) h6 j2) (* 1664 (* h1 h1) (* 
h2 h2 h2) (* h3 h3) (* h5 h5) h6) (* 5 (* h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* h6
 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 139 (* h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 1247 (* h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* h6 h6)
 (* j2 j2 j2 j2 j2)) (* 5077 (* h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* j2
 j2 j2 j2)) (* 10752 (* h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2))
 (* 12260 (* h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2)) (* 7136 (* h1
 h1) (* h2 h2 h2) (* h3 h3) h5 (* h6 h6) j2) (* 1664 (* h1 h1) (* h2 h2 h2) (* 
h3 h3) h5 (* h6 h6)) (* 20 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 236 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 
j2 j2 j2)) (* 1084 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2)
) (* 2484 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2)) (* 3008 
(* h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2)) (* 1840 (* h1 h1) (* h2
 h2 h2) (* h3 h3) (* h6 h6 h6) j2) (* 448 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h6
 h6 h6)) (* 36 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 
j2)) (* 384 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) 
(* 1464 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 2688 
(* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 2580 (* h1 h1) 
(* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2)) (* 1248 (* h1 h1) (* h2 h2 h2) h3
 (* h4 h4) (* h5 h5) j2) (* 240 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h5 h5)) 
(* 3 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 54 
(* h1 h1) (* h2 h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 354 (* h1 h1
) (* h2 h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 1128 (* h1 h1) (* h2 h2
 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 1947 (* h1 h1) (* h2 h2 h2) h3 (* h4
 h4) h5 h6 (* j2 j2 j2)) (* 1866 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) h5 h6 (* j2
 j2)) (* 936 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) h5 h6 j2) (* 192 (* h1 h1) (* 
h2 h2 h2) h3 (* h4 h4) h5 h6) (* 4 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h6 h6)
 (* j2 j2 j2 j2 j2 j2)) (* 32 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h6 h6) (* 
j2 j2 j2 j2 j2)) (* 104 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 j2 
j2 j2)) (* 176 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 
164 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 j2)) (* 80 (* h1 h1) (* 
h2 h2 h2) h3 (* h4 h4) (* h6 h6) j2) (* 16 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) 
(* h6 h6)) (* 36 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)
) (* 348 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 1260 
(* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 2244 (* h1 h1) (* 
h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2)) (* 2112 (* h1 h1) (* h2 h2 h2) h3 h4 
(* h5 h5 h5) (* j2 j2)) (* 1008 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5 h5) j2) 
(* 192 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5 h5)) (* 8 (* h1 h1) (* h2 h2 h2) h3
 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 172 (* h1 h1) (* h2 h2 h2) h3 h4 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 1248 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 
h5) h6 (* j2 j2 j2 j2 j2)) (* 4152 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) h6 (* 
j2 j2 j2 j2)) (* 7224 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2)) 
(* 6828 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2)) (* 3328 (* h1 h1) 
(* h2 h2 h2) h3 h4 (* h5 h5) h6 j2) (* 656 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5
) h6) (* 8 (* h1 h1) (* h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 134 (* h1 h1) (* h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 836 
(* h1 h1) (* h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2580 (* h1 h1) 
(* h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 4360 (* h1 h1) (* h2 h2 h2) 
h3 h4 h5 (* h6 h6) (* j2 j2 j2)) (* 4118 (* h1 h1) (* h2 h2 h2) h3 h4 h5 (* h6 
h6) (* j2 j2)) (* 2044 (* h1 h1) (* h2 h2 h2) h3 h4 h5 (* h6 h6) j2) (* 416 (* 
h1 h1) (* h2 h2 h2) h3 h4 h5 (* h6 h6)) (* 8 (* h1 h1) (* h2 h2 h2) h3 h4 (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 64 (* h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2)) (* 208 (* h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2 j2
 j2)) (* 352 (* h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2 j2)) (* 328 (* 
h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2)) (* 160 (* h1 h1) (* h2 h2 h2) 
h3 h4 (* h6 h6 h6) j2) (* 32 (* h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6 h6)) (* 6 (* 
h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 46 (* h1 h1) 
(* h2 h2 h2) h3 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 142 (* h1 h1) (* h2 h2 h2
) h3 (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 226 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 
h5 h5) (* j2 j2 j2)) (* 196 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* j2 j2))
 (* 88 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5 h5) j2) (* 16 (* h1 h1) (* h2 h2 h2
) h3 (* h5 h5 h5 h5)) (* 3 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2
 j2 j2 j2 j2)) (* 64 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2
 j2)) (* 462 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
1524 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 2619 (* h1 h1
) (* h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 2436 (* h1 h1) (* h2 h2 h2) 
h3 (* h5 h5 h5) h6 (* j2 j2)) (* 1164 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) h6 
j2) (* 224 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) h6) (* 9 (* h1 h1) (* h2 h2 h2
) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 146 (* h1 h1) (* h2 h2 h2)
 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 902 (* h1 h1) (* h2 h2 h2) h3 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2760 (* h1 h1) (* h2 h2 h2) h3 (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2)) (* 4609 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* h6
 h6) (* j2 j2 j2)) (* 4286 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 
j2)) (* 2088 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* h6 h6) j2) (* 416 (* h1 h1) 
(* h2 h2 h2) h3 (* h5 h5) (* h6 h6)) (* 5 (* h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 80 (* h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 482 (* h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2
 j2 j2 j2)) (* 1452 (* h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) 
(* 2413 (* h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 2252 (* h1 h1
) (* h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2)) (* 1108 (* h1 h1) (* h2 h2 h2) h3 
h5 (* h6 h6 h6) j2) (* 224 (* h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6 h6)) (* 4 (* h1
 h1) (* h2 h2 h2) h3 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 32 (* h1 h1) (* 
h2 h2 h2) h3 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 104 (* h1 h1) (* h2 h2 h2) 
h3 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 176 (* h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6
 h6) (* j2 j2 j2)) (* 164 (* h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6 h6) (* j2 j2)) 
(* 80 (* h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6 h6) j2) (* 16 (* h1 h1) (* h2 h2 h2)
 h3 (* h6 h6 h6 h6)) (* 3 (* h1 h1) (* h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2
 j2 j2 j2 j2 j2)) (* 33 (* h1 h1) (* h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 
j2 j2 j2 j2)) (* 144 (* h1 h1) (* h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 
j2 j2)) (* 330 (* h1 h1) (* h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) 
(* 435 (* h1 h1) (* h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 333 (* h1 
h1) (* h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 138 (* h1 h1) (* h2 h2 h2)
 (* h4 h4) (* h5 h5) h6 j2) (* 24 (* h1 h1) (* h2 h2 h2) (* h4 h4) (* h5 h5) h6)
 (* (* h1 h1) (* h2 h2 h2) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 9
 (* h1 h1) (* h2 h2 h2) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 34 (* 
h1 h1) (* h2 h2 h2) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 70 (* h1 h1) 
(* h2 h2 h2) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 85 (* h1 h1) (* h2 h2 h2
) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 61 (* h1 h1) (* h2 h2 h2) (* h4 h4) h5
 (* h6 h6) (* j2 j2)) (* 24 (* h1 h1) (* h2 h2 h2) (* h4 h4) h5 (* h6 h6) j2) 
(* 4 (* h1 h1) (* h2 h2 h2) (* h4 h4) h5 (* h6 h6)) (* 4 (* h1 h1) (* h2 h2 h2) 
h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 42 (* h1 h1) (* h2 h2 h2) h4 (* 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 178 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5 h5
) h6 (* j2 j2 j2 j2 j2)) (* 400 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5 h5) h6 (* j2 
j2 j2 j2)) (* 520 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 394
 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2)) (* 162 (* h1 h1) (* h2 h2 
h2) h4 (* h5 h5 h5) h6 j2) (* 28 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5 h5) h6) (* 7
 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 75 
(* h1 h1) (* h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 322 (* 
h1 h1) (* h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 730 (* h1 h1) 
(* h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 955 (* h1 h1) (* h2 h2 
h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 727 (* h1 h1) (* h2 h2 h2) h4 (* h5 
h5) (* h6 h6) (* j2 j2)) (* 300 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5) (* h6 h6) j2
) (* 52 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5) (* h6 h6)) (* 2 (* h1 h1) (* h2 h2 
h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 18 (* h1 h1) (* h2 h2 h2) h4
 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 68 (* h1 h1) (* h2 h2 h2) h4 h5 (* h6
 h6 h6) (* j2 j2 j2 j2 j2)) (* 140 (* h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6 h6) (* 
j2 j2 j2 j2)) (* 170 (* h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 
122 (* h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2)) (* 48 (* h1 h1) (* h2 
h2 h2) h4 h5 (* h6 h6 h6) j2) (* 8 (* h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6 h6)) 
(* (* h1 h1) (* h2 h2 h2) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 9 (* 
h1 h1) (* h2 h2 h2) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 34 (* h1 h1) 
(* h2 h2 h2) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 70 (* h1 h1) (* h2 h2 h2)
 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 85 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5 h5
) h6 (* j2 j2 j2)) (* 61 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5 h5) h6 (* j2 j2)) 
(* 24 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5 h5) h6 j2) (* 4 (* h1 h1) (* h2 h2 h2) 
(* h5 h5 h5 h5) h6) (* 4 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 42 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2
 j2 j2 j2)) (* 178 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 400 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 
520 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 394 (* h1 h1)
 (* h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 162 (* h1 h1) (* h2 h2 h2) 
(* h5 h5 h5) (* h6 h6) j2) (* 28 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5) (* h6 h6)) 
(* 4 (* h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
42 (* h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 178 
(* h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 400 (* h1 
h1) (* h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 520 (* h1 h1) (* h2 
h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 394 (* h1 h1) (* h2 h2 h2) (* h5 
h5) (* h6 h6 h6) (* j2 j2)) (* 162 (* h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6 h6)
 j2) (* 28 (* h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6 h6)) (* (* h1 h1) (* h2 h2 
h2) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 9 (* h1 h1) (* h2 h2 h2) h5 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 34 (* h1 h1) (* h2 h2 h2) h5 (* h6 h6 
h6 h6) (* j2 j2 j2 j2 j2)) (* 70 (* h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6 h6) (* j2
 j2 j2 j2)) (* 85 (* h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 61 
(* h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2)) (* 24 (* h1 h1) (* h2 h2 h2
) h5 (* h6 h6 h6 h6) j2) (* 4 (* h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6 h6)) (* 18 
(* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 366 (* h1
 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 3044 (* h1 h1) 
(* h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 13272 (* h1 h1) (* h2 h2)
 (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2)) (* 32272 (* h1 h1) (* h2 h2) (* h3 h3 h3
 h3) h4 h5 (* j2 j2 j2)) (* 42944 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* 
j2 j2)) (* 28416 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h5 j2) (* 7168 (* h1 h1)
 (* h2 h2) (* h3 h3 h3 h3) h4 h5) (* 8 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h6
 (* j2 j2 j2 j2 j2 j2 j2)) (* 160 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h6 (* 
j2 j2 j2 j2 j2 j2)) (* 1320 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2 
j2 j2 j2)) (* 5776 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2)) 
(* 14336 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2)) (* 19968 (* h1 
h1) (* h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2)) (* 14336 (* h1 h1) (* h2 h2) (* 
h3 h3 h3 h3) h4 h6 j2) (* 4096 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h6) (* 72 
(* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1104 (* 
h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 6560 (* h1 h1)
 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 18880 (* h1 h1) (* h2 
h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2)) (* 26880 (* h1 h1) (* h2 h2) (* h3 
h3 h3 h3) (* h5 h5) (* j2 j2)) (* 17408 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* 
h5 h5) j2) (* 4096 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h5 h5)) (* 12 (* h1 h1
) (* h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 296 (* h1 h1) (* 
h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 2796 (* h1 h1) (* h2 h2) 
(* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 13280 (* h1 h1) (* h2 h2) (* h3 h3 
h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 34192 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 h6
 (* j2 j2 j2)) (* 47232 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2)) (* 
32000 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 h6 j2) (* 8192 (* h1 h1) (* h2 h2) 
(* h3 h3 h3 h3) h5 h6) (* 8 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 168 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 1416 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 
j2 j2 j2)) (* 6200 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2)
) (* 15184 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2)) (* 20736 
(* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2)) (* 14592 (* h1 h1) (* 
h2 h2) (* h3 h3 h3 h3) (* h6 h6) j2) (* 4096 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3)
 (* h6 h6)) (* 36 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 
j2 j2 j2)) (* 696 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 
j2 j2)) (* 5380 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)
) (* 21264 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 
45632 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 52384 (* h1
 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2)) (* 29952 (* h1 h1) (* h2 h2)
 (* h3 h3 h3) (* h4 h4) h5 j2) (* 6656 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4
) h5) (* 12 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 
j2)) (* 212 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2))
 (* 1508 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 
5548 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2)) (* 11328 (* 
h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2)) (* 12848 (* h1 h1) (* 
h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2)) (* 7552 (* h1 h1) (* h2 h2) (* h3 h3
 h3) (* h4 h4) h6 j2) (* 1792 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h6) (* 
54 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
1044 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 
8106 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 32436 
(* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 70424 (* h1 h1
) (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 80048 (* h1 h1) (* h2 h2)
 (* h3 h3 h3) h4 (* h5 h5) (* j2 j2)) (* 44416 (* h1 h1) (* h2 h2) (* h3 h3 h3) 
h4 (* h5 h5) j2) (* 9472 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h5 h5)) (* 2 (* 
h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 138 (* h1
 h1) (* h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2158 (* h1 h1)
 (* h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 15214 (* h1 h1) (* h2
 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 56944 (* h1 h1) (* h2 h2) (* 
h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 117928 (* h1 h1) (* h2 h2) (* h3 h3 h3) 
h4 h5 h6 (* j2 j2 j2)) (* 132800 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2
 j2)) (* 75520 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 h6 j2) (* 16896 (* h1 h1) 
(* h2 h2) (* h3 h3 h3) h4 h5 h6) (* 32 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h6
 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 536 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 3640 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h6 h6)
 (* j2 j2 j2 j2 j2)) (* 12888 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* 
j2 j2 j2 j2)) (* 25544 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2
)) (* 28336 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2)) (* 16384 
(* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h6 h6) j2) (* 3840 (* h1 h1) (* h2 h2) 
(* h3 h3 h3) h4 (* h6 h6)) (* 144 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2)) (* 1776 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* 
j2 j2 j2 j2 j2)) (* 8224 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 
j2 j2)) (* 17984 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2)) (* 
19584 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2)) (* 10240 (* h1 h1
) (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) j2) (* 2048 (* h1 h1) (* h2 h2) (* h3 h3 
h3) (* h5 h5 h5)) (* 48 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2)) (* 1028 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 
j2 j2 j2 j2)) (* 8260 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 
j2 j2)) (* 33792 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) 
(* 74448 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 85440 
(* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2)) (* 47744 (* h1 h1) (* 
h2 h2) (* h3 h3 h3) (* h5 h5) h6 j2) (* 10240 (* h1 h1) (* h2 h2) (* h3 h3 h3) 
(* h5 h5) h6) (* 2 (* h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 98 (* h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2
 j2 j2 j2)) (* 1488 (* h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2
 j2 j2)) (* 10166 (* h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 36746 (* h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 
73812 (* h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 81424 (* h1
 h1) (* h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2)) (* 45824 (* h1 h1) (* h2 h2)
 (* h3 h3 h3) h5 (* h6 h6) j2) (* 10240 (* h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* 
h6 h6)) (* 20 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2
 j2)) (* 324 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)
) (* 2132 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
7340 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 14216 (* 
h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2)) (* 15488 (* h1 h1) (* 
h2 h2) (* h3 h3 h3) (* h6 h6 h6) (* j2 j2)) (* 8832 (* h1 h1) (* h2 h2) (* h3 h3
 h3) (* h6 h6 h6) j2) (* 2048 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6 h6)) (* 
108 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 1188
 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 4884 (* h1
 h1) (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 9564 (* h1 h1) (* 
h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 9648 (* h1 h1) (* h2 h2) (* h3
 h3) (* h4 h4 h4) h5 (* j2 j2)) (* 4848 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4 
h4) h5 j2) (* 960 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4 h4) h5) (* 16 (* h1 h1)
 (* h2 h2) (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 160 (* h1 h1) (* 
h2 h2) (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 608 (* h1 h1) (* h2 h2) 
(* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2)) (* 1152 (* h1 h1) (* h2 h2) (* h3 h3)
 (* h4 h4 h4) h6 (* j2 j2 j2)) (* 1168 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4 h4
) h6 (* j2 j2)) (* 608 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4 h4) h6 j2) (* 128 
(* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4 h4) h6) (* 72 (* h1 h1) (* h2 h2) (* h3 
h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1176 (* h1 h1) (* h2 h2) 
(* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 7448 (* h1 h1) (* h2 h2)
 (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 23496 (* h1 h1) (* h2 h2) 
(* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 39808 (* h1 h1) (* h2 h2) (* 
h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 36800 (* h1 h1) (* h2 h2) (* h3 h3) 
(* h4 h4) (* h5 h5) (* j2 j2)) (* 17472 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) 
(* h5 h5) j2) (* 3328 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5)) (* 3 
(* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 98
 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1352
 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 8566 
(* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 27673 (* h1
 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 48088 (* h1 h1) (* 
h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 45580 (* h1 h1) (* h2 h2) (* 
h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 22208 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 
h4) h5 h6 j2) (* 4352 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 h6) (* 8 (* h1 
h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 152 (* 
h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 992 (* 
h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 3120 (* h1
 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 5320 (* h1 h1) 
(* h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 5048 (* h1 h1) (* h2 h2
) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2)) (* 2512 (* h1 h1) (* h2 h2) (* h3 h3)
 (* h4 h4) (* h6 h6) j2) (* 512 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h6 h6
)) (* 54 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2))
 (* 882 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 
5622 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 18054 
(* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 30644 (* h1 h1
) (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2)) (* 27896 (* h1 h1) (* h2 h2)
 (* h3 h3) h4 (* h5 h5 h5) (* j2 j2)) (* 12880 (* h1 h1) (* h2 h2) (* h3 h3) h4 
(* h5 h5 h5) j2) (* 2368 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5 h5)) (* 6 (* 
h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 276 
(* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 3456 
(* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 19660 
(* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 58642 (* h1
 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 96448 (* h1 h1) (* 
h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 87880 (* h1 h1) (* h2 h2) (* 
h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 41536 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* 
h5 h5) h6 j2) (* 7936 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) h6) (* 8 (* h1 
h1) (* h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 232 (* 
h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2642 (* 
h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 14530 (* h1
 h1) (* h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 42690 (* h1 h1) 
(* h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 69950 (* h1 h1) (* h2 h2
) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 64028 (* h1 h1) (* h2 h2) (* h3 h3)
 h4 h5 (* h6 h6) (* j2 j2)) (* 30608 (* h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* h6 
h6) j2) (* 5952 (* h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* h6 h6)) (* 16 (* h1 h1) 
(* h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 256 (* h1 h1) 
(* h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1504 (* h1 h1) (* 
h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 4416 (* h1 h1) (* h2 h2)
 (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 7184 (* h1 h1) (* h2 h2) (* h3 h3
) h4 (* h6 h6 h6) (* j2 j2 j2)) (* 6592 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 
h6 h6) (* j2 j2)) (* 3200 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6 h6) j2) (* 
640 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6 h6)) (* 72 (* h1 h1) (* h2 h2) (* 
h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 672 (* h1 h1) (* h2 h2) (* h3 
h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 2312 (* h1 h1) (* h2 h2) (* h3 h3) 
(* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 3856 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 
h5 h5) (* j2 j2 j2)) (* 3360 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2
 j2)) (* 1472 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) j2) (* 256 (* h1 h1)
 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5)) (* 60 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 952 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 6056 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2)) (* 19448 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) 
h6 (* j2 j2 j2 j2)) (* 33020 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2
 j2 j2)) (* 30080 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2)) (* 
13904 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) h6 j2) (* 2560 (* h1 h1) (* h2 
h2) (* h3 h3) (* h5 h5 h5) h6) (* 6 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 208 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2340 (* h1 h1) (* h2 h2) (* h3 h3) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 12480 (* h1 h1) (* h2 h2) (* h3 h3
) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 35694 (* h1 h1) (* h2 h2) (* h3 h3)
 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 57216 (* h1 h1) (* h2 h2) (* h3 h3) (* 
h5 h5) (* h6 h6) (* j2 j2 j2)) (* 51384 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) 
(* h6 h6) (* j2 j2)) (* 24128 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) 
j2) (* 4608 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6)) (* 5 (* h1 h1) 
(* h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 134 (* h1 h1
) (* h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1398 (* h1 h1
) (* h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 7152 (* h1 h1) 
(* h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 19901 (* h1 h1) (* h2
 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 31426 (* h1 h1) (* h2 h2) (* 
h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 28096 (* h1 h1) (* h2 h2) (* h3 h3) h5 
(* h6 h6 h6) (* j2 j2)) (* 13248 (* h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6 h6) 
j2) (* 2560 (* h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6 h6)) (* 8 (* h1 h1) (* h2 
h2) (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 120 (* h1 h1) (* h2 
h2) (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 672 (* h1 h1) (* h2 h2) 
(* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1904 (* h1 h1) (* h2 h2) (* h3 
h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 3016 (* h1 h1) (* h2 h2) (* h3 h3) (* h6
 h6 h6 h6) (* j2 j2 j2)) (* 2712 (* h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6 h6) 
(* j2 j2)) (* 1296 (* h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6 h6) j2) (* 256 (* 
h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6 h6)) (* 108 (* h1 h1) (* h2 h2) h3 (* h4 
h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 864 (* h1 h1) (* h2 h2) h3 (* h4 h4 
h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 2616 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) 
(* h5 h5) (* j2 j2 j2 j2)) (* 3984 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) (* h5 h5)
 (* j2 j2 j2)) (* 3276 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2)) 
(* 1392 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) j2) (* 240 (* h1 h1) (* h2
 h2) h3 (* h4 h4 h4) (* h5 h5)) (* 4 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) h5 h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 60 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) h5 h6 (* j2 
j2 j2 j2 j2 j2)) (* 304 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2
 j2)) (* 760 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 1060 
(* h1 h1) (* h2 h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 844 (* h1 h1) (* h2 
h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2)) (* 360 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) 
h5 h6 j2) (* 64 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) h5 h6) (* 36 (* h1 h1) (* h2
 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 480 (* h1 h1) (* h2 
h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2392 (* h1 h1) (* h2 h2)
 h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 5904 (* h1 h1) (* h2 h2) h3 
(* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 8036 (* h1 h1) (* h2 h2) h3 (* h4 h4)
 (* h5 h5 h5) (* j2 j2 j2)) (* 6160 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5 h5
) (* j2 j2)) (* 2496 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) j2) (* 416 
(* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5 h5)) (* 6 (* h1 h1) (* h2 h2) h3 (* h4
 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 124 (* h1 h1) (* h2 h2) h3 (* 
h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1204 (* h1 h1) (* h2 h2) h3 (* 
h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 5712 (* h1 h1) (* h2 h2) h3 (* h4 
h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 14166 (* h1 h1) (* h2 h2) h3 (* h4 h4) 
(* h5 h5) h6 (* j2 j2 j2 j2)) (* 19620 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5
) h6 (* j2 j2 j2)) (* 15360 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 
j2)) (* 6368 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) h6 j2) (* 1088 (* h1 h1)
 (* h2 h2) h3 (* h4 h4) (* h5 h5) h6) (* 2 (* h1 h1) (* h2 h2) h3 (* h4 h4) h5 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 48 (* h1 h1) (* h2 h2) h3 (* h4 h4) h5
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 406 (* h1 h1) (* h2 h2) h3 (* h4 h4) h5 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1636 (* h1 h1) (* h2 h2) h3 (* h4 h4) h5 (* 
h6 h6) (* j2 j2 j2 j2 j2)) (* 3630 (* h1 h1) (* h2 h2) h3 (* h4 h4) h5 (* h6 h6)
 (* j2 j2 j2 j2)) (* 4712 (* h1 h1) (* h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2
 j2)) (* 3578 (* h1 h1) (* h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 1476 
(* h1 h1) (* h2 h2) h3 (* h4 h4) h5 (* h6 h6) j2) (* 256 (* h1 h1) (* h2 h2) h3 
(* h4 h4) h5 (* h6 h6)) (* 18 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2
 j2 j2 j2 j2 j2)) (* 204 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 
j2 j2 j2)) (* 884 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) 
(* 1968 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 2482 (* h1
 h1) (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2)) (* 1796 (* h1 h1) (* h2 h2) 
h3 h4 (* h5 h5 h5 h5) (* j2 j2)) (* 696 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5 h5
) j2) (* 112 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5 h5)) (* 6 (* h1 h1) (* h2 h2)
 h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 170 (* h1 h1) (* h2 h2) 
h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1576 (* h1 h1) (* h2 h2) h3 
h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 6820 (* h1 h1) (* h2 h2) h3 h4 (* 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 15766 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5)
 h6 (* j2 j2 j2 j2)) (* 20770 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2
 j2)) (* 15676 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2)) (* 6320 (* 
h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) h6 j2) (* 1056 (* h1 h1) (* h2 h2) h3 h4 (* 
h5 h5 h5) h6) (* 15 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2
 j2 j2 j2 j2)) (* 283 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 2256 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 9302 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 21271 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 
28119 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 21434 (* h1
 h1) (* h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 8760 (* h1 h1) (* h2 h2) 
h3 h4 (* h5 h5) (* h6 h6) j2) (* 1488 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* h6 
h6)) (* 4 (* h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2))
 (* 84 (* h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
632 (* h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2360 (* 
h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 4980 (* h1 h1) (* 
h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 6244 (* h1 h1) (* h2 h2) h3 h4 
h5 (* h6 h6 h6) (* j2 j2 j2)) (* 4624 (* h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6 h6) 
(* j2 j2)) (* 1872 (* h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6 h6) j2) (* 320 (* h1 h1
) (* h2 h2) h3 h4 h5 (* h6 h6 h6)) (* 24 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 256 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 1072 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* 2336 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2))
 (* 2904 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 2080 (* h1 
h1) (* h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 800 (* h1 h1) (* h2 h2) h3 (* 
h5 h5 h5 h5) h6 j2) (* 128 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) h6) (* 6 (* h1
 h1) (* h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 136 (* 
h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1110 (* 
h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4468 (* h1 
h1) (* h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 9922 (* h1 h1) 
(* h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 12784 (* h1 h1) (* h2 h2
) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 9538 (* h1 h1) (* h2 h2) h3 (* h5 
h5 h5) (* h6 h6) (* j2 j2)) (* 3828 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* h6 h6
) j2) (* 640 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* h6 h6)) (* 9 (* h1 h1) (* h2
 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 159 (* h1 h1) (* 
h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1160 (* h1 h1) (* 
h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4454 (* h1 h1) (* h2 
h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 9721 (* h1 h1) (* h2 h2) h3
 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 12483 (* h1 h1) (* h2 h2) h3 (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2)) (* 9350 (* h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6
 h6) (* j2 j2)) (* 3784 (* h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6 h6) j2) (* 640
 (* h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6 h6)) (* 2 (* h1 h1) (* h2 h2) h3 h5 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 40 (* h1 h1) (* h2 h2) h3 h5 (* 
h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 286 (* h1 h1) (* h2 h2) h3 h5 (* h6 h6
 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1028 (* h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6 h6)
 (* j2 j2 j2 j2 j2)) (* 2110 (* h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 
j2 j2)) (* 2592 (* h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 1890 
(* h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2)) (* 756 (* h1 h1) (* h2 h2) 
h3 h5 (* h6 h6 h6 h6) j2) (* 128 (* h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6 h6)) (* 4
 (* h1 h1) (* h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 32 
(* h1 h1) (* h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 108 (* 
h1 h1) (* h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 200 (* h1 h1) 
(* h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 220 (* h1 h1) (* h2 h2) 
(* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 144 (* h1 h1) (* h2 h2) (* h4 h4 h4) 
(* h5 h5) h6 (* j2 j2)) (* 52 (* h1 h1) (* h2 h2) (* h4 h4 h4) (* h5 h5) h6 j2) 
(* 8 (* h1 h1) (* h2 h2) (* h4 h4 h4) (* h5 h5) h6) (* 3 (* h1 h1) (* h2 h2) (* 
h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 38 (* h1 h1) (* h2 h2) 
(* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 193 (* h1 h1) (* h2 h2) 
(* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 528 (* h1 h1) (* h2 h2) (* 
h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 865 (* h1 h1) (* h2 h2) (* h4 h4) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 878 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5 
h5) h6 (* j2 j2 j2)) (* 543 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 
j2)) (* 188 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5 h5) h6 j2) (* 28 (* h1 h1) 
(* h2 h2) (* h4 h4) (* h5 h5 h5) h6) (* 2 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5
) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 32 (* h1 h1) (* h2 h2) (* h4 h4) (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 182 (* h1 h1) (* h2 h2) (* h4 h4) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 532 (* h1 h1) (* h2 h2) (* h4 h4) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 910 (* h1 h1) (* h2 h2) (* h4 h4) (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 952 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5)
 (* h6 h6) (* j2 j2 j2)) (* 602 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6
) (* j2 j2)) (* 212 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) j2) (* 32 
(* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6)) (* 2 (* h1 h1) (* h2 h2) h4 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 24 (* h1 h1) (* h2 h2) h4 (* 
h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 118 (* h1 h1) (* h2 h2) h4 (* h5 h5
 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 316 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2)) (* 510 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2
 j2 j2)) (* 512 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 314 
(* h1 h1) (* h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 108 (* h1 h1) (* h2 h2) 
h4 (* h5 h5 h5 h5) h6 j2) (* 16 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5 h5) h6) (* 7 
(* h1 h1) (* h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 86
 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 429 
(* h1 h1) (* h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1160 (* 
h1 h1) (* h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1885 (* h1 h1)
 (* h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 1902 (* h1 h1) (* h2 h2
) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 1171 (* h1 h1) (* h2 h2) h4 (* h5 
h5 h5) (* h6 h6) (* j2 j2)) (* 404 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5) (* h6 h6)
 j2) (* 60 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5) (* h6 h6)) (* 4 (* h1 h1) (* h2 
h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 52 (* h1 h1) (* h2
 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 268 (* h1 h1) (* h2 
h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 740 (* h1 h1) (* h2 h2) 
h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1220 (* h1 h1) (* h2 h2) h4 (* 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1244 (* h1 h1) (* h2 h2) h4 (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2)) (* 772 (* h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6 h6) 
(* j2 j2)) (* 268 (* h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6 h6) j2) (* 40 (* h1 
h1) (* h2 h2) h4 (* h5 h5) (* h6 h6 h6)) (* 2 (* h1 h1) (* h2 h2) (* h5 h5 h5 h5
) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 24 (* h1 h1) (* h2 h2) (* h5 h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 118 (* h1 h1) (* h2 h2) (* h5 h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 316 (* h1 h1) (* h2 h2) (* h5 h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 510 (* h1 h1) (* h2 h2) (* h5 h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2)) (* 512 (* h1 h1) (* h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 
j2 j2)) (* 314 (* h1 h1) (* h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 108 
(* h1 h1) (* h2 h2) (* h5 h5 h5 h5) (* h6 h6) j2) (* 16 (* h1 h1) (* h2 h2) (* 
h5 h5 h5 h5) (* h6 h6)) (* 4 (* h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 48 (* h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 236 (* h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 632 (* h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2)) (* 1020 (* h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2)) (* 1024 (* h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 628 
(* h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 216 (* h1 h1) (* h2 
h2) (* h5 h5 h5) (* h6 h6 h6) j2) (* 32 (* h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 
h6 h6)) (* 2 (* h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 24 (* h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2
 j2)) (* 118 (* h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)
) (* 316 (* h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
510 (* h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 512 (* h1 
h1) (* h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 314 (* h1 h1) (* h2 h2)
 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 108 (* h1 h1) (* h2 h2) (* h5 h5) (* h6
 h6 h6 h6) j2) (* 16 (* h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6 h6)) (* 48 (* h1 
h1) h2 (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 872 (* h1 h1) 
h2 (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 6416 (* h1 h1) h2 (* 
h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 24424 (* h1 h1) h2 (* h3 h3 h3 
h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 51024 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4
) h5 (* j2 j2 j2)) (* 57536 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2))
 (* 32512 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h5 j2) (* 7168 (* h1 h1) h2 (* 
h3 h3 h3 h3) (* h4 h4) h5) (* 8 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 
j2 j2 j2 j2 j2 j2)) (* 136 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2
 j2 j2 j2)) (* 936 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2))
 (* 3352 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2)) (* 6704 (* 
h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2)) (* 7488 (* h1 h1) h2 (* h3 
h3 h3 h3) (* h4 h4) h6 (* j2 j2)) (* 4352 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4)
 h6 j2) (* 1024 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h6) (* 108 (* h1 h1) h2 
(* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1980 (* h1 h1) h2 (* 
h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 14592 (* h1 h1) h2 (* h3 h3 
h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 54960 (* h1 h1) h2 (* h3 h3 h3 h3) h4
 (* h5 h5) (* j2 j2 j2 j2)) (* 111360 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h5 h5) 
(* j2 j2 j2)) (* 118272 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2)) (* 
61440 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h5 h5) j2) (* 12288 (* h1 h1) h2 (* h3 
h3 h3 h3) h4 (* h5 h5)) (* 216 (* h1 h1) h2 (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2
 j2 j2 j2 j2)) (* 3648 (* h1 h1) h2 (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 
j2)) (* 24920 (* h1 h1) h2 (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 88208
 (* h1 h1) h2 (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 172512 (* h1 h1) h2 
(* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 184640 (* h1 h1) h2 (* h3 h3 h3 h3) h4
 h5 h6 (* j2 j2)) (* 100352 (* h1 h1) h2 (* h3 h3 h3 h3) h4 h5 h6 j2) (* 21504 
(* h1 h1) h2 (* h3 h3 h3 h3) h4 h5 h6) (* 40 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 616 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6
) (* j2 j2 j2 j2 j2 j2)) (* 3848 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6) (* j2
 j2 j2 j2 j2)) (* 12600 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2
)) (* 23344 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2)) (* 24512 (* 
h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2)) (* 13568 (* h1 h1) h2 (* h3 h3
 h3 h3) h4 (* h6 h6) j2) (* 3072 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6)) (* 
216 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2592 (* 
h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 11520 (* h1 h1) h2
 (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 23680 (* h1 h1) h2 (* h3 h3 h3
 h3) (* h5 h5 h5) (* j2 j2 j2)) (* 23680 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5 
h5) (* j2 j2)) (* 11264 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5 h5) j2) (* 2048 
(* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5 h5)) (* 72 (* h1 h1) h2 (* h3 h3 h3 h3) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1824 (* h1 h1) h2 (* h3 h3 h3 h3) (* 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 15512 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5)
 h6 (* j2 j2 j2 j2 j2)) (* 62112 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) h6 (* j2
 j2 j2 j2)) (* 128736 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2)) 
(* 137728 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2)) (* 71680 (* h1 h1
) h2 (* h3 h3 h3 h3) (* h5 h5) h6 j2) (* 14336 (* h1 h1) h2 (* h3 h3 h3 h3) (* 
h5 h5) h6) (* 156 (* h1 h1) h2 (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2
 j2)) (* 2720 (* h1 h1) h2 (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 18604 (* h1 h1) h2 (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 64616 
(* h1 h1) h2 (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 122944 (* h1 h1) 
h2 (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 128128 (* h1 h1) h2 (* h3 h3 h3
 h3) h5 (* h6 h6) (* j2 j2)) (* 68096 (* h1 h1) h2 (* h3 h3 h3 h3) h5 (* h6 h6) 
j2) (* 14336 (* h1 h1) h2 (* h3 h3 h3 h3) h5 (* h6 h6)) (* 32 (* h1 h1) h2 (* h3
 h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 480 (* h1 h1) h2 (* h3 h3 
h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2912 (* h1 h1) h2 (* h3 h3 h3 h3) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 9248 (* h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6 
h6) (* j2 j2 j2 j2)) (* 16640 (* h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2
 j2)) (* 17024 (* h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2)) (* 9216 (* 
h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6 h6) j2) (* 2048 (* h1 h1) h2 (* h3 h3 h3 h3) 
(* h6 h6 h6)) (* 72 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 
j2 j2)) (* 1128 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2))
 (* 6984 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 21816 
(* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 36816 (* h1 h1) h2
 (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 33984 (* h1 h1) h2 (* h3 h3 h3) 
(* h4 h4 h4) h5 (* j2 j2)) (* 16128 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h5 j2
) (* 3072 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h5) (* 8 (* h1 h1) h2 (* h3 h3 
h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 112 (* h1 h1) h2 (* h3 h3 h3) 
(* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 624 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4
 h4) h6 (* j2 j2 j2 j2 j2)) (* 1792 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h6 
(* j2 j2 j2 j2)) (* 2888 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2))
 (* 2640 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2)) (* 1280 (* h1 h1) 
h2 (* h3 h3 h3) (* h4 h4 h4) h6 j2) (* 256 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4
) h6) (* 360 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 
j2)) (* 5136 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)
) (* 29232 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 
84800 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 134056 
(* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 116592 (* h1 h1) 
h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 52352 (* h1 h1) h2 (* h3 h3 h3
) (* h4 h4) (* h5 h5) j2) (* 9472 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h5 h5))
 (* 2 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
492 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 6604 
(* h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 36464 (* h1 
h1) h2 (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 104546 (* h1 h1) h2 
(* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 166356 (* h1 h1) h2 (* h3 h3 h3
) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 147648 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5
 h6 (* j2 j2)) (* 68288 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 h6 j2) (* 12800 
(* h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 h6) (* 48 (* h1 h1) h2 (* h3 h3 h3) (* h4
 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 608 (* h1 h1) h2 (* h3 h3 h3) (* h4 
h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3104 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4)
 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 8320 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h6
 h6) (* j2 j2 j2 j2)) (* 12720 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h6 h6) (* 
j2 j2 j2)) (* 11168 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2)) (* 
5248 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h6 h6) j2) (* 1024 (* h1 h1) h2 (* 
h3 h3 h3) (* h4 h4) (* h6 h6)) (* 216 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 3312 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* 
j2 j2 j2 j2 j2 j2)) (* 19896 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 
j2 j2 j2)) (* 59520 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) 
(* 94560 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2)) (* 81024 (* h1 
h1) h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2)) (* 35328 (* h1 h1) h2 (* h3 h3 h3
) h4 (* h5 h5 h5) j2) (* 6144 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5 h5)) (* 24 
(* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1300 
(* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 15028 (* 
h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 77740 (* h1 h1)
 h2 (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 214116 (* h1 h1) h2 (* 
h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 329280 (* h1 h1) h2 (* h3 h3 h3) 
h4 (* h5 h5) h6 (* j2 j2 j2)) (* 282448 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) 
h6 (* j2 j2)) (* 126080 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6 j2) (* 22784 
(* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6) (* 14 (* h1 h1) h2 (* h3 h3 h3) h4 h5
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1008 (* h1 h1) h2 (* h3 h3 h3) h4 h5 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 11360 (* h1 h1) h2 (* h3 h3 h3) h4 h5 (* 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 56812 (* h1 h1) h2 (* h3 h3 h3) h4 h5 (* h6 h6)
 (* j2 j2 j2 j2 j2)) (* 152530 (* h1 h1) h2 (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 
j2 j2 j2)) (* 232388 (* h1 h1) h2 (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 
200480 (* h1 h1) h2 (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 91072 (* h1 h1) 
h2 (* h3 h3 h3) h4 h5 (* h6 h6) j2) (* 16896 (* h1 h1) h2 (* h3 h3 h3) h4 h5 (* 
h6 h6)) (* 72 (* h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 880 (* h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
4336 (* h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 11264 (* 
h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 16776 (* h1 h1) h2 
(* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2)) (* 14416 (* h1 h1) h2 (* h3 h3 h3) h4
 (* h6 h6 h6) (* j2 j2)) (* 6656 (* h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6 h6) j2) 
(* 1280 (* h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6 h6)) (* 216 (* h1 h1) h2 (* h3 h3 
h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1944 (* h1 h1) h2 (* h3 h3 h3) (* 
h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 6336 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5 
h5) (* j2 j2 j2 j2)) (* 9856 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 
j2)) (* 7936 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2)) (* 3200 (* h1 
h1) h2 (* h3 h3 h3) (* h5 h5 h5 h5) j2) (* 512 (* h1 h1) h2 (* h3 h3 h3) (* h5 
h5 h5 h5)) (* 216 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2
 j2)) (* 3744 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 23352 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 70320 
(* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 111488 (* h1 h1) 
h2 (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 95168 (* h1 h1) h2 (* h3 h3 h3)
 (* h5 h5 h5) h6 (* j2 j2)) (* 41344 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) h6 
j2) (* 7168 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) h6) (* 18 (* h1 h1) h2 (* h3 
h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 882 (* h1 h1) h2 (* 
h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 9778 (* h1 h1) h2 (* 
h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 48678 (* h1 h1) h2 (* h3
 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 130148 (* h1 h1) h2 (* h3 h3 
h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 196304 (* h1 h1) h2 (* h3 h3 h3) (* 
h5 h5) (* h6 h6) (* j2 j2 j2)) (* 166464 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* 
h6 h6) (* j2 j2)) (* 73856 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* h6 h6) j2) (* 
13312 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* h6 h6)) (* 12 (* h1 h1) h2 (* h3 h3
 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 588 (* h1 h1) h2 (* h3 h3 
h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 5884 (* h1 h1) h2 (* h3 h3 h3) 
h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 27332 (* h1 h1) h2 (* h3 h3 h3) h5 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 69800 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6 h6)
 (* j2 j2 j2 j2)) (* 102848 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 
j2)) (* 86816 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 38912 (* 
h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6 h6) j2) (* 7168 (* h1 h1) h2 (* h3 h3 h3) h5 
(* h6 h6 h6)) (* 32 (* h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 384 (* h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 1856 (* h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 4736 
(* h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 6944 (* h1 h1) h2 
(* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 5888 (* h1 h1) h2 (* h3 h3 h3) (* 
h6 h6 h6 h6) (* j2 j2)) (* 2688 (* h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6 h6) j2) 
(* 512 (* h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6 h6)) (* 72 (* h1 h1) h2 (* h3 h3) 
(* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 624 (* h1 h1) h2 (* h3 h3) (* h4 h4
 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 1968 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4 h4) h5
 (* j2 j2 j2 j2)) (* 3072 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2)
) (* 2568 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2)) (* 1104 (* h1 h1)
 h2 (* h3 h3) (* h4 h4 h4 h4) h5 j2) (* 192 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4 
h4) h5) (* 144 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 
j2 j2)) (* 1824 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 
j2)) (* 8928 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) 
(* 21888 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 29712
 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 22752 (* h1 h1) 
h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 9216 (* h1 h1) h2 (* h3 h3) 
(* h4 h4 h4) (* h5 h5) j2) (* 1536 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) (* h5 h5)
) (* 2 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 82 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
1128 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 6020 
(* h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 15586 (* h1 h1)
 h2 (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 21946 (* h1 h1) h2 (* h3 h3
) (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 17268 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) 
h5 h6 (* j2 j2)) (* 7152 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 h6 j2) (* 1216 
(* h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 h6) (* 360 (* h1 h1) h2 (* h3 h3) (* h4 
h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 4056 (* h1 h1) h2 (* h3 h3) (* h4 
h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 18144 (* h1 h1) h2 (* h3 h3) (* h4 h4
) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 41456 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* 
h5 h5 h5) (* j2 j2 j2 j2)) (* 53032 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5 h5
) (* j2 j2 j2)) (* 38520 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2)
) (* 14864 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) j2) (* 2368 (* h1 h1) 
h2 (* h3 h3) (* h4 h4) (* h5 h5 h5)) (* 42 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1266 (* h1 h1) h2 (* h3 h3) (* h4 h4) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 11144 (* h1 h1) h2 (* h3 h3) (* h4 h4)
 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 45924 (* h1 h1) h2 (* h3 h3) (* h4 h4) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 102378 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* 
h5 h5) h6 (* j2 j2 j2 j2)) (* 131194 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) 
h6 (* j2 j2 j2)) (* 96804 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2
)) (* 38256 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) h6 j2) (* 6272 (* h1 h1) 
h2 (* h3 h3) (* h4 h4) (* h5 h5) h6) (* 16 (* h1 h1) h2 (* h3 h3) (* h4 h4) h5 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 444 (* h1 h1) h2 (* h3 h3) (* h4 h4) 
h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4176 (* h1 h1) h2 (* h3 h3) (* h4 h4) 
h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 18072 (* h1 h1) h2 (* h3 h3) (* h4 h4) h5
 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 41600 (* h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* 
h6 h6) (* j2 j2 j2 j2)) (* 54556 (* h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* h6 h6) 
(* j2 j2 j2)) (* 41024 (* h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2)) 
(* 16496 (* h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* h6 h6) j2) (* 2752 (* h1 h1) h2 
(* h3 h3) (* h4 h4) h5 (* h6 h6)) (* 108 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5 
h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1332 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2)) (* 6276 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 
j2 j2 j2 j2)) (* 14604 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2)
) (* 18624 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2)) (* 13296 (* 
h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2)) (* 4992 (* h1 h1) h2 (* h3 h3)
 h4 (* h5 h5 h5 h5) j2) (* 768 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5 h5)) (* 48 
(* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1376 
(* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 11888 (* 
h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 48032 (* h1 h1)
 h2 (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 104560 (* h1 h1) h2 (* 
h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 130432 (* h1 h1) h2 (* h3 h3) h4 
(* h5 h5 h5) h6 (* j2 j2 j2)) (* 93488 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) h6
 (* j2 j2)) (* 35840 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) h6 j2) (* 5696 (* h1
 h1) h2 (* h3 h3) h4 (* h5 h5 h5) h6) (* (* h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 121 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5
) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2402 (* h1 h1) h2 (* h3 h3) h4 (* h5
 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 17982 (* h1 h1) h2 (* h3 h3) h4 (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 67685 (* h1 h1) h2 (* h3 h3) h4 (* h5
 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 142845 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5)
 (* h6 h6) (* j2 j2 j2 j2)) (* 176792 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* h6 
h6) (* j2 j2 j2)) (* 127516 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 
j2)) (* 49648 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* h6 h6) j2) (* 8064 (* h1 h1
) h2 (* h3 h3) h4 (* h5 h5) (* h6 h6)) (* 26 (* h1 h1) h2 (* h3 h3) h4 h5 (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 642 (* h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6
 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 5256 (* h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2)) (* 20580 (* h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6) (* j2
 j2 j2 j2 j2)) (* 44314 (* h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2
)) (* 55562 (* h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 40516 (* 
h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2)) (* 15952 (* h1 h1) h2 (* h3 h3
) h4 h5 (* h6 h6 h6) j2) (* 2624 (* h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6)) (* 
144 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1704 
(* h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 7768 (* h1 
h1) h2 (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 17688 (* h1 h1) h2 
(* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 22232 (* h1 h1) h2 (* h3 h3) 
(* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 15712 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5)
 h6 (* j2 j2)) (* 5856 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) h6 j2) (* 896 (* 
h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) h6) (* 42 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5
) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 988 (* h1 h1) h2 (* h3 h3) (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 7804 (* h1 h1) h2 (* h3 h3) (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 29952 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5
) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 63290 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2)) (* 77588 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2)) (* 55056 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2)) 
(* 20992 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* h6 h6) j2) (* 3328 (* h1 h1) h2 
(* h3 h3) (* h5 h5 h5) (* h6 h6)) (* (* h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 79 (* h1 h1) h2 (* h3 h3) (* h5 h5) (* h6
 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1280 (* h1 h1) h2 (* h3 h3) (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 8662 (* h1 h1) h2 (* h3 h3) (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 30689 (* h1 h1) h2 (* h3 h3) (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 62355 (* h1 h1) h2 (* h3 h3) (* h5 h5) (* h6
 h6 h6) (* j2 j2 j2 j2)) (* 75310 (* h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2)) (* 53464 (* h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2)) 
(* 20608 (* h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6 h6) j2) (* 3328 (* h1 h1) h2 
(* h3 h3) (* h5 h5) (* h6 h6 h6)) (* 12 (* h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 280 (* h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 2136 (* h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 7904 (* h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 
j2 j2 j2)) (* 16332 (* h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) 
(* 19880 (* h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 14192 (* h1 
h1) h2 (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2)) (* 5504 (* h1 h1) h2 (* h3 h3) h5
 (* h6 h6 h6 h6) j2) (* 896 (* h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6 h6)) (* 72 (* 
h1 h1) h2 h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 408 (* h1 h1) 
h2 h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 960 (* h1 h1) h2 h3 (* h4
 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 1200 (* h1 h1) h2 h3 (* h4 h4 h4 h4) 
(* h5 h5) (* j2 j2 j2)) (* 840 (* h1 h1) h2 h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 
j2)) (* 312 (* h1 h1) h2 h3 (* h4 h4 h4 h4) (* h5 h5) j2) (* 48 (* h1 h1) h2 h3 
(* h4 h4 h4 h4) (* h5 h5)) (* 72 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5 h5) (* j2
 j2 j2 j2 j2 j2 j2)) (* 696 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 
j2 j2 j2 j2)) (* 2592 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 
j2)) (* 5040 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 5640 
(* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 3672 (* h1 h1) h2 h3 
(* h4 h4 h4) (* h5 h5 h5) (* j2 j2)) (* 1296 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 
h5 h5) j2) (* 192 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5 h5)) (* 4 (* h1 h1) h2 
h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 104 (* h1 h1) h2 h3
 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 956 (* h1 h1) h2 h3 (* 
h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 3664 (* h1 h1) h2 h3 (* h4 h4 
h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 7340 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 
h5) h6 (* j2 j2 j2 j2)) (* 8424 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 
j2 j2)) (* 5604 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 2016 (* 
h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) h6 j2) (* 304 (* h1 h1) h2 h3 (* h4 h4 h4) 
(* h5 h5) h6) (* 48 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 
j2 j2)) (* 440 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) 
(* 1592 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 3040 
(* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 3360 (* h1 h1) h2 
h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 2168 (* h1 h1) h2 h3 (* h4 h4) (* 
h5 h5 h5 h5) (* j2 j2)) (* 760 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5 h5) j2) (* 
112 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5 h5)) (* 42 (* h1 h1) h2 h3 (* h4 h4) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 692 (* h1 h1) h2 h3 (* h4 h4) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 4314 (* h1 h1) h2 h3 (* h4 h4) (* 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 13460 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2)) (* 23870 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) h6 
(* j2 j2 j2 j2)) (* 25292 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)
) (* 15902 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 5484 (* h1 h1
) h2 h3 (* h4 h4) (* h5 h5 h5) h6 j2) (* 800 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 
h5) h6) (* (* h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2
 j2 j2)) (* 42 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 549 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 3350 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 10603 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2
)) (* 19166 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 
20687 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 13234 (* h1
 h1) h2 h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 4640 (* h1 h1) h2 h3 (* 
h4 h4) (* h5 h5) (* h6 h6) j2) (* 688 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* h6 
h6)) (* 24 (* h1 h1) h2 h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 364 (* h1 h1) h2 h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2116 
(* h1 h1) h2 h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 6296 (* h1 h1) 
h2 h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 10800 (* h1 h1) h2 h3 h4 (* 
h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 11164 (* h1 h1) h2 h3 h4 (* h5 h5 h5 h5) h6 
(* j2 j2 j2)) (* 6884 (* h1 h1) h2 h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 2336 
(* h1 h1) h2 h3 h4 (* h5 h5 h5 h5) h6 j2) (* 336 (* h1 h1) h2 h3 h4 (* h5 h5 h5 
h5) h6) (* 2 (* h1 h1) h2 h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 110 (* h1 h1) h2 h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2
 j2)) (* 1314 (* h1 h1) h2 h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 7010 (* h1 h1) h2 h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
20106 (* h1 h1) h2 h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 33922 (* 
h1 h1) h2 h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 34830 (* h1 h1) h2 h3
 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 21454 (* h1 h1) h2 h3 h4 (* h5 h5 h5
) (* h6 h6) (* j2 j2)) (* 7300 (* h1 h1) h2 h3 h4 (* h5 h5 h5) (* h6 h6) j2) (* 
1056 (* h1 h1) h2 h3 h4 (* h5 h5 h5) (* h6 h6)) (* 2 (* h1 h1) h2 h3 h4 (* h5 h5
) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 72 (* h1 h1) h2 h3 h4 (* h5 h5
) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 786 (* h1 h1) h2 h3 h4 (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4120 (* h1 h1) h2 h3 h4 (* h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 11846 (* h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2)) (* 20152 (* h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6 h6) (* j2
 j2 j2 j2)) (* 20902 (* h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 
13016 (* h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 4480 (* h1 h1) h2 
h3 h4 (* h5 h5) (* h6 h6 h6) j2) (* 656 (* h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6 h6
)) (* 24 (* h1 h1) h2 h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 316 (* h1 h1) h2 h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
1676 (* h1 h1) h2 h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4704 
(* h1 h1) h2 h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 7760 (* h1 h1) 
h2 h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 7804 (* h1 h1) h2 h3 (* h5 
h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 4716 (* h1 h1) h2 h3 (* h5 h5 h5 h5) (* h6 
h6) (* j2 j2)) (* 1576 (* h1 h1) h2 h3 (* h5 h5 h5 h5) (* h6 h6) j2) (* 224 (* 
h1 h1) h2 h3 (* h5 h5 h5 h5) (* h6 h6)) (* 2 (* h1 h1) h2 h3 (* h5 h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 68 (* h1 h1) h2 h3 (* h5 h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 694 (* h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6
 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3392 (* h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2)) (* 9238 (* h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2)) (* 15092 (* h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)
) (* 15178 (* h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 9224 (* h1
 h1) h2 h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 3112 (* h1 h1) h2 h3 (* h5 h5
 h5) (* h6 h6 h6) j2) (* 448 (* h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6 h6)) (* (* h1
 h1) h2 h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 34 (* h1
 h1) h2 h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 341 (* h1 
h1) h2 h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1654 (* h1 h1) 
h2 h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4499 (* h1 h1) h2 h3 
(* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 7366 (* h1 h1) h2 h3 (* h5 h5) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 7439 (* h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6 
h6) (* j2 j2 j2)) (* 4546 (* h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) 
(* 1544 (* h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6 h6) j2) (* 224 (* h1 h1) h2 h3 (* 
h5 h5) (* h6 h6 h6 h6)) (* 2 (* h1 h1) h2 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 18 (* h1 h1) h2 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2)) (* 70 (* h1 h1) h2 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2)) (* 154 (* h1 h1) h2 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 210
 (* h1 h1) h2 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 182 (* h1 h1) h2 
(* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 98 (* h1 h1) h2 (* h4 h4 h4) (* h5
 h5 h5) h6 (* j2 j2)) (* 30 (* h1 h1) h2 (* h4 h4 h4) (* h5 h5 h5) h6 j2) (* 4 
(* h1 h1) h2 (* h4 h4 h4) (* h5 h5 h5) h6) (* 2 (* h1 h1) h2 (* h4 h4) (* h5 h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 18 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 70 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5 h5) h6
 (* j2 j2 j2 j2 j2 j2)) (* 154 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* 210 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) 
(* 182 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 98 (* h1 h1) 
h2 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 30 (* h1 h1) h2 (* h4 h4) (* h5 h5
 h5 h5) h6 j2) (* 4 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5 h5) h6) (* (* h1 h1) h2 
(* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 17 (* h1 h1)
 h2 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 107 (* h1 
h1) h2 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 357 (* h1 
h1) h2 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 721 (* h1 h1) 
h2 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 931 (* h1 h1) h2 (* 
h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 777 (* h1 h1) h2 (* h4 h4) (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 407 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5) (* 
h6 h6) (* j2 j2)) (* 122 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5) (* h6 h6) j2) (* 16
 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5) (* h6 h6)) (* (* h1 h1) h2 h4 (* h5 h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 15 (* h1 h1) h2 h4 (* h5 h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 89 (* h1 h1) h2 h4 (* h5 h5 h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 287 (* h1 h1) h2 h4 (* h5 h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 567 (* h1 h1) h2 h4 (* h5 h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* 721 (* h1 h1) h2 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2
 j2)) (* 595 (* h1 h1) h2 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 309 (* 
h1 h1) h2 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 92 (* h1 h1) h2 h4 (* h5 h5
 h5 h5) (* h6 h6) j2) (* 12 (* h1 h1) h2 h4 (* h5 h5 h5 h5) (* h6 h6)) (* 2 (* 
h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 28 (* 
h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 160 (* h1
 h1) h2 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 504 (* h1 h1) 
h2 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 980 (* h1 h1) h2 h4 
(* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1232 (* h1 h1) h2 h4 (* h5 h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1008 (* h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6 
h6) (* j2 j2 j2)) (* 520 (* h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) 
(* 154 (* h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6 h6) j2) (* 20 (* h1 h1) h2 h4 (* h5
 h5 h5) (* h6 h6 h6)) (* (* h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 13 (* h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 71 (* h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 217 (* h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2
)) (* 413 (* h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 511 
(* h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 413 (* h1 h1) h2 
(* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 211 (* h1 h1) h2 (* h5 h5 h5 h5) 
(* h6 h6 h6) (* j2 j2)) (* 62 (* h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6 h6) j2) (* 8
 (* h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6 h6)) (* (* h1 h1) h2 (* h5 h5 h5) (* h6 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 13 (* h1 h1) h2 (* h5 h5 h5) (* h6 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 71 (* h1 h1) h2 (* h5 h5 h5) (* h6 h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 217 (* h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6 h6
) (* j2 j2 j2 j2 j2 j2)) (* 413 (* h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 
j2 j2 j2 j2)) (* 511 (* h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) 
(* 413 (* h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 211 (* h1 h1) 
h2 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 62 (* h1 h1) h2 (* h5 h5 h5) (* h6
 h6 h6 h6) j2) (* 8 (* h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6 h6)) (* 24 (* h1 h1) 
(* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 376 (* h1 h1) (* h3
 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 2328 (* h1 h1) (* h3 h3 h3 
h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 7272 (* h1 h1) (* h3 h3 h3 h3) (* h4 
h4 h4) h5 (* j2 j2 j2 j2)) (* 12272 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4 h4) h5 
(* j2 j2 j2)) (* 11328 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2)) (* 
5376 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4 h4) h5 j2) (* 1024 (* h1 h1) (* h3 h3 h3
 h3) (* h4 h4 h4) h5) (* 144 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2
 j2 j2 j2 j2 j2 j2)) (* 2208 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2
 j2 j2 j2 j2 j2)) (* 13264 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 
j2 j2 j2 j2)) (* 39680 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2
 j2)) (* 63040 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 
54016 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 23552 (* h1 h1
) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) j2) (* 4096 (* h1 h1) (* h3 h3 h3 h3) (* 
h4 h4) (* h5 h5)) (* 12 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2
 j2 j2 j2 j2)) (* 356 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 
j2 j2 j2)) (* 3604 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 
j2)) (* 17692 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 
47376 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 72048 (* h1 
h1) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 61888 (* h1 h1) (* h3 h3 h3
 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 27904 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 
h6 j2) (* 5120 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 h6) (* 432 (* h1 h1) (* h3
 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 4752 (* h1 h1) (* h3 h3 h3 
h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 18720 (* h1 h1) (* h3 h3 h3 h3) h4 
(* h5 h5 h5) (* j2 j2 j2 j2)) (* 32960 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5 h5)
 (* j2 j2 j2)) (* 28800 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2)) (* 
12288 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5 h5) j2) (* 2048 (* h1 h1) (* h3 h3 
h3 h3) h4 (* h5 h5 h5)) (* 72 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2
 j2 j2 j2 j2 j2 j2)) (* 1464 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2)) (* 12728 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 
j2 j2 j2)) (* 58376 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)
) (* 149216 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 215456
 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 173696 (* h1 h1) (* 
h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 72704 (* h1 h1) (* h3 h3 h3 h3) h4 
(* h5 h5) h6 j2) (* 12288 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) h6) (* 60 (* h1
 h1) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1180 (* h1 
h1) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 9388 (* h1 h1) 
(* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 39220 (* h1 h1) (* h3 
h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 93736 (* h1 h1) (* h3 h3 h3 h3)
 h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 131520 (* h1 h1) (* h3 h3 h3 h3) h4 h5 (* 
h6 h6) (* j2 j2 j2)) (* 106624 (* h1 h1) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 
j2)) (* 46080 (* h1 h1) (* h3 h3 h3 h3) h4 h5 (* h6 h6) j2) (* 8192 (* h1 h1) 
(* h3 h3 h3 h3) h4 h5 (* h6 h6)) (* 216 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 3240 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 18864 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* 53920 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)
) (* 80320 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 63744 (* 
h1 h1) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2)) (* 25600 (* h1 h1) (* h3 h3 h3
 h3) (* h5 h5 h5) h6 j2) (* 4096 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5 h5) h6) (* 
36 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 984 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 9364 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
43184 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
107856 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 151680 
(* h1 h1) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 119552 (* h1 h1) 
(* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 49152 (* h1 h1) (* h3 h3 h3 h3
) (* h5 h5) (* h6 h6) j2) (* 8192 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6))
 (* 48 (* h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 848 (* h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
6160 (* h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 23856 
(* h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 53632 (* h1 h1)
 (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 71744 (* h1 h1) (* h3 h3 h3
 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 56064 (* h1 h1) (* h3 h3 h3 h3) h5 (* h6 
h6 h6) (* j2 j2)) (* 23552 (* h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6 h6) j2) (* 4096
 (* h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6 h6)) (* 24 (* h1 h1) (* h3 h3 h3) (* h4 
h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 304 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4
 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 1488 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4 h4) h5
 (* j2 j2 j2 j2 j2)) (* 3648 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 
j2 j2)) (* 4952 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2)) (* 3792 
(* h1 h1) (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2)) (* 1536 (* h1 h1) (* h3 h3 
h3) (* h4 h4 h4 h4) h5 j2) (* 256 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4 h4) h5) (* 
288 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
3288 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 
14616 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 33016
 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 41704 (* h1 
h1) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 29904 (* h1 h1) (* h3 
h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 11392 (* h1 h1) (* h3 h3 h3) (* h4 
h4 h4) (* h5 h5) j2) (* 1792 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5)) (* 
12 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 344
 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2984 (* 
h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 12064 (* h1 h1)
 (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 26412 (* h1 h1) (* h3 h3
 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 33320 (* h1 h1) (* h3 h3 h3) (* h4 
h4 h4) h5 h6 (* j2 j2 j2)) (* 24256 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 h6 
(* j2 j2)) (* 9472 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 h6 j2) (* 1536 (* h1 
h1) (* h3 h3 h3) (* h4 h4 h4) h5 h6) (* 288 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* 
h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 3552 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* 
h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 16736 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5
 h5 h5) (* j2 j2 j2 j2 j2)) (* 38944 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5 
h5) (* j2 j2 j2 j2)) (* 49664 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* 
j2 j2 j2)) (* 35456 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 
13312 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) j2) (* 2048 (* h1 h1) (* h3 
h3 h3) (* h4 h4) (* h5 h5 h5)) (* 156 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5)
 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3044 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 21772 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5
 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 78452 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 
h5) h6 (* j2 j2 j2 j2 j2)) (* 158552 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) 
h6 (* j2 j2 j2 j2)) (* 187704 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* 
j2 j2 j2)) (* 129296 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2)) 
(* 48000 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 j2) (* 7424 (* h1 h1) (* 
h3 h3 h3) (* h4 h4) (* h5 h5) h6) (* 72 (* h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1320 (* h1 h1) (* h3 h3 h3) (* h4 h4) h5 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 9248 (* h1 h1) (* h3 h3 h3) (* h4 h4) h5 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 32912 (* h1 h1) (* h3 h3 h3) (* h4 h4) h5 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 66376 (* h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* h6
 h6) (* j2 j2 j2 j2)) (* 79176 (* h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* 
j2 j2 j2)) (* 55376 (* h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 
20992 (* h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) j2) (* 3328 (* h1 h1) (* h3 
h3 h3) (* h4 h4) h5 (* h6 h6)) (* 432 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2)) (* 3456 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 
j2 j2 j2 j2)) (* 9648 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2))
 (* 13088 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2)) (* 9408 (* h1 
h1) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2)) (* 3456 (* h1 h1) (* h3 h3 h3) h4
 (* h5 h5 h5 h5) j2) (* 512 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5 h5)) (* 144 
(* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2568 
(* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 18712 (* 
h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 69144 (* h1 h1)
 (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 141208 (* h1 h1) (* h3 
h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 166528 (* h1 h1) (* h3 h3 h3) h4 
(* h5 h5 h5) h6 (* j2 j2 j2)) (* 112992 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) 
h6 (* j2 j2)) (* 40960 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) h6 j2) (* 6144 (* 
h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) h6) (* 6 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 448 (* h1 h1) (* h3 h3 h3) h4 (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6128 (* h1 h1) (* h3 h3 h3) h4 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 36732 (* h1 h1) (* h3 h3 h3) h4
 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 119354 (* h1 h1) (* h3 h3 h3) h4 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 226660 (* h1 h1) (* h3 h3 h3) h4 (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 258224 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5) 
(* h6 h6) (* j2 j2 j2)) (* 173632 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) 
(* j2 j2)) (* 63488 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) j2) (* 9728 
(* h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6)) (* 108 (* h1 h1) (* h3 h3 h3) h4 
h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1704 (* h1 h1) (* h3 h3 h3) h4 
h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 10760 (* h1 h1) (* h3 h3 h3) h4 h5 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 35584 (* h1 h1) (* h3 h3 h3) h4 h5 (* h6 
h6 h6) (* j2 j2 j2 j2 j2)) (* 68108 (* h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6 h6) 
(* j2 j2 j2 j2)) (* 78200 (* h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2)
) (* 53152 (* h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2)) (* 19712 (* h1 
h1) (* h3 h3 h3) h4 h5 (* h6 h6 h6) j2) (* 3072 (* h1 h1) (* h3 h3 h3) h4 h5 (* 
h6 h6 h6)) (* 216 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2
 j2)) (* 2592 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 11736 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 25840 
(* h1 h1) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 30880 (* h1 h1) 
(* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 20544 (* h1 h1) (* h3 h3 h3) 
(* h5 h5 h5 h5) h6 (* j2 j2)) (* 7168 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5 h5) h6 
j2) (* 1024 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5 h5) h6) (* 108 (* h1 h1) (* h3 h3
 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2052 (* h1 h1) (* h3
 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 14580 (* h1 h1) (* 
h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 51644 (* h1 h1) (* h3
 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 101712 (* h1 h1) (* h3 h3 
h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 116656 (* h1 h1) (* h3 h3 h3) (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 77504 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5) 
(* h6 h6) (* j2 j2)) (* 27648 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) j2) 
(* 4096 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6)) (* 6 (* h1 h1) (* h3 h3 
h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 292 (* h1 h1) (* 
h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3372 (* h1 h1) 
(* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 18248 (* h1 h1)
 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 55518 (* h1 h1) 
(* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 101124 (* h1 h1) (* 
h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 112224 (* h1 h1) (* h3 h3 
h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 74240 (* h1 h1) (* h3 h3 h3) (* h5 
h5) (* h6 h6 h6) (* j2 j2)) (* 26880 (* h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6 
h6) j2) (* 4096 (* h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6)) (* 48 (* h1 h1) 
(* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 704 (* h1 h1) 
(* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4192 (* h1 h1) (* 
h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 13248 (* h1 h1) (* h3 h3 
h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 24496 (* h1 h1) (* h3 h3 h3) h5 
(* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 27392 (* h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6 
h6) (* j2 j2 j2)) (* 18240 (* h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2)) 
(* 6656 (* h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6 h6) j2) (* 1024 (* h1 h1) (* h3 h3
 h3) h5 (* h6 h6 h6 h6)) (* 48 (* h1 h1) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 464 (* h1 h1) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* 
j2 j2 j2 j2 j2 j2)) (* 1728 (* h1 h1) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 
j2 j2 j2 j2)) (* 3360 (* h1 h1) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 
j2)) (* 3760 (* h1 h1) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 2448
 (* h1 h1) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2)) (* 864 (* h1 h1) (* h3
 h3) (* h4 h4 h4 h4) (* h5 h5) j2) (* 128 (* h1 h1) (* h3 h3) (* h4 h4 h4 h4) 
(* h5 h5)) (* 288 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 
j2 j2 j2)) (* 2424 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 
j2 j2)) (* 8208 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)
) (* 14800 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 
15520 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 9528 (* h1 
h1) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2)) (* 3184 (* h1 h1) (* h3 h3) 
(* h4 h4 h4) (* h5 h5 h5) j2) (* 448 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5 
h5)) (* 36 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2
 j2)) (* 684 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2)) (* 4352 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)
) (* 13528 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
23780 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 24956 
(* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 15544 (* h1 h1) 
(* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 5312 (* h1 h1) (* h3 h3) (* h4
 h4 h4) (* h5 h5) h6 j2) (* 768 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6) 
(* 144 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 1344 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 
4768 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 8768 
(* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 9232 (* h1 h1)
 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 5632 (* h1 h1) (* h3 h3) 
(* h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 1856 (* h1 h1) (* h3 h3) (* h4 h4) (* h5
 h5 h5 h5) j2) (* 256 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5)) (* 168 (* 
h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2572 
(* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 14576
 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 41912 
(* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 69304 (* h1
 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 69004 (* h1 h1) (* 
h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 40976 (* h1 h1) (* h3 h3) (* 
h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 13392 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 
h5 h5) h6 j2) (* 1856 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6) (* 6 (* h1 
h1) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
226 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 2560 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 13044 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 35974 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2)) (* 58746 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2)) (* 58676 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2))
 (* 35280 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 11744 
(* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) j2) (* 1664 (* h1 h1) (* h3 h3
) (* h4 h4) (* h5 h5) (* h6 h6)) (* 72 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) h6
 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1104 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 6416 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2)) (* 18688 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 
j2 j2 j2)) (* 30920 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) 
(* 30512 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 17824 (* h1 
h1) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 5696 (* h1 h1) (* h3 h3) h4 
(* h5 h5 h5 h5) h6 j2) (* 768 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) h6) (* 12 
(* h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 464 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 4876 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 23496 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 62052 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
97632 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 94244 
(* h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 54856 (* h1 h1) 
(* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 17696 (* h1 h1) (* h3 h3) h4 
(* h5 h5 h5) (* h6 h6) j2) (* 2432 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6)
) (* 12 (* h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
 j2)) (* 344 (* h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 3260 (* h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 14888 (* h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2
 j2)) (* 38276 (* h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2))
 (* 59592 (* h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 
57524 (* h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 33720 (* h1
 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 11008 (* h1 h1) (* h3 h3)
 h4 (* h5 h5) (* h6 h6 h6) j2) (* 1536 (* h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6
 h6)) (* 72 (* h1 h1) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 960 (* h1 h1) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 5072 (* h1 h1) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 13920 (* h1 h1) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 22152 (* h1 h1) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 21280
 (* h1 h1) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 12192 (* h1 h1) 
(* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 3840 (* h1 h1) (* h3 h3) (* h5
 h5 h5 h5) (* h6 h6) j2) (* 512 (* h1 h1) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6)) 
(* 12 (* h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 296 (* h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 2592 (* h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 11344 (* h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2
 j2)) (* 28348 (* h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2))
 (* 43128 (* h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 
40760 (* h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 23408 (* h1
 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 7488 (* h1 h1) (* h3 h3) 
(* h5 h5 h5) (* h6 h6 h6) j2) (* 1024 (* h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 
h6)) (* 6 (* h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 154 (* h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 1336 (* h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 5732 (* h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 14102 (* h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2
)) (* 21266 (* h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 
20044 (* h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 11536 (* h1
 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 3712 (* h1 h1) (* h3 h3) 
(* h5 h5) (* h6 h6 h6 h6) j2) (* 512 (* h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6 
h6)) (* 24 (* h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 160 (* h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 456 
(* h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 720 (* h1 h1) 
h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 680 (* h1 h1) h3 (* h4 h4 h4
 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 384 (* h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5 h5)
 (* j2 j2)) (* 120 (* h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5 h5) j2) (* 16 (* h1 h1)
 h3 (* h4 h4 h4 h4) (* h5 h5 h5)) (* 24 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5 h5
) (* j2 j2 j2 j2 j2 j2 j2)) (* 160 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* 
j2 j2 j2 j2 j2 j2)) (* 456 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2
 j2 j2)) (* 720 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 
680 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 384 (* h1 h1) h3 
(* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 120 (* h1 h1) h3 (* h4 h4 h4) (* h5 
h5 h5 h5) j2) (* 16 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5 h5)) (* 24 (* h1 h1) 
h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 304 (* h1 h1) h3
 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1416 (* h1 h1) h3 (* 
h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 3456 (* h1 h1) h3 (* h4 h4 
h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 5000 (* h1 h1) h3 (* h4 h4 h4) (* h5 
h5 h5) h6 (* j2 j2 j2 j2)) (* 4464 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* 
j2 j2 j2)) (* 2424 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 736 
(* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) h6 j2) (* 96 (* h1 h1) h3 (* h4 h4 h4) 
(* h5 h5 h5) h6) (* 24 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 280 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2
 j2 j2)) (* 1256 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)
) (* 3000 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 4280 
(* h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 3784 (* h1 h1) h3 
(* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 2040 (* h1 h1) h3 (* h4 h4) (* h5 
h5 h5 h5) h6 (* j2 j2)) (* 616 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) h6 j2) (* 
80 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) h6) (* 6 (* h1 h1) h3 (* h4 h4) (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 136 (* h1 h1) h3 (* h4 h4) 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1066 (* h1 h1) h3 (* h4 
h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4084 (* h1 h1) h3 (* h4 
h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 8978 (* h1 h1) h3 (* h4 h4)
 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 12176 (* h1 h1) h3 (* h4 h4) (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 10406 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5
) (* h6 h6) (* j2 j2 j2)) (* 5476 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) 
(* j2 j2)) (* 1624 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) j2) (* 208 (* 
h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6)) (* 6 (* h1 h1) h3 h4 (* h5 h5 h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 112 (* h1 h1) h3 h4 (* h5 h5 h5 h5
) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 786 (* h1 h1) h3 h4 (* h5 h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2828 (* h1 h1) h3 h4 (* h5 h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 5978 (* h1 h1) h3 h4 (* h5 h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* 7896 (* h1 h1) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2)) (* 6622 (* h1 h1) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 3436 
(* h1 h1) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 1008 (* h1 h1) h3 h4 (* 
h5 h5 h5 h5) (* h6 h6) j2) (* 128 (* h1 h1) h3 h4 (* h5 h5 h5 h5) (* h6 h6)) (* 
12 (* h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
200 (* h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
1316 (* h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4560
 (* h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 9412 (* h1 
h1) h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 12232 (* h1 h1) h3 h4
 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 10140 (* h1 h1) h3 h4 (* h5 h5 h5
) (* h6 h6 h6) (* j2 j2 j2)) (* 5216 (* h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6 h6) 
(* j2 j2)) (* 1520 (* h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6 h6) j2) (* 192 (* h1 h1
) h3 h4 (* h5 h5 h5) (* h6 h6 h6)) (* 6 (* h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 88 (* h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 530 (* h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 1732 (* h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 3434 (* h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2)) (* 4336 (* h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) 
(* 3518 (* h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 1780 (* h1 h1
) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 512 (* h1 h1) h3 (* h5 h5 h5 h5)
 (* h6 h6 h6) j2) (* 64 (* h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6 h6)) (* 6 (* h1 h1
) h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 88 (* h1 h1
) h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 530 (* h1 h1) 
h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1732 (* h1 h1) h3 
(* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3434 (* h1 h1) h3 (* h5 
h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 4336 (* h1 h1) h3 (* h5 h5 h5) (* 
h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 3518 (* h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6 h6) 
(* j2 j2 j2)) (* 1780 (* h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 
512 (* h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6 h6) j2) (* 64 (* h1 h1) h3 (* h5 h5 h5
) (* h6 h6 h6 h6)) (* 12 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2
)) (* 140 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2)) (* 592 h1 (* h2
 h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2)) (* 1104 h1 (* h2 h2 h2 h2) (* h3 h3 
h3) h4 h5 (* j2 j2)) (* 896 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 j2) (* 256 h1 
(* h2 h2 h2 h2) (* h3 h3 h3) h4 h5) (* 4 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h6 
(* j2 j2 j2 j2 j2)) (* 48 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2))
 (* 212 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2)) (* 424 h1 (* h2 h2 
h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2)) (* 384 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 
h6 j2) (* 128 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h6) (* 36 h1 (* h2 h2 h2 h2) 
(* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 264 h1 (* h2 h2 h2 h2) (* h3 h3 h3) 
(* h5 h5) (* j2 j2 j2)) (* 592 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 
j2)) (* 480 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) j2) (* 128 h1 (* h2 h2 h2 
h2) (* h3 h3 h3) (* h5 h5)) (* 6 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 
j2 j2 j2)) (* 94 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 480 
h1 (* h2 h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2)) (* 1000 h1 (* h2 h2 h2 h2) 
(* h3 h3 h3) h5 h6 (* j2 j2)) (* 864 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h5 h6 j2) 
(* 256 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h5 h6) (* 4 h1 (* h2 h2 h2 h2) (* h3 h3 
h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 48 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h6 h6
) (* j2 j2 j2 j2)) (* 212 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2)
) (* 424 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2)) (* 384 h1 (* h2 h2
 h2 h2) (* h3 h3 h3) (* h6 h6) j2) (* 128 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h6 
h6)) (* 18 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 156 
h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 474 h1 (* h2 h2 h2
 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 648 h1 (* h2 h2 h2 h2) (* h3 h3) 
(* h4 h4) h5 (* j2 j2)) (* 408 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 j2) (* 
96 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5) (* 4 h1 (* h2 h2 h2 h2) (* h3 h3) 
(* h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 36 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h6
 (* j2 j2 j2 j2)) (* 116 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2 j2))
 (* 172 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2)) (* 120 h1 (* h2 h2 
h2 h2) (* h3 h3) (* h4 h4) h6 j2) (* 32 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) 
h6) (* 24 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 208 
h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 632 h1 (* h2 h2 h2
 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 864 h1 (* h2 h2 h2 h2) (* h3 h3) h4
 (* h5 h5) (* j2 j2)) (* 544 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) j2) (* 
128 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5)) (* h1 (* h2 h2 h2 h2) (* h3 h3) 
h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 51 h1 (* h2 h2 h2 h2) (* h3 h3) h4 h5 h6 (* 
j2 j2 j2 j2 j2)) (* 373 h1 (* h2 h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) 
(* 1069 h1 (* h2 h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 1442 h1 (* h2 h2 
h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2)) (* 920 h1 (* h2 h2 h2 h2) (* h3 h3) h4 h5 
h6 j2) (* 224 h1 (* h2 h2 h2 h2) (* h3 h3) h4 h5 h6) (* 8 h1 (* h2 h2 h2 h2) (* 
h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 72 h1 (* h2 h2 h2 h2) (* h3 h3) h4 
(* h6 h6) (* j2 j2 j2 j2)) (* 232 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h6 h6) (* 
j2 j2 j2)) (* 344 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2)) (* 240 h1
 (* h2 h2 h2 h2) (* h3 h3) h4 (* h6 h6) j2) (* 64 h1 (* h2 h2 h2 h2) (* h3 h3) 
h4 (* h6 h6)) (* 36 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2)) 
(* 156 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2)) (* 232 h1 (* h2 
h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2)) (* 144 h1 (* h2 h2 h2 h2) (* h3 h3) 
(* h5 h5 h5) j2) (* 32 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5)) (* 18 h1 (* h2
 h2 h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 180 h1 (* h2 h2 h2 h2) 
(* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 586 h1 (* h2 h2 h2 h2) (* h3 h3) (* 
h5 h5) h6 (* j2 j2 j2)) (* 832 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 
j2)) (* 536 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) h6 j2) (* 128 h1 (* h2 h2 h2 
h2) (* h3 h3) (* h5 h5) h6) (* h1 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 33 h1 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 217 h1 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 595 h1
 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 794 h1 (* h2 h2 h2 h2) 
(* h3 h3) h5 (* h6 h6) (* j2 j2)) (* 512 h1 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 
h6) j2) (* 128 h1 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6)) (* 4 h1 (* h2 h2 h2 h2
) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 36 h1 (* h2 h2 h2 h2) (* h3 h3) 
(* h6 h6 h6) (* j2 j2 j2 j2)) (* 116 h1 (* h2 h2 h2 h2) (* h3 h3) (* h6 h6 h6) 
(* j2 j2 j2)) (* 172 h1 (* h2 h2 h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2)) (* 120
 h1 (* h2 h2 h2 h2) (* h3 h3) (* h6 h6 h6) j2) (* 32 h1 (* h2 h2 h2 h2) (* h3 h3
) (* h6 h6 h6)) (* 18 h1 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 
j2)) (* 102 h1 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 222 h1
 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 234 h1 (* h2 h2 h2 h2) 
h3 (* h4 h4) (* h5 h5) (* j2 j2)) (* 120 h1 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 
h5) j2) (* 24 h1 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5)) (* h1 (* h2 h2 h2 h2) 
h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 14 h1 (* h2 h2 h2 h2) h3 (* h4 h4) 
h5 h6 (* j2 j2 j2 j2 j2)) (* 62 h1 (* h2 h2 h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 
j2 j2)) (* 128 h1 (* h2 h2 h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2)) (* 137 h1 (* 
h2 h2 h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2)) (* 74 h1 (* h2 h2 h2 h2) h3 (* h4 h4)
 h5 h6 j2) (* 16 h1 (* h2 h2 h2 h2) h3 (* h4 h4) h5 h6) (* 12 h1 (* h2 h2 h2 h2)
 h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 68 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5 
h5) (* j2 j2 j2 j2)) (* 148 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2)) 
(* 156 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2)) (* 80 h1 (* h2 h2 h2 h2)
 h3 h4 (* h5 h5 h5) j2) (* 16 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5)) (* 2 h1 (* 
h2 h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 48 h1 (* h2 h2 h2 h2) 
h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 236 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5)
 h6 (* j2 j2 j2 j2)) (* 496 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2)) 
(* 522 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2)) (* 272 h1 (* h2 h2 h2 h2
) h3 h4 (* h5 h5) h6 j2) (* 56 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5) h6) (* 2 h1 
(* h2 h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 28 h1 (* h2 h2 h2 
h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 124 h1 (* h2 h2 h2 h2) h3 h4 h5 
(* h6 h6) (* j2 j2 j2 j2)) (* 256 h1 (* h2 h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2
 j2)) (* 274 h1 (* h2 h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2)) (* 148 h1 (* h2 h2
 h2 h2) h3 h4 h5 (* h6 h6) j2) (* 32 h1 (* h2 h2 h2 h2) h3 h4 h5 (* h6 h6)) (* 
12 h1 (* h2 h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 68 h1 (* h2 h2 
h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 148 h1 (* h2 h2 h2 h2) h3 (* h5 h5
 h5) h6 (* j2 j2 j2)) (* 156 h1 (* h2 h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2)) 
(* 80 h1 (* h2 h2 h2 h2) h3 (* h5 h5 h5) h6 j2) (* 16 h1 (* h2 h2 h2 h2) h3 (* 
h5 h5 h5) h6) (* 2 h1 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 30 h1 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 134 
h1 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 274 h1 (* h2 h2 h2
 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 288 h1 (* h2 h2 h2 h2) h3 (* h5 h5)
 (* h6 h6) (* j2 j2)) (* 152 h1 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6) j2) (* 32
 h1 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6)) (* h1 (* h2 h2 h2 h2) h3 h5 (* h6 h6
 h6) (* j2 j2 j2 j2 j2 j2)) (* 14 h1 (* h2 h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2
 j2 j2 j2)) (* 62 h1 (* h2 h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 128 
h1 (* h2 h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 137 h1 (* h2 h2 h2 h2) h3
 h5 (* h6 h6 h6) (* j2 j2)) (* 74 h1 (* h2 h2 h2 h2) h3 h5 (* h6 h6 h6) j2) (* 
16 h1 (* h2 h2 h2 h2) h3 h5 (* h6 h6 h6)) (* h1 (* h2 h2 h2 h2) (* h4 h4) (* h5 
h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 7 h1 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* 
j2 j2 j2 j2 j2)) (* 20 h1 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)
) (* 30 h1 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 25 h1 (* h2 
h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 11 h1 (* h2 h2 h2 h2) (* h4 h4) 
(* h5 h5) h6 j2) (* 2 h1 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5) h6) (* h1 (* h2 h2 
h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 7 h1 (* h2 h2 h2 h2) h4 (* 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 20 h1 (* h2 h2 h2 h2) h4 (* h5 h5 h5) h6 (* 
j2 j2 j2 j2)) (* 30 h1 (* h2 h2 h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 25 h1
 (* h2 h2 h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2)) (* 11 h1 (* h2 h2 h2 h2) h4 (* h5
 h5 h5) h6 j2) (* 2 h1 (* h2 h2 h2 h2) h4 (* h5 h5 h5) h6) (* 2 h1 (* h2 h2 h2 
h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 14 h1 (* h2 h2 h2 h2) h4 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 40 h1 (* h2 h2 h2 h2) h4 (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2)) (* 60 h1 (* h2 h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2
 j2 j2)) (* 50 h1 (* h2 h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 22 h1 (* 
h2 h2 h2 h2) h4 (* h5 h5) (* h6 h6) j2) (* 4 h1 (* h2 h2 h2 h2) h4 (* h5 h5) (* 
h6 h6)) (* h1 (* h2 h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 7
 h1 (* h2 h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 20 h1 (* h2 h2
 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 30 h1 (* h2 h2 h2 h2) (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2)) (* 25 h1 (* h2 h2 h2 h2) (* h5 h5 h5) (* h6 h6) 
(* j2 j2)) (* 11 h1 (* h2 h2 h2 h2) (* h5 h5 h5) (* h6 h6) j2) (* 2 h1 (* h2 h2 
h2 h2) (* h5 h5 h5) (* h6 h6)) (* h1 (* h2 h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 7 h1 (* h2 h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2)) (* 20 h1 (* h2 h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 30 
h1 (* h2 h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 25 h1 (* h2 h2 h2 h2)
 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 11 h1 (* h2 h2 h2 h2) (* h5 h5) (* h6 h6 
h6) j2) (* 2 h1 (* h2 h2 h2 h2) (* h5 h5) (* h6 h6 h6)) (* 12 h1 (* h2 h2 h2) 
(* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 188 h1 (* h2 h2 h2) (* h3 h3 h3 
h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 1152 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 (* 
j2 j2 j2 j2)) (* 3472 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2)) (* 
5312 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2)) (* 3840 h1 (* h2 h2 h2) 
(* h3 h3 h3 h3) h4 h5 j2) (* 1024 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5) (* 4 h1
 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2)) (* 64 h1 (* h2 h2 h2)
 (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 404 h1 (* h2 h2 h2) (* h3 h3 h3 h3
) h4 h6 (* j2 j2 j2 j2)) (* 1272 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2 
j2)) (* 2080 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2)) (* 1664 h1 (* h2 
h2 h2) (* h3 h3 h3 h3) h4 h6 j2) (* 512 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h6) 
(* 36 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 408 h1 
(* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 1648 h1 (* h2 h2 h2) 
(* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2)) (* 2848 h1 (* h2 h2 h2) (* h3 h3 h3 h3) 
(* h5 h5) (* j2 j2)) (* 2048 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) j2) (* 
512 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5)) (* 6 h1 (* h2 h2 h2) (* h3 h3 h3 
h3) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 118 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h5 h6 
(* j2 j2 j2 j2 j2)) (* 856 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2)
) (* 2920 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2)) (* 4864 h1 (* h2 
h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2)) (* 3712 h1 (* h2 h2 h2) (* h3 h3 h3 h3) 
h5 h6 j2) (* 1024 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h5 h6) (* 4 h1 (* h2 h2 h2) 
(* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 64 h1 (* h2 h2 h2) (* h3 h3 
h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 404 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* 
h6 h6) (* j2 j2 j2 j2)) (* 1272 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 
j2 j2)) (* 2080 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2)) (* 1664 h1 
(* h2 h2 h2) (* h3 h3 h3 h3) (* h6 h6) j2) (* 512 h1 (* h2 h2 h2) (* h3 h3 h3 h3
) (* h6 h6)) (* 36 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 
j2)) (* 504 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 
2708 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 6992 h1 (* h2
 h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 8976 h1 (* h2 h2 h2) (* h3 h3
 h3) (* h4 h4) h5 (* j2 j2)) (* 5504 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 
j2) (* 1280 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5) (* 8 h1 (* h2 h2 h2) (* 
h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 104 h1 (* h2 h2 h2) (* h3 h3 h3
) (* h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 520 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4)
 h6 (* j2 j2 j2 j2)) (* 1272 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 
j2)) (* 1616 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2)) (* 1024 h1 (* 
h2 h2 h2) (* h3 h3 h3) (* h4 h4) h6 j2) (* 256 h1 (* h2 h2 h2) (* h3 h3 h3) (* 
h4 h4) h6) (* 36 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)
) (* 528 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 3084 
h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 8624 h1 (* h2 h2 
h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 11344 h1 (* h2 h2 h2) (* h3 h3 h3
) h4 (* h5 h5) (* j2 j2)) (* 6848 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) j2) 
(* 1536 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5)) (* h1 (* h2 h2 h2) (* h3 h3 
h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 89 h1 (* h2 h2 h2) (* h3 h3 h3) h4 h5 
h6 (* j2 j2 j2 j2 j2 j2)) (* 1141 h1 (* h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2
 j2 j2 j2)) (* 5963 h1 (* h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 
15190 h1 (* h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 19432 h1 (* h2 h2 
h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2)) (* 11968 h1 (* h2 h2 h2) (* h3 h3 h3) h4 h5
 h6 j2) (* 2816 h1 (* h2 h2 h2) (* h3 h3 h3) h4 h5 h6) (* 16 h1 (* h2 h2 h2) (* 
h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 208 h1 (* h2 h2 h2) (* h3 h3 h3
) h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1040 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h6
 h6) (* j2 j2 j2 j2)) (* 2544 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2
 j2)) (* 3232 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2)) (* 2048 h1 
(* h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6) j2) (* 512 h1 (* h2 h2 h2) (* h3 h3 h3) 
h4 (* h6 h6)) (* 72 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2)
) (* 600 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 1712 h1 
(* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2)) (* 2144 h1 (* h2 h2 h2) (* 
h3 h3 h3) (* h5 h5 h5) (* j2 j2)) (* 1216 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 
h5) j2) (* 256 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5)) (* 24 h1 (* h2 h2 h2) 
(* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 424 h1 (* h2 h2 h2) (* h3 h3
 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 2768 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5
 h5) h6 (* j2 j2 j2 j2)) (* 8192 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2
 j2 j2)) (* 11072 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2)) (* 6784 
h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 j2) (* 1536 h1 (* h2 h2 h2) (* h3 h3 
h3) (* h5 h5) h6) (* h1 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2)) (* 53 h1 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 637 h1 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 3255 h1 
(* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 8198 h1 (* h2 h2 h2) 
(* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 10456 h1 (* h2 h2 h2) (* h3 h3 h3) h5
 (* h6 h6) (* j2 j2)) (* 6464 h1 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) j2) (* 
1536 h1 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6)) (* 8 h1 (* h2 h2 h2) (* h3 h3 h3
) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 104 h1 (* h2 h2 h2) (* h3 h3 h3) (* h6 
h6 h6) (* j2 j2 j2 j2 j2)) (* 520 h1 (* h2 h2 h2) (* h3 h3 h3) (* h6 h6 h6) (* 
j2 j2 j2 j2)) (* 1272 h1 (* h2 h2 h2) (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2)) 
(* 1616 h1 (* h2 h2 h2) (* h3 h3 h3) (* h6 h6 h6) (* j2 j2)) (* 1024 h1 (* h2 h2
 h2) (* h3 h3 h3) (* h6 h6 h6) j2) (* 256 h1 (* h2 h2 h2) (* h3 h3 h3) (* h6 h6 
h6)) (* 24 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 
280 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 1208 h1 (* 
h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 2440 h1 (* h2 h2 h2) (* 
h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 2512 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 
h4) h5 (* j2 j2)) (* 1280 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 j2) (* 256 
h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5) (* 4 h1 (* h2 h2 h2) (* h3 h3) (* h4 
h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 40 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h6
 (* j2 j2 j2 j2 j2)) (* 152 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 
j2 j2)) (* 288 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2)) (* 292 h1
 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h6 (* j2 j2)) (* 152 h1 (* h2 h2 h2) (* h3 
h3) (* h4 h4 h4) h6 j2) (* 32 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h6) (* 72 
h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 792 h1 
(* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 3256 h1 (* h2 
h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 6376 h1 (* h2 h2 h2) 
(* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 6432 h1 (* h2 h2 h2) (* h3 h3) 
(* h4 h4) (* h5 h5) (* j2 j2)) (* 3232 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5
 h5) j2) (* 640 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5)) (* 2 h1 (* h2 h2 
h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 110 h1 (* h2 h2 h2) 
(* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 1086 h1 (* h2 h2 h2) (* h3 
h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 4378 h1 (* h2 h2 h2) (* h3 h3) (* h4 
h4) h5 h6 (* j2 j2 j2 j2)) (* 8584 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* 
j2 j2 j2)) (* 8736 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 4448 
h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 j2) (* 896 h1 (* h2 h2 h2) (* h3 h3) 
(* h4 h4) h5 h6) (* 12 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2
 j2 j2 j2)) (* 120 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 456 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 
864 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 876 h1 (* h2 
h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2)) (* 456 h1 (* h2 h2 h2) (* h3 h3)
 (* h4 h4) (* h6 h6) j2) (* 96 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h6 h6)) 
(* 36 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 420 h1
 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 1932 h1 (* h2 h2 
h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 3980 h1 (* h2 h2 h2) (* h3 h3)
 h4 (* h5 h5 h5) (* j2 j2 j2)) (* 4048 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5)
 (* j2 j2)) (* 2000 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) j2) (* 384 h1 (* 
h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5)) (* 3 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5)
 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 174 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 1718 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* 6844 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2))
 (* 13263 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 13358 h1 
(* h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 6736 h1 (* h2 h2 h2) (* h3 
h3) h4 (* h5 h5) h6 j2) (* 1344 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6) (* 4 
h1 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 148 h1 
(* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1332 h1 (* h2 
h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 5132 h1 (* h2 h2 h2) (* 
h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 9848 h1 (* h2 h2 h2) (* h3 h3) h4 h5 
(* h6 h6) (* j2 j2 j2)) (* 9936 h1 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 
j2)) (* 5056 h1 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) j2) (* 1024 h1 (* h2 h2 
h2) (* h3 h3) h4 h5 (* h6 h6)) (* 12 h1 (* h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 120 h1 (* h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2
 j2 j2 j2)) (* 456 h1 (* h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2)) 
(* 864 h1 (* h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2)) (* 876 h1 (* h2 
h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2)) (* 456 h1 (* h2 h2 h2) (* h3 h3) h4 
(* h6 h6 h6) j2) (* 96 h1 (* h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6)) (* 36 h1 (* h2
 h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 192 h1 (* h2 h2 h2) (* 
h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 388 h1 (* h2 h2 h2) (* h3 h3) (* h5 
h5 h5 h5) (* j2 j2 j2)) (* 376 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 
j2)) (* 176 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) j2) (* 32 h1 (* h2 h2 h2) 
(* h3 h3) (* h5 h5 h5 h5)) (* 30 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2
 j2 j2 j2 j2 j2)) (* 386 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2)) (* 1858 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 
3902 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 4008 h1 (* h2 h2
 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2)) (* 1992 h1 (* h2 h2 h2) (* h3 h3) (* 
h5 h5 h5) h6 j2) (* 384 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6) (* 3 h1 (* h2
 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 102 h1 (* h2 
h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 926 h1 (* h2 h2 
h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 3588 h1 (* h2 h2 h2) 
(* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 6887 h1 (* h2 h2 h2) (* h3 h3)
 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 6926 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5) 
(* h6 h6) (* j2 j2)) (* 3504 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) j2) 
(* 704 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6)) (* 2 h1 (* h2 h2 h2) (* h3
 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 62 h1 (* h2 h2 h2) (* h3 h3) 
h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 526 h1 (* h2 h2 h2) (* h3 h3) h5 (* h6
 h6 h6) (* j2 j2 j2 j2 j2)) (* 1962 h1 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) 
(* j2 j2 j2 j2)) (* 3704 h1 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2))
 (* 3712 h1 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 1888 h1 (* h2 
h2 h2) (* h3 h3) h5 (* h6 h6 h6) j2) (* 384 h1 (* h2 h2 h2) (* h3 h3) h5 (* h6 
h6 h6)) (* 4 h1 (* h2 h2 h2) (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 40 h1 (* h2 h2 h2) (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 152 h1 
(* h2 h2 h2) (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 288 h1 (* h2 h2 h2) 
(* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 292 h1 (* h2 h2 h2) (* h3 h3) (* h6 
h6 h6 h6) (* j2 j2)) (* 152 h1 (* h2 h2 h2) (* h3 h3) (* h6 h6 h6 h6) j2) (* 32 
h1 (* h2 h2 h2) (* h3 h3) (* h6 h6 h6 h6)) (* 24 h1 (* h2 h2 h2) h3 (* h4 h4 h4)
 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 208 h1 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 
h5) (* j2 j2 j2 j2 j2)) (* 656 h1 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 
j2 j2 j2)) (* 1024 h1 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 
856 h1 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 368 h1 (* h2 h2 h2) 
h3 (* h4 h4 h4) (* h5 h5) j2) (* 64 h1 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5)) 
(* h1 (* h2 h2 h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 15 h1 (* 
h2 h2 h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 76 h1 (* h2 h2 h2) h3 
(* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 190 h1 (* h2 h2 h2) h3 (* h4 h4 h4) h5
 h6 (* j2 j2 j2 j2)) (* 265 h1 (* h2 h2 h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2)) 
(* 211 h1 (* h2 h2 h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2)) (* 90 h1 (* h2 h2 h2) h3
 (* h4 h4 h4) h5 h6 j2) (* 16 h1 (* h2 h2 h2) h3 (* h4 h4 h4) h5 h6) (* 36 h1 
(* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 288 h1 (* h2 h2
 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 872 h1 (* h2 h2 h2) h3 (* 
h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 1328 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 
h5 h5) (* j2 j2 j2)) (* 1092 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2)
) (* 464 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) j2) (* 80 h1 (* h2 h2 h2) h3 
(* h4 h4) (* h5 h5 h5)) (* 4 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2)) (* 112 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2
 j2 j2)) (* 792 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) 
(* 2352 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 3588 h1 
(* h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 2976 h1 (* h2 h2 h2) h3 
(* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 1280 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5)
 h6 j2) (* 224 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6) (* 3 h1 (* h2 h2 h2) 
h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 45 h1 (* h2 h2 h2) h3 (* 
h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 228 h1 (* h2 h2 h2) h3 (* h4 h4) 
h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 570 h1 (* h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6
) (* j2 j2 j2 j2)) (* 795 h1 (* h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2)
) (* 633 h1 (* h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 270 h1 (* h2 h2
 h2) h3 (* h4 h4) h5 (* h6 h6) j2) (* 48 h1 (* h2 h2 h2) h3 (* h4 h4) h5 (* h6 
h6)) (* 12 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 80 h1
 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 216 h1 (* h2 h2 h2) 
h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 304 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5 
h5) (* j2 j2 j2)) (* 236 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2)) (* 96 
h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) j2) (* 16 h1 (* h2 h2 h2) h3 h4 (* h5 h5 
h5 h5)) (* 3 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
97 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 668 h1 (* h2 
h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 1938 h1 (* h2 h2 h2) h3 h4 
(* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 2907 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5) h6 
(* j2 j2 j2)) (* 2381 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2)) (* 1014 
h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5) h6 j2) (* 176 h1 (* h2 h2 h2) h3 h4 (* h5 h5 
h5) h6) (* 8 h1 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2))
 (* 152 h1 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 960 
h1 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2736 h1 (* h2 
h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 4104 h1 (* h2 h2 h2) h3 h4 
(* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 3384 h1 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 
h6) (* j2 j2)) (* 1456 h1 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) j2) (* 256 h1 
(* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6)) (* 3 h1 (* h2 h2 h2) h3 h4 h5 (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 45 h1 (* h2 h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 228 h1 (* h2 h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)
) (* 570 h1 (* h2 h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 795 h1 (* h2 
h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 633 h1 (* h2 h2 h2) h3 h4 h5 (* h6
 h6 h6) (* j2 j2)) (* 270 h1 (* h2 h2 h2) h3 h4 h5 (* h6 h6 h6) j2) (* 48 h1 (* 
h2 h2 h2) h3 h4 h5 (* h6 h6 h6)) (* 12 h1 (* h2 h2 h2) h3 (* h5 h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2)) (* 80 h1 (* h2 h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 
j2)) (* 216 h1 (* h2 h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 304 h1 (* 
h2 h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 236 h1 (* h2 h2 h2) h3 (* h5 h5
 h5 h5) h6 (* j2 j2)) (* 96 h1 (* h2 h2 h2) h3 (* h5 h5 h5 h5) h6 j2) (* 16 h1 
(* h2 h2 h2) h3 (* h5 h5 h5 h5) h6) (* 3 h1 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 61 h1 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 380 h1 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2
 j2 j2 j2)) (* 1066 h1 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) 
(* 1579 h1 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 1289 h1 (* h2
 h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 550 h1 (* h2 h2 h2) h3 (* h5 h5 
h5) (* h6 h6) j2) (* 96 h1 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6)) (* 4 h1 (* h2
 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 64 h1 (* h2 h2 h2
) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 376 h1 (* h2 h2 h2) h3 (* 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1040 h1 (* h2 h2 h2) h3 (* h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2)) (* 1540 h1 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* 
j2 j2 j2)) (* 1264 h1 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 544 
h1 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) j2) (* 96 h1 (* h2 h2 h2) h3 (* h5 h5)
 (* h6 h6 h6)) (* h1 (* h2 h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 15 h1 (* h2 h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 76 h1 
(* h2 h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 190 h1 (* h2 h2 h2) h3
 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 265 h1 (* h2 h2 h2) h3 h5 (* h6 h6 h6 h6
) (* j2 j2 j2)) (* 211 h1 (* h2 h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2)) (* 90 h1
 (* h2 h2 h2) h3 h5 (* h6 h6 h6 h6) j2) (* 16 h1 (* h2 h2 h2) h3 h5 (* h6 h6 h6 
h6)) (* h1 (* h2 h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 8
 h1 (* h2 h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 27 h1 (* h2
 h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 50 h1 (* h2 h2 h2) (* 
h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 55 h1 (* h2 h2 h2) (* h4 h4 h4) (* h5
 h5) h6 (* j2 j2 j2)) (* 36 h1 (* h2 h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2))
 (* 13 h1 (* h2 h2 h2) (* h4 h4 h4) (* h5 h5) h6 j2) (* 2 h1 (* h2 h2 h2) (* h4 
h4 h4) (* h5 h5) h6) (* 2 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2)) (* 16 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2)) (* 54 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 100 
h1 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 110 h1 (* h2 h2 h2
) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 72 h1 (* h2 h2 h2) (* h4 h4) (* h5 
h5 h5) h6 (* j2 j2)) (* 26 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5) h6 j2) (* 4 h1
 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5) h6) (* 3 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5
) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 24 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 81 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5) (* h6
 h6) (* j2 j2 j2 j2 j2)) (* 150 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2)) (* 165 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 
j2)) (* 108 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 39 h1 
(* h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) j2) (* 6 h1 (* h2 h2 h2) (* h4 h4) 
(* h5 h5) (* h6 h6)) (* h1 (* h2 h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 8 h1 (* h2 h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 27 
h1 (* h2 h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 50 h1 (* h2 h2 h2) 
h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 55 h1 (* h2 h2 h2) h4 (* h5 h5 h5 h5) 
h6 (* j2 j2 j2)) (* 36 h1 (* h2 h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 13 h1
 (* h2 h2 h2) h4 (* h5 h5 h5 h5) h6 j2) (* 2 h1 (* h2 h2 h2) h4 (* h5 h5 h5 h5) 
h6) (* 4 h1 (* h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
32 h1 (* h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 108 h1 
(* h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 200 h1 (* h2 h2 h2
) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 220 h1 (* h2 h2 h2) h4 (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2)) (* 144 h1 (* h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* 
j2 j2)) (* 52 h1 (* h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6) j2) (* 8 h1 (* h2 h2 h2)
 h4 (* h5 h5 h5) (* h6 h6)) (* 3 h1 (* h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2 j2)) (* 24 h1 (* h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2
 j2 j2 j2)) (* 81 h1 (* h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 150 h1 (* h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 165 h1 (* 
h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 108 h1 (* h2 h2 h2) h4 (* 
h5 h5) (* h6 h6 h6) (* j2 j2)) (* 39 h1 (* h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6) 
j2) (* 6 h1 (* h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6)) (* h1 (* h2 h2 h2) (* h5 h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 8 h1 (* h2 h2 h2) (* h5 h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 27 h1 (* h2 h2 h2) (* h5 h5 h5 h5) (* h6 h6)
 (* j2 j2 j2 j2 j2)) (* 50 h1 (* h2 h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2
 j2)) (* 55 h1 (* h2 h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 36 h1 (* 
h2 h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 13 h1 (* h2 h2 h2) (* h5 h5 h5
 h5) (* h6 h6) j2) (* 2 h1 (* h2 h2 h2) (* h5 h5 h5 h5) (* h6 h6)) (* 2 h1 (* h2
 h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 16 h1 (* h2 h2 h2
) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 54 h1 (* h2 h2 h2) (* h5 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 100 h1 (* h2 h2 h2) (* h5 h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2)) (* 110 h1 (* h2 h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* 
j2 j2 j2)) (* 72 h1 (* h2 h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 26 h1 
(* h2 h2 h2) (* h5 h5 h5) (* h6 h6 h6) j2) (* 4 h1 (* h2 h2 h2) (* h5 h5 h5) (* 
h6 h6 h6)) (* h1 (* h2 h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 8 h1 (* h2 h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 27 h1
 (* h2 h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 50 h1 (* h2 h2 h2
) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 55 h1 (* h2 h2 h2) (* h5 h5) (* 
h6 h6 h6 h6) (* j2 j2 j2)) (* 36 h1 (* h2 h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2
 j2)) (* 13 h1 (* h2 h2 h2) (* h5 h5) (* h6 h6 h6 h6) j2) (* 2 h1 (* h2 h2 h2) 
(* h5 h5) (* h6 h6 h6 h6)) (* 18 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2
 j2 j2 j2 j2 j2 j2)) (* 336 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 
j2 j2 j2 j2)) (* 2538 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 
j2)) (* 9900 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 21120
 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 24192 h1 (* h2 h2) 
(* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2)) (* 13824 h1 (* h2 h2) (* h3 h3 h3 h3) 
(* h4 h4) h5 j2) (* 3072 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5) (* 4 h1 (* 
h2 h2) (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 68 h1 (* h2 h2)
 (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 468 h1 (* h2 h2) (* h3 
h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 1676 h1 (* h2 h2) (* h3 h3 h3 h3) 
(* h4 h4) h6 (* j2 j2 j2 j2)) (* 3352 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h6 
(* j2 j2 j2)) (* 3744 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2)) (* 
2176 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h6 j2) (* 512 h1 (* h2 h2) (* h3 h3 
h3 h3) (* h4 h4) h6) (* 144 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 
j2 j2 j2 j2)) (* 1992 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 
j2)) (* 10456 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 
25856 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 30816 h1 (* h2 
h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2)) (* 17152 h1 (* h2 h2) (* h3 h3 h3 h3
) h4 (* h5 h5) j2) (* 3584 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5)) (* 30 h1 
(* h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 632 h1 (* h2 h2)
 (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 5142 h1 (* h2 h2) (* h3 h3 
h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 20892 h1 (* h2 h2) (* h3 h3 h3 h3) h4 h5 
h6 (* j2 j2 j2 j2)) (* 45376 h1 (* h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2))
 (* 52320 h1 (* h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2)) (* 29952 h1 (* h2 h2)
 (* h3 h3 h3 h3) h4 h5 h6 j2) (* 6656 h1 (* h2 h2) (* h3 h3 h3 h3) h4 h5 h6) (* 
8 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 136 h1 
(* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 936 h1 (* h2 h2
) (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 3352 h1 (* h2 h2) (* h3 h3
 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 6704 h1 (* h2 h2) (* h3 h3 h3 h3) h4 
(* h6 h6) (* j2 j2 j2)) (* 7488 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 
j2)) (* 4352 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6) j2) (* 1024 h1 (* h2 h2) 
(* h3 h3 h3 h3) h4 (* h6 h6)) (* 216 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) 
(* j2 j2 j2 j2 j2)) (* 1728 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 
j2 j2)) (* 4608 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2)) (* 5248 
h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2)) (* 2688 h1 (* h2 h2) (* h3 
h3 h3 h3) (* h5 h5 h5) j2) (* 512 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5)) (* 
108 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 1692 h1 
(* h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 9600 h1 (* h2 h2) 
(* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 24784 h1 (* h2 h2) (* h3 h3 h3 
h3) (* h5 h5) h6 (* j2 j2 j2)) (* 30208 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) 
h6 (* j2 j2)) (* 17024 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 j2) (* 3584 h1 
(* h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6) (* 12 h1 (* h2 h2) (* h3 h3 h3 h3) h5 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 296 h1 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6
 h6) (* j2 j2 j2 j2 j2 j2)) (* 2604 h1 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* 10992 h1 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 
j2 j2)) (* 24256 h1 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 
28128 h1 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2)) (* 16128 h1 (* h2 h2)
 (* h3 h3 h3 h3) h5 (* h6 h6) j2) (* 3584 h1 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 
h6)) (* 4 h1 (* h2 h2) (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 68 h1 (* h2 h2) (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 468 h1
 (* h2 h2) (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1676 h1 (* h2 h2)
 (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 3352 h1 (* h2 h2) (* h3 h3 h3 
h3) (* h6 h6 h6) (* j2 j2 j2)) (* 3744 h1 (* h2 h2) (* h3 h3 h3 h3) (* h6 h6 h6)
 (* j2 j2)) (* 2176 h1 (* h2 h2) (* h3 h3 h3 h3) (* h6 h6 h6) j2) (* 512 h1 (* 
h2 h2) (* h3 h3 h3 h3) (* h6 h6 h6)) (* 24 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4
) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 400 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 
(* j2 j2 j2 j2 j2 j2)) (* 2608 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 
j2 j2 j2 j2)) (* 8480 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2))
 (* 14712 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 13840 h1 
(* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2)) (* 6656 h1 (* h2 h2) (* h3 h3 
h3) (* h4 h4 h4) h5 j2) (* 1280 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5) (* 4 
h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 56 h1 (* 
h2 h2) (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 312 h1 (* h2 h2) 
(* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 896 h1 (* h2 h2) (* h3 h3 h3
) (* h4 h4 h4) h6 (* j2 j2 j2 j2)) (* 1444 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4
) h6 (* j2 j2 j2)) (* 1320 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2)) 
(* 640 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h6 j2) (* 128 h1 (* h2 h2) (* h3 
h3 h3) (* h4 h4 h4) h6) (* 54 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 954 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* 
j2 j2 j2 j2 j2 j2)) (* 6462 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 
j2 j2 j2 j2)) (* 21414 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2
 j2)) (* 37164 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 
34560 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 16320 h1 (* h2
 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) j2) (* 3072 h1 (* h2 h2) (* h3 h3 h3) (* 
h4 h4) (* h5 h5)) (* h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 102 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 1514 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2))
 (* 9388 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 29621 
h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 50518 h1 (* h2 h2)
 (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 47112 h1 (* h2 h2) (* h3 h3 h3) 
(* h4 h4) h5 h6 (* j2 j2)) (* 22592 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 j2
) (* 4352 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6) (* 12 h1 (* h2 h2) (* h3 h3
 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 168 h1 (* h2 h2) (* h3 h3 
h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 936 h1 (* h2 h2) (* h3 h3 h3) 
(* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2688 h1 (* h2 h2) (* h3 h3 h3) (* h4 
h4) (* h6 h6) (* j2 j2 j2 j2)) (* 4332 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6
 h6) (* j2 j2 j2)) (* 3960 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 
j2)) (* 1920 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6) j2) (* 384 h1 (* h2 
h2) (* h3 h3 h3) (* h4 h4) (* h6 h6)) (* 288 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 
h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 3120 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) 
(* j2 j2 j2 j2 j2)) (* 12416 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 
j2 j2)) (* 22960 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2)) (* 
21504 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2)) (* 9920 h1 (* h2 h2) 
(* h3 h3 h3) h4 (* h5 h5 h5) j2) (* 1792 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 
h5)) (* 102 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 1946 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
13378 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 44438 h1 
(* h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 77168 h1 (* h2 h2) 
(* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 71816 h1 (* h2 h2) (* h3 h3 h3) h4
 (* h5 h5) h6 (* j2 j2)) (* 33952 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 j2) 
(* 6400 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6) (* 2 h1 (* h2 h2) (* h3 h3 h3
) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 132 h1 (* h2 h2) (* h3 h3 h3) 
h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1828 h1 (* h2 h2) (* h3 h3 h3) h4 
h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 10952 h1 (* h2 h2) (* h3 h3 h3) h4 h5 (* 
h6 h6) (* j2 j2 j2 j2 j2)) (* 33802 h1 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) 
(* j2 j2 j2 j2)) (* 56900 h1 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)
) (* 52704 h1 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 25216 h1 (* 
h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) j2) (* 4864 h1 (* h2 h2) (* h3 h3 h3) h4 h5 
(* h6 h6)) (* 12 h1 (* h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 168 h1 (* h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
936 h1 (* h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2688 h1 (* 
h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 4332 h1 (* h2 h2) (* h3 
h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2)) (* 3960 h1 (* h2 h2) (* h3 h3 h3) h4 (* h6 
h6 h6) (* j2 j2)) (* 1920 h1 (* h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6) j2) (* 384 
h1 (* h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6)) (* 216 h1 (* h2 h2) (* h3 h3 h3) (* 
h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 1080 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 
h5) (* j2 j2 j2 j2)) (* 2016 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 
j2)) (* 1792 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2)) (* 768 h1 (* 
h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) j2) (* 128 h1 (* h2 h2) (* h3 h3 h3) (* h5 
h5 h5 h5)) (* 252 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2
)) (* 2928 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
12028 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 22584 h1 (* 
h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 21328 h1 (* h2 h2) (* h3 h3
 h3) (* h5 h5 h5) h6 (* j2 j2)) (* 9888 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) 
h6 j2) (* 1792 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6) (* 48 h1 (* h2 h2) (* 
h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 992 h1 (* h2 h2) (* 
h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6916 h1 (* h2 h2) (* h3 
h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 23024 h1 (* h2 h2) (* h3 h3 h3
) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 40004 h1 (* h2 h2) (* h3 h3 h3) (* h5 
h5) (* h6 h6) (* j2 j2 j2)) (* 37256 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 
h6) (* j2 j2)) (* 17632 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) j2) (* 
3328 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6)) (* h1 (* h2 h2) (* h3 h3 h3)
 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 54 h1 (* h2 h2) (* h3 h3 h3) h5
 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 714 h1 (* h2 h2) (* h3 h3 h3) h5 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4172 h1 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 
h6) (* j2 j2 j2 j2 j2)) (* 12661 h1 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2
 j2 j2 j2)) (* 21094 h1 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 
19432 h1 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 9280 h1 (* h2 h2) 
(* h3 h3 h3) h5 (* h6 h6 h6) j2) (* 1792 h1 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 
h6)) (* 4 h1 (* h2 h2) (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 56 h1 (* h2 h2) (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 312 h1
 (* h2 h2) (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 896 h1 (* h2 h2) 
(* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 1444 h1 (* h2 h2) (* h3 h3 h3) 
(* h6 h6 h6 h6) (* j2 j2 j2)) (* 1320 h1 (* h2 h2) (* h3 h3 h3) (* h6 h6 h6 h6) 
(* j2 j2)) (* 640 h1 (* h2 h2) (* h3 h3 h3) (* h6 h6 h6 h6) j2) (* 128 h1 (* h2 
h2) (* h3 h3 h3) (* h6 h6 h6 h6)) (* 36 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) 
h5 (* j2 j2 j2 j2 j2 j2)) (* 312 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2
 j2 j2 j2 j2)) (* 984 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2))
 (* 1536 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2)) (* 1284 h1 (* 
h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2)) (* 552 h1 (* h2 h2) (* h3 h3) (* 
h4 h4 h4 h4) h5 j2) (* 96 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5) (* 48 h1 
(* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 656 h1 
(* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 3392 h1 (* 
h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 8608 h1 (* h2 h2)
 (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 11952 h1 (* h2 h2) (* h3 
h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 9296 h1 (* h2 h2) (* h3 h3) (* h4 h4
 h4) (* h5 h5) (* j2 j2)) (* 3808 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) 
j2) (* 640 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5)) (* h1 (* h2 h2) (* h3 
h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 29 h1 (* h2 h2) (* h3 h3)
 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 400 h1 (* h2 h2) (* h3 h3) (* 
h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 2258 h1 (* h2 h2) (* h3 h3) (* h4 h4 
h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 6089 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 
(* j2 j2 j2 j2)) (* 8817 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2))
 (* 7078 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2)) (* 2976 h1 (* h2 
h2) (* h3 h3) (* h4 h4 h4) h5 h6 j2) (* 512 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) 
h5 h6) (* 54 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 
j2)) (* 792 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2))
 (* 4248 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 
10884 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 15042 h1
 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 11556 h1 (* h2 h2) 
(* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 4656 h1 (* h2 h2) (* h3 h3) (* h4
 h4) (* h5 h5 h5) j2) (* 768 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5)) (* 3
 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
201 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
2388 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
11714 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 29003
 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 39765 h1 (* 
h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 30734 h1 (* h2 h2) (* 
h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 12560 h1 (* h2 h2) (* h3 h3) (* h4 
h4) (* h5 h5) h6 j2) (* 2112 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6) (* 3
 h1 (* h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
87 h1 (* h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
984 h1 (* h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4902
 h1 (* h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 12363 h1 
(* h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 17235 h1 (* h2 h2
) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 13530 h1 (* h2 h2) (* h3 h3)
 (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 5616 h1 (* h2 h2) (* h3 h3) (* h4 h4) h5 
(* h6 h6) j2) (* 960 h1 (* h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6)) (* 144 h1 
(* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1128 h1 (* h2 
h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 3256 h1 (* h2 h2) (* h3 
h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 4664 h1 (* h2 h2) (* h3 h3) h4 (* h5 
h5 h5 h5) (* j2 j2 j2)) (* 3576 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 
j2)) (* 1408 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) j2) (* 224 h1 (* h2 h2) 
(* h3 h3) h4 (* h5 h5 h5 h5)) (* 114 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 1672 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2)) (* 8912 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2)) (* 22740 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) 
(* 31358 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 24068 h1 (* 
h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2)) (* 9696 h1 (* h2 h2) (* h3 h3) h4
 (* h5 h5 h5) h6 j2) (* 1600 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6) (* 6 h1 
(* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 258 
h1 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2808 
h1 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 13252 h1
 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 32182 h1 (* 
h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 43674 h1 (* h2 h2) 
(* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 33580 h1 (* h2 h2) (* h3 h3) 
h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 13696 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5) 
(* h6 h6) j2) (* 2304 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6)) (* 3 h1 (* 
h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 87 h1 (* h2 
h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 912 h1 (* h2 h2) 
(* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4278 h1 (* h2 h2) (* h3 
h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 10395 h1 (* h2 h2) (* h3 h3) h4 h5
 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 14163 h1 (* h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6
) (* j2 j2 j2)) (* 10962 h1 (* h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2)) 
(* 4512 h1 (* h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) j2) (* 768 h1 (* h2 h2) (* h3 
h3) h4 h5 (* h6 h6 h6)) (* 144 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2)) (* 1128 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 
j2 j2)) (* 3256 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 
4664 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 3576 h1 (* h2 h2
) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 1408 h1 (* h2 h2) (* h3 h3) (* h5 
h5 h5 h5) h6 j2) (* 224 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6) (* 60 h1 (* 
h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 880 h1 (* 
h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4664 h1 (* h2 
h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 11856 h1 (* h2 h2) 
(* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 16316 h1 (* h2 h2) (* h3 h3
) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 12512 h1 (* h2 h2) (* h3 h3) (* h5 h5 
h5) (* h6 h6) (* j2 j2)) (* 5040 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) 
j2) (* 832 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6)) (* 3 h1 (* h2 h2) (* 
h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 105 h1 (* h2 h2) 
(* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1076 h1 (* h2 h2) 
(* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4930 h1 (* h2 h2) (* 
h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 11787 h1 (* h2 h2) (* h3 h3
) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 15861 h1 (* h2 h2) (* h3 h3) (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2)) (* 12142 h1 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 
h6 h6) (* j2 j2)) (* 4944 h1 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) j2) (* 
832 h1 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6)) (* h1 (* h2 h2) (* h3 h3) h5 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 29 h1 (* h2 h2) (* h3 h3) h5 (* 
h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 292 h1 (* h2 h2) (* h3 h3) h5 (* h6 h6
 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1322 h1 (* h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6)
 (* j2 j2 j2 j2 j2)) (* 3137 h1 (* h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 
j2 j2)) (* 4209 h1 (* h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 3226 
h1 (* h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2)) (* 1320 h1 (* h2 h2) (* h3 
h3) h5 (* h6 h6 h6 h6) j2) (* 224 h1 (* h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6)) (* 
36 h1 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 204 h1 
(* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 480 h1 (* h2 h2) 
h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 600 h1 (* h2 h2) h3 (* h4 h4 h4
 h4) (* h5 h5) (* j2 j2 j2)) (* 420 h1 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) 
(* j2 j2)) (* 156 h1 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) j2) (* 24 h1 (* h2 
h2) h3 (* h4 h4 h4 h4) (* h5 h5)) (* 24 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5
) (* j2 j2 j2 j2 j2 j2 j2)) (* 256 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) (* 
j2 j2 j2 j2 j2 j2)) (* 1000 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 
j2 j2 j2)) (* 2000 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) 
(* 2280 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 1504 h1 (* h2
 h2) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2)) (* 536 h1 (* h2 h2) h3 (* h4 h4 h4)
 (* h5 h5 h5) j2) (* 80 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5)) (* 2 h1 (* h2
 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 34 h1 (* h2 h2
) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 340 h1 (* h2 h2) h3 
(* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 1388 h1 (* h2 h2) h3 (* h4 
h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 2890 h1 (* h2 h2) h3 (* h4 h4 h4) (* 
h5 h5) h6 (* j2 j2 j2 j2)) (* 3402 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* 
j2 j2 j2)) (* 2304 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 840 
h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 j2) (* 128 h1 (* h2 h2) h3 (* h4 h4 h4
) (* h5 h5) h6) (* 18 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 
j2 j2 j2)) (* 174 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2
)) (* 648 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 1260 
h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 1410 h1 (* h2 h2) 
h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 918 h1 (* h2 h2) h3 (* h4 h4) (* 
h5 h5 h5 h5) (* j2 j2)) (* 324 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) j2) (* 
48 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5)) (* 3 h1 (* h2 h2) h3 (* h4 h4) (* 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 112 h1 (* h2 h2) h3 (* h4 h4) (* h5
 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 977 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 3582 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2)) (* 6965 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 
j2 j2)) (* 7828 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 5127 
h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 1822 h1 (* h2 h2) h3 (* 
h4 h4) (* h5 h5 h5) h6 j2) (* 272 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6) (* 
6 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
102 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
804 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2940
 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 5790 h1 
(* h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 6606 h1 (* h2 h2)
 h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 4392 h1 (* h2 h2) h3 (* h4 h4
) (* h5 h5) (* h6 h6) (* j2 j2)) (* 1584 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5) (* 
h6 h6) j2) (* 240 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6)) (* 42 h1 (* h2 
h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 394 h1 (* h2 h2) h3 h4
 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 1444 h1 (* h2 h2) h3 h4 (* h5 h5 
h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 2780 h1 (* h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* 
j2 j2 j2 j2)) (* 3090 h1 (* h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 
2002 h1 (* h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 704 h1 (* h2 h2) h3 h4 
(* h5 h5 h5 h5) h6 j2) (* 104 h1 (* h2 h2) h3 h4 (* h5 h5 h5 h5) h6) (* 6 h1 (* 
h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 152 h1 (* h2
 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1186 h1 (* h2 h2)
 h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4164 h1 (* h2 h2) h3 h4 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 7930 h1 (* h2 h2) h3 h4 (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2)) (* 8816 h1 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6)
 (* j2 j2 j2)) (* 5742 h1 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 
2036 h1 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) j2) (* 304 h1 (* h2 h2) h3 h4 (* 
h5 h5 h5) (* h6 h6)) (* 6 h1 (* h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 102 h1 (* h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2
 j2 j2 j2)) (* 732 h1 (* h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 2532 h1 (* h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
4830 h1 (* h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 5406 h1 (* h2
 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 3552 h1 (* h2 h2) h3 h4 (* h5
 h5) (* h6 h6 h6) (* j2 j2)) (* 1272 h1 (* h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) 
j2) (* 192 h1 (* h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6)) (* 24 h1 (* h2 h2) h3 (* 
h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 220 h1 (* h2 h2) h3 (* h5 h5
 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 796 h1 (* h2 h2) h3 (* h5 h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 1520 h1 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2)) (* 1680 h1 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2))
 (* 1084 h1 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 380 h1 (* h2 h2
) h3 (* h5 h5 h5 h5) (* h6 h6) j2) (* 56 h1 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 
h6)) (* 3 h1 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2))
 (* 64 h1 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
465 h1 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1582 h1 
(* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2965 h1 (* h2 h2) 
h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 3268 h1 (* h2 h2) h3 (* h5 h5 
h5) (* h6 h6 h6) (* j2 j2 j2)) (* 2119 h1 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6)
 (* j2 j2)) (* 750 h1 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) j2) (* 112 h1 (* h2
 h2) h3 (* h5 h5 h5) (* h6 h6 h6)) (* 2 h1 (* h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 34 h1 (* h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 232 h1 (* h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2
 j2 j2 j2 j2 j2)) (* 776 h1 (* h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 
j2 j2)) (* 1450 h1 (* h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 
1602 h1 (* h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 1044 h1 (* h2 h2
) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 372 h1 (* h2 h2) h3 (* h5 h5) (* h6
 h6 h6 h6) j2) (* 56 h1 (* h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6)) (* h1 (* h2 h2) 
(* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 9 h1 (* h2 h2) (* 
h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 35 h1 (* h2 h2) (* h4 h4 
h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 77 h1 (* h2 h2) (* h4 h4 h4) (* h5
 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 105 h1 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5) h6 
(* j2 j2 j2 j2)) (* 91 h1 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) 
(* 49 h1 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 15 h1 (* h2 h2) 
(* h4 h4 h4) (* h5 h5 h5) h6 j2) (* 2 h1 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5) h6)
 (* h1 (* h2 h2) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 9 
h1 (* h2 h2) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 35 h1 (* 
h2 h2) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 77 h1 (* h2 h2) 
(* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 105 h1 (* h2 h2) (* h4 h4) 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 91 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5 h5)
 h6 (* j2 j2 j2)) (* 49 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 
15 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5 h5) h6 j2) (* 2 h1 (* h2 h2) (* h4 h4) (* 
h5 h5 h5 h5) h6) (* 3 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 27 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2
 j2 j2 j2 j2)) (* 105 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 231 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 315 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 
273 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 147 h1 (* h2 
h2) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 45 h1 (* h2 h2) (* h4 h4) (* 
h5 h5 h5) (* h6 h6) j2) (* 6 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6)) (* 2
 h1 (* h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 18 h1
 (* h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 70 h1 (* h2
 h2) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 154 h1 (* h2 h2) h4 
(* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 210 h1 (* h2 h2) h4 (* h5 h5 h5
 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 182 h1 (* h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6)
 (* j2 j2 j2)) (* 98 h1 (* h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 30 
h1 (* h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6) j2) (* 4 h1 (* h2 h2) h4 (* h5 h5 h5 
h5) (* h6 h6)) (* 3 h1 (* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 27 h1 (* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 105 h1 (* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
231 h1 (* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 315 h1 (* 
h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 273 h1 (* h2 h2) h4 (* 
h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 147 h1 (* h2 h2) h4 (* h5 h5 h5) (* h6 
h6 h6) (* j2 j2)) (* 45 h1 (* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6) j2) (* 6 h1 
(* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6)) (* h1 (* h2 h2) (* h5 h5 h5 h5) (* h6 h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 9 h1 (* h2 h2) (* h5 h5 h5 h5) (* h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2)) (* 35 h1 (* h2 h2) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2)) (* 77 h1 (* h2 h2) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2
 j2)) (* 105 h1 (* h2 h2) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 91 h1
 (* h2 h2) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 49 h1 (* h2 h2) (* h5 
h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 15 h1 (* h2 h2) (* h5 h5 h5 h5) (* h6 h6 h6
) j2) (* 2 h1 (* h2 h2) (* h5 h5 h5 h5) (* h6 h6 h6)) (* h1 (* h2 h2) (* h5 h5 
h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 9 h1 (* h2 h2) (* h5 h5 h5) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 35 h1 (* h2 h2) (* h5 h5 h5) (* h6 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 77 h1 (* h2 h2) (* h5 h5 h5) (* h6 h6 h6 h6)
 (* j2 j2 j2 j2 j2)) (* 105 h1 (* h2 h2) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 
j2 j2)) (* 91 h1 (* h2 h2) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 49 h1 
(* h2 h2) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 15 h1 (* h2 h2) (* h5 h5 h5
) (* h6 h6 h6 h6) j2) (* 2 h1 (* h2 h2) (* h5 h5 h5) (* h6 h6 h6 h6)) (* 24 h1 
h2 (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 376 h1 h2 (* h3 
h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 2328 h1 h2 (* h3 h3 h3 h3) 
(* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 7272 h1 h2 (* h3 h3 h3 h3) (* h4 h4 h4) 
h5 (* j2 j2 j2 j2)) (* 12272 h1 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2))
 (* 11328 h1 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2)) (* 5376 h1 h2 (* h3 
h3 h3 h3) (* h4 h4 h4) h5 j2) (* 1024 h1 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h5) (* 
108 h1 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1728 
h1 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 10764 h1 h2 
(* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 33128 h1 h2 (* h3 h3 
h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 53648 h1 h2 (* h3 h3 h3 h3) (* h4
 h4) (* h5 h5) (* j2 j2 j2)) (* 46560 h1 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) 
(* j2 j2)) (* 20480 h1 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) j2) (* 3584 h1 h2 
(* h3 h3 h3 h3) (* h4 h4) (* h5 h5)) (* 132 h1 h2 (* h3 h3 h3 h3) (* h4 h4) h5 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1924 h1 h2 (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2
 j2 j2 j2 j2 j2)) (* 11124 h1 h2 (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 
j2)) (* 32748 h1 h2 (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 52856 h1
 h2 (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 47232 h1 h2 (* h3 h3 h3 h3)
 (* h4 h4) h5 h6 (* j2 j2)) (* 21888 h1 h2 (* h3 h3 h3 h3) (* h4 h4) h5 h6 j2) 
(* 4096 h1 h2 (* h3 h3 h3 h3) (* h4 h4) h5 h6) (* 432 h1 h2 (* h3 h3 h3 h3) h4 
(* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 4752 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5
) (* j2 j2 j2 j2 j2)) (* 18720 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2
 j2)) (* 32960 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2)) (* 28800 h1 
h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2)) (* 12288 h1 h2 (* h3 h3 h3 h3) h4 
(* h5 h5 h5) j2) (* 2048 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5)) (* 180 h1 h2 (* 
h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 3336 h1 h2 (* h3 h3 h3
 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 22244 h1 h2 (* h3 h3 h3 h3) h4 
(* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 70208 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5) h6 
(* j2 j2 j2 j2)) (* 114672 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) 
(* 99776 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 43904 h1 h2 (* h3 
h3 h3 h3) h4 (* h5 h5) h6 j2) (* 7680 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5) h6) (* 
192 h1 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2720 h1 
h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 15264 h1 h2 (* h3 
h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 43680 h1 h2 (* h3 h3 h3 h3) h4 
h5 (* h6 h6) (* j2 j2 j2 j2)) (* 68896 h1 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* 
j2 j2 j2)) (* 60480 h1 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 27648 h1
 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6) j2) (* 5120 h1 h2 (* h3 h3 h3 h3) h4 h5 (* 
h6 h6)) (* 432 h1 h2 (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
4752 h1 h2 (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 18720 h1 h2 
(* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 32960 h1 h2 (* h3 h3 h3 h3) 
(* h5 h5 h5) h6 (* j2 j2 j2)) (* 28800 h1 h2 (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* 
j2 j2)) (* 12288 h1 h2 (* h3 h3 h3 h3) (* h5 h5 h5) h6 j2) (* 2048 h1 h2 (* h3 
h3 h3 h3) (* h5 h5 h5) h6) (* 72 h1 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2
 j2 j2 j2 j2 j2 j2)) (* 1608 h1 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 11480 h1 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 37080 h1 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 
61024 h1 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 53216 h1 h2 (* 
h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 23424 h1 h2 (* h3 h3 h3 h3) (* h5
 h5) (* h6 h6) j2) (* 4096 h1 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6)) (* 84 h1 
h2 (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1172 h1 h2 (* h3
 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6468 h1 h2 (* h3 h3 h3 h3) 
h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 18204 h1 h2 (* h3 h3 h3 h3) h5 (* h6 h6 
h6) (* j2 j2 j2 j2)) (* 28312 h1 h2 (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)
) (* 24576 h1 h2 (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 11136 h1 h2 (* h3
 h3 h3 h3) h5 (* h6 h6 h6) j2) (* 2048 h1 h2 (* h3 h3 h3 h3) h5 (* h6 h6 h6)) 
(* 24 h1 h2 (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 304 h1 
h2 (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 1488 h1 h2 (* h3 h3
 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 3648 h1 h2 (* h3 h3 h3) (* h4 h4 
h4 h4) h5 (* j2 j2 j2 j2)) (* 4952 h1 h2 (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 
j2 j2)) (* 3792 h1 h2 (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2)) (* 1536 h1 h2 
(* h3 h3 h3) (* h4 h4 h4 h4) h5 j2) (* 256 h1 h2 (* h3 h3 h3) (* h4 h4 h4 h4) h5
) (* 216 h1 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
2544 h1 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 11632 
h1 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 26848 h1 h2 (* 
h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 34488 h1 h2 (* h3 h3 h3) 
(* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 25072 h1 h2 (* h3 h3 h3) (* h4 h4 h4) 
(* h5 h5) (* j2 j2)) (* 9664 h1 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) j2) (* 
1536 h1 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5)) (* 156 h1 h2 (* h3 h3 h3) (* h4 
h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1832 h1 h2 (* h3 h3 h3) (* h4 h4 h4) 
h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 8424 h1 h2 (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2
 j2 j2 j2 j2)) (* 19776 h1 h2 (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) 
(* 26044 h1 h2 (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 19512 h1 h2 (* 
h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2)) (* 7776 h1 h2 (* h3 h3 h3) (* h4 h4 h4) 
h5 h6 j2) (* 1280 h1 h2 (* h3 h3 h3) (* h4 h4 h4) h5 h6) (* 216 h1 h2 (* h3 h3 
h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 2808 h1 h2 (* h3 h3 h3) 
(* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 13752 h1 h2 (* h3 h3 h3) (* h4 
h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 32776 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5
 h5 h5) (* j2 j2 j2 j2)) (* 42448 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* 
j2 j2 j2)) (* 30624 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 
11584 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) j2) (* 1792 h1 h2 (* h3 h3 h3) 
(* h4 h4) (* h5 h5 h5)) (* 12 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2
 j2 j2 j2 j2 j2 j2)) (* 908 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2)) (* 9324 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 
j2 j2 j2)) (* 40436 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)
) (* 91096 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 115664 
h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 83648 h1 h2 (* h3 h3 
h3) (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 32192 h1 h2 (* h3 h3 h3) (* h4 h4) (* 
h5 h5) h6 j2) (* 5120 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) h6) (* 324 h1 h2 
(* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3672 h1 h2 (* 
h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 16344 h1 h2 (* h3 h3 
h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 37440 h1 h2 (* h3 h3 h3) (* h4
 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 48420 h1 h2 (* h3 h3 h3) (* h4 h4) h5 (* 
h6 h6) (* j2 j2 j2)) (* 35784 h1 h2 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2
)) (* 14112 h1 h2 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) j2) (* 2304 h1 h2 (* h3 h3
 h3) (* h4 h4) h5 (* h6 h6)) (* 432 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 
j2 j2 j2 j2 j2)) (* 3456 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2
)) (* 9648 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 13088 h1 h2
 (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2)) (* 9408 h1 h2 (* h3 h3 h3) h4 (* 
h5 h5 h5 h5) (* j2 j2)) (* 3456 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) j2) (* 512
 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5)) (* 432 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5
) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 5976 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2)) (* 29640 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2)) (* 70728 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 91464
 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 65856 h1 h2 (* h3 h3 h3)
 h4 (* h5 h5 h5) h6 (* j2 j2)) (* 24864 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5) h6 j2
) (* 3840 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5) h6) (* 24 h1 h2 (* h3 h3 h3) h4 (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1168 h1 h2 (* h3 h3 h3) h4 (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 11016 h1 h2 (* h3 h3 h3) h4 (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 45976 h1 h2 (* h3 h3 h3) h4 (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 101648 h1 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6
) (* j2 j2 j2 j2)) (* 127864 h1 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 
j2)) (* 92080 h1 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 35392 h1 
h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) j2) (* 5632 h1 h2 (* h3 h3 h3) h4 (* h5 
h5) (* h6 h6)) (* 276 h1 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2
 j2)) (* 3064 h1 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
13368 h1 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 30144 h1 h2 
(* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 38516 h1 h2 (* h3 h3 h3) h4 
h5 (* h6 h6 h6) (* j2 j2 j2)) (* 28200 h1 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* 
j2 j2)) (* 11040 h1 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6) j2) (* 1792 h1 h2 (* h3 
h3 h3) h4 h5 (* h6 h6 h6)) (* 432 h1 h2 (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2
 j2 j2 j2 j2)) (* 3456 h1 h2 (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2))
 (* 9648 h1 h2 (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 13088 h1 h2 
(* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 9408 h1 h2 (* h3 h3 h3) (* h5 
h5 h5 h5) h6 (* j2 j2)) (* 3456 h1 h2 (* h3 h3 h3) (* h5 h5 h5 h5) h6 j2) (* 512
 h1 h2 (* h3 h3 h3) (* h5 h5 h5 h5) h6) (* 216 h1 h2 (* h3 h3 h3) (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3168 h1 h2 (* h3 h3 h3) (* h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 15888 h1 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6)
 (* j2 j2 j2 j2 j2)) (* 37952 h1 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2
 j2 j2)) (* 49016 h1 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 
35232 h1 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 13280 h1 h2 (* h3 
h3 h3) (* h5 h5 h5) (* h6 h6) j2) (* 2048 h1 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 
h6)) (* 12 h1 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 476 h1 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
4236 h1 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 17172 
h1 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 37400 h1 h2 (* 
h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 46688 h1 h2 (* h3 h3 h3) 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 33504 h1 h2 (* h3 h3 h3) (* h5 h5) (* h6
 h6 h6) (* j2 j2)) (* 12864 h1 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) j2) (* 
2048 h1 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6)) (* 84 h1 h2 (* h3 h3 h3) h5 (* 
h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 920 h1 h2 (* h3 h3 h3) h5 (* h6 h6 h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 3960 h1 h2 (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 
j2 j2 j2 j2)) (* 8832 h1 h2 (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 
11188 h1 h2 (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 8136 h1 h2 (* h3 h3
 h3) h5 (* h6 h6 h6 h6) (* j2 j2)) (* 3168 h1 h2 (* h3 h3 h3) h5 (* h6 h6 h6 h6)
 j2) (* 512 h1 h2 (* h3 h3 h3) h5 (* h6 h6 h6 h6)) (* 48 h1 h2 (* h3 h3) (* h4 
h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 464 h1 h2 (* h3 h3) (* h4 h4 h4
 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1728 h1 h2 (* h3 h3) (* h4 h4 h4 h4) 
(* h5 h5) (* j2 j2 j2 j2 j2)) (* 3360 h1 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) 
(* j2 j2 j2 j2)) (* 3760 h1 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2))
 (* 2448 h1 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2)) (* 864 h1 h2 (* h3
 h3) (* h4 h4 h4 h4) (* h5 h5) j2) (* 128 h1 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 
h5)) (* 216 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 1896 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 6592
 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 12112 h1 h2 
(* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 12888 h1 h2 (* h3 h3) 
(* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 8008 h1 h2 (* h3 h3) (* h4 h4 h4) (* 
h5 h5 h5) (* j2 j2)) (* 2704 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) j2) (* 
384 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5)) (* 12 h1 h2 (* h3 h3) (* h4 h4 h4
) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 392 h1 h2 (* h3 h3) (* h4 h4 h4) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2956 h1 h2 (* h3 h3) (* h4 h4 h4) (* 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 9960 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) 
h6 (* j2 j2 j2 j2 j2)) (* 18340 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 
j2 j2 j2)) (* 19832 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 
12612 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 4376 h1 h2 (* h3 
h3) (* h4 h4 h4) (* h5 h5) h6 j2) (* 640 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) 
h6) (* 108 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 1080 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 3960
 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 7424 h1 h2 (* 
h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 7916 h1 h2 (* h3 h3) (* h4 
h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 4872 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 
h5) (* j2 j2)) (* 1616 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) j2) (* 224 h1 
h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5)) (* 24 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5
 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 916 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 6924 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2)) (* 22912 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2)) (* 41168 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 
j2)) (* 43316 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 26764 
h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 9016 h1 h2 (* h3 h3) (* 
h4 h4) (* h5 h5 h5) h6 j2) (* 1280 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) h6) 
(* 36 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2))
 (* 888 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 6084 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
19512 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 34860
 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 36936 h1 h2 
(* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 23148 h1 h2 (* h3 h3) 
(* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 7944 h1 h2 (* h3 h3) (* h4 h4) (* h5
 h5) (* h6 h6) j2) (* 1152 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6)) (* 252
 h1 h2 (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2424 h1 h2 
(* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 8728 h1 h2 (* h3 h3) 
h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 16192 h1 h2 (* h3 h3) h4 (* h5 h5 
h5 h5) h6 (* j2 j2 j2 j2)) (* 17148 h1 h2 (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 
j2 j2)) (* 10504 h1 h2 (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 3472 h1 h2 
(* h3 h3) h4 (* h5 h5 h5 h5) h6 j2) (* 480 h1 h2 (* h3 h3) h4 (* h5 h5 h5 h5) h6
) (* 48 h1 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 1184 h1 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
8160 h1 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 26048 
h1 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 46000 h1 h2 (* 
h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 47968 h1 h2 (* h3 h3) h4 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 29504 h1 h2 (* h3 h3) h4 (* h5 h5 h5) 
(* h6 h6) (* j2 j2)) (* 9920 h1 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) j2) (* 
1408 h1 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6)) (* 36 h1 h2 (* h3 h3) h4 (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 792 h1 h2 (* h3 h3) h4 (* h5 h5
) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 5156 h1 h2 (* h3 h3) h4 (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 16056 h1 h2 (* h3 h3) h4 (* h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2)) (* 28140 h1 h2 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2)) (* 29416 h1 h2 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)
) (* 18252 h1 h2 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 6216 h1 h2 
(* h3 h3) h4 (* h5 h5) (* h6 h6 h6) j2) (* 896 h1 h2 (* h3 h3) h4 (* h5 h5) (* 
h6 h6 h6)) (* 144 h1 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2
 j2)) (* 1344 h1 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 4768 h1 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 8768 h1
 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 9232 h1 h2 (* h3 h3)
 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 5632 h1 h2 (* h3 h3) (* h5 h5 h5 h5)
 (* h6 h6) (* j2 j2)) (* 1856 h1 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) j2) (* 
256 h1 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6)) (* 24 h1 h2 (* h3 h3) (* h5 h5 h5
) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 484 h1 h2 (* h3 h3) (* h5 h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3132 h1 h2 (* h3 h3) (* h5 h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 9728 h1 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2)) (* 16944 h1 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2
 j2 j2 j2)) (* 17540 h1 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 
10748 h1 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 3608 h1 h2 (* h3 
h3) (* h5 h5 h5) (* h6 h6 h6) j2) (* 512 h1 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 
h6)) (* 12 h1 h2 (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 248 h1 h2 (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
1564 h1 h2 (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4776 h1
 h2 (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 8260 h1 h2 (* h3 
h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 8552 h1 h2 (* h3 h3) (* h5 h5)
 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 5268 h1 h2 (* h3 h3) (* h5 h5) (* h6 h6 h6 h6)
 (* j2 j2)) (* 1784 h1 h2 (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) j2) (* 256 h1 h2 
(* h3 h3) (* h5 h5) (* h6 h6 h6 h6)) (* 24 h1 h2 h3 (* h4 h4 h4 h4) (* h5 h5 h5)
 (* j2 j2 j2 j2 j2 j2 j2)) (* 160 h1 h2 h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2
 j2 j2 j2 j2)) (* 456 h1 h2 h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) 
(* 720 h1 h2 h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 680 h1 h2 h3 
(* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 384 h1 h2 h3 (* h4 h4 h4 h4) (* h5
 h5 h5) (* j2 j2)) (* 120 h1 h2 h3 (* h4 h4 h4 h4) (* h5 h5 h5) j2) (* 16 h1 h2 
h3 (* h4 h4 h4 h4) (* h5 h5 h5)) (* 24 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 160 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 
j2 j2 j2)) (* 456 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 
720 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 680 h1 h2 h3 (* h4
 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 384 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5 
h5) (* j2 j2)) (* 120 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5 h5) j2) (* 16 h1 h2 h3 
(* h4 h4 h4) (* h5 h5 h5 h5)) (* 12 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 200 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2)) (* 1028 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2
)) (* 2640 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 3940 h1 
h2 h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 3592 h1 h2 h3 (* h4 h4 h4
) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 1980 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5) h6 
(* j2 j2)) (* 608 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5) h6 j2) (* 80 h1 h2 h3 (* h4
 h4 h4) (* h5 h5 h5) h6) (* 12 h1 h2 h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 176 h1 h2 h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2
 j2 j2)) (* 868 h1 h2 h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
2184 h1 h2 h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 3220 h1 h2 h3 
(* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 2912 h1 h2 h3 (* h4 h4) (* h5 
h5 h5 h5) h6 (* j2 j2 j2)) (* 1596 h1 h2 h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 
j2)) (* 488 h1 h2 h3 (* h4 h4) (* h5 h5 h5 h5) h6 j2) (* 64 h1 h2 h3 (* h4 h4) 
(* h5 h5 h5 h5) h6) (* 36 h1 h2 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 456 h1 h2 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2
 j2 j2 j2)) (* 2124 h1 h2 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 5184 h1 h2 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
7500 h1 h2 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 6696 h1 h2 h3
 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 3636 h1 h2 h3 (* h4 h4) (* h5
 h5 h5) (* h6 h6) (* j2 j2)) (* 1104 h1 h2 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) 
j2) (* 144 h1 h2 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6)) (* 24 h1 h2 h3 h4 (* h5 h5
 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 280 h1 h2 h3 h4 (* h5 h5 h5 h5
) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1256 h1 h2 h3 h4 (* h5 h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 3000 h1 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2)) (* 4280 h1 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 
3784 h1 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 2040 h1 h2 h3 h4 (* 
h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 616 h1 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6) 
j2) (* 80 h1 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6)) (* 36 h1 h2 h3 h4 (* h5 h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 408 h1 h2 h3 h4 (* h5 h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1804 h1 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 4272 h1 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2
 j2 j2)) (* 6060 h1 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 5336 
h1 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 2868 h1 h2 h3 h4 (* h5 h5
 h5) (* h6 h6 h6) (* j2 j2)) (* 864 h1 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6) j2) 
(* 112 h1 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6)) (* 12 h1 h2 h3 (* h5 h5 h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 128 h1 h2 h3 (* h5 h5 h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 548 h1 h2 h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2)) (* 1272 h1 h2 h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2)) (* 1780 h1 h2 h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1552 h1 
h2 h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 828 h1 h2 h3 (* h5 h5 h5 h5)
 (* h6 h6 h6) (* j2 j2)) (* 248 h1 h2 h3 (* h5 h5 h5 h5) (* h6 h6 h6) j2) (* 32 
h1 h2 h3 (* h5 h5 h5 h5) (* h6 h6 h6)) (* 12 h1 h2 h3 (* h5 h5 h5) (* h6 h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 128 h1 h2 h3 (* h5 h5 h5) (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 548 h1 h2 h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 1272 h1 h2 h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 1780 h1 h2 h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 1552 h1 h2 h3 
(* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 828 h1 h2 h3 (* h5 h5 h5) (* h6 h6
 h6 h6) (* j2 j2)) (* 248 h1 h2 h3 (* h5 h5 h5) (* h6 h6 h6 h6) j2) (* 32 h1 h2 
h3 (* h5 h5 h5) (* h6 h6 h6 h6)) (* 72 h1 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5)
 (* j2 j2 j2 j2 j2 j2 j2)) (* 888 h1 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* 
j2 j2 j2 j2 j2 j2)) (* 4184 h1 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 
j2 j2 j2)) (* 9736 h1 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) 
(* 12416 h1 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 8864 h1 (* 
h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 3328 h1 (* h3 h3 h3 h3) (* h4 
h4 h4) (* h5 h5) j2) (* 512 h1 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5)) (* 432 h1
 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 3456 h1 (* h3 
h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 9648 h1 (* h3 h3 h3 h3) 
(* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 13088 h1 (* h3 h3 h3 h3) (* h4 h4) 
(* h5 h5 h5) (* j2 j2 j2)) (* 9408 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* 
j2 j2)) (* 3456 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) j2) (* 512 h1 (* h3 h3
 h3 h3) (* h4 h4) (* h5 h5 h5)) (* 36 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 732 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 5644 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2)) (* 21604 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 
j2 j2 j2)) (* 45152 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) 
(* 54096 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 37120 h1 (* 
h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 13568 h1 (* h3 h3 h3 h3) (* h4
 h4) (* h5 h5) h6 j2) (* 2048 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6) (* 216 
h1 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 3024 h1 (* h3
 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 15192 h1 (* h3 h3 h3 h3)
 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 35488 h1 (* h3 h3 h3 h3) h4 (* h5 h5 
h5) h6 (* j2 j2 j2 j2)) (* 43968 h1 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 
j2)) (* 29952 h1 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2)) (* 10624 h1 (* h3
 h3 h3 h3) h4 (* h5 h5 h5) h6 j2) (* 1536 h1 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6)
 (* 72 h1 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 1248 h1 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
8624 h1 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 30656 
h1 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 61096 h1 (* h3 
h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 70944 h1 (* h3 h3 h3 h3) h4
 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 47648 h1 (* h3 h3 h3 h3) h4 (* h5 h5) (* 
h6 h6) (* j2 j2)) (* 17152 h1 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) j2) (* 2560
 h1 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6)) (* 216 h1 (* h3 h3 h3 h3) (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2592 h1 (* h3 h3 h3 h3) (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 11736 h1 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2)) (* 25840 h1 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2
 j2 j2 j2)) (* 30880 h1 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 
20544 h1 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 7168 h1 (* h3 h3 
h3 h3) (* h5 h5 h5) (* h6 h6) j2) (* 1024 h1 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 
h6)) (* 36 h1 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 588 h1 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
3868 h1 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 13236 
h1 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 25680 h1 (* h3 
h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 29264 h1 (* h3 h3 h3 h3) 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 19392 h1 (* h3 h3 h3 h3) (* h5 h5) (* h6
 h6 h6) (* j2 j2)) (* 6912 h1 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) j2) (* 1024
 h1 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6)) (* 72 h1 (* h3 h3 h3) (* h4 h4 h4 h4
) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 672 h1 (* h3 h3 h3) (* h4 h4 h4 h4) (* 
h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2384 h1 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) 
(* j2 j2 j2 j2 j2)) (* 4384 h1 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 
j2 j2)) (* 4616 h1 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 2816 
h1 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2)) (* 928 h1 (* h3 h3 h3) (* 
h4 h4 h4 h4) (* h5 h5) j2) (* 128 h1 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5)) (* 
144 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1344 
h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 4768 h1 (* 
h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 8768 h1 (* h3 h3 h3) 
(* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 9232 h1 (* h3 h3 h3) (* h4 h4 h4) 
(* h5 h5 h5) (* j2 j2 j2)) (* 5632 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* 
j2 j2)) (* 1856 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) j2) (* 256 h1 (* h3 h3
 h3) (* h4 h4 h4) (* h5 h5 h5)) (* 36 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 696 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 4552 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2)) (* 14112 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 
j2 j2 j2)) (* 24228 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) 
(* 24488 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 14544 h1 (* 
h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 4704 h1 (* h3 h3 h3) (* h4 h4 
h4) (* h5 h5) h6 j2) (* 640 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6) (* 432 h1
 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2160 h1 (* h3 
h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 4464 h1 (* h3 h3 h3) (* 
h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 4880 h1 (* h3 h3 h3) (* h4 h4) (* h5 
h5 h5 h5) (* j2 j2 j2)) (* 2976 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 
j2)) (* 960 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) j2) (* 128 h1 (* h3 h3 h3)
 (* h4 h4) (* h5 h5 h5 h5)) (* 72 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 1248 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2)) (* 7760 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2)) (* 23456 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2)) (* 39688 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 
39744 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 23456 h1 (* h3 
h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 7552 h1 (* h3 h3 h3) (* h4 h4) 
(* h5 h5 h5) h6 j2) (* 1024 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6) (* 108 h1
 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1656
 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 9624
 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 28032 
h1 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 46380 h1 
(* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 45768 h1 (* h3 h3
 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 26736 h1 (* h3 h3 h3) (* h4 
h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 8544 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5) 
(* h6 h6) j2) (* 1152 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6)) (* 216 h1 
(* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2376 h1 (* h3 h3
 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 8712 h1 (* h3 h3 h3) h4 (* 
h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 15832 h1 (* h3 h3 h3) h4 (* h5 h5 h5 h5) 
h6 (* j2 j2 j2 j2)) (* 16128 h1 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2))
 (* 9408 h1 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 2944 h1 (* h3 h3 h3
) h4 (* h5 h5 h5 h5) h6 j2) (* 384 h1 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6) (* 144
 h1 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2064 
h1 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 11488 h1 
(* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 32608 h1 (* h3 
h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 53072 h1 (* h3 h3 h3) h4
 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 51792 h1 (* h3 h3 h3) h4 (* h5 h5 h5
) (* h6 h6) (* j2 j2 j2)) (* 30016 h1 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* 
j2 j2)) (* 9536 h1 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) j2) (* 1280 h1 (* h3 
h3 h3) h4 (* h5 h5 h5) (* h6 h6)) (* 108 h1 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1512 h1 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 8280 h1 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 23264 h1 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2)) (* 37612 h1 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)
) (* 36536 h1 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 21104 h1 
(* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 6688 h1 (* h3 h3 h3) h4 (* 
h5 h5) (* h6 h6 h6) j2) (* 896 h1 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6)) (* 216
 h1 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1944 h1 
(* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6552 h1 (* h3 
h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 11368 h1 (* h3 h3 h3) 
(* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 11248 h1 (* h3 h3 h3) (* h5 h5 h5 
h5) (* h6 h6) (* j2 j2 j2)) (* 6432 h1 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) 
(* j2 j2)) (* 1984 h1 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) j2) (* 256 h1 (* h3
 h3 h3) (* h5 h5 h5 h5) (* h6 h6)) (* 72 h1 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 960 h1 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6
) (* j2 j2 j2 j2 j2 j2 j2)) (* 5072 h1 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 13920 h1 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2)) (* 22152 h1 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)
) (* 21280 h1 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 12192 h1 
(* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 3840 h1 (* h3 h3 h3) (* h5 
h5 h5) (* h6 h6 h6) j2) (* 512 h1 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6)) (* 36 
h1 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 480 h1
 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2536 h1 (* 
h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6960 h1 (* h3 h3 
h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 11076 h1 (* h3 h3 h3) (* h5
 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 10640 h1 (* h3 h3 h3) (* h5 h5) (* h6 
h6 h6 h6) (* j2 j2 j2)) (* 6096 h1 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 
j2)) (* 1920 h1 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) j2) (* 256 h1 (* h3 h3 h3
) (* h5 h5) (* h6 h6 h6 h6)) (* 72 h1 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 456 h1 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2
 j2 j2 j2 j2)) (* 1232 h1 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 
j2)) (* 1840 h1 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 1640 
h1 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 872 h1 (* h3 h3) (* 
h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2)) (* 256 h1 (* h3 h3) (* h4 h4 h4 h4) (* h5 
h5 h5) j2) (* 32 h1 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5)) (* 72 h1 (* h3 h3) 
(* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 456 h1 (* h3 h3) (* h4
 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1232 h1 (* h3 h3) (* h4 h4 h4)
 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 1840 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 
h5 h5) (* j2 j2 j2 j2)) (* 1640 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 
j2 j2)) (* 872 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 256 h1 
(* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) j2) (* 32 h1 (* h3 h3) (* h4 h4 h4) (* h5
 h5 h5 h5)) (* 36 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 588 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2)) (* 2896 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 7080 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 10020 
h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 8636 h1 (* h3 h3) 
(* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 4488 h1 (* h3 h3) (* h4 h4 h4) (* 
h5 h5 h5) h6 (* j2 j2)) (* 1296 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 j2) 
(* 160 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6) (* 36 h1 (* h3 h3) (* h4 h4) 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 516 h1 (* h3 h3) (* h4 h4) 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2440 h1 (* h3 h3) (* h4 h4) (* 
h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 5848 h1 (* h3 h3) (* h4 h4) (* h5 h5 
h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 8180 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 
(* j2 j2 j2 j2)) (* 6996 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2))
 (* 3616 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 1040 h1 (* h3 
h3) (* h4 h4) (* h5 h5 h5 h5) h6 j2) (* 128 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5 
h5) h6) (* 108 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 1332 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 5952 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 13848 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2
)) (* 19020 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 
16068 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 8232 h1 (* 
h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 2352 h1 (* h3 h3) (* h4 h4
) (* h5 h5 h5) (* h6 h6) j2) (* 288 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6
)) (* 72 h1 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 816 h1 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
3512 h1 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 8000 h1
 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 10840 h1 (* h3 h3
) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 9072 h1 (* h3 h3) h4 (* h5 h5
 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 4616 h1 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6
) (* j2 j2)) (* 1312 h1 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) j2) (* 160 h1 (* 
h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6)) (* 108 h1 (* h3 h3) h4 (* h5 h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1188 h1 (* h3 h3) h4 (* h5 h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 5040 h1 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 11384 h1 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2)) (* 15340 h1 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2)) (* 12788 h1 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 6488
 h1 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 1840 h1 (* h3 h3) h4 
(* h5 h5 h5) (* h6 h6 h6) j2) (* 224 h1 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6)) 
(* 36 h1 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
372 h1 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1528 
h1 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3384 h1 (* 
h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 4500 h1 (* h3 h3) (* 
h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 3716 h1 (* h3 h3) (* h5 h5 h5 h5) 
(* h6 h6 h6) (* j2 j2 j2)) (* 1872 h1 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* 
j2 j2)) (* 528 h1 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) j2) (* 64 h1 (* h3 h3) 
(* h5 h5 h5 h5) (* h6 h6 h6)) (* 36 h1 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 372 h1 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 1528 h1 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 3384 h1 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 
j2 j2 j2)) (* 4500 h1 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) 
(* 3716 h1 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 1872 h1 (* h3
 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 528 h1 (* h3 h3) (* h5 h5 h5) 
(* h6 h6 h6 h6) j2) (* 64 h1 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6)) (* 6 (* h2 
h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 64 (* h2 h2 h2 h2) 
(* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 238 (* h2 h2 h2 h2) (* h3 h3 h3) 
(* h4 h4) h5 (* j2 j2 j2)) (* 372 (* h2 h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* 
j2 j2)) (* 256 (* h2 h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 j2) (* 64 (* h2 h2 h2 
h2) (* h3 h3 h3) (* h4 h4) h5) (* 36 (* h2 h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) 
(* j2 j2 j2 j2)) (* 228 (* h2 h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2)) 
(* 400 (* h2 h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2)) (* 272 (* h2 h2 h2 
h2) (* h3 h3 h3) h4 (* h5 h5) j2) (* 64 (* h2 h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5
)) (* 12 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 128 (* h2 
h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 476 (* h2 h2 h2 h2) (* h3 h3
 h3) h4 h5 h6 (* j2 j2 j2)) (* 744 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 
j2)) (* 512 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 h6 j2) (* 128 (* h2 h2 h2 h2) (* 
h3 h3 h3) h4 h5 h6) (* 36 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 
j2)) (* 228 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 400 (* h2
 h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2)) (* 272 (* h2 h2 h2 h2) (* h3 h3 
h3) (* h5 h5) h6 j2) (* 64 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6) (* 6 (* h2
 h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 64 (* h2 h2 h2 h2) 
(* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 238 (* h2 h2 h2 h2) (* h3 h3 h3) 
h5 (* h6 h6) (* j2 j2 j2)) (* 372 (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* 
j2 j2)) (* 256 (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) j2) (* 64 (* h2 h2 h2 
h2) (* h3 h3 h3) h5 (* h6 h6)) (* 6 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 
(* j2 j2 j2 j2 j2)) (* 46 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 
j2)) (* 118 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 138 (* h2
 h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2)) (* 76 (* h2 h2 h2 h2) (* h3 h3) 
(* h4 h4 h4) h5 j2) (* 16 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5) (* 12 (* h2
 h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 92 (* h2 h2 h2 
h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 236 (* h2 h2 h2 h2) (* h3 
h3) (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 276 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4)
 (* h5 h5) (* j2 j2)) (* 152 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) j2) 
(* 32 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5)) (* 18 (* h2 h2 h2 h2) (* h3
 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 138 (* h2 h2 h2 h2) (* h3 h3) (* h4 
h4) h5 h6 (* j2 j2 j2 j2)) (* 354 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* 
j2 j2 j2)) (* 414 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 228 
(* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 j2) (* 48 (* h2 h2 h2 h2) (* h3 h3) 
(* h4 h4) h5 h6) (* 36 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)
) (* 120 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2)) (* 148 (* h2 h2
 h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2)) (* 80 (* h2 h2 h2 h2) (* h3 h3) h4 
(* h5 h5 h5) j2) (* 16 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5)) (* 24 (* h2 h2
 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 184 (* h2 h2 h2 h2) (* 
h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 472 (* h2 h2 h2 h2) (* h3 h3) h4 (* 
h5 h5) h6 (* j2 j2 j2)) (* 552 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 
j2)) (* 304 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 j2) (* 64 (* h2 h2 h2 h2) 
(* h3 h3) h4 (* h5 h5) h6) (* 18 (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2
 j2 j2 j2 j2)) (* 138 (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2))
 (* 354 (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 414 (* h2 h2 
h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 228 (* h2 h2 h2 h2) (* h3 h3) h4 
h5 (* h6 h6) j2) (* 48 (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6)) (* 36 (* h2 h2
 h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 120 (* h2 h2 h2 h2) (* h3 
h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 148 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) 
h6 (* j2 j2)) (* 80 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 j2) (* 16 (* h2 h2
 h2 h2) (* h3 h3) (* h5 h5 h5) h6) (* 12 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2)) (* 92 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2)) (* 236 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 
j2)) (* 276 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 152 (* 
h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) j2) (* 32 (* h2 h2 h2 h2) (* h3 h3) 
(* h5 h5) (* h6 h6)) (* 6 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 
j2 j2)) (* 46 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 118 
(* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 138 (* h2 h2 h2 h2) 
(* h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 76 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6
 h6) j2) (* 16 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6)) (* 6 (* h2 h2 h2 h2) 
h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 28 (* h2 h2 h2 h2) h3 (* h4 h4 
h4) (* h5 h5) (* j2 j2 j2 j2)) (* 52 (* h2 h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) 
(* j2 j2 j2)) (* 48 (* h2 h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 22 
(* h2 h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) j2) (* 4 (* h2 h2 h2 h2) h3 (* h4 h4 
h4) (* h5 h5)) (* 6 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)
) (* 28 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 52 (* h2 
h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 48 (* h2 h2 h2 h2) h3 (* h4
 h4) (* h5 h5 h5) (* j2 j2)) (* 22 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) j2)
 (* 4 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5)) (* 18 (* h2 h2 h2 h2) h3 (* h4 
h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 84 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5
) h6 (* j2 j2 j2 j2)) (* 156 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 
j2)) (* 144 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 66 (* h2 h2 
h2 h2) h3 (* h4 h4) (* h5 h5) h6 j2) (* 12 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5
) h6) (* 12 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 56 (* 
h2 h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 104 (* h2 h2 h2 h2) h3 h4
 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 96 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2
 j2)) (* 44 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) h6 j2) (* 8 (* h2 h2 h2 h2) h3 h4
 (* h5 h5 h5) h6) (* 18 (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2
 j2)) (* 84 (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 156 
(* h2 h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 144 (* h2 h2 h2 h2) 
h3 h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 66 (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* h6
 h6) j2) (* 12 (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6)) (* 6 (* h2 h2 h2 h2) 
h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 28 (* h2 h2 h2 h2) h3 (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2)) (* 52 (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2)) (* 48 (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 22 
(* h2 h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) j2) (* 4 (* h2 h2 h2 h2) h3 (* h5 h5 
h5) (* h6 h6)) (* 6 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)
) (* 28 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 52 (* h2 
h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 48 (* h2 h2 h2 h2) h3 (* h5
 h5) (* h6 h6 h6) (* j2 j2)) (* 22 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) j2)
 (* 4 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6)) (* 6 (* h2 h2 h2) (* h3 h3 h3 
h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 88 (* h2 h2 h2) (* h3 h3 h3 h3) (* h4
 h4) h5 (* j2 j2 j2 j2 j2)) (* 494 (* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* 
j2 j2 j2 j2)) (* 1324 (* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2)) 
(* 1744 (* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2)) (* 1088 (* h2 h2 h2
) (* h3 h3 h3 h3) (* h4 h4) h5 j2) (* 256 (* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4)
 h5) (* 36 (* h2 h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 372 
(* h2 h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 1312 (* h2 h2 h2) 
(* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 1872 (* h2 h2 h2) (* h3 h3 h3 h3) 
h4 (* h5 h5) (* j2 j2)) (* 1152 (* h2 h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) j2) 
(* 256 (* h2 h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5)) (* 12 (* h2 h2 h2) (* h3 h3 h3
 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 176 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 
h6 (* j2 j2 j2 j2 j2)) (* 988 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 
j2)) (* 2648 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 3488 (* h2 
h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2)) (* 2176 (* h2 h2 h2) (* h3 h3 h3 h3) 
h4 h5 h6 j2) (* 512 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 h6) (* 36 (* h2 h2 h2) 
(* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 372 (* h2 h2 h2) (* h3 h3 h3
 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 1312 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5
) h6 (* j2 j2 j2)) (* 1872 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2)) 
(* 1152 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 j2) (* 256 (* h2 h2 h2) (* h3 
h3 h3 h3) (* h5 h5) h6) (* 6 (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 88 (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)
) (* 494 (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 1324 (* 
h2 h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 1744 (* h2 h2 h2) (* h3 
h3 h3 h3) h5 (* h6 h6) (* j2 j2)) (* 1088 (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* h6 
h6) j2) (* 256 (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6)) (* 12 (* h2 h2 h2) (* 
h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 140 (* h2 h2 h2) (* h3 h3 h3
) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 604 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4 
h4) h5 (* j2 j2 j2 j2)) (* 1220 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 
j2 j2)) (* 1256 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2)) (* 640 (* 
h2 h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 j2) (* 128 (* h2 h2 h2) (* h3 h3 h3) (* 
h4 h4 h4) h5) (* 18 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2
 j2 j2)) (* 246 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)
) (* 1170 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 2458
 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 2556 (* h2 h2 h2
) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 1296 (* h2 h2 h2) (* h3 h3 h3) 
(* h4 h4) (* h5 h5) j2) (* 256 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5)) 
(* 36 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 420 
(* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 1812 (* h2 h2 
h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 3660 (* h2 h2 h2) (* h3 h3 
h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 3768 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5
 h6 (* j2 j2)) (* 1920 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 j2) (* 384 (* 
h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6) (* 72 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5
 h5 h5) (* j2 j2 j2 j2 j2)) (* 528 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* 
j2 j2 j2 j2)) (* 1256 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2)) 
(* 1344 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2)) (* 672 (* h2 h2 h2)
 (* h3 h3 h3) h4 (* h5 h5 h5) j2) (* 128 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5 
h5)) (* 36 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
492 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 2340 (* h2 
h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 4916 (* h2 h2 h2) (* h3 
h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 5112 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 
h5) h6 (* j2 j2)) (* 2592 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 j2) (* 512 
(* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6) (* 36 (* h2 h2 h2) (* h3 h3 h3) h4 h5
 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 420 (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* h6 
h6) (* j2 j2 j2 j2 j2)) (* 1812 (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 
j2 j2 j2)) (* 3660 (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 
3768 (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 1920 (* h2 h2 h2) 
(* h3 h3 h3) h4 h5 (* h6 h6) j2) (* 384 (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6
)) (* 72 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 528 
(* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 1256 (* h2 h2 h2) 
(* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 1344 (* h2 h2 h2) (* h3 h3 h3) (* 
h5 h5 h5) h6 (* j2 j2)) (* 672 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 j2) (* 
128 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6) (* 18 (* h2 h2 h2) (* h3 h3 h3) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 246 (* h2 h2 h2) (* h3 h3 h3) (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1170 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5)
 (* h6 h6) (* j2 j2 j2 j2)) (* 2458 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6
) (* j2 j2 j2)) (* 2556 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2))
 (* 1296 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) j2) (* 256 (* h2 h2 h2) 
(* h3 h3 h3) (* h5 h5) (* h6 h6)) (* 12 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6
) (* j2 j2 j2 j2 j2 j2)) (* 140 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 
j2 j2 j2 j2)) (* 604 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) 
(* 1220 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 1256 (* h2 h2
 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 640 (* h2 h2 h2) (* h3 h3 h3) h5
 (* h6 h6 h6) j2) (* 128 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6)) (* 6 (* h2 
h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 52 (* h2 h2 h2) 
(* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 164 (* h2 h2 h2) (* h3 h3) 
(* h4 h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 256 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4 h4
) h5 (* j2 j2 j2)) (* 214 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2)) 
(* 92 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 j2) (* 16 (* h2 h2 h2) (* h3 h3)
 (* h4 h4 h4 h4) h5) (* 24 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 
j2 j2 j2 j2 j2)) (* 208 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 
j2 j2 j2)) (* 656 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2))
 (* 1024 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 856 (* 
h2 h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 368 (* h2 h2 h2) (* h3 
h3) (* h4 h4 h4) (* h5 h5) j2) (* 64 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 
h5)) (* 24 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 
208 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 656 (* h2 
h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 1024 (* h2 h2 h2) (* h3 
h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 856 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) 
h5 h6 (* j2 j2)) (* 368 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 j2) (* 64 (* 
h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6) (* 18 (* h2 h2 h2) (* h3 h3) (* h4 h4) 
(* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 192 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* 
h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 648 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 
h5) (* j2 j2 j2 j2)) (* 1036 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2
 j2 j2)) (* 870 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 372 
(* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) j2) (* 64 (* h2 h2 h2) (* h3 h3) 
(* h4 h4) (* h5 h5 h5)) (* 72 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2)) (* 624 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* 1968 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 
j2)) (* 3072 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 2568
 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 1104 (* h2 h2 h2) 
(* h3 h3) (* h4 h4) (* h5 h5) h6 j2) (* 192 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* 
h5 h5) h6) (* 36 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2
 j2)) (* 312 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 984 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 1536 
(* h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 1284 (* h2 h2 h2)
 (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 552 (* h2 h2 h2) (* h3 h3) (* h4
 h4) h5 (* h6 h6) j2) (* 96 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6)) (* 36
 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 156 (* h2 h2 
h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 268 (* h2 h2 h2) (* h3 h3) 
h4 (* h5 h5 h5 h5) (* j2 j2 j2)) (* 228 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5
) (* j2 j2)) (* 96 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) j2) (* 16 (* h2 h2 
h2) (* h3 h3) h4 (* h5 h5 h5 h5)) (* 36 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2)) (* 384 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2
 j2 j2 j2 j2)) (* 1296 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)
) (* 2072 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 1740 (* h2 
h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2)) (* 744 (* h2 h2 h2) (* h3 h3) h4 
(* h5 h5 h5) h6 j2) (* 128 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6) (* 72 (* 
h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 624 (* h2 
h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1968 (* h2 h2 h2)
 (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 3072 (* h2 h2 h2) (* h3 h3
) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 2568 (* h2 h2 h2) (* h3 h3) h4 (* h5 
h5) (* h6 h6) (* j2 j2)) (* 1104 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) 
j2) (* 192 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6)) (* 24 (* h2 h2 h2) (* 
h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 208 (* h2 h2 h2) (* h3 h3) 
h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 656 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6
 h6 h6) (* j2 j2 j2 j2)) (* 1024 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2
 j2 j2)) (* 856 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2)) (* 368 (* 
h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) j2) (* 64 (* h2 h2 h2) (* h3 h3) h4 h5 
(* h6 h6 h6)) (* 36 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)
) (* 156 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 268 (* h2
 h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 228 (* h2 h2 h2) (* h3 h3)
 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 96 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 
j2) (* 16 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6) (* 18 (* h2 h2 h2) (* h3 h3
) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 192 (* h2 h2 h2) (* h3 h3) 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 648 (* h2 h2 h2) (* h3 h3) (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 1036 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2)) (* 870 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* 
j2 j2)) (* 372 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) j2) (* 64 (* h2 h2 
h2) (* h3 h3) (* h5 h5 h5) (* h6 h6)) (* 24 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 208 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2)) (* 656 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2)) (* 1024 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 
j2)) (* 856 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 368 (* 
h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) j2) (* 64 (* h2 h2 h2) (* h3 h3) (* 
h5 h5) (* h6 h6 h6)) (* 6 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 52 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 164 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 256 (* h2 
h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 214 (* h2 h2 h2) (* h3 h3) 
h5 (* h6 h6 h6 h6) (* j2 j2)) (* 92 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) j2
) (* 16 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6)) (* 6 (* h2 h2 h2) h3 (* h4 h4
 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 34 (* h2 h2 h2) h3 (* h4 h4 h4 h4) 
(* h5 h5) (* j2 j2 j2 j2 j2)) (* 80 (* h2 h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) 
(* j2 j2 j2 j2)) (* 100 (* h2 h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2)) 
(* 70 (* h2 h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2)) (* 26 (* h2 h2 h2) h3
 (* h4 h4 h4 h4) (* h5 h5) j2) (* 4 (* h2 h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5)) 
(* 12 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 68 (* 
h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 160 (* h2 h2 h2) 
h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 200 (* h2 h2 h2) h3 (* h4 h4 h4
) (* h5 h5 h5) (* j2 j2 j2)) (* 140 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) 
(* j2 j2)) (* 52 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) j2) (* 8 (* h2 h2 h2)
 h3 (* h4 h4 h4) (* h5 h5 h5)) (* 24 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 136 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2
 j2 j2 j2)) (* 320 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) 
(* 400 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 280 (* h2 h2 
h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 104 (* h2 h2 h2) h3 (* h4 h4 h4) 
(* h5 h5) h6 j2) (* 16 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6) (* 6 (* h2 h2 
h2) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 34 (* h2 h2 h2) h3 
(* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 80 (* h2 h2 h2) h3 (* h4 h4) 
(* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 100 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5
) (* j2 j2 j2)) (* 70 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 26
 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) j2) (* 4 (* h2 h2 h2) h3 (* h4 h4) 
(* h5 h5 h5 h5)) (* 36 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2)) (* 204 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
480 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 600 (* h2 h2 
h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 420 (* h2 h2 h2) h3 (* h4 h4) 
(* h5 h5 h5) h6 (* j2 j2)) (* 156 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 j2) 
(* 24 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6) (* 36 (* h2 h2 h2) h3 (* h4 h4)
 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 204 (* h2 h2 h2) h3 (* h4 h4) (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 480 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2)) (* 600 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) 
(* j2 j2 j2)) (* 420 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) 
(* 156 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) j2) (* 24 (* h2 h2 h2) h3 
(* h4 h4) (* h5 h5) (* h6 h6)) (* 12 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2
 j2 j2 j2 j2 j2)) (* 68 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)
) (* 160 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 200 (* h2 h2 
h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 140 (* h2 h2 h2) h3 h4 (* h5 h5 h5
 h5) h6 (* j2 j2)) (* 52 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) h6 j2) (* 8 (* h2 h2
 h2) h3 h4 (* h5 h5 h5 h5) h6) (* 36 (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 204 (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2
 j2 j2 j2)) (* 480 (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) 
(* 600 (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 420 (* h2 h2 
h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 156 (* h2 h2 h2) h3 h4 (* h5 h5 
h5) (* h6 h6) j2) (* 24 (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6)) (* 24 (* h2 
h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 136 (* h2 h2 h2) 
h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 320 (* h2 h2 h2) h3 h4 (* h5
 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 400 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2)) (* 280 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2)) 
(* 104 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) j2) (* 16 (* h2 h2 h2) h3 h4 
(* h5 h5) (* h6 h6 h6)) (* 6 (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 34 (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)
) (* 80 (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 100 (* h2 
h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 70 (* h2 h2 h2) h3 (* h5 h5
 h5 h5) (* h6 h6) (* j2 j2)) (* 26 (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) j2)
 (* 4 (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6)) (* 12 (* h2 h2 h2) h3 (* h5 h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 68 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6
 h6 h6) (* j2 j2 j2 j2 j2)) (* 160 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2)) (* 200 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 
140 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 52 (* h2 h2 h2) h3 
(* h5 h5 h5) (* h6 h6 h6) j2) (* 8 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6)) 
(* 6 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 34 (* 
h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 80 (* h2 h2 h2) h3
 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 100 (* h2 h2 h2) h3 (* h5 h5) (* 
h6 h6 h6 h6) (* j2 j2 j2)) (* 70 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2
 j2)) (* 26 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) j2) (* 4 (* h2 h2 h2) h3 
(* h5 h5) (* h6 h6 h6 h6)) (* 6 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 
j2 j2 j2 j2 j2 j2)) (* 94 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 
j2 j2 j2)) (* 582 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) 
(* 1818 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 3068 (* h2
 h2) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 2832 (* h2 h2) (* h3 h3 h3
 h3) (* h4 h4 h4) h5 (* j2 j2)) (* 1344 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4 h4) 
h5 j2) (* 256 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4 h4) h5) (* 72 (* h2 h2) (* h3 
h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 816 (* h2 h2) (* h3 h3 
h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 3368 (* h2 h2) (* h3 h3 h3 h3)
 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 6368 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4
) (* h5 h5) (* j2 j2 j2)) (* 6048 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) 
(* j2 j2)) (* 2816 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) j2) (* 512 (* 
h2 h2) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5)) (* 18 (* h2 h2) (* h3 h3 h3 h3) (* 
h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 282 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4
) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 1746 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 h6
 (* j2 j2 j2 j2 j2)) (* 5454 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 
j2 j2)) (* 9204 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 8496 
(* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 4032 (* h2 h2) (* h3 h3 
h3 h3) (* h4 h4) h5 h6 j2) (* 768 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 h6) (* 
216 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 1512 (* h2 
h2) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 3312 (* h2 h2) (* h3 h3 
h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2)) (* 3232 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 
h5 h5) (* j2 j2)) (* 1472 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5 h5) j2) (* 256 
(* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5 h5)) (* 144 (* h2 h2) (* h3 h3 h3 h3) h4 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 1632 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 
h5) h6 (* j2 j2 j2 j2 j2)) (* 6736 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* 
j2 j2 j2 j2)) (* 12736 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) 
(* 12096 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 5632 (* h2 h2) 
(* h3 h3 h3 h3) h4 (* h5 h5) h6 j2) (* 1024 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 
h5) h6) (* 18 (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 282 (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
1746 (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 5454 (* h2
 h2) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 9204 (* h2 h2) (* h3 h3
 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 8496 (* h2 h2) (* h3 h3 h3 h3) h4 h5 
(* h6 h6) (* j2 j2)) (* 4032 (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* h6 h6) j2) (* 
768 (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* h6 h6)) (* 216 (* h2 h2) (* h3 h3 h3 h3) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 1512 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 
h5) h6 (* j2 j2 j2 j2)) (* 3312 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 
j2 j2)) (* 3232 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2)) (* 1472 (* 
h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) h6 j2) (* 256 (* h2 h2) (* h3 h3 h3 h3) (* 
h5 h5 h5) h6) (* 72 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2
 j2 j2)) (* 816 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)
) (* 3368 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 6368
 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 6048 (* h2 h2) 
(* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 2816 (* h2 h2) (* h3 h3 h3 h3)
 (* h5 h5) (* h6 h6) j2) (* 512 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6)) 
(* 6 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 94 
(* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 582 (* h2 h2
) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1818 (* h2 h2) (* h3 h3
 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 3068 (* h2 h2) (* h3 h3 h3 h3) h5 
(* h6 h6 h6) (* j2 j2 j2)) (* 2832 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* 
j2 j2)) (* 1344 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6 h6) j2) (* 256 (* h2 h2) 
(* h3 h3 h3 h3) h5 (* h6 h6 h6)) (* 6 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4 h4) h5 
(* j2 j2 j2 j2 j2 j2 j2)) (* 76 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 
j2 j2 j2 j2 j2)) (* 372 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2
 j2)) (* 912 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 1238 
(* h2 h2) (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2)) (* 948 (* h2 h2) (* h3 
h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2)) (* 384 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4 
h4) h5 j2) (* 64 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4 h4) h5) (* 18 (* h2 h2) (* 
h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 264 (* h2 h2) (* 
h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1416 (* h2 h2) (* h3 
h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 3628 (* h2 h2) (* h3 h3 h3)
 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 5014 (* h2 h2) (* h3 h3 h3) (* h4 h4
 h4) (* h5 h5) (* j2 j2 j2)) (* 3852 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* h5 
h5) (* j2 j2)) (* 1552 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) j2) (* 256 
(* h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5)) (* 24 (* h2 h2) (* h3 h3 h3) (* 
h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 304 (* h2 h2) (* h3 h3 h3) (* h4 h4
 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 1488 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5
 h6 (* j2 j2 j2 j2 j2)) (* 3648 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 
j2 j2 j2)) (* 4952 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 
3792 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2)) (* 1536 (* h2 h2) (* 
h3 h3 h3) (* h4 h4 h4) h5 h6 j2) (* 256 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 
h6) (* 144 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) 
(* 1200 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 
3568 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 5200 (* 
h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 4032 (* h2 h2) (* h3
 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 1600 (* h2 h2) (* h3 h3 h3) (* h4 
h4) (* h5 h5 h5) j2) (* 256 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5)) (* 54
 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 792 
(* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 4248 (* 
h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 10884 (* h2 h2
) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 15042 (* h2 h2) (* h3 
h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 11556 (* h2 h2) (* h3 h3 h3) (* 
h4 h4) (* h5 h5) h6 (* j2 j2)) (* 4656 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5
) h6 j2) (* 768 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6) (* 36 (* h2 h2) 
(* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 456 (* h2 h2) 
(* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2232 (* h2 h2) (* 
h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 5472 (* h2 h2) (* h3 h3 
h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 7428 (* h2 h2) (* h3 h3 h3) (* h4
 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 5688 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* 
h6 h6) (* j2 j2)) (* 2304 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) j2) (* 
384 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6)) (* 216 (* h2 h2) (* h3 h3 h3)
 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 864 (* h2 h2) (* h3 h3 h3) h4 (* h5 
h5 h5 h5) (* j2 j2 j2 j2)) (* 1368 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* 
j2 j2 j2)) (* 1072 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2)) (* 416 
(* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5 h5) j2) (* 64 (* h2 h2) (* h3 h3 h3) h4 
(* h5 h5 h5 h5)) (* 288 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2
 j2 j2)) (* 2400 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) 
(* 7136 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 10400 (* 
h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 8064 (* h2 h2) (* h3 h3 
h3) h4 (* h5 h5 h5) h6 (* j2 j2)) (* 3200 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5)
 h6 j2) (* 512 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) h6) (* 54 (* h2 h2) (* h3 
h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 792 (* h2 h2) (* h3 
h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4248 (* h2 h2) (* h3 h3 
h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 10884 (* h2 h2) (* h3 h3 h3) 
h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 15042 (* h2 h2) (* h3 h3 h3) h4 (* h5
 h5) (* h6 h6) (* j2 j2 j2)) (* 11556 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* h6 
h6) (* j2 j2)) (* 4656 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) j2) (* 768 
(* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6)) (* 24 (* h2 h2) (* h3 h3 h3) h4 
h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 304 (* h2 h2) (* h3 h3 h3) h4 h5 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1488 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 
h6 h6) (* j2 j2 j2 j2 j2)) (* 3648 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* 
j2 j2 j2 j2)) (* 4952 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2)) 
(* 3792 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2)) (* 1536 (* h2 h2) 
(* h3 h3 h3) h4 h5 (* h6 h6 h6) j2) (* 256 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6
 h6)) (* 216 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
864 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 1368 (* h2 h2)
 (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 1072 (* h2 h2) (* h3 h3 h3) 
(* h5 h5 h5 h5) h6 (* j2 j2)) (* 416 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) h6 
j2) (* 64 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) h6) (* 144 (* h2 h2) (* h3 h3 
h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1200 (* h2 h2) (* h3 h3 h3)
 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 3568 (* h2 h2) (* h3 h3 h3) (* h5
 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 5200 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2)) (* 4032 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) 
(* j2 j2)) (* 1600 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) j2) (* 256 (* 
h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6)) (* 18 (* h2 h2) (* h3 h3 h3) (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 264 (* h2 h2) (* h3 h3 h3) (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1416 (* h2 h2) (* h3 h3 h3) (* h5 h5)
 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 3628 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6
 h6 h6) (* j2 j2 j2 j2)) (* 5014 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2)) (* 3852 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2)) 
(* 1552 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) j2) (* 256 (* h2 h2) (* h3
 h3 h3) (* h5 h5) (* h6 h6 h6)) (* 6 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 76 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 372 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2
 j2)) (* 912 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 1238 
(* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 948 (* h2 h2) (* h3 
h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2)) (* 384 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 
h6 h6) j2) (* 64 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6 h6)) (* 12 (* h2 h2) (* 
h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 116 (* h2 h2) (* 
h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 432 (* h2 h2) (* h3 
h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 840 (* h2 h2) (* h3 h3) (* 
h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 940 (* h2 h2) (* h3 h3) (* h4 h4 h4 
h4) (* h5 h5) (* j2 j2 j2)) (* 612 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5)
 (* j2 j2)) (* 216 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) j2) (* 32 (* h2
 h2) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5)) (* 18 (* h2 h2) (* h3 h3) (* h4 h4 h4)
 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 210 (* h2 h2) (* h3 h3) (* h4 h4 h4) 
(* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 840 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* 
h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 1684 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5 
h5) (* j2 j2 j2 j2)) (* 1906 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2
 j2 j2)) (* 1242 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2)) (* 436
 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) j2) (* 64 (* h2 h2) (* h3 h3) (* 
h4 h4 h4) (* h5 h5 h5)) (* 48 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2)) (* 464 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2)) (* 1728 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* 3360 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 
j2)) (* 3760 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 2448
 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 864 (* h2 h2) (* h3
 h3) (* h4 h4 h4) (* h5 h5) h6 j2) (* 128 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5
 h5) h6) (* 72 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 
j2)) (* 384 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) 
(* 848 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 992 (* 
h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 648 (* h2 h2) (* h3 
h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 224 (* h2 h2) (* h3 h3) (* h4 h4) 
(* h5 h5 h5 h5) j2) (* 32 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5)) (* 54 
(* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 630 
(* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 2520 (* 
h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 5052 (* h2 h2)
 (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 5718 (* h2 h2) (* h3 h3
) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 3726 (* h2 h2) (* h3 h3) (* h4 h4) 
(* h5 h5 h5) h6 (* j2 j2)) (* 1308 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6
 j2) (* 192 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6) (* 72 (* h2 h2) (* h3
 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 696 (* h2 h2) 
(* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2592 (* h2 h2)
 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 5040 (* h2 h2) 
(* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 5640 (* h2 h2) (* h3
 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 3672 (* h2 h2) (* h3 h3) (* 
h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 1296 (* h2 h2) (* h3 h3) (* h4 h4) (* 
h5 h5) (* h6 h6) j2) (* 192 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6)) 
(* 144 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 768 
(* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 1696 (* h2 h2) 
(* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 1984 (* h2 h2) (* h3 h3) h4 
(* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 1296 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) 
h6 (* j2 j2)) (* 448 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) h6 j2) (* 64 (* h2 
h2) (* h3 h3) h4 (* h5 h5 h5 h5) h6) (* 54 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 630 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2520 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2)) (* 5052 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6)
 (* j2 j2 j2 j2)) (* 5718 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2
 j2)) (* 3726 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 1308 
(* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) j2) (* 192 (* h2 h2) (* h3 h3) h4 
(* h5 h5 h5) (* h6 h6)) (* 48 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 464 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 1728 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2)) (* 3360 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2)) (* 3760 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 2448
 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 864 (* h2 h2) (* h3
 h3) h4 (* h5 h5) (* h6 h6 h6) j2) (* 128 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6
 h6 h6)) (* 72 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 384 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 848 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 992 (* 
h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 648 (* h2 h2) (* h3 
h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 224 (* h2 h2) (* h3 h3) (* h5 h5 h5 
h5) (* h6 h6) j2) (* 32 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6)) (* 18 (* 
h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 210 (* 
h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 840 (* h2 
h2) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1684 (* h2 h2) 
(* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1906 (* h2 h2) (* h3 h3)
 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 1242 (* h2 h2) (* h3 h3) (* h5 h5 h5
) (* h6 h6 h6) (* j2 j2)) (* 436 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) 
j2) (* 64 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6)) (* 12 (* h2 h2) (* h3 
h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 116 (* h2 h2) (* h3 
h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 432 (* h2 h2) (* h3 h3) 
(* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 840 (* h2 h2) (* h3 h3) (* h5 
h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 940 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 
h6 h6 h6) (* j2 j2 j2)) (* 612 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* 
j2 j2)) (* 216 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) j2) (* 32 (* h2 h2)
 (* h3 h3) (* h5 h5) (* h6 h6 h6 h6)) (* 6 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5
 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 40 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2)) (* 114 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2
 j2 j2 j2)) (* 180 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) 
(* 170 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 96 (* h2 h2) 
h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2)) (* 30 (* h2 h2) h3 (* h4 h4 h4 h4) 
(* h5 h5 h5) j2) (* 4 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5 h5)) (* 6 (* h2 h2) 
h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 40 (* h2 h2) h3 (* 
h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 114 (* h2 h2) h3 (* h4 h4 h4
) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 180 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 
h5 h5) (* j2 j2 j2 j2)) (* 170 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 
j2 j2)) (* 96 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 30 (* h2 
h2) h3 (* h4 h4 h4) (* h5 h5 h5 h5) j2) (* 4 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 
h5 h5)) (* 24 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)
) (* 160 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 456
 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 720 (* h2 h2) 
h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 680 (* h2 h2) h3 (* h4 h4 h4
) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 384 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) h6
 (* j2 j2)) (* 120 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) h6 j2) (* 16 (* h2 h2)
 h3 (* h4 h4 h4) (* h5 h5 h5) h6) (* 18 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 120 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 342 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2
 j2 j2 j2)) (* 540 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) 
(* 510 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 288 (* h2 h2) 
h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 90 (* h2 h2) h3 (* h4 h4) (* h5 h5
 h5 h5) h6 j2) (* 12 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) h6) (* 36 (* h2 h2) 
h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 240 (* h2 h2) 
h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 684 (* h2 h2) h3 
(* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1080 (* h2 h2) h3 (* h4 
h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 1020 (* h2 h2) h3 (* h4 h4) (* h5
 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 576 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* h6
 h6) (* j2 j2)) (* 180 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) j2) (* 24 
(* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6)) (* 18 (* h2 h2) h3 h4 (* h5 h5 h5
 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 120 (* h2 h2) h3 h4 (* h5 h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 342 (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* h6 h6
) (* j2 j2 j2 j2 j2)) (* 540 (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2)) (* 510 (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 288 
(* h2 h2) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 90 (* h2 h2) h3 h4 (* h5
 h5 h5 h5) (* h6 h6) j2) (* 12 (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* h6 h6)) (* 24 
(* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 160 (* h2
 h2) h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 456 (* h2 h2) h3 
h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 720 (* h2 h2) h3 h4 (* h5 h5
 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 680 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6 
h6) (* j2 j2 j2)) (* 384 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) 
(* 120 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6 h6) j2) (* 16 (* h2 h2) h3 h4 (* h5
 h5 h5) (* h6 h6 h6)) (* 6 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2
 j2 j2 j2 j2)) (* 40 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2
 j2)) (* 114 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
180 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 170 (* h2 h2) 
h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 96 (* h2 h2) h3 (* h5 h5 h5 h5)
 (* h6 h6 h6) (* j2 j2)) (* 30 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6 h6) j2) (* 
4 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6 h6)) (* 6 (* h2 h2) h3 (* h5 h5 h5) (* 
h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 40 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 114 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2)) (* 180 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2
 j2)) (* 170 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 96 (* h2
 h2) h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 30 (* h2 h2) h3 (* h5 h5 h5) 
(* h6 h6 h6 h6) j2) (* 4 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6 h6)) (* 36 h2 (* 
h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 444 h2 (* h3 h3
 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2092 h2 (* h3 h3 h3 h3)
 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 4868 h2 (* h3 h3 h3 h3) (* h4 h4 
h4) (* h5 h5) (* j2 j2 j2 j2)) (* 6208 h2 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5)
 (* j2 j2 j2)) (* 4432 h2 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 
1664 h2 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) j2) (* 256 h2 (* h3 h3 h3 h3) (* 
h4 h4 h4) (* h5 h5)) (* 216 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 
j2 j2 j2 j2)) (* 1728 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 
j2)) (* 4824 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 6544 
h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 4704 h2 (* h3 h3 h3 
h3) (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 1728 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5
 h5 h5) j2) (* 256 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5)) (* 108 h2 (* h3 h3
 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1332 h2 (* h3 h3 h3 
h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 6276 h2 (* h3 h3 h3 h3) (* 
h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 14604 h2 (* h3 h3 h3 h3) (* h4 h4) 
(* h5 h5) h6 (* j2 j2 j2 j2)) (* 18624 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6
 (* j2 j2 j2)) (* 13296 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 
4992 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 j2) (* 768 h2 (* h3 h3 h3 h3) (* 
h4 h4) (* h5 h5) h6) (* 432 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2
 j2 j2)) (* 3456 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
9648 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 13088 h2 (* h3 h3
 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 9408 h2 (* h3 h3 h3 h3) h4 (* h5 h5 
h5) h6 (* j2 j2)) (* 3456 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 j2) (* 512 h2 
(* h3 h3 h3 h3) h4 (* h5 h5 h5) h6) (* 108 h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6
 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1332 h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6)
 (* j2 j2 j2 j2 j2 j2)) (* 6276 h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2)) (* 14604 h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)
) (* 18624 h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 13296 h2 
(* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 4992 h2 (* h3 h3 h3 h3) h4 
(* h5 h5) (* h6 h6) j2) (* 768 h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6)) (* 216
 h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1728 h2 (* 
h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 4824 h2 (* h3 h3 h3 
h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 6544 h2 (* h3 h3 h3 h3) (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2)) (* 4704 h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) 
(* j2 j2)) (* 1728 h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) j2) (* 256 h2 (* h3
 h3 h3 h3) (* h5 h5 h5) (* h6 h6)) (* 36 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 444 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 2092 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2)) (* 4868 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2))
 (* 6208 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 4432 h2 (* 
h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 1664 h2 (* h3 h3 h3 h3) (* h5 
h5) (* h6 h6 h6) j2) (* 256 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6)) (* 36 h2 
(* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 336 h2 (* h3
 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1192 h2 (* h3 h3 h3)
 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 2192 h2 (* h3 h3 h3) (* h4 h4 
h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 2308 h2 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 
h5) (* j2 j2 j2)) (* 1408 h2 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2)) 
(* 464 h2 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) j2) (* 64 h2 (* h3 h3 h3) (* h4
 h4 h4 h4) (* h5 h5)) (* 72 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 
j2 j2 j2 j2 j2)) (* 672 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2
 j2 j2)) (* 2384 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) 
(* 4384 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 4616 h2 
(* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 2816 h2 (* h3 h3 h3) (* 
h4 h4 h4) (* h5 h5 h5) (* j2 j2)) (* 928 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 
h5) j2) (* 128 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5)) (* 144 h2 (* h3 h3 h3)
 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1344 h2 (* h3 h3 h3) (* 
h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 4768 h2 (* h3 h3 h3) (* h4 h4 
h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 8768 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 
h5) h6 (* j2 j2 j2 j2)) (* 9232 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 
j2 j2)) (* 5632 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 1856 h2 
(* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 j2) (* 256 h2 (* h3 h3 h3) (* h4 h4 h4) 
(* h5 h5) h6) (* 216 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2
 j2)) (* 1080 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 
2232 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 2440 h2 (* h3
 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 1488 h2 (* h3 h3 h3) (* h4 h4
) (* h5 h5 h5 h5) (* j2 j2)) (* 480 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) j2
) (* 64 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5)) (* 216 h2 (* h3 h3 h3) (* h4 
h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2016 h2 (* h3 h3 h3) (* h4 h4) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 7152 h2 (* h3 h3 h3) (* h4 h4) (* h5 
h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 13152 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6
 (* j2 j2 j2 j2)) (* 13848 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2
)) (* 8448 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 2784 h2 (* h3
 h3 h3) (* h4 h4) (* h5 h5 h5) h6 j2) (* 384 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 
h5) h6) (* 216 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 2016 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 7152 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 13152 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 13848
 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 8448 h2 (* h3 h3
 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 2784 h2 (* h3 h3 h3) (* h4 h4) 
(* h5 h5) (* h6 h6) j2) (* 384 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6)) 
(* 432 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 2160 h2 
(* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 4464 h2 (* h3 h3 h3) 
h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 4880 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5
) h6 (* j2 j2 j2)) (* 2976 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 
960 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 j2) (* 128 h2 (* h3 h3 h3) h4 (* h5 h5
 h5 h5) h6) (* 216 h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 2016 h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2))
 (* 7152 h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 13152 
h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 13848 h2 (* h3 h3 
h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 8448 h2 (* h3 h3 h3) h4 (* h5 h5 
h5) (* h6 h6) (* j2 j2)) (* 2784 h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) j2) 
(* 384 h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6)) (* 144 h2 (* h3 h3 h3) h4 (* 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1344 h2 (* h3 h3 h3) h4 (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4768 h2 (* h3 h3 h3) h4 (* h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 8768 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2)) (* 9232 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2))
 (* 5632 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 1856 h2 (* h3 
h3 h3) h4 (* h5 h5) (* h6 h6 h6) j2) (* 256 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 
h6 h6)) (* 216 h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 1080 h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2232 h2
 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 2440 h2 (* h3 h3 h3)
 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 1488 h2 (* h3 h3 h3) (* h5 h5 h5 h5)
 (* h6 h6) (* j2 j2)) (* 480 h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) j2) (* 64
 h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6)) (* 72 h2 (* h3 h3 h3) (* h5 h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 672 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6
 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2384 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6)
 (* j2 j2 j2 j2 j2)) (* 4384 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2)) (* 4616 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 2816 
h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 928 h2 (* h3 h3 h3) (* 
h5 h5 h5) (* h6 h6 h6) j2) (* 128 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6)) (* 
36 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 336 h2
 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1192 h2 (* h3 
h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2192 h2 (* h3 h3 h3) (* 
h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 2308 h2 (* h3 h3 h3) (* h5 h5) (* h6 
h6 h6 h6) (* j2 j2 j2)) (* 1408 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 
j2)) (* 464 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) j2) (* 64 h2 (* h3 h3 h3) 
(* h5 h5) (* h6 h6 h6 h6)) (* 36 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2
 j2 j2 j2 j2 j2 j2)) (* 228 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 
j2 j2 j2 j2)) (* 616 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2
)) (* 920 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 820 h2 
(* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 436 h2 (* h3 h3) (* h4 
h4 h4 h4) (* h5 h5 h5) (* j2 j2)) (* 128 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 
h5) j2) (* 16 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5)) (* 36 h2 (* h3 h3) (* 
h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 228 h2 (* h3 h3) (* h4 h4
 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 616 h2 (* h3 h3) (* h4 h4 h4) (* 
h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 920 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5
) (* j2 j2 j2 j2)) (* 820 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)
) (* 436 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 128 h2 (* h3 h3
) (* h4 h4 h4) (* h5 h5 h5 h5) j2) (* 16 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 
h5)) (* 144 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 912 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 2464 
h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 3680 h2 (* h3 
h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 3280 h2 (* h3 h3) (* h4 h4 
h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 1744 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5)
 h6 (* j2 j2)) (* 512 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 j2) (* 64 h2 (* 
h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6) (* 108 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 684 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2)) (* 1848 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2)) (* 2760 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 
j2)) (* 2460 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 1308 h2 
(* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 384 h2 (* h3 h3) (* h4 h4) 
(* h5 h5 h5 h5) h6 j2) (* 48 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6) (* 216 
h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1368 
h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3696 h2 
(* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 5520 h2 (* h3 
h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 4920 h2 (* h3 h3) (* h4
 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 2616 h2 (* h3 h3) (* h4 h4) (* h5 
h5 h5) (* h6 h6) (* j2 j2)) (* 768 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6)
 j2) (* 96 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6)) (* 108 h2 (* h3 h3) h4
 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 684 h2 (* h3 h3) h4 (* 
h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1848 h2 (* h3 h3) h4 (* h5 h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2760 h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2)) (* 2460 h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 
j2 j2)) (* 1308 h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 384 h2 
(* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) j2) (* 48 h2 (* h3 h3) h4 (* h5 h5 h5 h5)
 (* h6 h6)) (* 144 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 912 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 2464 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 3680 h2
 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 3280 h2 (* h3 h3) h4
 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 1744 h2 (* h3 h3) h4 (* h5 h5 h5) 
(* h6 h6 h6) (* j2 j2)) (* 512 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) j2) (* 
64 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6)) (* 36 h2 (* h3 h3) (* h5 h5 h5 h5)
 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 228 h2 (* h3 h3) (* h5 h5 h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 616 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6
) (* j2 j2 j2 j2 j2)) (* 920 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2)) (* 820 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 436 h2
 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 128 h2 (* h3 h3) (* h5 h5 
h5 h5) (* h6 h6 h6) j2) (* 16 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6)) (* 36 
h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 228 h2 
(* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 616 h2 (* h3 h3
) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 920 h2 (* h3 h3) (* h5 h5 
h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 820 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 
h6 h6) (* j2 j2 j2)) (* 436 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2))
 (* 128 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) j2) (* 16 h2 (* h3 h3) (* h5 
h5 h5) (* h6 h6 h6 h6))) 0)))
(check-sat)
(exit)

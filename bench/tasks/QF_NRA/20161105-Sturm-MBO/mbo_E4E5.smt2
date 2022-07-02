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
(set-info :instance |E4E5|)
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
(+ (* 2 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 
28 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2 j2 j2)) (* 144 (* h1
 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2 j2)) (* 372 (* h1 h1 h1 h1) 
(* h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2)) (* 534 (* h1 h1 h1 h1) (* h2 h2 h2) 
(* h3 h3) h5 (* j2 j2 j2)) (* 432 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* 
j2 j2)) (* 184 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 j2) (* 32 (* h1 h1 h1 
h1) (* h2 h2 h2) (* h3 h3) h5) (* 4 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 36 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h6 (* j2 
j2 j2 j2 j2 j2)) (* 132 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h6 (* j2 j2 j2 j2
 j2)) (* 252 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h6 (* j2 j2 j2 j2)) (* 264 
(* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h6 (* j2 j2 j2)) (* 144 (* h1 h1 h1 h1) 
(* h2 h2 h2) (* h3 h3) h6 (* j2 j2)) (* 32 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3
) h6 j2) (* (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 13 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 60 (* 
h1 h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 138 (* h1 h1 h1 h1
) (* h2 h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2)) (* 177 (* h1 h1 h1 h1) (* h2 h2 h2)
 h3 (* h5 h5) (* j2 j2 j2)) (* 129 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* 
j2 j2)) (* 50 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) j2) (* 8 (* h1 h1 h1 h1)
 (* h2 h2 h2) h3 (* h5 h5)) (* 3 (* h1 h1 h1 h1) (* h2 h2 h2) h3 h5 h6 (* j2 j2 
j2 j2 j2 j2 j2)) (* 24 (* h1 h1 h1 h1) (* h2 h2 h2) h3 h5 h6 (* j2 j2 j2 j2 j2 
j2)) (* 78 (* h1 h1 h1 h1) (* h2 h2 h2) h3 h5 h6 (* j2 j2 j2 j2 j2)) (* 132 (* 
h1 h1 h1 h1) (* h2 h2 h2) h3 h5 h6 (* j2 j2 j2 j2)) (* 123 (* h1 h1 h1 h1) (* h2
 h2 h2) h3 h5 h6 (* j2 j2 j2)) (* 60 (* h1 h1 h1 h1) (* h2 h2 h2) h3 h5 h6 (* j2
 j2)) (* 12 (* h1 h1 h1 h1) (* h2 h2 h2) h3 h5 h6 j2) (* 2 (* h1 h1 h1 h1) (* h2
 h2 h2) h3 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 14 (* h1 h1 h1 h1) (* h2 h2 h2
) h3 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 38 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* 
h6 h6) (* j2 j2 j2 j2 j2)) (* 50 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6) (* j2
 j2 j2 j2)) (* 32 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6) (* j2 j2 j2)) (* 8 
(* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6) (* j2 j2)) (* (* h1 h1 h1 h1) (* h2 h2
 h2) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 8 (* h1 h1 h1 h1) (* h2 h2 h2) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 27 (* h1 h1 h1 h1) (* h2 h2 h2) (* h5 h5)
 h6 (* j2 j2 j2 j2 j2)) (* 50 (* h1 h1 h1 h1) (* h2 h2 h2) (* h5 h5) h6 (* j2 j2
 j2 j2)) (* 55 (* h1 h1 h1 h1) (* h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2)) (* 36 (* 
h1 h1 h1 h1) (* h2 h2 h2) (* h5 h5) h6 (* j2 j2)) (* 13 (* h1 h1 h1 h1) (* h2 h2
 h2) (* h5 h5) h6 j2) (* 2 (* h1 h1 h1 h1) (* h2 h2 h2) (* h5 h5) h6) (* (* h1 
h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 7 (* h1 h1 h1 
h1) (* h2 h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 20 (* h1 h1 h1 h1) (* h2
 h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 30 (* h1 h1 h1 h1) (* h2 h2 h2) h5 
(* h6 h6) (* j2 j2 j2 j2)) (* 25 (* h1 h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6) (* j2
 j2 j2)) (* 11 (* h1 h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6) (* j2 j2)) (* 2 (* h1 
h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6) j2) (* 4 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 
h3) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 68 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3)
 h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 460 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 
(* j2 j2 j2 j2 j2 j2)) (* 1660 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* j2 
j2 j2 j2 j2)) (* 3536 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2))
 (* 4576 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2)) (* 3520 (* h1 
h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* j2 j2)) (* 1472 (* h1 h1 h1 h1) (* h2 h2)
 (* h3 h3 h3) h5 j2) (* 256 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5) (* 8 (* 
h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 96 (* h1 
h1 h1 h1) (* h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 488 (* h1 h1 h1
 h1) (* h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2 j2 j2 j2)) (* 1360 (* h1 h1 h1 h1) 
(* h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2 j2 j2)) (* 2240 (* h1 h1 h1 h1) (* h2 h2) 
(* h3 h3 h3) h6 (* j2 j2 j2 j2)) (* 2176 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) 
h6 (* j2 j2 j2)) (* 1152 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h6 (* j2 j2)) 
(* 256 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h6 j2) (* 6 (* h1 h1 h1 h1) (* h2 
h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 80 (* h1 h1 h1 h1) (* h2 h2) 
(* h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 400 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3
) h4 h5 (* j2 j2 j2 j2 j2)) (* 1008 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 
(* j2 j2 j2 j2)) (* 1402 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2))
 (* 1080 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* j2 j2)) (* 424 (* h1 h1 h1
 h1) (* h2 h2) (* h3 h3) h4 h5 j2) (* 64 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 
h5) (* 12 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 108 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2)) (* 396 
(* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 756 (* h1 h1 h1
 h1) (* h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 792 (* h1 h1 h1 h1) (* h2 h2)
 (* h3 h3) h4 h6 (* j2 j2 j2)) (* 432 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h6 
(* j2 j2)) (* 96 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h6 j2) (* 4 (* h1 h1 h1 
h1) (* h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 62 (* h1 h1 h1
 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 371 (* h1 h1 h1 
h1) (* h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1161 (* h1 h1 h1 h1)
 (* h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 2103 (* h1 h1 h1 h1) (* h2
 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 2265 (* h1 h1 h1 h1) (* h2 h2) (* 
h3 h3) (* h5 h5) (* j2 j2 j2)) (* 1418 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h5
 h5) (* j2 j2)) (* 472 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) j2) (* 64 
(* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5)) (* 8 (* h1 h1 h1 h1) (* h2 h2) 
(* h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 96 (* h1 h1 h1 h1) (* h2 h2) (* 
h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 498 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3
) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 1420 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h5 h6
 (* j2 j2 j2 j2 j2)) (* 2378 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h5 h6 (* j2 j2 
j2 j2)) (* 2344 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2)) (* 1296 
(* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h5 h6 (* j2 j2)) (* 352 (* h1 h1 h1 h1) (* 
h2 h2) (* h3 h3) h5 h6 j2) (* 32 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h5 h6) (* 8
 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
88 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
400 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 968 
(* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1336 (* h1 
h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 1040 (* h1 h1 h1 h1)
 (* h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2)) (* 416 (* h1 h1 h1 h1) (* h2 h2) 
(* h3 h3) (* h6 h6) (* j2 j2)) (* 64 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 
h6) j2) (* 3 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2))
 (* 37 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 165 
(* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 361 (* h1 h1 h1
 h1) (* h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2)) (* 424 (* h1 h1 h1 h1) (* h2 h2)
 h3 h4 (* h5 h5) (* j2 j2 j2)) (* 266 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) 
(* j2 j2)) (* 80 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) j2) (* 8 (* h1 h1 h1 
h1) (* h2 h2) h3 h4 (* h5 h5)) (* 11 (* h1 h1 h1 h1) (* h2 h2) h3 h4 h5 h6 (* j2
 j2 j2 j2 j2 j2 j2)) (* 86 (* h1 h1 h1 h1) (* h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2 
j2 j2)) (* 270 (* h1 h1 h1 h1) (* h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 432 
(* h1 h1 h1 h1) (* h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2)) (* 367 (* h1 h1 h1 h1) 
(* h2 h2) h3 h4 h5 h6 (* j2 j2 j2)) (* 154 (* h1 h1 h1 h1) (* h2 h2) h3 h4 h5 h6
 (* j2 j2)) (* 24 (* h1 h1 h1 h1) (* h2 h2) h3 h4 h5 h6 j2) (* 6 (* h1 h1 h1 h1)
 (* h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 42 (* h1 h1 h1 h1) (* h2
 h2) h3 h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 114 (* h1 h1 h1 h1) (* h2 h2) h3 
h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 150 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6
) (* j2 j2 j2 j2)) (* 96 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2))
 (* 24 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6) (* j2 j2)) (* (* h1 h1 h1 h1) 
(* h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 15 (* h1 h1 h1 h1) (* 
h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 85 (* h1 h1 h1 h1) (* h2 h2)
 h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 246 (* h1 h1 h1 h1) (* h2 h2) h3 (* 
h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 405 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) 
(* j2 j2 j2 j2)) (* 393 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2)) 
(* 221 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* j2 j2)) (* 66 (* h1 h1 h1 h1
) (* h2 h2) h3 (* h5 h5 h5) j2) (* 8 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5)) 
(* 4 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
45 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 214 
(* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 551 (* h1 h1
 h1 h1) (* h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 827 (* h1 h1 h1 h1) (* 
h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 730 (* h1 h1 h1 h1) (* h2 h2) h3 (* 
h5 h5) h6 (* j2 j2 j2)) (* 363 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5) h6 (* j2 
j2)) (* 90 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5) h6 j2) (* 8 (* h1 h1 h1 h1) 
(* h2 h2) h3 (* h5 h5) h6) (* 5 (* h1 h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 50 (* h1 h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 201 (* h1 h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2
 j2 j2)) (* 417 (* h1 h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 476 (* h1 h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 293 (* h1 
h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2)) (* 86 (* h1 h1 h1 h1) (* h2 h2
) h3 h5 (* h6 h6) (* j2 j2)) (* 8 (* h1 h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6) j2) 
(* 2 (* h1 h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
18 (* h1 h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 64 (* 
h1 h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 114 (* h1 h1 h1
 h1) (* h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 106 (* h1 h1 h1 h1) (* h2 
h2) h3 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 48 (* h1 h1 h1 h1) (* h2 h2) h3 (* h6 h6
 h6) (* j2 j2 j2)) (* 8 (* h1 h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6) (* j2 j2)) (* 
3 (* h1 h1 h1 h1) (* h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 23 (* 
h1 h1 h1 h1) (* h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 72 (* h1 h1 h1 
h1) (* h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 119 (* h1 h1 h1 h1) (* h2 
h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 112 (* h1 h1 h1 h1) (* h2 h2) h4 (* h5 
h5) h6 (* j2 j2 j2)) (* 60 (* h1 h1 h1 h1) (* h2 h2) h4 (* h5 h5) h6 (* j2 j2)) 
(* 17 (* h1 h1 h1 h1) (* h2 h2) h4 (* h5 h5) h6 j2) (* 2 (* h1 h1 h1 h1) (* h2 
h2) h4 (* h5 h5) h6) (* 3 (* h1 h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 20 (* h1 h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 53 (* h1 h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 72 
(* h1 h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 54 (* h1 h1 h1 h1)
 (* h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 22 (* h1 h1 h1 h1) (* h2 h2) h4 h5 
(* h6 h6) (* j2 j2)) (* 4 (* h1 h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6) j2) (* (* h1
 h1 h1 h1) (* h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 10 (* h1 h1
 h1 h1) (* h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 42 (* h1 h1 h1 h1
) (* h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 97 (* h1 h1 h1 h1) (* h2 
h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 135 (* h1 h1 h1 h1) (* h2 h2) (* h5 
h5 h5) h6 (* j2 j2 j2 j2)) (* 116 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5 h5) h6 (* 
j2 j2 j2)) (* 60 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5 h5) h6 (* j2 j2)) (* 17 (* 
h1 h1 h1 h1) (* h2 h2) (* h5 h5 h5) h6 j2) (* 2 (* h1 h1 h1 h1) (* h2 h2) (* h5 
h5 h5) h6) (* 2 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 19 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2)) (* 74 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 154 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 186 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 131 (* 
h1 h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 50 (* h1 h1 h1 h1) 
(* h2 h2) (* h5 h5) (* h6 h6) (* j2 j2)) (* 8 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5
) (* h6 h6) j2) (* (* h1 h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 9 (* h1 h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 33 (* h1 h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
64 (* h1 h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 71 (* h1 h1 
h1 h1) (* h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 45 (* h1 h1 h1 h1) (* h2 h2
) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 15 (* h1 h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6) 
(* j2 j2)) (* 2 (* h1 h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6) j2) (* 8 (* h1 h1 h1 
h1) h2 (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 128 (* h1 h1 h1 h1) h2
 (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 832 (* h1 h1 h1 h1) h2 (* h3 h3
 h3) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 2904 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h5 
(* j2 j2 j2 j2 j2)) (* 5968 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2
)) (* 7360 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h5 (* j2 j2 j2)) (* 5248 (* h1 h1 
h1 h1) h2 (* h3 h3 h3) h4 h5 (* j2 j2)) (* 1920 (* h1 h1 h1 h1) h2 (* h3 h3 h3) 
h4 h5 j2) (* 256 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h5) (* 16 (* h1 h1 h1 h1) h2
 (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 192 (* h1 h1 h1 h1) h2 (* h3
 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 976 (* h1 h1 h1 h1) h2 (* h3 h3 h3) 
h4 h6 (* j2 j2 j2 j2 j2 j2)) (* 2720 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h6 (* j2
 j2 j2 j2 j2)) (* 4480 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2)) 
(* 4352 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h6 (* j2 j2 j2)) (* 2304 (* h1 h1 h1 
h1) h2 (* h3 h3 h3) h4 h6 (* j2 j2)) (* 512 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 
h6 j2) (* 2 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2
 j2)) (* 42 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 364 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 1714 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 4834
 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 8444 (* h1 h1 
h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 9080 (* h1 h1 h1 h1) h2 (* 
h3 h3 h3) (* h5 h5) (* j2 j2 j2)) (* 5744 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h5 
h5) (* j2 j2)) (* 1920 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) j2) (* 256 (* 
h1 h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5)) (* 28 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h5
 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 352 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h5 h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 1848 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h5 h6 (* j2 j2
 j2 j2 j2 j2)) (* 5236 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2))
 (* 8608 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 8160 (* h1 h1
 h1 h1) h2 (* h3 h3 h3) h5 h6 (* j2 j2 j2)) (* 4096 (* h1 h1 h1 h1) h2 (* h3 h3 
h3) h5 h6 (* j2 j2)) (* 832 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h5 h6 j2) (* 8 (* h1
 h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 112 (* 
h1 h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 672 (* h1
 h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2248 (* h1 h1 
h1 h1) h2 (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4560 (* h1 h1 h1 h1) 
h2 (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 5696 (* h1 h1 h1 h1) h2 (* h3 
h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 4224 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h6 
h6) (* j2 j2 j2)) (* 1664 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6) (* j2 j2)) 
(* 256 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6) j2) (* 6 (* h1 h1 h1 h1) h2 (* 
h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 76 (* h1 h1 h1 h1) h2 (* h3 h3)
 (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 368 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 
h4) h5 (* j2 j2 j2 j2 j2)) (* 900 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* 
j2 j2 j2 j2)) (* 1202 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* j2 j2 j2)) 
(* 864 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* j2 j2)) (* 296 (* h1 h1 h1 
h1) h2 (* h3 h3) (* h4 h4) h5 j2) (* 32 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) 
h5) (* 12 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 108 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 396 
(* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 756 (* h1 h1 h1
 h1) h2 (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2)) (* 792 (* h1 h1 h1 h1) h2 (* h3 
h3) (* h4 h4) h6 (* j2 j2 j2)) (* 432 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h6 
(* j2 j2)) (* 96 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h6 j2) (* 8 (* h1 h1 h1 
h1) h2 (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 118 (* h1 h1 h1 h1
) h2 (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 692 (* h1 h1 h1 h1) h2 
(* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2130 (* h1 h1 h1 h1) h2 (* h3 
h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 3754 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* 
h5 h5) (* j2 j2 j2 j2)) (* 3838 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* j2 
j2 j2)) (* 2184 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* j2 j2)) (* 616 (* 
h1 h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) j2) (* 64 (* h1 h1 h1 h1) h2 (* h3 h3) h4
 (* h5 h5)) (* 24 (* h1 h1 h1 h1) h2 (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 280 (* h1 h1 h1 h1) h2 (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
1396 (* h1 h1 h1 h1) h2 (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 3812 (* h1 
h1 h1 h1) h2 (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 6112 (* h1 h1 h1 h1) h2 
(* h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 5760 (* h1 h1 h1 h1) h2 (* h3 h3) h4 h5 
h6 (* j2 j2 j2)) (* 3024 (* h1 h1 h1 h1) h2 (* h3 h3) h4 h5 h6 (* j2 j2)) (* 768
 (* h1 h1 h1 h1) h2 (* h3 h3) h4 h5 h6 j2) (* 64 (* h1 h1 h1 h1) h2 (* h3 h3) h4
 h5 h6) (* 16 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 176 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 800 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1936 
(* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2672 (* h1 h1 
h1 h1) h2 (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 2080 (* h1 h1 h1 h1) h2 (* 
h3 h3) h4 (* h6 h6) (* j2 j2 j2)) (* 832 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h6 
h6) (* j2 j2)) (* 128 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6) j2) (* (* h1 h1 
h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 20 (* h1 h1 
h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 162 (* h1 h1 h1
 h1) h2 (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 696 (* h1 h1 h1 h1) 
h2 (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1738 (* h1 h1 h1 h1) h2 (* 
h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 2594 (* h1 h1 h1 h1) h2 (* h3 h3) (* 
h5 h5 h5) (* j2 j2 j2 j2)) (* 2295 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* 
j2 j2 j2)) (* 1158 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* j2 j2)) (* 304 
(* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) j2) (* 32 (* h1 h1 h1 h1) h2 (* h3 h3)
 (* h5 h5 h5)) (* (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2
 j2 j2 j2)) (* 44 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 414 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2)) (* 1800 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 4354 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 6222 
(* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 5271 (* h1 h1 h1 
h1) h2 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 2550 (* h1 h1 h1 h1) h2 (* h3 h3)
 (* h5 h5) h6 (* j2 j2)) (* 640 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5) h6 j2) 
(* 64 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5) h6) (* 8 (* h1 h1 h1 h1) h2 (* h3 
h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 110 (* h1 h1 h1 h1) h2 (* h3
 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 662 (* h1 h1 h1 h1) h2 (* h3 
h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2246 (* h1 h1 h1 h1) h2 (* h3 h3) 
h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4630 (* h1 h1 h1 h1) h2 (* h3 h3) h5 (* 
h6 h6) (* j2 j2 j2 j2 j2)) (* 5870 (* h1 h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6) (* 
j2 j2 j2 j2)) (* 4462 (* h1 h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6) (* j2 j2 j2)) 
(* 1912 (* h1 h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6) (* j2 j2)) (* 408 (* h1 h1 h1 
h1) h2 (* h3 h3) h5 (* h6 h6) j2) (* 32 (* h1 h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6
)) (* 4 (* h1 h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 52 (* h1 h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 284 (* h1 h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
844 (* h1 h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1476 (* 
h1 h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1532 (* h1 h1 h1 
h1) h2 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 904 (* h1 h1 h1 h1) h2 (* h3 
h3) (* h6 h6 h6) (* j2 j2 j2)) (* 272 (* h1 h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6) 
(* j2 j2)) (* 32 (* h1 h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6) j2) (* 3 (* h1 h1 h1 
h1) h2 h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 35 (* h1 h1 h1 h1) h2
 h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 150 (* h1 h1 h1 h1) h2 h3 (* 
h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 310 (* h1 h1 h1 h1) h2 h3 (* h4 h4) (* 
h5 h5) (* j2 j2 j2 j2)) (* 327 (* h1 h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* j2 
j2 j2)) (* 165 (* h1 h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* j2 j2)) (* 30 (* h1 
h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) j2) (* 13 (* h1 h1 h1 h1) h2 h3 (* h4 h4) h5
 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 100 (* h1 h1 h1 h1) h2 h3 (* h4 h4) h5 h6 (* j2
 j2 j2 j2 j2 j2)) (* 306 (* h1 h1 h1 h1) h2 h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2
)) (* 468 (* h1 h1 h1 h1) h2 h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 365 (* h1 h1
 h1 h1) h2 h3 (* h4 h4) h5 h6 (* j2 j2 j2)) (* 128 (* h1 h1 h1 h1) h2 h3 (* h4 
h4) h5 h6 (* j2 j2)) (* 12 (* h1 h1 h1 h1) h2 h3 (* h4 h4) h5 h6 j2) (* 6 (* h1 
h1 h1 h1) h2 h3 (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 42 (* h1 h1 h1 
h1) h2 h3 (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 114 (* h1 h1 h1 h1) h2 
h3 (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 150 (* h1 h1 h1 h1) h2 h3 (* h4 h4
) (* h6 h6) (* j2 j2 j2 j2)) (* 96 (* h1 h1 h1 h1) h2 h3 (* h4 h4) (* h6 h6) (* 
j2 j2 j2)) (* 24 (* h1 h1 h1 h1) h2 h3 (* h4 h4) (* h6 h6) (* j2 j2)) (* 2 (* h1
 h1 h1 h1) h2 h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 28 (* h1 h1 h1 
h1) h2 h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 151 (* h1 h1 h1 h1) h2 h3
 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 411 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5
 h5) (* j2 j2 j2 j2 j2)) (* 610 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5 h5) (* j2 j2 
j2 j2)) (* 491 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5 h5) (* j2 j2 j2)) (* 197 (* h1 
h1 h1 h1) h2 h3 h4 (* h5 h5 h5) (* j2 j2)) (* 30 (* h1 h1 h1 h1) h2 h3 h4 (* h5 
h5 h5) j2) (* 12 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 129 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
584 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 1428 (* h1 
h1 h1 h1) h2 h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 2019 (* h1 h1 h1 h1) h2 
h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 1652 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5) 
h6 (* j2 j2 j2)) (* 750 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5) h6 (* j2 j2)) (* 172 
(* h1 h1 h1 h1) h2 h3 h4 (* h5 h5) h6 j2) (* 16 (* h1 h1 h1 h1) h2 h3 h4 (* h5 
h5) h6) (* 14 (* h1 h1 h1 h1) h2 h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2))
 (* 140 (* h1 h1 h1 h1) h2 h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 564 
(* h1 h1 h1 h1) h2 h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1174 (* h1 h1 h1
 h1) h2 h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1344 (* h1 h1 h1 h1) h2 h3 h4 
h5 (* h6 h6) (* j2 j2 j2 j2)) (* 828 (* h1 h1 h1 h1) h2 h3 h4 h5 (* h6 h6) (* j2
 j2 j2)) (* 244 (* h1 h1 h1 h1) h2 h3 h4 h5 (* h6 h6) (* j2 j2)) (* 24 (* h1 h1 
h1 h1) h2 h3 h4 h5 (* h6 h6) j2) (* 4 (* h1 h1 h1 h1) h2 h3 h4 (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 36 (* h1 h1 h1 h1) h2 h3 h4 (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 128 (* h1 h1 h1 h1) h2 h3 h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 228 (* h1 h1 h1 h1) h2 h3 h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 212 (* 
h1 h1 h1 h1) h2 h3 h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 96 (* h1 h1 h1 h1) h2 h3 
h4 (* h6 h6 h6) (* j2 j2 j2)) (* 16 (* h1 h1 h1 h1) h2 h3 h4 (* h6 h6 h6) (* j2 
j2)) (* 8 (* h1 h1 h1 h1) h2 h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
90 (* h1 h1 h1 h1) h2 h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 418 (* h1 
h1 h1 h1) h2 h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 1038 (* h1 h1 h1 h1) 
h2 h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 1494 (* h1 h1 h1 h1) h2 h3 (* h5 h5
 h5) h6 (* j2 j2 j2 j2)) (* 1266 (* h1 h1 h1 h1) h2 h3 (* h5 h5 h5) h6 (* j2 j2 
j2)) (* 614 (* h1 h1 h1 h1) h2 h3 (* h5 h5 h5) h6 (* j2 j2)) (* 156 (* h1 h1 h1 
h1) h2 h3 (* h5 h5 h5) h6 j2) (* 16 (* h1 h1 h1 h1) h2 h3 (* h5 h5 h5) h6) (* 4 
(* h1 h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 54 
(* h1 h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 312 
(* h1 h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 994 (* h1
 h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1888 (* h1 h1 h1 
h1) h2 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2176 (* h1 h1 h1 h1) h2 h3 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 1494 (* h1 h1 h1 h1) h2 h3 (* h5 h5) (* 
h6 h6) (* j2 j2 j2)) (* 578 (* h1 h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6) (* j2 j2))
 (* 112 (* h1 h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6) j2) (* 8 (* h1 h1 h1 h1) h2 h3
 (* h5 h5) (* h6 h6)) (* 2 (* h1 h1 h1 h1) h2 h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 26 (* h1 h1 h1 h1) h2 h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 140 (* h1 h1 h1 h1) h2 h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 404 (* h1 h1 h1 h1) h2 h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 676 (* 
h1 h1 h1 h1) h2 h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 664 (* h1 h1 h1 h1) h2
 h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 370 (* h1 h1 h1 h1) h2 h3 h5 (* h6 h6 h6
) (* j2 j2 j2)) (* 106 (* h1 h1 h1 h1) h2 h3 h5 (* h6 h6 h6) (* j2 j2)) (* 12 
(* h1 h1 h1 h1) h2 h3 h5 (* h6 h6 h6) j2) (* 3 (* h1 h1 h1 h1) h2 (* h4 h4) (* 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 22 (* h1 h1 h1 h1) h2 (* h4 h4) (* h5 h5)
 h6 (* j2 j2 j2 j2 j2 j2)) (* 63 (* h1 h1 h1 h1) h2 (* h4 h4) (* h5 h5) h6 (* j2
 j2 j2 j2 j2)) (* 89 (* h1 h1 h1 h1) h2 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) 
(* 65 (* h1 h1 h1 h1) h2 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 24 (* h1 h1 h1 
h1) h2 (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 4 (* h1 h1 h1 h1) h2 (* h4 h4) (* h5
 h5) h6 j2) (* 3 (* h1 h1 h1 h1) h2 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 19 (* h1 h1 h1 h1) h2 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
46 (* h1 h1 h1 h1) h2 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 54 (* h1 h1 
h1 h1) h2 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 33 (* h1 h1 h1 h1) h2 (* h4
 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 11 (* h1 h1 h1 h1) h2 (* h4 h4) h5 (* h6 h6) 
(* j2 j2)) (* 2 (* h1 h1 h1 h1) h2 (* h4 h4) h5 (* h6 h6) j2) (* 2 (* h1 h1 h1 
h1) h2 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 19 (* h1 h1 h1 h1) h2 
h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 73 (* h1 h1 h1 h1) h2 h4 (* h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 146 (* h1 h1 h1 h1) h2 h4 (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2)) (* 163 (* h1 h1 h1 h1) h2 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)
) (* 101 (* h1 h1 h1 h1) h2 h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 32 (* h1 h1 h1 
h1) h2 h4 (* h5 h5 h5) h6 (* j2 j2)) (* 4 (* h1 h1 h1 h1) h2 h4 (* h5 h5 h5) h6 
j2) (* 4 (* h1 h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 37 (* h1 h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 138
 (* h1 h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 271 (* h1 
h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 310 (* h1 h1 h1 h1) 
h2 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 218 (* h1 h1 h1 h1) h2 h4 (* h5 h5
) (* h6 h6) (* j2 j2 j2)) (* 95 (* h1 h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6) (* j2 
j2)) (* 23 (* h1 h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6) j2) (* 2 (* h1 h1 h1 h1) h2
 h4 (* h5 h5) (* h6 h6)) (* 2 (* h1 h1 h1 h1) h2 h4 h5 (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 17 (* h1 h1 h1 h1) h2 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 57 (* h1 h1 h1 h1) h2 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 97
 (* h1 h1 h1 h1) h2 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 91 (* h1 h1 h1 h1)
 h2 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 49 (* h1 h1 h1 h1) h2 h4 h5 (* h6 h6 
h6) (* j2 j2 j2)) (* 15 (* h1 h1 h1 h1) h2 h4 h5 (* h6 h6 h6) (* j2 j2)) (* 2 
(* h1 h1 h1 h1) h2 h4 h5 (* h6 h6 h6) j2) (* (* h1 h1 h1 h1) h2 (* h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 12 (* h1 h1 h1 h1) h2 (* h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 61 (* h1 h1 h1 h1) h2 (* h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 172 (* h1 h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 296 (* h1 h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6) (* j2 j2
 j2 j2 j2)) (* 322 (* h1 h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) 
(* 221 (* h1 h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 92 (* h1 h1 h1
 h1) h2 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 21 (* h1 h1 h1 h1) h2 (* h5 h5 h5) 
(* h6 h6) j2) (* 2 (* h1 h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6)) (* (* h1 h1 h1 h1)
 h2 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 12 (* h1 h1 h1 h1)
 h2 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 61 (* h1 h1 h1 h1) h2
 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 172 (* h1 h1 h1 h1) h2 (* 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 296 (* h1 h1 h1 h1) h2 (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 322 (* h1 h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6
) (* j2 j2 j2 j2)) (* 221 (* h1 h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)
) (* 92 (* h1 h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 21 (* h1 h1 h1 
h1) h2 (* h5 h5) (* h6 h6 h6) j2) (* 2 (* h1 h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6)
) (* 4 (* h1 h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 60 (* h1 h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 372
 (* h1 h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 1244 (* h1 
h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 2432 (* h1 h1 h1 h1) 
(* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 2784 (* h1 h1 h1 h1) (* h3 h3 h3) 
(* h4 h4) h5 (* j2 j2 j2)) (* 1728 (* h1 h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* 
j2 j2)) (* 448 (* h1 h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 j2) (* 8 (* h1 h1 h1 h1
) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 96 (* h1 h1 h1 h1) 
(* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 488 (* h1 h1 h1 h1) (* h3
 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 1360 (* h1 h1 h1 h1) (* h3 h3 h3)
 (* h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 2240 (* h1 h1 h1 h1) (* h3 h3 h3) (* h4 h4)
 h6 (* j2 j2 j2 j2)) (* 2176 (* h1 h1 h1 h1) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 
j2)) (* 1152 (* h1 h1 h1 h1) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2)) (* 256 (* h1 
h1 h1 h1) (* h3 h3 h3) (* h4 h4) h6 j2) (* 2 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 38 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 304 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h5
 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1334 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5)
 (* j2 j2 j2 j2 j2 j2)) (* 3498 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* j2 
j2 j2 j2 j2)) (* 5572 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2))
 (* 5192 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 2512 (* h1 
h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2)) (* 448 (* h1 h1 h1 h1) (* h3 h3 
h3) h4 (* h5 h5) j2) (* 8 (* h1 h1 h1 h1) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 140 (* h1 h1 h1 h1) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 1040 (* h1 h1 h1 h1) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2
)) (* 4288 (* h1 h1 h1 h1) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 10756
 (* h1 h1 h1 h1) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 16880 (* h1 h1 h1 
h1) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 16352 (* h1 h1 h1 h1) (* h3 h3 h3)
 h4 h5 h6 (* j2 j2 j2)) (* 9216 (* h1 h1 h1 h1) (* h3 h3 h3) h4 h5 h6 (* j2 j2))
 (* 2624 (* h1 h1 h1 h1) (* h3 h3 h3) h4 h5 h6 j2) (* 256 (* h1 h1 h1 h1) (* h3 
h3 h3) h4 h5 h6) (* 8 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 112 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2
 j2 j2 j2 j2)) (* 672 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 2248 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 4560 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
5696 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 4224 (* h1 h1
 h1 h1) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2)) (* 1664 (* h1 h1 h1 h1) (* h3 h3
 h3) h4 (* h6 h6) (* j2 j2)) (* 256 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h6 h6) j2
) (* 12 (* h1 h1 h1 h1) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 200 (* h1 h1 h1 h1) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 1412 (* h1 h1 h1 h1) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
5512 (* h1 h1 h1 h1) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 13004 
(* h1 h1 h1 h1) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 19008 (* h1 h1 
h1 h1) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 16960 (* h1 h1 h1 h1) (* h3
 h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 8768 (* h1 h1 h1 h1) (* h3 h3 h3) (* h5 h5
) h6 (* j2 j2)) (* 2368 (* h1 h1 h1 h1) (* h3 h3 h3) (* h5 h5) h6 j2) (* 256 (* 
h1 h1 h1 h1) (* h3 h3 h3) (* h5 h5) h6) (* 24 (* h1 h1 h1 h1) (* h3 h3 h3) h5 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 352 (* h1 h1 h1 h1) (* h3 h3 h3) h5
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2216 (* h1 h1 h1 h1) (* h3 h3 h3) h5 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 7808 (* h1 h1 h1 h1) (* h3 h3 h3) h5 (* 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 16824 (* h1 h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6)
 (* j2 j2 j2 j2 j2)) (* 22736 (* h1 h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2
 j2 j2)) (* 19008 (* h1 h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 
9344 (* h1 h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2)) (* 2432 (* h1 h1 h1 h1
) (* h3 h3 h3) h5 (* h6 h6) j2) (* 256 (* h1 h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6)
) (* 2 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 24
 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 112 (* h1 
h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 264 (* h1 h1 h1 h1) 
(* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 334 (* h1 h1 h1 h1) (* h3 h3) (* 
h4 h4 h4) h5 (* j2 j2 j2)) (* 216 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 (* 
j2 j2)) (* 56 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 j2) (* 4 (* h1 h1 h1 h1)
 (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 36 (* h1 h1 h1 h1) (* h3
 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 132 (* h1 h1 h1 h1) (* h3 h3) (* 
h4 h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 252 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4 h4) 
h6 (* j2 j2 j2 j2)) (* 264 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2
)) (* 144 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4 h4) h6 (* j2 j2)) (* 32 (* h1 h1 h1
 h1) (* h3 h3) (* h4 h4 h4) h6 j2) (* 4 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 56 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) 
(* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 317 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) 
(* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 941 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* 
h5 h5) (* j2 j2 j2 j2 j2)) (* 1571 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5)
 (* j2 j2 j2 j2)) (* 1453 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2
 j2)) (* 670 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 112 (* 
h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) j2) (* 16 (* h1 h1 h1 h1) (* h3 h3) 
(* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 184 (* h1 h1 h1 h1) (* h3 h3) 
(* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 898 (* h1 h1 h1 h1) (* h3 h3) (* h4
 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 2392 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) h5
 h6 (* j2 j2 j2 j2 j2)) (* 3734 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) h5 h6 (* j2 
j2 j2 j2)) (* 3416 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 
1728 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 416 (* h1 h1 h1 h1)
 (* h3 h3) (* h4 h4) h5 h6 j2) (* 32 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) h5 h6) 
(* 8 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 88 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 400 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
968 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1336 
(* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 1040 (* h1 h1 
h1 h1) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 416 (* h1 h1 h1 h1) (* h3 
h3) (* h4 h4) (* h6 h6) (* j2 j2)) (* 64 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* 
h6 h6) j2) (* (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 18 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 134 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 534 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1230 
(* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 1644 (* h1 h1 
h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 1207 (* h1 h1 h1 h1) (* h3 
h3) h4 (* h5 h5 h5) (* j2 j2 j2)) (* 426 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5 
h5) (* j2 j2)) (* 56 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) j2) (* 9 (* h1 h1
 h1 h1) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 144 (* h1 
h1 h1 h1) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 962 (* h1 h1
 h1 h1) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 3504 (* h1 h1 h1 
h1) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 7590 (* h1 h1 h1 h1) (* 
h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 9982 (* h1 h1 h1 h1) (* h3 h3) h4 
(* h5 h5) h6 (* j2 j2 j2 j2)) (* 7811 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5) h6 
(* j2 j2 j2)) (* 3434 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 
760 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5) h6 j2) (* 64 (* h1 h1 h1 h1) (* h3 h3
) h4 (* h5 h5) h6) (* 16 (* h1 h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 214 (* h1 h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 1238 (* h1 h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 4022 (* h1 h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 7974 (* h1 h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 9838 (* h1 h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 7414 (* h1
 h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 3232 (* h1 h1 h1 h1) (* h3
 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 728 (* h1 h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6)
 j2) (* 64 (* h1 h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6)) (* 4 (* h1 h1 h1 h1) (* h3
 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 52 (* h1 h1 h1 h1) (* h3
 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 284 (* h1 h1 h1 h1) (* h3 
h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 844 (* h1 h1 h1 h1) (* h3 h3) 
h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1476 (* h1 h1 h1 h1) (* h3 h3) h4 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1532 (* h1 h1 h1 h1) (* h3 h3) h4 (* h6 h6 h6) 
(* j2 j2 j2 j2)) (* 904 (* h1 h1 h1 h1) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2)) 
(* 272 (* h1 h1 h1 h1) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2)) (* 32 (* h1 h1 h1 h1
) (* h3 h3) h4 (* h6 h6 h6) j2) (* 6 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 94 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 612 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 2150 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2)) (* 4428 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2)) (* 5454 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) 
(* 3966 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 1648 (* h1 h1
 h1 h1) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2)) (* 360 (* h1 h1 h1 h1) (* h3 h3) 
(* h5 h5 h5) h6 j2) (* 32 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5 h5) h6) (* 30 (* h1
 h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 386 
(* h1 h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
2104 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
6322 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
11416 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 12690
 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 8594 (* h1 h1
 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 3416 (* h1 h1 h1 h1) (* 
h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 728 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5)
 (* h6 h6) j2) (* 64 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6)) (* 12 (* h1 
h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 164 (* h1
 h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 944 (* h1 
h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2972 (* h1 h1 
h1 h1) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 5568 (* h1 h1 h1 h1) 
(* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 6348 (* h1 h1 h1 h1) (* h3 h3) 
h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 4356 (* h1 h1 h1 h1) (* h3 h3) h5 (* h6 h6 
h6) (* j2 j2 j2)) (* 1736 (* h1 h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2)) 
(* 368 (* h1 h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6) j2) (* 32 (* h1 h1 h1 h1) (* h3
 h3) h5 (* h6 h6 h6)) (* (* h1 h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 
j2 j2 j2 j2)) (* 11 (* h1 h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 
j2)) (* 45 (* h1 h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 87 
(* h1 h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 80 (* h1 h1 h1 h1)
 h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 28 (* h1 h1 h1 h1) h3 (* h4 h4 h4) 
(* h5 h5) (* j2 j2)) (* 5 (* h1 h1 h1 h1) h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 
j2 j2 j2)) (* 38 (* h1 h1 h1 h1) h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) 
(* 114 (* h1 h1 h1 h1) h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 168 (* h1 h1
 h1 h1) h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 121 (* h1 h1 h1 h1) h3 (* h4 
h4 h4) h5 h6 (* j2 j2 j2)) (* 34 (* h1 h1 h1 h1) h3 (* h4 h4 h4) h5 h6 (* j2 j2)
) (* 2 (* h1 h1 h1 h1) h3 (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 14
 (* h1 h1 h1 h1) h3 (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 38 (* h1 h1
 h1 h1) h3 (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 50 (* h1 h1 h1 h1) h3 
(* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 32 (* h1 h1 h1 h1) h3 (* h4 h4 h4) 
(* h6 h6) (* j2 j2 j2)) (* 8 (* h1 h1 h1 h1) h3 (* h4 h4 h4) (* h6 h6) (* j2 j2)
) (* (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
13 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 66 (* 
h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 167 (* h1 h1 h1
 h1) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 219 (* h1 h1 h1 h1) h3 (* 
h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 136 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 
h5 h5) (* j2 j2 j2)) (* 28 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2)) 
(* 8 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
84 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 366 
(* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 845 (* h1 h1
 h1 h1) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 1092 (* h1 h1 h1 h1) h3
 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 766 (* h1 h1 h1 h1) h3 (* h4 h4) (* 
h5 h5) h6 (* j2 j2 j2)) (* 259 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5) h6 (* j2 
j2)) (* 30 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5) h6 j2) (* 9 (* h1 h1 h1 h1) h3
 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 90 (* h1 h1 h1 h1) h3 
(* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 363 (* h1 h1 h1 h1) h3 (* h4
 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 757 (* h1 h1 h1 h1) h3 (* h4 h4) h5 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 868 (* h1 h1 h1 h1) h3 (* h4 h4) h5 (* h6 h6) 
(* j2 j2 j2 j2)) (* 535 (* h1 h1 h1 h1) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2)) 
(* 158 (* h1 h1 h1 h1) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 16 (* h1 h1 h1 h1
) h3 (* h4 h4) h5 (* h6 h6) j2) (* 2 (* h1 h1 h1 h1) h3 (* h4 h4) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 18 (* h1 h1 h1 h1) h3 (* h4 h4) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 64 (* h1 h1 h1 h1) h3 (* h4 h4) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 114 (* h1 h1 h1 h1) h3 (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2
)) (* 106 (* h1 h1 h1 h1) h3 (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 48 (* h1
 h1 h1 h1) h3 (* h4 h4) (* h6 h6 h6) (* j2 j2 j2)) (* 8 (* h1 h1 h1 h1) h3 (* h4
 h4) (* h6 h6 h6) (* j2 j2)) (* 2 (* h1 h1 h1 h1) h3 h4 (* h5 h5 h5) h6 (* j2 j2
 j2 j2 j2 j2 j2 j2 j2)) (* 31 (* h1 h1 h1 h1) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 197 (* h1 h1 h1 h1) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 664 (* h1 h1 h1 h1) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
1279 (* h1 h1 h1 h1) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 1412 (* h1 h1 
h1 h1) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 853 (* h1 h1 h1 h1) h3 h4 (* h5
 h5 h5) h6 (* j2 j2 j2)) (* 257 (* h1 h1 h1 h1) h3 h4 (* h5 h5 h5) h6 (* j2 j2))
 (* 30 (* h1 h1 h1 h1) h3 h4 (* h5 h5 h5) h6 j2) (* 8 (* h1 h1 h1 h1) h3 h4 (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 99 (* h1 h1 h1 h1) h3 h4 (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 523 (* h1 h1 h1 h1) h3 h4 (* h5
 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1532 (* h1 h1 h1 h1) h3 h4 (* h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2705 (* h1 h1 h1 h1) h3 h4 (* h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2)) (* 2934 (* h1 h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6) (* j2 
j2 j2 j2)) (* 1911 (* h1 h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 
699 (* h1 h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 126 (* h1 h1 h1 h1) 
h3 h4 (* h5 h5) (* h6 h6) j2) (* 8 (* h1 h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6)) 
(* 4 (* h1 h1 h1 h1) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 50
 (* h1 h1 h1 h1) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 258 (* h1
 h1 h1 h1) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 710 (* h1 h1 h1 h1
) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1126 (* h1 h1 h1 h1) h3 h4 h5 
(* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1042 (* h1 h1 h1 h1) h3 h4 h5 (* h6 h6 h6) 
(* j2 j2 j2 j2)) (* 546 (* h1 h1 h1 h1) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 
148 (* h1 h1 h1 h1) h3 h4 h5 (* h6 h6 h6) (* j2 j2)) (* 16 (* h1 h1 h1 h1) h3 h4
 h5 (* h6 h6 h6) j2) (* 6 (* h1 h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 76 (* h1 h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 402 (* h1 h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2
 j2 j2 j2)) (* 1154 (* h1 h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 1962 (* h1 h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
2034 (* h1 h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 1284 (* h1 h1
 h1 h1) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 478 (* h1 h1 h1 h1) h3 (* h5 
h5 h5) (* h6 h6) (* j2 j2)) (* 96 (* h1 h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6) j2) 
(* 8 (* h1 h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6)) (* 6 (* h1 h1 h1 h1) h3 (* h5 h5
) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 76 (* h1 h1 h1 h1) h3 (* h5 h5
) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 402 (* h1 h1 h1 h1) h3 (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1154 (* h1 h1 h1 h1) h3 (* h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1962 (* h1 h1 h1 h1) h3 (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2)) (* 2034 (* h1 h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2)) (* 1284 (* h1 h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 
478 (* h1 h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 96 (* h1 h1 h1 h1) 
h3 (* h5 h5) (* h6 h6 h6) j2) (* 8 (* h1 h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6)) 
(* (* h1 h1 h1 h1) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 7 (* 
h1 h1 h1 h1) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 18 (* h1 h1 h1 
h1) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 20 (* h1 h1 h1 h1) (* h4 h4
 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 8 (* h1 h1 h1 h1) (* h4 h4 h4) (* h5 h5) 
h6 (* j2 j2 j2)) (* (* h1 h1 h1 h1) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 6 (* h1 h1 h1 h1) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 13 (* h1 h1 h1 h1) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 12 (* h1 
h1 h1 h1) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 4 (* h1 h1 h1 h1) (* h4 
h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* (* h1 h1 h1 h1) (* h4 h4) (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 9 (* h1 h1 h1 h1) (* h4 h4) (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2)) (* 31 (* h1 h1 h1 h1) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2)) (* 50 (* h1 h1 h1 h1) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)
) (* 36 (* h1 h1 h1 h1) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 8 (* h1 h1
 h1 h1) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 2 (* h1 h1 h1 h1) (* h4 h4) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 18 (* h1 h1 h1 h1) (* h4 h4)
 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 63 (* h1 h1 h1 h1) (* h4 h4) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 108 (* h1 h1 h1 h1) (* h4 h4) (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 93 (* h1 h1 h1 h1) (* h4 h4) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2)) (* 36 (* h1 h1 h1 h1) (* h4 h4) (* h5 h5) (* h6 h6) 
(* j2 j2 j2)) (* 4 (* h1 h1 h1 h1) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 
(* h1 h1 h1 h1) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 8 (* 
h1 h1 h1 h1) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 24 (* h1 h1 
h1 h1) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 33 (* h1 h1 h1 h1) 
(* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 20 (* h1 h1 h1 h1) (* h4 h4) h5
 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 4 (* h1 h1 h1 h1) (* h4 h4) h5 (* h6 h6 h6) 
(* j2 j2 j2)) (* (* h1 h1 h1 h1) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 11 (* h1 h1 h1 h1) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 49 (* h1 h1 h1 h1) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 113 (* h1 h1 h1 h1) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 143
 (* h1 h1 h1 h1) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 97 (* h1 h1 h1
 h1) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 32 (* h1 h1 h1 h1) h4 (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2)) (* 4 (* h1 h1 h1 h1) h4 (* h5 h5 h5) (* h6 h6) 
(* j2 j2)) (* (* h1 h1 h1 h1) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 11 (* h1 h1 h1 h1) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 49 (* h1 h1 h1 h1) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 113 (* h1 h1 h1 h1) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 143 
(* h1 h1 h1 h1) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 97 (* h1 h1 h1 
h1) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 32 (* h1 h1 h1 h1) h4 (* h5 h5
) (* h6 h6 h6) (* j2 j2 j2)) (* 4 (* h1 h1 h1 h1) h4 (* h5 h5) (* h6 h6 h6) (* 
j2 j2)) (* 2 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2 j2 j2 j2))
 (* 26 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2 j2 j2)) (* 120 
(* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2 j2)) (* 276 (* h1 h1 h1
) (* h2 h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2)) (* 354 (* h1 h1 h1) (* h2 h2 h2 
h2) (* h3 h3) h5 (* j2 j2 j2)) (* 258 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 
(* j2 j2)) (* 100 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 j2) (* 16 (* h1 h1 
h1) (* h2 h2 h2 h2) (* h3 h3) h5) (* 4 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h6
 (* j2 j2 j2 j2 j2 j2 j2)) (* 32 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h6 (* j2
 j2 j2 j2 j2 j2)) (* 104 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h6 (* j2 j2 j2 
j2 j2)) (* 176 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h6 (* j2 j2 j2 j2)) (* 164
 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h6 (* j2 j2 j2)) (* 80 (* h1 h1 h1) (* 
h2 h2 h2 h2) (* h3 h3) h6 (* j2 j2)) (* 16 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3
) h6 j2) (* (* h1 h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 12 (* h1 h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 49 (* 
h1 h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 100 (* h1 h1 h1) 
(* h2 h2 h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2)) (* 115 (* h1 h1 h1) (* h2 h2 h2 h2
) h3 (* h5 h5) (* j2 j2 j2)) (* 76 (* h1 h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) (* 
j2 j2)) (* 27 (* h1 h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) j2) (* 4 (* h1 h1 h1) 
(* h2 h2 h2 h2) h3 (* h5 h5)) (* 3 (* h1 h1 h1) (* h2 h2 h2 h2) h3 h5 h6 (* j2 
j2 j2 j2 j2 j2 j2)) (* 21 (* h1 h1 h1) (* h2 h2 h2 h2) h3 h5 h6 (* j2 j2 j2 j2 
j2 j2)) (* 60 (* h1 h1 h1) (* h2 h2 h2 h2) h3 h5 h6 (* j2 j2 j2 j2 j2)) (* 90 
(* h1 h1 h1) (* h2 h2 h2 h2) h3 h5 h6 (* j2 j2 j2 j2)) (* 75 (* h1 h1 h1) (* h2 
h2 h2 h2) h3 h5 h6 (* j2 j2 j2)) (* 33 (* h1 h1 h1) (* h2 h2 h2 h2) h3 h5 h6 (* 
j2 j2)) (* 6 (* h1 h1 h1) (* h2 h2 h2 h2) h3 h5 h6 j2) (* 2 (* h1 h1 h1) (* h2 
h2 h2 h2) h3 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 12 (* h1 h1 h1) (* h2 h2 h2 
h2) h3 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 28 (* h1 h1 h1) (* h2 h2 h2 h2) h3 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 32 (* h1 h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6) 
(* j2 j2 j2 j2)) (* 18 (* h1 h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6) (* j2 j2 j2)) 
(* 4 (* h1 h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6) (* j2 j2)) (* (* h1 h1 h1) (* h2 
h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 7 (* h1 h1 h1) (* h2 h2 h2 
h2) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 21 (* h1 h1 h1) (* h2 h2 h2 h2) (* h5
 h5) h6 (* j2 j2 j2 j2 j2)) (* 35 (* h1 h1 h1) (* h2 h2 h2 h2) (* h5 h5) h6 (* 
j2 j2 j2 j2)) (* 35 (* h1 h1 h1) (* h2 h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2)) (* 
21 (* h1 h1 h1) (* h2 h2 h2 h2) (* h5 h5) h6 (* j2 j2)) (* 7 (* h1 h1 h1) (* h2 
h2 h2 h2) (* h5 h5) h6 j2) (* (* h1 h1 h1) (* h2 h2 h2 h2) (* h5 h5) h6) (* (* 
h1 h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 6 (* h1 h1 
h1) (* h2 h2 h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 15 (* h1 h1 h1) (* h2
 h2 h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 20 (* h1 h1 h1) (* h2 h2 h2 h2) 
h5 (* h6 h6) (* j2 j2 j2 j2)) (* 15 (* h1 h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6) 
(* j2 j2 j2)) (* 6 (* h1 h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6) (* j2 j2)) (* (* h1
 h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6) j2) (* 8 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3
 h3) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 128 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 
h3) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 800 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) 
h5 (* j2 j2 j2 j2 j2 j2)) (* 2640 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 (* 
j2 j2 j2 j2 j2)) (* 5112 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 
j2)) (* 6000 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2)) (* 4192 (* 
h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2)) (* 1600 (* h1 h1 h1) (* h2 h2 
h2) (* h3 h3 h3) h5 j2) (* 256 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5) (* 16 
(* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 176 
(* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 816 (* h1
 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2 j2 j2 j2)) (* 2064 (* h1 h1 h1)
 (* h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2 j2 j2)) (* 3072 (* h1 h1 h1) (* h2 h2 
h2) (* h3 h3 h3) h6 (* j2 j2 j2 j2)) (* 2688 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 
h3) h6 (* j2 j2 j2)) (* 1280 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2)
) (* 256 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h6 j2) (* 12 (* h1 h1 h1) (* h2 
h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 160 (* h1 h1 h1) (* h2 h2 h2
) (* h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 788 (* h1 h1 h1) (* h2 h2 h2) (* h3 
h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 1956 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 
(* j2 j2 j2 j2)) (* 2704 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2))
 (* 2108 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 (* j2 j2)) (* 864 (* h1 h1 h1
) (* h2 h2 h2) (* h3 h3) h4 h5 j2) (* 144 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4
 h5) (* 24 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 208 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2)) (* 736 
(* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 1360 (* h1 h1 
h1) (* h2 h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 1384 (* h1 h1 h1) (* h2 h2 
h2) (* h3 h3) h4 h6 (* j2 j2 j2)) (* 736 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 
h6 (* j2 j2)) (* 160 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h6 j2) (* 8 (* h1 h1
 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 118 (* h1 
h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 661 (* h1 
h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1930 (* h1 h1 
h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 3280 (* h1 h1 h1) 
(* h2 h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 3364 (* h1 h1 h1) (* h2 h2 
h2) (* h3 h3) (* h5 h5) (* j2 j2 j2)) (* 2051 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3
) (* h5 h5) (* j2 j2)) (* 684 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) j2) 
(* 96 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5)) (* 16 (* h1 h1 h1) (* h2 h2
 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 182 (* h1 h1 h1) (* h2 h2 
h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 892 (* h1 h1 h1) (* h2 h2 h2) 
(* h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 2422 (* h1 h1 h1) (* h2 h2 h2) (* h3 
h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 3946 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 h6 
(* j2 j2 j2 j2)) (* 3928 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2))
 (* 2322 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 h6 (* j2 j2)) (* 740 (* h1 h1 h1
) (* h2 h2 h2) (* h3 h3) h5 h6 j2) (* 96 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 
h6) (* 16 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 160 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 668 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2))
 (* 1508 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
1988 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 1532 (* 
h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2)) (* 640 (* h1 h1 h1) (* 
h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2)) (* 112 (* h1 h1 h1) (* h2 h2 h2) (* h3 
h3) (* h6 h6) j2) (* 6 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2 
j2 j2 j2)) (* 74 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)
) (* 325 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 710 
(* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2)) (* 862 (* h1 h1 h1) 
(* h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2)) (* 592 (* h1 h1 h1) (* h2 h2 h2) h3 
h4 (* h5 h5) (* j2 j2)) (* 215 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) j2) (* 
32 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5)) (* 22 (* h1 h1 h1) (* h2 h2 h2) h3
 h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 164 (* h1 h1 h1) (* h2 h2 h2) h3 h4 h5 h6
 (* j2 j2 j2 j2 j2 j2)) (* 498 (* h1 h1 h1) (* h2 h2 h2) h3 h4 h5 h6 (* j2 j2 j2
 j2 j2)) (* 788 (* h1 h1 h1) (* h2 h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2)) (* 686 
(* h1 h1 h1) (* h2 h2 h2) h3 h4 h5 h6 (* j2 j2 j2)) (* 312 (* h1 h1 h1) (* h2 h2
 h2) h3 h4 h5 h6 (* j2 j2)) (* 58 (* h1 h1 h1) (* h2 h2 h2) h3 h4 h5 h6 j2) (* 
12 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 80 (* 
h1 h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 208 (* h1 h1 h1
) (* h2 h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 264 (* h1 h1 h1) (* h2 h2 
h2) h3 h4 (* h6 h6) (* j2 j2 j2 j2)) (* 164 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* 
h6 h6) (* j2 j2 j2)) (* 40 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6) (* j2 j2)) 
(* 2 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
28 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 145 
(* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 385 (* h1 h1
 h1) (* h2 h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 592 (* h1 h1 h1) (* h2 
h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 550 (* h1 h1 h1) (* h2 h2 h2) h3 (* 
h5 h5 h5) (* j2 j2 j2)) (* 305 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) (* j2 
j2)) (* 93 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) j2) (* 12 (* h1 h1 h1) (* 
h2 h2 h2) h3 (* h5 h5 h5)) (* 8 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 85 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2)) (* 380 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2
 j2 j2)) (* 930 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) 
(* 1362 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 1223 (* h1
 h1 h1) (* h2 h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2)) (* 658 (* h1 h1 h1) (* h2 h2 
h2) h3 (* h5 h5) h6 (* j2 j2)) (* 194 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) h6 
j2) (* 24 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) h6) (* 10 (* h1 h1 h1) (* h2 h2
 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 91 (* h1 h1 h1) (* h2 h2 h2
) h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 338 (* h1 h1 h1) (* h2 h2 h2) h3 
h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 666 (* h1 h1 h1) (* h2 h2 h2) h3 h5 (* h6
 h6) (* j2 j2 j2 j2 j2)) (* 756 (* h1 h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6) (* j2 
j2 j2 j2)) (* 497 (* h1 h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2)) (* 176
 (* h1 h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6) (* j2 j2)) (* 26 (* h1 h1 h1) (* h2 
h2 h2) h3 h5 (* h6 h6) j2) (* 4 (* h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 32 (* h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 104 (* h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2 j2
 j2 j2)) (* 176 (* h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 164 (* h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 80 (* h1 h1
 h1) (* h2 h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2)) (* 16 (* h1 h1 h1) (* h2 h2 h2) 
h3 (* h6 h6 h6) (* j2 j2)) (* 6 (* h1 h1 h1) (* h2 h2 h2) h4 (* h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2)) (* 44 (* h1 h1 h1) (* h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 
j2 j2 j2)) (* 135 (* h1 h1 h1) (* h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) 
(* 226 (* h1 h1 h1) (* h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 224 (* h1 
h1 h1) (* h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 132 (* h1 h1 h1) (* h2 h2 
h2) h4 (* h5 h5) h6 (* j2 j2)) (* 43 (* h1 h1 h1) (* h2 h2 h2) h4 (* h5 h5) h6 
j2) (* 6 (* h1 h1 h1) (* h2 h2 h2) h4 (* h5 h5) h6) (* 6 (* h1 h1 h1) (* h2 h2 
h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 38 (* h1 h1 h1) (* h2 h2 h2) h4
 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 98 (* h1 h1 h1) (* h2 h2 h2) h4 h5 (* h6
 h6) (* j2 j2 j2 j2 j2)) (* 133 (* h1 h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6) (* j2 
j2 j2 j2)) (* 101 (* h1 h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 41 
(* h1 h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6) (* j2 j2)) (* 7 (* h1 h1 h1) (* h2 h2 
h2) h4 h5 (* h6 h6) j2) (* 2 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 18 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2)) (* 69 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2)) (* 148 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 195
 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 162 (* h1 h1 h1) 
(* h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 83 (* h1 h1 h1) (* h2 h2 h2) (* h5
 h5 h5) h6 (* j2 j2)) (* 24 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5 h5) h6 j2) (* 3 
(* h1 h1 h1) (* h2 h2 h2) (* h5 h5 h5) h6) (* 4 (* h1 h1 h1) (* h2 h2 h2) (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 34 (* h1 h1 h1) (* h2 h2 h2) (* h5
 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 122 (* h1 h1 h1) (* h2 h2 h2) (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 243 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 295 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 
h6) (* j2 j2 j2 j2)) (* 224 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 
j2 j2)) (* 104 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 j2)) (* 27 
(* h1 h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6) j2) (* 3 (* h1 h1 h1) (* h2 h2 h2)
 (* h5 h5) (* h6 h6)) (* 2 (* h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 16 (* h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2
 j2 j2 j2)) (* 54 (* h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2
)) (* 100 (* h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 110 
(* h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 72 (* h1 h1 h1) 
(* h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 26 (* h1 h1 h1) (* h2 h2 h2) h5 
(* h6 h6 h6) (* j2 j2)) (* 4 (* h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6) j2) (* 8 
(* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 136 
(* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 920 (* h1
 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2 j2 j2 j2 j2)) (* 3320 (* h1 h1 h1)
 (* h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2 j2 j2 j2)) (* 7072 (* h1 h1 h1) (* h2 h2)
 (* h3 h3 h3 h3) h5 (* j2 j2 j2 j2)) (* 9152 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 
h3) h5 (* j2 j2 j2)) (* 7040 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2)
) (* 2944 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 j2) (* 512 (* h1 h1 h1) (* 
h2 h2) (* h3 h3 h3 h3) h5) (* 16 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h6 (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 192 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h6 (* j2 
j2 j2 j2 j2 j2 j2)) (* 976 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2 j2
 j2 j2 j2)) (* 2720 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2 j2 j2 j2)
) (* 4480 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2 j2 j2)) (* 4352 (* 
h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2 j2)) (* 2304 (* h1 h1 h1) (* h2 
h2) (* h3 h3 h3 h3) h6 (* j2 j2)) (* 512 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) 
h6 j2) (* 24 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 384 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 2480 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 8592
 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 17592 (* h1 h1
 h1) (* h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2)) (* 21840 (* h1 h1 h1) (* h2 
h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2)) (* 16032 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3
) h4 h5 (* j2 j2)) (* 6336 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 j2) (* 1024
 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5) (* 48 (* h1 h1 h1) (* h2 h2) (* h3 
h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 560 (* h1 h1 h1) (* h2 h2) (* h3 h3
 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2768 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3)
 h4 h6 (* j2 j2 j2 j2 j2 j2)) (* 7504 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h6 
(* j2 j2 j2 j2 j2)) (* 12032 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 
j2 j2)) (* 11392 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2)) (* 5888
 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2)) (* 1280 (* h1 h1 h1) (* h2
 h2) (* h3 h3 h3) h4 h6 j2) (* 6 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 132 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h5
 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1154 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) 
(* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 5260 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) 
(* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 13978 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) 
(* h5 h5) (* j2 j2 j2 j2 j2)) (* 22748 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h5
 h5) (* j2 j2 j2 j2)) (* 22894 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) (* 
j2 j2 j2)) (* 13844 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2)) (* 
4592 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) j2) (* 640 (* h1 h1 h1) (* h2
 h2) (* h3 h3 h3) (* h5 h5)) (* 116 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 h6 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1304 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 6216 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 h6 (* 
j2 j2 j2 j2 j2 j2)) (* 16344 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 
j2 j2 j2)) (* 25796 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2)) 
(* 24864 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2)) (* 14160 (* h1 
h1 h1) (* h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2)) (* 4288 (* h1 h1 h1) (* h2 h2) 
(* h3 h3 h3) h5 h6 j2) (* 512 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 h6) (* 24 
(* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 320 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 1832 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 5872 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 11504 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
14080 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 10496 
(* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2)) (* 4352 (* h1 h1 h1)
 (* h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2)) (* 768 (* h1 h1 h1) (* h2 h2) (* h3
 h3 h3) (* h6 h6) j2) (* 18 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 
j2 j2 j2 j2 j2 j2)) (* 236 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 
j2 j2 j2 j2 j2)) (* 1172 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 
j2 j2 j2)) (* 2940 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)
) (* 4066 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 3104 
(* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2)) (* 1200 (* h1 h1 h1) 
(* h2 h2) (* h3 h3) (* h4 h4) h5 j2) (* 176 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* 
h4 h4) h5) (* 36 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2
 j2 j2)) (* 324 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 
j2)) (* 1188 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2)) 
(* 2268 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2)) (* 2376 
(* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2 j2)) (* 1296 (* h1 h1 h1)
 (* h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2)) (* 288 (* h1 h1 h1) (* h2 h2) (* h3
 h3) (* h4 h4) h6 j2) (* 24 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 356 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 2081 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) (* 
j2 j2 j2 j2 j2 j2)) (* 6386 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 
j2 j2 j2 j2)) (* 11358 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2
 j2)) (* 12050 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 
7469 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2)) (* 2476 (* h1 h1 
h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) j2) (* 336 (* h1 h1 h1) (* h2 h2) (* h3 h3)
 h4 (* h5 h5)) (* 72 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 816 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 3974 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2))
 (* 10726 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 17304
 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 16818 (* h1 h1 h1
) (* h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 9422 (* h1 h1 h1) (* h2 h2) (* 
h3 h3) h4 h5 h6 (* j2 j2)) (* 2684 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6 j2)
 (* 272 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6) (* 48 (* h1 h1 h1) (* h2 h2) 
(* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 512 (* h1 h1 h1) (* h2 h2
) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2276 (* h1 h1 h1) (* h2 h2
) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 5436 (* h1 h1 h1) (* h2 h2) 
(* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 7484 (* h1 h1 h1) (* h2 h2) (* h3 
h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 5892 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 
(* h6 h6) (* j2 j2 j2)) (* 2432 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6) 
(* j2 j2)) (* 400 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6) j2) (* 3 (* h1 
h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 63 
(* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
515 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
2137 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 
5036 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 7096 
(* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 6062 (* h1 h1 
h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2)) (* 3064 (* h1 h1 h1) (* h2 h2
) (* h3 h3) (* h5 h5 h5) (* j2 j2)) (* 840 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* 
h5 h5 h5) j2) (* 96 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5)) (* 3 (* h1 h1
 h1) (* h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 154 (* 
h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1362 
(* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 5517 
(* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 12572 
(* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 17313 (* h1
 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 14627 (* h1 h1 h1) 
(* h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 7360 (* h1 h1 h1) (* h2 h2) 
(* h3 h3) (* h5 h5) h6 (* j2 j2)) (* 2004 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5
 h5) h6 j2) (* 224 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) h6) (* 24 (* h1 h1
 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 318 (* 
h1 h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1834 
(* h1 h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 5944 
(* h1 h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 11770 
(* h1 h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 14596 (* h1
 h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 11200 (* h1 h1 h1) 
(* h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 5038 (* h1 h1 h1) (* h2 h2) 
(* h3 h3) h5 (* h6 h6) (* j2 j2)) (* 1164 (* h1 h1 h1) (* h2 h2) (* h3 h3) h5 
(* h6 h6) j2) (* 96 (* h1 h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6)) (* 12 (* h1 
h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 148 
(* h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
772 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
2216 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
3812 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 4004 
(* h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 2492 (* h1 h1 
h1) (* h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2)) (* 832 (* h1 h1 h1) (* h2 h2)
 (* h3 h3) (* h6 h6 h6) (* j2 j2)) (* 112 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h6
 h6 h6) j2) (* 9 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2
 j2 j2)) (* 109 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 
j2)) (* 482 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) 
(* 1043 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 1204 
(* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 736 (* h1 h1 h1) 
(* h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2)) (* 213 (* h1 h1 h1) (* h2 h2) h3 (* 
h4 h4) (* h5 h5) j2) (* 20 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5)) (* 39 
(* h1 h1 h1) (* h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 298 (* h1
 h1 h1) (* h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 916 (* h1 h1 h1) 
(* h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 1436 (* h1 h1 h1) (* h2 h2) 
h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 1195 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) 
h5 h6 (* j2 j2 j2)) (* 490 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2)) 
(* 74 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) h5 h6 j2) (* 18 (* h1 h1 h1) (* h2 h2)
 h3 (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 126 (* h1 h1 h1) (* h2 h2) 
h3 (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 342 (* h1 h1 h1) (* h2 h2) h3 
(* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 450 (* h1 h1 h1) (* h2 h2) h3 (* h4 
h4) (* h6 h6) (* j2 j2 j2 j2)) (* 288 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h6 
h6) (* j2 j2 j2)) (* 72 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 j2))
 (* 6 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
84 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 452 
(* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1248 (* h1 
h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 1961 (* h1 h1 h1) (* 
h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 1815 (* h1 h1 h1) (* h2 h2) h3 h4 
(* h5 h5 h5) (* j2 j2 j2)) (* 973 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) (* 
j2 j2)) (* 277 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) j2) (* 32 (* h1 h1 h1) 
(* h2 h2) h3 h4 (* h5 h5 h5)) (* 36 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 375 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 1661 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2)) (* 4038 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 
j2 j2 j2)) (* 5812 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2)) 
(* 5000 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2)) (* 2465 (* h1 h1
 h1) (* h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2)) (* 617 (* h1 h1 h1) (* h2 h2) h3 h4
 (* h5 h5) h6 j2) (* 56 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6) (* 42 (* h1 
h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 402 (* h1 h1
 h1) (* h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1571 (* h1 h1 h1)
 (* h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3232 (* h1 h1 h1) (* h2 
h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 3753 (* h1 h1 h1) (* h2 h2) h3 h4 
h5 (* h6 h6) (* j2 j2 j2 j2)) (* 2428 (* h1 h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6) 
(* j2 j2 j2)) (* 788 (* h1 h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2)) (* 92 
(* h1 h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6) j2) (* 12 (* h1 h1 h1) (* h2 h2) h3 h4
 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 104 (* h1 h1 h1) (* h2 h2) h3 h4 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 364 (* h1 h1 h1) (* h2 h2) h3 h4 (* h6
 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 652 (* h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2)) (* 624 (* h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2 j2
 j2)) (* 300 (* h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2 j2)) (* 56 (* h1
 h1 h1) (* h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2)) (* (* h1 h1 h1) (* h2 h2) h3 (* 
h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 14 (* h1 h1 h1) (* h2 h2) h3 (* h5 
h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 72 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5 
h5) (* j2 j2 j2 j2 j2 j2)) (* 187 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) (* 
j2 j2 j2 j2 j2)) (* 277 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) (* j2 j2 j2 j2
)) (* 244 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) (* j2 j2 j2)) (* 126 (* h1 
h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) (* j2 j2)) (* 35 (* h1 h1 h1) (* h2 h2) h3 
(* h5 h5 h5 h5) j2) (* 4 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5)) (* 32 (* h1 
h1 h1) (* h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 313 (* h1 h1
 h1) (* h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1277 (* h1 h1 h1)
 (* h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 2828 (* h1 h1 h1) (* h2 
h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 3710 (* h1 h1 h1) (* h2 h2) h3 (* 
h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 2947 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) h6 
(* j2 j2 j2)) (* 1381 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2)) (* 
348 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) h6 j2) (* 36 (* h1 h1 h1) (* h2 h2) 
h3 (* h5 h5 h5) h6) (* 12 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2
 j2 j2 j2 j2 j2 j2 j2)) (* 156 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 853 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 2547 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 4552 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2)) (* 5037 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2)) (* 3438 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 
1384 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2)) (* 293 (* h1 h1 h1
) (* h2 h2) h3 (* h5 h5) (* h6 h6) j2) (* 24 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5)
 (* h6 h6)) (* 6 (* h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 76 (* h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 391 (* h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2
)) (* 1068 (* h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
1695 (* h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1599 (* h1
 h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 870 (* h1 h1 h1) (* h2 
h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 245 (* h1 h1 h1) (* h2 h2) h3 h5 (* h6 
h6 h6) (* j2 j2)) (* 26 (* h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6) j2) (* 2 (* h1
 h1 h1) (* h2 h2) h3 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1
 h1) (* h2 h2) h3 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 50 (* h1 h1 h1) 
(* h2 h2) h3 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 78 (* h1 h1 h1) (* h2 h2)
 h3 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 64 (* h1 h1 h1) (* h2 h2) h3 (* h6 h6
 h6 h6) (* j2 j2 j2 j2)) (* 26 (* h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6 h6) (* j2 
j2 j2)) (* 4 (* h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6 h6) (* j2 j2)) (* 9 (* h1 h1 
h1) (* h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 66 (* h1 h1 h1
) (* h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 194 (* h1 h1 h1) 
(* h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 295 (* h1 h1 h1) (* h2 
h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 250 (* h1 h1 h1) (* h2 h2) (* h4 
h4) (* h5 h5) h6 (* j2 j2 j2)) (* 118 (* h1 h1 h1) (* h2 h2) (* h4 h4) (* h5 h5)
 h6 (* j2 j2)) (* 29 (* h1 h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) h6 j2) (* 3 (* 
h1 h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) h6) (* 9 (* h1 h1 h1) (* h2 h2) (* h4 h4
) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 57 (* h1 h1 h1) (* h2 h2) (* h4 h4) 
h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 141 (* h1 h1 h1) (* h2 h2) (* h4 h4) h5 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 175 (* h1 h1 h1) (* h2 h2) (* h4 h4) h5 (* h6 
h6) (* j2 j2 j2 j2)) (* 117 (* h1 h1 h1) (* h2 h2) (* h4 h4) h5 (* h6 h6) (* j2 
j2 j2)) (* 42 (* h1 h1 h1) (* h2 h2) (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 7 (* 
h1 h1 h1) (* h2 h2) (* h4 h4) h5 (* h6 h6) j2) (* 6 (* h1 h1 h1) (* h2 h2) h4 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 55 (* h1 h1 h1) (* h2 h2) h4 (* 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 209 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5
 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 432 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2)) (* 535 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2
 j2)) (* 410 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 192 (* 
h1 h1 h1) (* h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2)) (* 51 (* h1 h1 h1) (* h2 h2) 
h4 (* h5 h5 h5) h6 j2) (* 6 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5 h5) h6) (* 12 (* 
h1 h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 107 
(* h1 h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 395 
(* h1 h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 793 (* 
h1 h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 953 (* h1 h1 
h1) (* h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 703 (* h1 h1 h1) (* h2 
h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 308 (* h1 h1 h1) (* h2 h2) h4 (* h5 
h5) (* h6 h6) (* j2 j2)) (* 71 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6) j2)
 (* 6 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6)) (* 6 (* h1 h1 h1) (* h2 h2)
 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 49 (* h1 h1 h1) (* h2 h2) h4
 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 164 (* h1 h1 h1) (* h2 h2) h4 h5 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 291 (* h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6
 h6) (* j2 j2 j2 j2 j2)) (* 297 (* h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6 h6) (* j2 
j2 j2 j2)) (* 176 (* h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 57 
(* h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2)) (* 8 (* h1 h1 h1) (* h2 h2)
 h4 h5 (* h6 h6 h6) j2) (* (* h1 h1 h1) (* h2 h2) (* h5 h5 h5 h5) h6 (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 9 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2)) (* 34 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)
) (* 71 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 90 (* 
h1 h1 h1) (* h2 h2) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 71 (* h1 h1 h1) (* h2
 h2) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 34 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5 
h5) h6 (* j2 j2)) (* 9 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5 h5) h6 j2) (* (* h1 h1
 h1) (* h2 h2) (* h5 h5 h5 h5) h6) (* 3 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 34 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 163 (* h1 h1 h1) (* h2 h2) (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 434 (* h1 h1 h1) (* h2 h2) (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 709 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 738 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2)) (* 489 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 
j2 j2)) (* 198 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 44 
(* h1 h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6) j2) (* 4 (* h1 h1 h1) (* h2 h2) 
(* h5 h5 h5) (* h6 h6)) (* 3 (* h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2 j2)) (* 34 (* h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 163 (* h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6
) (* j2 j2 j2 j2 j2 j2 j2)) (* 434 (* h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2)) (* 708 (* h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2)) (* 733 (* h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2)) (* 479 (* h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 
188 (* h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 39 (* h1 h1 h1) 
(* h2 h2) (* h5 h5) (* h6 h6 h6) j2) (* 3 (* h1 h1 h1) (* h2 h2) (* h5 h5) (* h6
 h6 h6)) (* (* h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 8 (* h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
26 (* h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 45 (* h1 
h1 h1) (* h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 45 (* h1 h1 h1) (* h2
 h2) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 26 (* h1 h1 h1) (* h2 h2) h5 (* h6 
h6 h6 h6) (* j2 j2 j2)) (* 8 (* h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2)
) (* (* h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6 h6) j2) (* 16 (* h1 h1 h1) h2 (* h3 
h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 256 (* h1 h1 h1) h2 (* h3 h3 h3 
h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 1664 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 
h5 (* j2 j2 j2 j2 j2 j2)) (* 5808 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h5 (* j2 j2
 j2 j2 j2)) (* 11936 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2)) (* 
14720 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2)) (* 10496 (* h1 h1 h1) 
h2 (* h3 h3 h3 h3) h4 h5 (* j2 j2)) (* 3840 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 
h5 j2) (* 512 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h5) (* 32 (* h1 h1 h1) h2 (* h3
 h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 384 (* h1 h1 h1) h2 (* h3 h3 h3
 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1952 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 
h6 (* j2 j2 j2 j2 j2 j2)) (* 5440 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h6 (* j2 j2
 j2 j2 j2)) (* 8960 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 
8704 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2)) (* 4608 (* h1 h1 h1) h2
 (* h3 h3 h3 h3) h4 h6 (* j2 j2)) (* 1024 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h6 
j2) (* 4 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2
)) (* 84 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 728 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
3428 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 9668 
(* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 16888 (* h1 h1 
h1) h2 (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 18160 (* h1 h1 h1) h2 (* h3
 h3 h3 h3) (* h5 h5) (* j2 j2 j2)) (* 11488 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* 
h5 h5) (* j2 j2)) (* 3840 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) j2) (* 512 
(* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5)) (* 56 (* h1 h1 h1) h2 (* h3 h3 h3 h3)
 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 704 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h5 h6
 (* j2 j2 j2 j2 j2 j2 j2)) (* 3696 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h5 h6 (* j2 
j2 j2 j2 j2 j2)) (* 10472 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 
j2)) (* 17216 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 16320 
(* h1 h1 h1) h2 (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2)) (* 8192 (* h1 h1 h1) h2 (* 
h3 h3 h3 h3) h5 h6 (* j2 j2)) (* 1664 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h5 h6 j2) 
(* 16 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 224 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 1344 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
4496 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 9120 
(* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 11392 (* h1 h1 
h1) h2 (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 8448 (* h1 h1 h1) h2 (* h3 
h3 h3 h3) (* h6 h6) (* j2 j2 j2)) (* 3328 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h6 
h6) (* j2 j2)) (* 512 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6) j2) (* 16 (* h1 
h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 256 (* h1 h1
 h1) h2 (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 1696 (* h1 h1 h1)
 h2 (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 6072 (* h1 h1 h1) h2 (* 
h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 12792 (* h1 h1 h1) h2 (* h3 h3 h3)
 (* h4 h4) h5 (* j2 j2 j2 j2)) (* 16080 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) 
h5 (* j2 j2 j2)) (* 11552 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 (* j2 j2)) 
(* 4160 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 j2) (* 512 (* h1 h1 h1) h2 (* 
h3 h3 h3) (* h4 h4) h5) (* 32 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h6 (* j2 j2
 j2 j2 j2 j2 j2 j2)) (* 400 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 
j2 j2 j2 j2 j2)) (* 2112 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 
j2 j2 j2)) (* 6096 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2))
 (* 10368 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2)) (* 10368 
(* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2)) (* 5632 (* h1 h1 h1) h2 
(* h3 h3 h3) (* h4 h4) h6 (* j2 j2)) (* 1280 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 
h4) h6 j2) (* 8 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 176 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 1564 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 
j2)) (* 7392 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) 
(* 20648 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 35504 
(* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 37540 (* h1 h1 h1)
 h2 (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 23392 (* h1 h1 h1) h2 (* h3 h3 h3
) h4 (* h5 h5) (* j2 j2)) (* 7728 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) j2) 
(* 1024 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5)) (* 32 (* h1 h1 h1) h2 (* h3 
h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 596 (* h1 h1 h1) h2 (* h3 h3 
h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4504 (* h1 h1 h1) h2 (* h3 h3 h3) 
h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 18568 (* h1 h1 h1) h2 (* h3 h3 h3) h4 h5 
h6 (* j2 j2 j2 j2 j2 j2)) (* 46356 (* h1 h1 h1) h2 (* h3 h3 h3) h4 h5 h6 (* j2 
j2 j2 j2 j2)) (* 72480 (* h1 h1 h1) h2 (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) 
(* 70128 (* h1 h1 h1) h2 (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 39488 (* h1 h1 
h1) h2 (* h3 h3 h3) h4 h5 h6 (* j2 j2)) (* 11136 (* h1 h1 h1) h2 (* h3 h3 h3) h4
 h5 h6 j2) (* 1024 (* h1 h1 h1) h2 (* h3 h3 h3) h4 h5 h6) (* 32 (* h1 h1 h1) h2 
(* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 464 (* h1 h1 h1) h2
 (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2880 (* h1 h1 h1) h2 
(* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 9968 (* h1 h1 h1) h2 (* 
h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 20960 (* h1 h1 h1) h2 (* h3 h3 
h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 27264 (* h1 h1 h1) h2 (* h3 h3 h3) h4 
(* h6 h6) (* j2 j2 j2 j2)) (* 21248 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6) 
(* j2 j2 j2)) (* 8960 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6) (* j2 j2)) (* 
1536 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6) j2) (* 4 (* h1 h1 h1) h2 (* h3 h3
 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 81 (* h1 h1 h1) h2 (* h3 h3
 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 668 (* h1 h1 h1) h2 (* h3 h3 
h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 2947 (* h1 h1 h1) h2 (* h3 h3 h3) 
(* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 7661 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 
h5 h5) (* j2 j2 j2 j2 j2)) (* 12164 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) 
(* j2 j2 j2 j2)) (* 11803 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2)
) (* 6752 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) (* j2 j2)) (* 2064 (* h1 h1 
h1) h2 (* h3 h3 h3) (* h5 h5 h5) j2) (* 256 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 
h5 h5)) (* 50 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 862 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2
 j2)) (* 5962 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)
) (* 22116 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
48874 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 66894 (* 
h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 56606 (* h1 h1 h1) h2
 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 28340 (* h1 h1 h1) h2 (* h3 h3 h3) 
(* h5 h5) h6 (* j2 j2)) (* 7488 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) h6 j2) 
(* 768 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) h6) (* 116 (* h1 h1 h1) h2 (* h3 
h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1544 (* h1 h1 h1) h2 (* 
h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 8860 (* h1 h1 h1) h2 (* 
h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 28628 (* h1 h1 h1) h2 (* h3 
h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 57024 (* h1 h1 h1) h2 (* h3 h3 h3)
 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 71940 (* h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6
 h6) (* j2 j2 j2 j2)) (* 56672 (* h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6) (* j2 
j2 j2)) (* 26256 (* h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2)) (* 6208 
(* h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6) j2) (* 512 (* h1 h1 h1) h2 (* h3 h3 h3
) h5 (* h6 h6)) (* 16 (* h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 208 (* h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2
 j2 j2 j2 j2)) (* 1152 (* h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 3536 (* h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 6544 (* h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
7424 (* h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 4992 (* h1 h1
 h1) h2 (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2)) (* 1792 (* h1 h1 h1) h2 (* h3 h3
 h3) (* h6 h6 h6) (* j2 j2)) (* 256 (* h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6) j2
) (* 8 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 
104 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 524 (* 
h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 1332 (* h1 h1 h1) 
h2 (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 1836 (* h1 h1 h1) h2 (* h3 h3) 
(* h4 h4 h4) h5 (* j2 j2 j2)) (* 1348 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 
(* j2 j2)) (* 464 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 j2) (* 48 (* h1 h1 
h1) h2 (* h3 h3) (* h4 h4 h4) h5) (* 16 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 152 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h6 
(* j2 j2 j2 j2 j2 j2)) (* 584 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h6 (* j2 j2
 j2 j2 j2)) (* 1160 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2)) 
(* 1256 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2)) (* 704 (* h1 h1 
h1) h2 (* h3 h3) (* h4 h4 h4) h6 (* j2 j2)) (* 160 (* h1 h1 h1) h2 (* h3 h3) (* 
h4 h4 h4) h6 j2) (* 16 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 240 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 
j2 j2 j2 j2 j2)) (* 1459 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 
j2 j2 j2 j2)) (* 4680 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 
j2 j2)) (* 8618 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) 
(* 9242 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 5553 (* 
h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 1660 (* h1 h1 h1) h2 
(* h3 h3) (* h4 h4) (* h5 h5) j2) (* 176 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* 
h5 h5)) (* 64 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 754 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 3784 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 
10442 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 17046 (* 
h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 16492 (* h1 h1 h1) h2
 (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 8950 (* h1 h1 h1) h2 (* h3 h3) (* h4
 h4) h5 h6 (* j2 j2)) (* 2348 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 h6 j2) (* 
192 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 h6) (* 32 (* h1 h1 h1) h2 (* h3 h3) 
(* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 368 (* h1 h1 h1) h2 (* h3 h3
) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1748 (* h1 h1 h1) h2 (* h3 h3
) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4412 (* h1 h1 h1) h2 (* h3 h3) 
(* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 6332 (* h1 h1 h1) h2 (* h3 h3) (* h4 
h4) (* h6 h6) (* j2 j2 j2 j2)) (* 5108 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h6
 h6) (* j2 j2 j2)) (* 2112 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h6 h6) (* j2 
j2)) (* 336 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h6 h6) j2) (* 4 (* h1 h1 h1) 
h2 (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 84 (* h1 h1 h1) 
h2 (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 699 (* h1 h1 h1) h2
 (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 3020 (* h1 h1 h1) h2 (* 
h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 7506 (* h1 h1 h1) h2 (* h3 h3) 
h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 11146 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 
h5 h5) (* j2 j2 j2 j2)) (* 9877 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) (* j2 
j2 j2)) (* 5040 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) (* j2 j2)) (* 1348 (* 
h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) j2) (* 144 (* h1 h1 h1) h2 (* h3 h3) h4 
(* h5 h5 h5)) (* 36 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 597 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 4019 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 14651 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)
) (* 31963 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
43129 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 35723 (* h1 
h1 h1) h2 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 17304 (* h1 h1 h1) h2 (* h3
 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 4356 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) 
h6 j2) (* 416 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) h6) (* 64 (* h1 h1 h1) h2 
(* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 850 (* h1 h1 h1) h2
 (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4900 (* h1 h1 h1) h2 
(* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 15932 (* h1 h1 h1) h2 (* 
h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 31806 (* h1 h1 h1) h2 (* h3 h3)
 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 39792 (* h1 h1 h1) h2 (* h3 h3) h4 h5 
(* h6 h6) (* j2 j2 j2 j2)) (* 30564 (* h1 h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6) 
(* j2 j2 j2)) (* 13536 (* h1 h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 
3016 (* h1 h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6) j2) (* 240 (* h1 h1 h1) h2 (* h3 
h3) h4 h5 (* h6 h6)) (* 16 (* h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2
 j2 j2 j2 j2 j2 j2)) (* 216 (* h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 1224 (* h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 3776 (* h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 6872 (* h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2))
 (* 7464 (* h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 4656 (* 
h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2)) (* 1504 (* h1 h1 h1) h2 (* 
h3 h3) h4 (* h6 h6 h6) (* j2 j2)) (* 192 (* h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6 
h6) j2) (* (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 19 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 144 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
570 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1294 (* 
h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 1744 (* h1 h1 h1) 
h2 (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 1401 (* h1 h1 h1) h2 (* h3 h3) 
(* h5 h5 h5 h5) (* j2 j2 j2)) (* 651 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) 
(* j2 j2)) (* 160 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) j2) (* 16 (* h1 h1 
h1) h2 (* h3 h3) (* h5 h5 h5 h5)) (* 25 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 408 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5)
 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2615 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 8822 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 17413 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* 20955 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)
) (* 15461 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 6785 (* h1
 h1 h1) h2 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2)) (* 1616 (* h1 h1 h1) h2 (* h3 h3
) (* h5 h5 h5) h6 j2) (* 160 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) h6) (* 132 
(* h1 h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 1549 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 7780 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2
)) (* 21842 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2))
 (* 37542 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
40708 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 27686 
(* h1 h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 11317 (* h1 h1 h1
) h2 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 2500 (* h1 h1 h1) h2 (* h3 h3) 
(* h5 h5) (* h6 h6) j2) (* 224 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6)) 
(* 62 (* h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 750 (* h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 3868 (* h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
11088 (* h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 19312 
(* h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 21000 (* h1 h1 
h1) h2 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 14114 (* h1 h1 h1) h2 (* h3
 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 5586 (* h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6
 h6) (* j2 j2)) (* 1164 (* h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6) j2) (* 96 (* 
h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6)) (* 4 (* h1 h1 h1) h2 (* h3 h3) (* h6 h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 48 (* h1 h1 h1) h2 (* h3 h3) (* h6 h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 240 (* h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6
 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 648 (* h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 1024 (* h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6 h6) (* j2 
j2 j2 j2 j2)) (* 960 (* h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) 
(* 516 (* h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 144 (* h1 h1 
h1) h2 (* h3 h3) (* h6 h6 h6 h6) (* j2 j2)) (* 16 (* h1 h1 h1) h2 (* h3 h3) (* 
h6 h6 h6 h6) j2) (* 4 (* h1 h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 
j2 j2 j2)) (* 48 (* h1 h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)
) (* 215 (* h1 h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 462 
(* h1 h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 500 (* h1 h1 h1) 
h2 h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 254 (* h1 h1 h1) h2 h3 (* h4 h4 h4
) (* h5 h5) (* j2 j2)) (* 45 (* h1 h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) j2) (* 20
 (* h1 h1 h1) h2 h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 160 (* h1 h1
 h1) h2 h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 506 (* h1 h1 h1) h2 h3 
(* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 796 (* h1 h1 h1) h2 h3 (* h4 h4 h4) h5
 h6 (* j2 j2 j2 j2)) (* 636 (* h1 h1 h1) h2 h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2)) 
(* 228 (* h1 h1 h1) h2 h3 (* h4 h4 h4) h5 h6 (* j2 j2)) (* 22 (* h1 h1 h1) h2 h3
 (* h4 h4 h4) h5 h6 j2) (* 8 (* h1 h1 h1) h2 h3 (* h4 h4 h4) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 60 (* h1 h1 h1) h2 h3 (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 172 (* h1 h1 h1) h2 h3 (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
236 (* h1 h1 h1) h2 h3 (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 156 (* h1 h1 
h1) h2 h3 (* h4 h4 h4) (* h6 h6) (* j2 j2 j2)) (* 40 (* h1 h1 h1) h2 h3 (* h4 h4
 h4) (* h6 h6) (* j2 j2)) (* 4 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 56 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 
j2 j2 j2 j2 j2)) (* 310 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2
 j2 j2)) (* 876 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) 
(* 1363 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 1168 (* h1
 h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 513 (* h1 h1 h1) h2 h3 (* 
h4 h4) (* h5 h5 h5) (* j2 j2)) (* 90 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) 
j2) (* 32 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2))
 (* 345 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
1560 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 3812 
(* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 5382 (* h1 h1 
h1) h2 h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 4351 (* h1 h1 h1) h2 h3 (* 
h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 1876 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5)
 h6 (* j2 j2)) (* 366 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) h6 j2) (* 24 (* h1 
h1 h1) h2 h3 (* h4 h4) (* h5 h5) h6) (* 36 (* h1 h1 h1) h2 h3 (* h4 h4) h5 (* h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 369 (* h1 h1 h1) h2 h3 (* h4 h4) h5 (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1534 (* h1 h1 h1) h2 h3 (* h4 h4) h5 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 3318 (* h1 h1 h1) h2 h3 (* h4 h4) h5 (* h6 h6) (* j2 
j2 j2 j2 j2)) (* 3976 (* h1 h1 h1) h2 h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2))
 (* 2581 (* h1 h1 h1) h2 h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 804 (* h1 h1
 h1) h2 h3 (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 82 (* h1 h1 h1) h2 h3 (* h4 h4) 
h5 (* h6 h6) j2) (* 8 (* h1 h1 h1) h2 h3 (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 76 (* h1 h1 h1) h2 h3 (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 288 (* h1 h1 h1) h2 h3 (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 548 (* h1 h1 h1) h2 h3 (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 544 (* 
h1 h1 h1) h2 h3 (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 264 (* h1 h1 h1) h2 
h3 (* h4 h4) (* h6 h6 h6) (* j2 j2 j2)) (* 48 (* h1 h1 h1) h2 h3 (* h4 h4) (* h6
 h6 h6) (* j2 j2)) (* 2 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 26 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2))
 (* 127 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 308 (* 
h1 h1 h1) h2 h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 405 (* h1 h1 h1) h2 h3
 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 291 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5 h5
) (* j2 j2 j2)) (* 106 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5 h5) (* j2 j2)) (* 15 
(* h1 h1 h1) h2 h3 h4 (* h5 h5 h5 h5) j2) (* 8 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5
) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 133 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 862 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2)) (* 2943 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2
 j2 j2 j2)) (* 5881 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) 
(* 7145 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 5282 (* h1 h1 
h1) h2 h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 2288 (* h1 h1 h1) h2 h3 h4 (* h5 
h5 h5) h6 (* j2 j2)) (* 524 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5) h6 j2) (* 48 (* 
h1 h1 h1) h2 h3 h4 (* h5 h5 h5) h6) (* 32 (* h1 h1 h1) h2 h3 h4 (* h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 393 (* h1 h1 h1) h2 h3 h4 (* h5 h5) (* h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2077 (* h1 h1 h1) h2 h3 h4 (* h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 6140 (* h1 h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 11057 (* h1 h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2)) (* 12380 (* h1 h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)
) (* 8436 (* h1 h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 3284 (* h1 
h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 643 (* h1 h1 h1) h2 h3 h4 (* 
h5 h5) (* h6 h6) j2) (* 48 (* h1 h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6)) (* 16 (* 
h1 h1 h1) h2 h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 201 (* h1 
h1 h1) h2 h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1037 (* h1 h1 h1
) h2 h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2861 (* h1 h1 h1) h2 h3 
h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4593 (* h1 h1 h1) h2 h3 h4 h5 (* h6
 h6 h6) (* j2 j2 j2 j2 j2)) (* 4355 (* h1 h1 h1) h2 h3 h4 h5 (* h6 h6 h6) (* j2 
j2 j2 j2)) (* 2349 (* h1 h1 h1) h2 h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 644 
(* h1 h1 h1) h2 h3 h4 h5 (* h6 h6 h6) (* j2 j2)) (* 66 (* h1 h1 h1) h2 h3 h4 h5 
(* h6 h6 h6) j2) (* 4 (* h1 h1 h1) h2 h3 h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 32 (* h1 h1 h1) h2 h3 h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 100 (* h1 h1 h1) h2 h3 h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 156 (* h1
 h1 h1) h2 h3 h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 128 (* h1 h1 h1) h2 h3 
h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 52 (* h1 h1 h1) h2 h3 h4 (* h6 h6 h6 h6) 
(* j2 j2 j2)) (* 8 (* h1 h1 h1) h2 h3 h4 (* h6 h6 h6 h6) (* j2 j2)) (* 8 (* h1 
h1 h1) h2 h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 82 (* h1 h1 h1) 
h2 h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 344 (* h1 h1 h1) h2 h3 (* 
h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 768 (* h1 h1 h1) h2 h3 (* h5 h5 h5 h5)
 h6 (* j2 j2 j2 j2 j2)) (* 996 (* h1 h1 h1) h2 h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2
 j2)) (* 768 (* h1 h1 h1) h2 h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 344 (* h1 h1
 h1) h2 h3 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 82 (* h1 h1 h1) h2 h3 (* h5 h5 h5 h5
) h6 j2) (* 8 (* h1 h1 h1) h2 h3 (* h5 h5 h5 h5) h6) (* 29 (* h1 h1 h1) h2 h3 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 334 (* h1 h1 h1) h2 h3
 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1626 (* h1 h1 h1) h2 h3 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4372 (* h1 h1 h1) h2 h3 (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 7133 (* h1 h1 h1) h2 h3 (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 7315 (* h1 h1 h1) h2 h3 (* h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2)) (* 4715 (* h1 h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 
j2)) (* 1843 (* h1 h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 397 (* h1 
h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6) j2) (* 36 (* h1 h1 h1) h2 h3 (* h5 h5 h5) 
(* h6 h6)) (* 31 (* h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 349 (* h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 1662 (* h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 4372 (* h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 6964 (* h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 6928 
(* h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 4277 (* h1 h1 h1) 
h2 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 1567 (* h1 h1 h1) h2 h3 (* h5 h5) 
(* h6 h6 h6) (* j2 j2)) (* 306 (* h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6) j2) (* 
24 (* h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6)) (* 2 (* h1 h1 h1) h2 h3 h5 (* h6 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 24 (* h1 h1 h1) h2 h3 h5 (* h6 h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 118 (* h1 h1 h1) h2 h3 h5 (* h6 h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2)) (* 308 (* h1 h1 h1) h2 h3 h5 (* h6 h6 h6 h6) (* j2 j2
 j2 j2 j2 j2)) (* 464 (* h1 h1 h1) h2 h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 412 (* h1 h1 h1) h2 h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 210 (* h1 h1 h1
) h2 h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 56 (* h1 h1 h1) h2 h3 h5 (* h6 h6 h6
 h6) (* j2 j2)) (* 6 (* h1 h1 h1) h2 h3 h5 (* h6 h6 h6 h6) j2) (* 4 (* h1 h1 h1)
 h2 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 30 (* h1 h1 h1) h2 
(* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 85 (* h1 h1 h1) h2 (* h4 h4 
h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 113 (* h1 h1 h1) h2 (* h4 h4 h4) (* h5 
h5) h6 (* j2 j2 j2 j2)) (* 71 (* h1 h1 h1) h2 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2
 j2)) (* 19 (* h1 h1 h1) h2 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 2 (* h1 h1 
h1) h2 (* h4 h4 h4) (* h5 h5) h6 j2) (* 4 (* h1 h1 h1) h2 (* h4 h4 h4) h5 (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 26 (* h1 h1 h1) h2 (* h4 h4 h4) h5 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 62 (* h1 h1 h1) h2 (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 
j2 j2 j2)) (* 67 (* h1 h1 h1) h2 (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 
33 (* h1 h1 h1) h2 (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 7 (* h1 h1 h1) h2 
(* h4 h4 h4) h5 (* h6 h6) (* j2 j2)) (* (* h1 h1 h1) h2 (* h4 h4 h4) h5 (* h6 h6
) j2) (* 4 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 38 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
143 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 275 (* 
h1 h1 h1) h2 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 292 (* h1 h1 h1) 
h2 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 174 (* h1 h1 h1) h2 (* h4 h4) 
(* h5 h5 h5) h6 (* j2 j2 j2)) (* 56 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5 h5) h6 
(* j2 j2)) (* 8 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5 h5) h6 j2) (* 8 (* h1 h1 h1) 
h2 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 76 (* h1 h1 h1)
 h2 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 286 (* h1 h1 h1) 
h2 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 549 (* h1 h1 h1) h2 
(* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 578 (* h1 h1 h1) h2 (* h4 
h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 338 (* h1 h1 h1) h2 (* h4 h4) (* h5 
h5) (* h6 h6) (* j2 j2 j2)) (* 110 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 h6)
 (* j2 j2)) (* 20 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 h6) j2) (* (* h1 h1 
h1) h2 (* h4 h4) (* h5 h5) (* h6 h6)) (* 4 (* h1 h1 h1) h2 (* h4 h4) h5 (* h6 h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 34 (* h1 h1 h1) h2 (* h4 h4) h5 (* h6 h6 h6
) (* j2 j2 j2 j2 j2 j2 j2)) (* 113 (* h1 h1 h1) h2 (* h4 h4) h5 (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 184 (* h1 h1 h1) h2 (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2
 j2 j2)) (* 154 (* h1 h1 h1) h2 (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 67
 (* h1 h1 h1) h2 (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 16 (* h1 h1 h1) h2 
(* h4 h4) h5 (* h6 h6 h6) (* j2 j2)) (* 2 (* h1 h1 h1) h2 (* h4 h4) h5 (* h6 h6 
h6) j2) (* 2 (* h1 h1 h1) h2 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 17 (* h1 h1 h1) h2 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 58 (* 
h1 h1 h1) h2 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 103 (* h1 h1 h1) h2
 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 103 (* h1 h1 h1) h2 h4 (* h5 h5 h5
 h5) h6 (* j2 j2 j2 j2)) (* 58 (* h1 h1 h1) h2 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2
)) (* 17 (* h1 h1 h1) h2 h4 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 2 (* h1 h1 h1) h2 
h4 (* h5 h5 h5 h5) h6 j2) (* 4 (* h1 h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 46 (* h1 h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 218 (* h1 h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2
 j2 j2 j2 j2 j2)) (* 557 (* h1 h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 851 (* h1 h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 820 (* h1 h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 510 (* h1 
h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 201 (* h1 h1 h1) h2 h4 (* 
h5 h5 h5) (* h6 h6) (* j2 j2)) (* 45 (* h1 h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6) 
j2) (* 4 (* h1 h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6)) (* 4 (* h1 h1 h1) h2 h4 (* 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 46 (* h1 h1 h1) h2 h4 (* 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 217 (* h1 h1 h1) h2 h4 (* h5
 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 548 (* h1 h1 h1) h2 h4 (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 816 (* h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6
 h6) (* j2 j2 j2 j2 j2)) (* 748 (* h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2)) (* 428 (* h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 150
 (* h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 29 (* h1 h1 h1) h2 h4 
(* h5 h5) (* h6 h6 h6) j2) (* 2 (* h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6 h6)) (* 2 
(* h1 h1 h1) h2 h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 15 (* h1 
h1 h1) h2 h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 44 (* h1 h1 h1) h2 
h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 66 (* h1 h1 h1) h2 h4 h5 (* h6 
h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 56 (* h1 h1 h1) h2 h4 h5 (* h6 h6 h6 h6) (* j2 
j2 j2 j2)) (* 28 (* h1 h1 h1) h2 h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 8 (* h1 
h1 h1) h2 h4 h5 (* h6 h6 h6 h6) (* j2 j2)) (* (* h1 h1 h1) h2 h4 h5 (* h6 h6 h6 
h6) j2) (* (* h1 h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 11 (* h1 h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 51 (* h1 h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
131 (* h1 h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 206 (* 
h1 h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 206 (* h1 h1 h1) 
h2 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 131 (* h1 h1 h1) h2 (* h5 h5 h5
 h5) (* h6 h6) (* j2 j2 j2)) (* 51 (* h1 h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6) (* 
j2 j2)) (* 11 (* h1 h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6) j2) (* (* h1 h1 h1) h2 
(* h5 h5 h5 h5) (* h6 h6)) (* 2 (* h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 22 (* h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 103 (* h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2
 j2 j2 j2 j2 j2)) (* 270 (* h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 438 (* h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 457 (* h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 307 (* h1 
h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 128 (* h1 h1 h1) h2 (* h5 
h5 h5) (* h6 h6 h6) (* j2 j2)) (* 30 (* h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6) 
j2) (* 3 (* h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6)) (* (* h1 h1 h1) h2 (* h5 h5)
 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 11 (* h1 h1 h1) h2 (* h5 h5)
 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 51 (* h1 h1 h1) h2 (* h5 h5) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 131 (* h1 h1 h1) h2 (* h5 h5) (* h6
 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 206 (* h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6 
h6) (* j2 j2 j2 j2 j2)) (* 206 (* h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6 h6) (* j2 
j2 j2 j2)) (* 131 (* h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 51 
(* h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 11 (* h1 h1 h1) h2 (* h5
 h5) (* h6 h6 h6 h6) j2) (* (* h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6 h6)) (* 8 (* 
h1 h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 120 (* h1
 h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 744 (* h1 h1 
h1) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 2488 (* h1 h1 h1) (* 
h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 4864 (* h1 h1 h1) (* h3 h3 h3 
h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 5568 (* h1 h1 h1) (* h3 h3 h3 h3) (* h4 h4)
 h5 (* j2 j2 j2)) (* 3456 (* h1 h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2)) 
(* 896 (* h1 h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 j2) (* 16 (* h1 h1 h1) (* h3 h3
 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 192 (* h1 h1 h1) (* h3 h3 
h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 976 (* h1 h1 h1) (* h3 h3 h3 h3
) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 2720 (* h1 h1 h1) (* h3 h3 h3 h3) (* h4
 h4) h6 (* j2 j2 j2 j2 j2)) (* 4480 (* h1 h1 h1) (* h3 h3 h3 h3) (* h4 h4) h6 
(* j2 j2 j2 j2)) (* 4352 (* h1 h1 h1) (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2))
 (* 2304 (* h1 h1 h1) (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2)) (* 512 (* h1 h1 h1
) (* h3 h3 h3 h3) (* h4 h4) h6 j2) (* 4 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5
) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 76 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5
) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 608 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 2668 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) (* 
j2 j2 j2 j2 j2 j2)) (* 6996 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 
j2 j2 j2)) (* 11144 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) 
(* 10384 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 5024 (* h1 
h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2)) (* 896 (* h1 h1 h1) (* h3 h3 h3 
h3) h4 (* h5 h5) j2) (* 16 (* h1 h1 h1) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 280 (* h1 h1 h1) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 2080 (* h1 h1 h1) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2
)) (* 8576 (* h1 h1 h1) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 21512
 (* h1 h1 h1) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 33760 (* h1 h1 h1)
 (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 32704 (* h1 h1 h1) (* h3 h3 h3 h3)
 h4 h5 h6 (* j2 j2 j2)) (* 18432 (* h1 h1 h1) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2)
) (* 5248 (* h1 h1 h1) (* h3 h3 h3 h3) h4 h5 h6 j2) (* 512 (* h1 h1 h1) (* h3 h3
 h3 h3) h4 h5 h6) (* 16 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 224 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 1344 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 4496 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 9120 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 11392 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 8448 (* 
h1 h1 h1) (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2)) (* 3328 (* h1 h1 h1) (* h3 
h3 h3 h3) h4 (* h6 h6) (* j2 j2)) (* 512 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h6 
h6) j2) (* 24 (* h1 h1 h1) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 400 (* h1 h1 h1) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2
 j2)) (* 2824 (* h1 h1 h1) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)
) (* 11024 (* h1 h1 h1) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
26008 (* h1 h1 h1) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 38016 (* 
h1 h1 h1) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 33920 (* h1 h1 h1) 
(* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 17536 (* h1 h1 h1) (* h3 h3 h3 h3)
 (* h5 h5) h6 (* j2 j2)) (* 4736 (* h1 h1 h1) (* h3 h3 h3 h3) (* h5 h5) h6 j2) 
(* 512 (* h1 h1 h1) (* h3 h3 h3 h3) (* h5 h5) h6) (* 48 (* h1 h1 h1) (* h3 h3 h3
 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 704 (* h1 h1 h1) (* h3 h3 
h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4432 (* h1 h1 h1) (* h3 h3 
h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 15616 (* h1 h1 h1) (* h3 h3 h3 
h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 33648 (* h1 h1 h1) (* h3 h3 h3 h3) h5
 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 45472 (* h1 h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6
) (* j2 j2 j2 j2)) (* 38016 (* h1 h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 
j2)) (* 18688 (* h1 h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2)) (* 4864 (* h1
 h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6) j2) (* 512 (* h1 h1 h1) (* h3 h3 h3 h3) h5 
(* h6 h6)) (* 8 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 
j2)) (* 104 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 
536 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 1416 (* h1 
h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 2032 (* h1 h1 h1) (* h3 
h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 1504 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4 
h4) h5 (* j2 j2)) (* 448 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 j2) (* 16 (* 
h1 h1 h1) (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 160 (* h1 h1
 h1) (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 656 (* h1 h1 h1) (* 
h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 1408 (* h1 h1 h1) (* h3 h3 h3) 
(* h4 h4 h4) h6 (* j2 j2 j2 j2)) (* 1664 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4 h4) 
h6 (* j2 j2 j2)) (* 1024 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2)) 
(* 256 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4 h4) h6 j2) (* 14 (* h1 h1 h1) (* h3 h3
 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 210 (* h1 h1 h1) (* h3 
h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1302 (* h1 h1 h1) (* h3 
h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 4348 (* h1 h1 h1) (* h3 h3 
h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 8448 (* h1 h1 h1) (* h3 h3 h3) 
(* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 9502 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4)
 (* h5 h5) (* j2 j2 j2)) (* 5660 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) 
(* j2 j2)) (* 1344 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) j2) (* 52 (* h1
 h1 h1) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 664 (* h1 
h1 h1) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 3648 (* h1 h1 
h1) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 11112 (* h1 h1 h1) 
(* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 20172 (* h1 h1 h1) (* h3 h3 
h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 21808 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4
) h5 h6 (* j2 j2 j2)) (* 13168 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 
j2)) (* 3712 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 h6 j2) (* 256 (* h1 h1 h1) 
(* h3 h3 h3) (* h4 h4) h5 h6) (* 32 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) (* h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 376 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1848 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) (* h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 4896 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) (* h6 h6)
 (* j2 j2 j2 j2 j2)) (* 7488 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2
 j2 j2 j2)) (* 6528 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2)) 
(* 2944 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2)) (* 512 (* h1 h1
 h1) (* h3 h3 h3) (* h4 h4) (* h6 h6) j2) (* 4 (* h1 h1 h1) (* h3 h3 h3) h4 (* 
h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 73 (* h1 h1 h1) (* h3 h3 h3) h4 (* 
h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 554 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5
 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 2271 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5 
h5) (* j2 j2 j2 j2 j2 j2)) (* 5465 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) (* 
j2 j2 j2 j2 j2)) (* 7842 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 
j2)) (* 6479 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2)) (* 2764 (* 
h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2)) (* 448 (* h1 h1 h1) (* h3 h3 
h3) h4 (* h5 h5 h5) j2) (* 28 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2
 j2 j2 j2 j2 j2 j2 j2)) (* 474 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 3412 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2)) (* 13712 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 
j2 j2 j2 j2)) (* 33740 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 
j2)) (* 52162 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 
49766 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 27484 (* h1 h1 
h1) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 7664 (* h1 h1 h1) (* h3 h3 h3) h4
 (* h5 h5) h6 j2) (* 768 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) h6) (* 48 (* h1 
h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 696 (* h1
 h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4440 (* h1 
h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 16172 (* h1 h1 
h1) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 36516 (* h1 h1 h1) 
(* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 52012 (* h1 h1 h1) (* h3 h3 
h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 45616 (* h1 h1 h1) (* h3 h3 h3) h4 h5 
(* h6 h6) (* j2 j2 j2)) (* 23024 (* h1 h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2
 j2)) (* 5824 (* h1 h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6) j2) (* 512 (* h1 h1 h1) 
(* h3 h3 h3) h4 h5 (* h6 h6)) (* 16 (* h1 h1 h1) (* h3 h3 h3) h4 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 208 (* h1 h1 h1) (* h3 h3 h3) h4 (* h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1152 (* h1 h1 h1) (* h3 h3 h3) h4 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 3536 (* h1 h1 h1) (* h3 h3 h3) h4 (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 6544 (* h1 h1 h1) (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 
j2 j2 j2)) (* 7424 (* h1 h1 h1) (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2)) 
(* 4992 (* h1 h1 h1) (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2)) (* 1792 (* h1 h1
 h1) (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2)) (* 256 (* h1 h1 h1) (* h3 h3 h3) h4
 (* h6 h6 h6) j2) (* 24 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 382 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 2542 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2)) (* 9218 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2)) (* 19914 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) 
(* 26366 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 21258 (* 
h1 h1 h1) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 10028 (* h1 h1 h1) (* h3
 h3 h3) (* h5 h5 h5) h6 (* j2 j2)) (* 2512 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5 h5
) h6 j2) (* 256 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5 h5) h6) (* 96 (* h1 h1 h1) 
(* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1300 (* h1 
h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 7508 (* 
h1 h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 24220 
(* h1 h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 47988 
(* h1 h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 60372 (* h1
 h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 47948 (* h1 h1 h1) 
(* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 22960 (* h1 h1 h1) (* h3 h3 h3
) (* h5 h5) (* h6 h6) (* j2 j2)) (* 5968 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5) (* 
h6 h6) j2) (* 640 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6)) (* 48 (* h1 h1 
h1) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 656 (* h1 h1
 h1) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3824 (* h1 h1 
h1) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 12400 (* h1 h1 h1)
 (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 24464 (* h1 h1 h1) (* h3
 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 30192 (* h1 h1 h1) (* h3 h3 h3) 
h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 23104 (* h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6 
h6) (* j2 j2 j2)) (* 10496 (* h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2)) 
(* 2560 (* h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6) j2) (* 256 (* h1 h1 h1) (* h3 
h3 h3) h5 (* h6 h6 h6)) (* 2 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 
j2 j2 j2 j2)) (* 20 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2)
) (* 72 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 120 (* h1 
h1 h1) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2)) (* 94 (* h1 h1 h1) (* h3 h3) 
(* h4 h4 h4 h4) h5 (* j2 j2)) (* 28 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4 h4) h5 j2
) (* 4 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 28 
(* h1 h1 h1) (* h3 h3) (* h4 h4 h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 76 (* h1 h1 h1)
 (* h3 h3) (* h4 h4 h4 h4) h6 (* j2 j2 j2 j2)) (* 100 (* h1 h1 h1) (* h3 h3) (* 
h4 h4 h4 h4) h6 (* j2 j2 j2)) (* 64 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4 h4) h6 
(* j2 j2)) (* 16 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4 h4) h6 j2) (* 8 (* h1 h1 h1)
 (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 97 (* h1 h1 h1) 
(* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 456 (* h1 h1 h1) (* 
h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 1072 (* h1 h1 h1) (* h3 h3)
 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 1328 (* h1 h1 h1) (* h3 h3) (* h4 h4
 h4) (* h5 h5) (* j2 j2 j2)) (* 819 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5
) (* j2 j2)) (* 196 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) j2) (* 32 (* 
h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 302 (* h1 h1
 h1) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 1166 (* h1 h1 h1) 
(* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 2332 (* h1 h1 h1) (* h3 h3) 
(* h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 2530 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) 
h5 h6 (* j2 j2 j2)) (* 1418 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2))
 (* 340 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 h6 j2) (* 16 (* h1 h1 h1) (* h3 
h3) (* h4 h4 h4) h5 h6) (* 16 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 140 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 484 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 
j2 j2 j2 j2)) (* 836 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 
j2)) (* 748 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2)) (* 320 
(* h1 h1 h1) (* h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2)) (* 48 (* h1 h1 h1) (* 
h3 h3) (* h4 h4 h4) (* h6 h6) j2) (* 7 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5
 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 98 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 555 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 
h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1648 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 
h5) (* j2 j2 j2 j2 j2)) (* 2748 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) 
(* j2 j2 j2 j2)) (* 2532 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 
j2)) (* 1162 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 196 (* 
h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) j2) (* 45 (* h1 h1 h1) (* h3 h3) (* 
h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 545 (* h1 h1 h1) (* h3 h3) 
(* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2788 (* h1 h1 h1) (* h3 h3) 
(* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 7729 (* h1 h1 h1) (* h3 h3) (* 
h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 12422 (* h1 h1 h1) (* h3 h3) (* h4 h4
) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 11537 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 
h5) h6 (* j2 j2 j2)) (* 5854 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2
 j2)) (* 1416 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) h6 j2) (* 112 (* h1 h1 
h1) (* h3 h3) (* h4 h4) (* h5 h5) h6) (* 58 (* h1 h1 h1) (* h3 h3) (* h4 h4) h5 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 648 (* h1 h1 h1) (* h3 h3) (* h4 h4) 
h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3022 (* h1 h1 h1) (* h3 h3) (* h4 h4) 
h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 7578 (* h1 h1 h1) (* h3 h3) (* h4 h4) h5 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 10946 (* h1 h1 h1) (* h3 h3) (* h4 h4) h5 (* h6
 h6) (* j2 j2 j2 j2)) (* 9062 (* h1 h1 h1) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* 
j2 j2 j2)) (* 4034 (* h1 h1 h1) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 
820 (* h1 h1 h1) (* h3 h3) (* h4 h4) h5 (* h6 h6) j2) (* 48 (* h1 h1 h1) (* h3 
h3) (* h4 h4) h5 (* h6 h6)) (* 16 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 168 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h6 h6 h6
) (* j2 j2 j2 j2 j2 j2 j2)) (* 716 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2)) (* 1584 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2)) (* 1928 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 
j2 j2 j2)) (* 1260 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2)) 
(* 400 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2)) (* 48 (* h1 h1 
h1) (* h3 h3) (* h4 h4) (* h6 h6 h6) j2) (* (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 17 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 118 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5
 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 432 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2)) (* 900 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2
 j2 j2 j2)) (* 1074 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2)) 
(* 703 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2)) (* 227 (* h1 h1 
h1) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2)) (* 28 (* h1 h1 h1) (* h3 h3) h4 (* 
h5 h5 h5 h5) j2) (* 14 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 223 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2
 j2 j2 j2 j2)) (* 1490 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2)) (* 5462 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2)) (* 11960 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
15927 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 12639 (* h1 
h1 h1) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 5670 (* h1 h1 h1) (* h3 h3)
 h4 (* h5 h5 h5) h6 (* j2 j2)) (* 1288 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) h6
 j2) (* 112 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) h6) (* 41 (* h1 h1 h1) (* h3 
h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 570 (* h1 h1 h1) 
(* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3446 (* h1 h1 
h1) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 11659 (* h1 h1
 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 23876 (* h1 h1 
h1) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 30157 (* h1 h1 h1) 
(* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 23103 (* h1 h1 h1) (* h3 h3
) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 10209 (* h1 h1 h1) (* h3 h3) h4 (* h5 
h5) (* h6 h6) (* j2 j2)) (* 2336 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6) 
j2) (* 208 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6)) (* 28 (* h1 h1 h1) (* 
h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 360 (* h1 h1 h1) 
(* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2020 (* h1 h1 h1) 
(* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 6370 (* h1 h1 h1) (* 
h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 12128 (* h1 h1 h1) (* h3 h3)
 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 14042 (* h1 h1 h1) (* h3 h3) h4 h5 
(* h6 h6 h6) (* j2 j2 j2 j2)) (* 9612 (* h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6) 
(* j2 j2 j2)) (* 3682 (* h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2)) (* 
700 (* h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6) j2) (* 48 (* h1 h1 h1) (* h3 h3) 
h4 h5 (* h6 h6 h6)) (* 4 (* h1 h1 h1) (* h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 48 (* h1 h1 h1) (* h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 240 (* h1 h1 h1) (* h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2
 j2 j2 j2)) (* 648 (* h1 h1 h1) (* h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 1024 (* h1 h1 h1) (* h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
960 (* h1 h1 h1) (* h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 516 (* h1 h1 
h1) (* h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 144 (* h1 h1 h1) (* h3 h3) h4 
(* h6 h6 h6 h6) (* j2 j2)) (* 16 (* h1 h1 h1) (* h3 h3) h4 (* h6 h6 h6 h6) j2) 
(* 6 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 88 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
530 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1702 
(* h1 h1 h1) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 3174 (* h1 
h1 h1) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 3534 (* h1 h1 h1) (* 
h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 2352 (* h1 h1 h1) (* h3 h3) (* h5 
h5 h5 h5) h6 (* j2 j2 j2)) (* 910 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5 h5) h6 (* 
j2 j2)) (* 188 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5 h5) h6 j2) (* 16 (* h1 h1 h1) 
(* h3 h3) (* h5 h5 h5 h5) h6) (* 48 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 602 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3182 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 9242 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 16154 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 17542 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* h6
 h6) (* j2 j2 j2 j2)) (* 11818 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2)) (* 4768 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 
1048 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6) j2) (* 96 (* h1 h1 h1) (* h3 
h3) (* h5 h5 h5) (* h6 h6)) (* 54 (* h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 660 (* h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3410 (* h1 h1 h1) (* h3 h3) (* h5 h5) (* h6
 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 9718 (* h1 h1 h1) (* h3 h3) (* h5 h5) (* h6
 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 16734 (* h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2)) (* 17966 (* h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6
) (* j2 j2 j2 j2)) (* 12000 (* h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 
j2 j2)) (* 4810 (* h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 1052
 (* h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6) j2) (* 96 (* h1 h1 h1) (* h3 h3) 
(* h5 h5) (* h6 h6 h6)) (* 12 (* h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2
 j2 j2 j2 j2 j2 j2 j2)) (* 152 (* h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 804 (* h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2
 j2 j2 j2 j2 j2)) (* 2308 (* h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 3924 (* h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2))
 (* 4068 (* h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 2568 (* 
h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 956 (* h1 h1 h1) (* h3 
h3) h5 (* h6 h6 h6 h6) (* j2 j2)) (* 192 (* h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6 
h6) j2) (* 16 (* h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6 h6)) (* (* h1 h1 h1) h3 (* 
h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 9 (* h1 h1 h1) h3 (* h4 h4 h4 
h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 27 (* h1 h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5
) (* j2 j2 j2 j2)) (* 33 (* h1 h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2))
 (* 14 (* h1 h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2)) (* 5 (* h1 h1 h1) h3
 (* h4 h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 28 (* h1 h1 h1) h3 (* h4 h4 h4 
h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 58 (* h1 h1 h1) h3 (* h4 h4 h4 h4) h5 h6 (* j2 
j2 j2 j2)) (* 52 (* h1 h1 h1) h3 (* h4 h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 17 (* h1
 h1 h1) h3 (* h4 h4 h4 h4) h5 h6 (* j2 j2)) (* 2 (* h1 h1 h1) h3 (* h4 h4 h4 h4)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 10 (* h1 h1 h1) h3 (* h4 h4 h4 h4) (* h6 h6
) (* j2 j2 j2 j2 j2)) (* 18 (* h1 h1 h1) h3 (* h4 h4 h4 h4) (* h6 h6) (* j2 j2 
j2 j2)) (* 14 (* h1 h1 h1) h3 (* h4 h4 h4 h4) (* h6 h6) (* j2 j2 j2)) (* 4 (* h1
 h1 h1) h3 (* h4 h4 h4 h4) (* h6 h6) (* j2 j2)) (* 2 (* h1 h1 h1) h3 (* h4 h4 h4
) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 22 (* h1 h1 h1) h3 (* h4 h4 h4) (* 
h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 90 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5)
 (* j2 j2 j2 j2 j2)) (* 174 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 
j2 j2)) (* 160 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 56 (* 
h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2)) (* 16 (* h1 h1 h1) h3 (* h4 h4
 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 135 (* h1 h1 h1) h3 (* h4 h4 h4) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 456 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5
) h6 (* j2 j2 j2 j2 j2)) (* 763 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 
j2 j2 j2)) (* 632 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 221
 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 15 (* h1 h1 h1) h3 (* 
h4 h4 h4) (* h5 h5) h6 j2) (* 18 (* h1 h1 h1) h3 (* h4 h4 h4) h5 (* h6 h6) (* j2
 j2 j2 j2 j2 j2 j2)) (* 139 (* h1 h1 h1) h3 (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 412 (* h1 h1 h1) h3 (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2
)) (* 587 (* h1 h1 h1) h3 (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 408 (* 
h1 h1 h1) h3 (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 120 (* h1 h1 h1) h3 (* 
h4 h4 h4) h5 (* h6 h6) (* j2 j2)) (* 8 (* h1 h1 h1) h3 (* h4 h4 h4) h5 (* h6 h6)
 j2) (* 4 (* h1 h1 h1) h3 (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 28 (* h1 h1 h1) h3 (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 72 (* 
h1 h1 h1) h3 (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 84 (* h1 h1 h1) h3
 (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 44 (* h1 h1 h1) h3 (* h4 h4 h4) 
(* h6 h6 h6) (* j2 j2 j2)) (* 8 (* h1 h1 h1) h3 (* h4 h4 h4) (* h6 h6 h6) (* j2 
j2)) (* (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 12 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 55 
(* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 123 (* h1 h1
 h1) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 140 (* h1 h1 h1) h3 (* 
h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 75 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5
 h5 h5) (* j2 j2 j2)) (* 14 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2))
 (* 13 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 140 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
628 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 1489 (* 
h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 1964 (* h1 h1 h1) 
h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 1401 (* h1 h1 h1) h3 (* h4 h4) 
(* h5 h5 h5) h6 (* j2 j2 j2)) (* 487 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) h6 
(* j2 j2)) (* 60 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) h6 j2) (* 29 (* h1 h1 h1
) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 295 (* h1 h1 
h1) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1230 (* h1 h1 
h1) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2710 (* h1 h1 h1)
 h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 3374 (* h1 h1 h1) h3 
(* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 2337 (* h1 h1 h1) h3 (* h4 h4)
 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 819 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5) 
(* h6 h6) (* j2 j2)) (* 116 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5) (* h6 h6) j2) 
(* 4 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5) (* h6 h6)) (* 17 (* h1 h1 h1) h3 (* h4 
h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 164 (* h1 h1 h1) h3 (* h4 h4
) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 631 (* h1 h1 h1) h3 (* h4 h4) h5 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1232 (* h1 h1 h1) h3 (* h4 h4) h5 (* h6 
h6 h6) (* j2 j2 j2 j2 j2)) (* 1290 (* h1 h1 h1) h3 (* h4 h4) h5 (* h6 h6 h6) (* 
j2 j2 j2 j2)) (* 711 (* h1 h1 h1) h3 (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 
185 (* h1 h1 h1) h3 (* h4 h4) h5 (* h6 h6 h6) (* j2 j2)) (* 16 (* h1 h1 h1) h3 
(* h4 h4) h5 (* h6 h6 h6) j2) (* 2 (* h1 h1 h1) h3 (* h4 h4) (* h6 h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1 h1) h3 (* h4 h4) (* h6 h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 50 (* h1 h1 h1) h3 (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 78 (* h1 h1 h1) h3 (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 64 (* h1 h1 h1) h3 (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 26 (* h1 h1 
h1) h3 (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 4 (* h1 h1 h1) h3 (* h4 h4) 
(* h6 h6 h6 h6) (* j2 j2)) (* 2 (* h1 h1 h1) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 29 (* h1 h1 h1) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 170 (* h1 h1 h1) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 521 (* h1 h1 h1) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
901 (* h1 h1 h1) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 889 (* h1 h1 h1
) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 487 (* h1 h1 h1) h3 h4 (* h5 h5 
h5 h5) h6 (* j2 j2 j2)) (* 136 (* h1 h1 h1) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2)) 
(* 15 (* h1 h1 h1) h3 h4 (* h5 h5 h5 h5) h6 j2) (* 12 (* h1 h1 h1) h3 h4 (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 150 (* h1 h1 h1) h3 h4 (* h5
 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 810 (* h1 h1 h1) h3 h4 (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2434 (* h1 h1 h1) h3 h4 (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4393 (* h1 h1 h1) h3 h4 (* h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2)) (* 4843 (* h1 h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2)) (* 3206 (* h1 h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) 
(* 1207 (* h1 h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 229 (* h1 h1 h1)
 h3 h4 (* h5 h5 h5) (* h6 h6) j2) (* 16 (* h1 h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6
)) (* 14 (* h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2
)) (* 166 (* h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2))
 (* 851 (* h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
2430 (* h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4154 
(* h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 4294 (* h1 h1 
h1) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 2624 (* h1 h1 h1) h3 h4 (* 
h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 892 (* h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6 
h6) (* j2 j2)) (* 147 (* h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6) j2) (* 8 (* h1 
h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6)) (* 4 (* h1 h1 h1) h3 h4 h5 (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 46 (* h1 h1 h1) h3 h4 h5 (* h6 h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 216 (* h1 h1 h1) h3 h4 h5 (* h6 h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 536 (* h1 h1 h1) h3 h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 764 (* h1 h1 h1) h3 h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 640 (* 
h1 h1 h1) h3 h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 308 (* h1 h1 h1) h3 h4 h5
 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 78 (* h1 h1 h1) h3 h4 h5 (* h6 h6 h6 h6) (* j2
 j2)) (* 8 (* h1 h1 h1) h3 h4 h5 (* h6 h6 h6 h6) j2) (* 6 (* h1 h1 h1) h3 (* h5 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 70 (* h1 h1 h1) h3 (* h5 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 338 (* h1 h1 h1) h3 (* h5 h5
 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 880 (* h1 h1 h1) h3 (* h5 h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1356 (* h1 h1 h1) h3 (* h5 h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2)) (* 1284 (* h1 h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2)) (* 750 (* h1 h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 
262 (* h1 h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 50 (* h1 h1 h1) h3 
(* h5 h5 h5 h5) (* h6 h6) j2) (* 4 (* h1 h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6)) 
(* 12 (* h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 140 (* h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 682 (* h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
1812 (* h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2888 
(* h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2868 (* h1 h1 
h1) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1780 (* h1 h1 h1) h3 (* h5 
h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 668 (* h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6 
h6) (* j2 j2)) (* 138 (* h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6) j2) (* 12 (* h1 
h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6)) (* 6 (* h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 70 (* h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 338 (* h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6 h6
) (* j2 j2 j2 j2 j2 j2 j2)) (* 880 (* h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 1356 (* h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 
j2 j2 j2)) (* 1284 (* h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) 
(* 750 (* h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 262 (* h1 h1 
h1) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 50 (* h1 h1 h1) h3 (* h5 h5) (* 
h6 h6 h6 h6) j2) (* 4 (* h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6 h6)) (* (* h1 h1 h1)
 (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 5 (* h1 h1 h1) (* h4 h4 
h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 8 (* h1 h1 h1) (* h4 h4 h4 h4) (* h5 
h5) h6 (* j2 j2 j2 j2)) (* 4 (* h1 h1 h1) (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2 
j2)) (* (* h1 h1 h1) (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4 
(* h1 h1 h1) (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 5 (* h1 h1 h1) 
(* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 2 (* h1 h1 h1) (* h4 h4 h4 h4) 
h5 (* h6 h6) (* j2 j2 j2)) (* 2 (* h1 h1 h1) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2)) (* 14 (* h1 h1 h1) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2)) (* 36 (* h1 h1 h1) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) 
(* 40 (* h1 h1 h1) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 16 (* h1 h1 
h1) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 4 (* h1 h1 h1) (* h4 h4 h4) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 27 (* h1 h1 h1) (* h4 h4 h4) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 67 (* h1 h1 h1) (* h4 h4 h4) (* h5
 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 73 (* h1 h1 h1) (* h4 h4 h4) (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2)) (* 31 (* h1 h1 h1) (* h4 h4 h4) (* h5 h5) (* h6 h6) (* 
j2 j2 j2)) (* 2 (* h1 h1 h1) (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 2 
(* h1 h1 h1) (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 12 (* h1 
h1 h1) (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 24 (* h1 h1 h1) 
(* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 18 (* h1 h1 h1) (* h4 h4 h4)
 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 4 (* h1 h1 h1) (* h4 h4 h4) h5 (* h6 h6 h6)
 (* j2 j2 j2)) (* (* h1 h1 h1) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 8 (* h1 h1 h1) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)
) (* 24 (* h1 h1 h1) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 33 
(* h1 h1 h1) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 20 (* h1 h1 h1)
 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 4 (* h1 h1 h1) (* h4 h4) (* h5
 h5 h5 h5) h6 (* j2 j2 j2)) (* 4 (* h1 h1 h1) (* h4 h4) (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 35 (* h1 h1 h1) (* h4 h4) (* h5 h5 h5) (* h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2)) (* 119 (* h1 h1 h1) (* h4 h4) (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 199 (* h1 h1 h1) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2)) (* 169 (* h1 h1 h1) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2)) (* 66 (* h1 h1 h1) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 8 
(* h1 h1 h1) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 4 (* h1 h1 h1) (* h4
 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 34 (* h1 h1 h1) (* 
h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 111 (* h1 h1 h1) (* 
h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 174 (* h1 h1 h1) (* h4 
h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 133 (* h1 h1 h1) (* h4 h4) (* 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 44 (* h1 h1 h1) (* h4 h4) (* h5 h5) (* 
h6 h6 h6) (* j2 j2 j2)) (* 4 (* h1 h1 h1) (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2
 j2)) (* (* h1 h1 h1) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 7 (* h1 h1 h1) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 18 
(* h1 h1 h1) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 21 (* h1 h1 
h1) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 11 (* h1 h1 h1) (* h4 h4
) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 2 (* h1 h1 h1) (* h4 h4) h5 (* h6 h6 h6
 h6) (* j2 j2 j2)) (* (* h1 h1 h1) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 10 (* h1 h1 h1) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 40 (* h1 h1 h1) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 82 (* h1 h1 h1) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 92 (* h1 h1 h1) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 56 (* h1 
h1 h1) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 17 (* h1 h1 h1) h4 (* h5
 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 2 (* h1 h1 h1) h4 (* h5 h5 h5 h5) (* h6 h6
) (* j2 j2)) (* 2 (* h1 h1 h1) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2 j2)) (* 20 (* h1 h1 h1) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 81 (* h1 h1 h1) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2
)) (* 171 (* h1 h1 h1) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
202 (* h1 h1 h1) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 133 (* h1 
h1 h1) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 45 (* h1 h1 h1) h4 (* h5
 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 6 (* h1 h1 h1) h4 (* h5 h5 h5) (* h6 h6 h6
) (* j2 j2)) (* (* h1 h1 h1) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 10 (* h1 h1 h1) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 40 (* h1 h1 h1) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 82 (* h1 h1 h1) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 92 
(* h1 h1 h1) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 56 (* h1 h1 h1)
 h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 17 (* h1 h1 h1) h4 (* h5 h5) 
(* h6 h6 h6 h6) (* j2 j2 j2)) (* 2 (* h1 h1 h1) h4 (* h5 h5) (* h6 h6 h6 h6) (* 
j2 j2)) (* 4 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 60 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 344 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2 j2 j2)) (* 1032 
(* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2 j2)) (* 1812 (* h1 h1) 
(* h2 h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2)) (* 1932 (* h1 h1) (* h2 h2 h2 
h2) (* h3 h3 h3) h5 (* j2 j2 j2)) (* 1232 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3)
 h5 (* j2 j2)) (* 432 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h5 j2) (* 64 (* h1 
h1) (* h2 h2 h2 h2) (* h3 h3 h3) h5) (* 8 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3)
 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 80 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h6
 (* j2 j2 j2 j2 j2 j2 j2)) (* 336 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h6 (* 
j2 j2 j2 j2 j2 j2)) (* 768 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2
 j2 j2)) (* 1032 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2 j2)) (* 
816 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2)) (* 352 (* h1 h1) (* 
h2 h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2)) (* 64 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3
 h3) h6 j2) (* 6 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 
j2)) (* 78 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 
360 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 828 (* h1 
h1) (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2)) (* 1062 (* h1 h1) (* h2 h2 
h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2)) (* 774 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) 
h4 h5 (* j2 j2)) (* 300 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h5 j2) (* 48 (* 
h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h5) (* 12 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3
) h4 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 96 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 
h6 (* j2 j2 j2 j2 j2 j2)) (* 312 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h6 (* j2
 j2 j2 j2 j2)) (* 528 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2))
 (* 492 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2)) (* 240 (* h1 h1)
 (* h2 h2 h2 h2) (* h3 h3) h4 h6 (* j2 j2)) (* 48 (* h1 h1) (* h2 h2 h2 h2) (* 
h3 h3) h4 h6 j2) (* 4 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 56 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2
 j2 j2 j2 j2)) (* 292 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 
j2 j2 j2)) (* 792 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2 
j2)) (* 1260 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 
1224 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2)) (* 716 (* h1 h1
) (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* j2 j2)) (* 232 (* h1 h1) (* h2 h2 h2 h2
) (* h3 h3) (* h5 h5) j2) (* 32 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h5 h5)) 
(* 8 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
86 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 394 
(* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 1000 (* h1 
h1) (* h2 h2 h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 1532 (* h1 h1) (* h2 
h2 h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 1446 (* h1 h1) (* h2 h2 h2 h2) (* 
h3 h3) h5 h6 (* j2 j2 j2)) (* 818 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 h6 (* 
j2 j2)) (* 252 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 h6 j2) (* 32 (* h1 h1) (* 
h2 h2 h2 h2) (* h3 h3) h5 h6) (* 8 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 72 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h6 h6
) (* j2 j2 j2 j2 j2 j2 j2)) (* 272 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h6 h6)
 (* j2 j2 j2 j2 j2 j2)) (* 560 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h6 h6) (* 
j2 j2 j2 j2 j2)) (* 680 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 
j2 j2)) (* 488 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2)) (* 
192 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2)) (* 32 (* h1 h1) (* 
h2 h2 h2 h2) (* h3 h3) (* h6 h6) j2) (* 3 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h5 
h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 36 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h5 h5) 
(* j2 j2 j2 j2 j2 j2)) (* 147 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2
 j2 j2 j2)) (* 300 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2)) 
(* 345 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2)) (* 228 (* h1 h1) 
(* h2 h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2)) (* 81 (* h1 h1) (* h2 h2 h2 h2) h3 h4
 (* h5 h5) j2) (* 12 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h5 h5)) (* 11 (* h1 h1) 
(* h2 h2 h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 75 (* h1 h1) (* h2 h2 
h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 210 (* h1 h1) (* h2 h2 h2 h2) h3 h4
 h5 h6 (* j2 j2 j2 j2 j2)) (* 310 (* h1 h1) (* h2 h2 h2 h2) h3 h4 h5 h6 (* j2 j2
 j2 j2)) (* 255 (* h1 h1) (* h2 h2 h2 h2) h3 h4 h5 h6 (* j2 j2 j2)) (* 111 (* h1
 h1) (* h2 h2 h2 h2) h3 h4 h5 h6 (* j2 j2)) (* 20 (* h1 h1) (* h2 h2 h2 h2) h3 
h4 h5 h6 j2) (* 6 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2
 j2)) (* 36 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
84 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 96 (* h1 h1)
 (* h2 h2 h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2 j2)) (* 54 (* h1 h1) (* h2 h2 h2 h2
) h3 h4 (* h6 h6) (* j2 j2 j2)) (* 12 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h6 h6) 
(* j2 j2)) (* (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 13 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 61 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 149 
(* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 215 (* h1 h1) 
(* h2 h2 h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 191 (* h1 h1) (* h2 h2 h2 h2
) h3 (* h5 h5 h5) (* j2 j2 j2)) (* 103 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5 h5)
 (* j2 j2)) (* 31 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5 h5) j2) (* 4 (* h1 h1) 
(* h2 h2 h2 h2) h3 (* h5 h5 h5)) (* 4 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 40 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2)) (* 166 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) h6 (* j2 j2
 j2 j2 j2 j2)) (* 378 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2 
j2)) (* 520 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 444 
(* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2)) (* 230 (* h1 h1) (* h2 
h2 h2 h2) h3 (* h5 h5) h6 (* j2 j2)) (* 66 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5
) h6 j2) (* 8 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) h6) (* 5 (* h1 h1) (* h2 h2
 h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 41 (* h1 h1) (* h2 h2 h2
 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 138 (* h1 h1) (* h2 h2 h2 h2) 
h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 250 (* h1 h1) (* h2 h2 h2 h2) h3 h5 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 265 (* h1 h1) (* h2 h2 h2 h2) h3 h5 (* h6 h6) 
(* j2 j2 j2 j2)) (* 165 (* h1 h1) (* h2 h2 h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2)) 
(* 56 (* h1 h1) (* h2 h2 h2 h2) h3 h5 (* h6 h6) (* j2 j2)) (* 8 (* h1 h1) (* h2 
h2 h2 h2) h3 h5 (* h6 h6) j2) (* 2 (* h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 14 (* h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 40 (* h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 60 (* h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 50 (* h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 22 (* h1 h1)
 (* h2 h2 h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2)) (* 4 (* h1 h1) (* h2 h2 h2 h2) h3
 (* h6 h6 h6) (* j2 j2)) (* 3 (* h1 h1) (* h2 h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2
 j2 j2 j2 j2 j2)) (* 20 (* h1 h1) (* h2 h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2
 j2 j2)) (* 57 (* h1 h1) (* h2 h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
90 (* h1 h1) (* h2 h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 85 (* h1 h1) 
(* h2 h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 48 (* h1 h1) (* h2 h2 h2 h2) h4
 (* h5 h5) h6 (* j2 j2)) (* 15 (* h1 h1) (* h2 h2 h2 h2) h4 (* h5 h5) h6 j2) (* 
2 (* h1 h1) (* h2 h2 h2 h2) h4 (* h5 h5) h6) (* 3 (* h1 h1) (* h2 h2 h2 h2) h4 
h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 17 (* h1 h1) (* h2 h2 h2 h2) h4 h5 (* 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 40 (* h1 h1) (* h2 h2 h2 h2) h4 h5 (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* 50 (* h1 h1) (* h2 h2 h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 
j2)) (* 35 (* h1 h1) (* h2 h2 h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 13 (* h1 
h1) (* h2 h2 h2 h2) h4 h5 (* h6 h6) (* j2 j2)) (* 2 (* h1 h1) (* h2 h2 h2 h2) h4
 h5 (* h6 h6) j2) (* (* h1 h1) (* h2 h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 8 (* h1 h1) (* h2 h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2)) (* 28 (* h1 h1) (* h2 h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
56 (* h1 h1) (* h2 h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 70 (* h1 h1)
 (* h2 h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 56 (* h1 h1) (* h2 h2 h2 h2
) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 28 (* h1 h1) (* h2 h2 h2 h2) (* h5 h5 h5) h6 
(* j2 j2)) (* 8 (* h1 h1) (* h2 h2 h2 h2) (* h5 h5 h5) h6 j2) (* (* h1 h1) (* h2
 h2 h2 h2) (* h5 h5 h5) h6) (* 2 (* h1 h1) (* h2 h2 h2 h2) (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 15 (* h1 h1) (* h2 h2 h2 h2) (* h5 h5) (* h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2)) (* 49 (* h1 h1) (* h2 h2 h2 h2) (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 91 (* h1 h1) (* h2 h2 h2 h2) (* h5 h5) (* h6 h6) (* j2
 j2 j2 j2 j2)) (* 105 (* h1 h1) (* h2 h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2)) (* 77 (* h1 h1) (* h2 h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 35 (* 
h1 h1) (* h2 h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 j2)) (* 9 (* h1 h1) (* h2 h2 h2
 h2) (* h5 h5) (* h6 h6) j2) (* (* h1 h1) (* h2 h2 h2 h2) (* h5 h5) (* h6 h6)) 
(* (* h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 7 
(* h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 21 (* h1 
h1) (* h2 h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 35 (* h1 h1) (* h2
 h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 35 (* h1 h1) (* h2 h2 h2 h2) 
h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 21 (* h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6 h6)
 (* j2 j2 j2)) (* 7 (* h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2)) (* (* 
h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6 h6) j2) (* 8 (* h1 h1) (* h2 h2 h2) (* h3 h3 
h3 h3) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 128 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3
 h3) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 800 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) 
h5 (* j2 j2 j2 j2 j2 j2)) (* 2640 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* 
j2 j2 j2 j2 j2)) (* 5112 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2 j2 
j2)) (* 6000 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2 j2)) (* 4192 (* 
h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2)) (* 1600 (* h1 h1) (* h2 h2 h2)
 (* h3 h3 h3 h3) h5 j2) (* 256 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h5) (* 16 
(* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 176 
(* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 816 (* h1
 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2 j2 j2 j2 j2)) (* 2064 (* h1 h1) 
(* h2 h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2 j2 j2 j2)) (* 3072 (* h1 h1) (* h2 h2 
h2) (* h3 h3 h3 h3) h6 (* j2 j2 j2 j2)) (* 2688 (* h1 h1) (* h2 h2 h2) (* h3 h3 
h3 h3) h6 (* j2 j2 j2)) (* 1280 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h6 (* j2 
j2)) (* 256 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h6 j2) (* 24 (* h1 h1) (* h2 
h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 376 (* h1 h1) (* h2 h2
 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 2328 (* h1 h1) (* h2 h2 h2)
 (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 7640 (* h1 h1) (* h2 h2 h2) (* h3 
h3 h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 14720 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4
 h5 (* j2 j2 j2 j2)) (* 17168 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2
 j2)) (* 11888 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2)) (* 4480 (* 
h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h5 j2) (* 704 (* h1 h1) (* h2 h2 h2) (* h3 
h3 h3) h4 h5) (* 48 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 528 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2
 j2)) (* 2448 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2)) 
(* 6192 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 9216 
(* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 8064 (* h1 h1) (* 
h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2)) (* 3840 (* h1 h1) (* h2 h2 h2) (* h3 
h3 h3) h4 h6 (* j2 j2)) (* 768 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h6 j2) (* 
6 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 130 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 1088 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)
) (* 4620 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) 
(* 11310 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 
16962 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 15852 
(* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2)) (* 9008 (* h1 h1) 
(* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2)) (* 2848 (* h1 h1) (* h2 h2 h2) 
(* h3 h3 h3) (* h5 h5) j2) (* 384 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h5 h5))
 (* 128 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 1300 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
5648 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 13688 
(* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 20192 (* h1 h1)
 (* h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 18500 (* h1 h1) (* h2 h2 h2
) (* h3 h3 h3) h5 h6 (* j2 j2 j2)) (* 10224 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) 
h5 h6 (* j2 j2)) (* 3088 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 h6 j2) (* 384 
(* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 h6) (* 24 (* h1 h1) (* h2 h2 h2) (* h3 h3
 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 296 (* h1 h1) (* h2 h2 h2) (* 
h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1568 (* h1 h1) (* h2 h2 h2) 
(* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4656 (* h1 h1) (* h2 h2 h2) 
(* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 8472 (* h1 h1) (* h2 h2 h2) (* 
h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 9672 (* h1 h1) (* h2 h2 h2) (* h3 h3 
h3) (* h6 h6) (* j2 j2 j2 j2)) (* 6768 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h6
 h6) (* j2 j2 j2)) (* 2656 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 
j2)) (* 448 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h6 h6) j2) (* 18 (* h1 h1) 
(* h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 238 (* h1 h1) 
(* h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 1168 (* h1 h1) (* 
h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 2892 (* h1 h1) (* h2 h2 
h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 3986 (* h1 h1) (* h2 h2 h2) (* h3
 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 3094 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h4 
h4) h5 (* j2 j2)) (* 1260 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 j2) (* 
208 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h4 h4) h5) (* 36 (* h1 h1) (* h2 h2 h2) 
(* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 312 (* h1 h1) (* h2 h2 h2) 
(* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 1104 (* h1 h1) (* h2 h2 h2) (* 
h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 2040 (* h1 h1) (* h2 h2 h2) (* h3 h3)
 (* h4 h4) h6 (* j2 j2 j2 j2)) (* 2076 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h4 h4
) h6 (* j2 j2 j2)) (* 1104 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 
j2)) (* 240 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h4 h4) h6 j2) (* 24 (* h1 h1) 
(* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 350 (* h1 h1
) (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1967 (* h1 h1
) (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 5766 (* h1 h1) 
(* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 9832 (* h1 h1) (* h2 
h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 10112 (* h1 h1) (* h2 h2 h2) 
(* h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 6177 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4
 (* h5 h5) (* j2 j2)) (* 2060 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) j2) 
(* 288 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h5 h5)) (* 72 (* h1 h1) (* h2 h2 
h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 776 (* h1 h1) (* h2 h2 h2
) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 3608 (* h1 h1) (* h2 h2 h2) 
(* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 9372 (* h1 h1) (* h2 h2 h2) (* h3 
h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 14764 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5
 h6 (* j2 j2 j2 j2)) (* 14348 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2
 j2)) (* 8340 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2)) (* 2624 (* h1
 h1) (* h2 h2 h2) (* h3 h3) h4 h5 h6 j2) (* 336 (* h1 h1) (* h2 h2 h2) (* h3 h3)
 h4 h5 h6) (* 48 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 480 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 2004 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 4524 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2)
) (* 5964 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 4596
 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2)) (* 1920 (* h1 h1) 
(* h2 h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2)) (* 336 (* h1 h1) (* h2 h2 h2) (* 
h3 h3) h4 (* h6 h6) j2) (* 3 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* j2
 j2 j2 j2 j2 j2 j2 j2 j2)) (* 62 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 484 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5 h5
) (* j2 j2 j2 j2 j2 j2 j2)) (* 1867 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5 h5
) (* j2 j2 j2 j2 j2 j2)) (* 4095 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) 
(* j2 j2 j2 j2 j2)) (* 5472 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 
j2 j2 j2)) (* 4554 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2)) 
(* 2311 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2)) (* 656 (* h1 h1
) (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) j2) (* 80 (* h1 h1) (* h2 h2 h2) (* h3 h3)
 (* h5 h5 h5)) (* 3 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 164 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 1343 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2)) (* 5060 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 
j2 j2 j2 j2 j2)) (* 10895 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2
 j2 j2 j2)) (* 14474 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 
j2)) (* 12075 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 
6150 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2)) (* 1740 (* h1 h1) 
(* h2 h2 h2) (* h3 h3) (* h5 h5) h6 j2) (* 208 (* h1 h1) (* h2 h2 h2) (* h3 h3) 
(* h5 h5) h6) (* 24 (* h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 300 (* h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 1628 (* h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 5004 (* h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 9558 (* h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 
j2 j2 j2)) (* 11722 (* h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2
)) (* 9194 (* h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 4422 
(* h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2)) (* 1172 (* h1 h1) (* h2
 h2 h2) (* h3 h3) h5 (* h6 h6) j2) (* 128 (* h1 h1) (* h2 h2 h2) (* h3 h3) h5 
(* h6 h6)) (* 12 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2 j2)) (* 136 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 656 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 1760 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 2876 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 
j2 j2)) (* 2936 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2)) 
(* 1832 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2)) (* 640 (* h1
 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2)) (* 96 (* h1 h1) (* h2 h2 h2)
 (* h3 h3) (* h6 h6 h6) j2) (* 9 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 110 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) 
(* j2 j2 j2 j2 j2 j2)) (* 481 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* 
j2 j2 j2 j2 j2)) (* 1044 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 
j2 j2)) (* 1255 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 
850 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2)) (* 303 (* h1 h1) 
(* h2 h2 h2) h3 (* h4 h4) (* h5 h5) j2) (* 44 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4
) (* h5 h5)) (* 39 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 285 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) 
(* 850 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 1322 (* 
h1 h1) (* h2 h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 1131 (* h1 h1) (* h2 
h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2)) (* 505 (* h1 h1) (* h2 h2 h2) h3 (* h4 
h4) h5 h6 (* j2 j2)) (* 92 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) h5 h6 j2) (* 18 
(* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 120 
(* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 312 (* 
h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 396 (* h1 h1) 
(* h2 h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 246 (* h1 h1) (* h2 h2 
h2) h3 (* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 60 (* h1 h1) (* h2 h2 h2) h3 (* h4 
h4) (* h6 h6) (* j2 j2)) (* 6 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2
 j2 j2 j2 j2 j2 j2)) (* 82 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2
 j2 j2 j2 j2)) (* 421 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 
j2 j2)) (* 1111 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) 
(* 1696 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 1560 (* h1
 h1) (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2)) (* 853 (* h1 h1) (* h2 h2 h2)
 h3 h4 (* h5 h5 h5) (* j2 j2)) (* 255 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5 h5) 
j2) (* 32 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5 h5)) (* 36 (* h1 h1) (* h2 h2 h2
) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 355 (* h1 h1) (* h2 h2 h2) 
h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1500 (* h1 h1) (* h2 h2 h2) h3 
h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 3519 (* h1 h1) (* h2 h2 h2) h3 h4 (* 
h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 4990 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) h6 
(* j2 j2 j2 j2)) (* 4367 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2))
 (* 2298 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2)) (* 663 (* h1 h1) 
(* h2 h2 h2) h3 h4 (* h5 h5) h6 j2) (* 80 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5)
 h6) (* 42 (* h1 h1) (* h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 374 (* h1 h1) (* h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
1372 (* h1 h1) (* h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2695 
(* h1 h1) (* h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 3071 (* h1 h1) 
(* h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 2035 (* h1 h1) (* h2 h2 h2) 
h3 h4 h5 (* h6 h6) (* j2 j2 j2)) (* 727 (* h1 h1) (* h2 h2 h2) h3 h4 h5 (* h6 h6
) (* j2 j2)) (* 108 (* h1 h1) (* h2 h2 h2) h3 h4 h5 (* h6 h6) j2) (* 12 (* h1 h1
) (* h2 h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 96 (* h1 h1) 
(* h2 h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 312 (* h1 h1) (* h2
 h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 528 (* h1 h1) (* h2 h2 h2) 
h3 h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 492 (* h1 h1) (* h2 h2 h2) h3 h4 (* h6
 h6 h6) (* j2 j2 j2 j2)) (* 240 (* h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6 h6) (* j2 
j2 j2)) (* 48 (* h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2)) (* (* h1 h1) 
(* h2 h2 h2) h3 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 13 (* h1 h1) (* 
h2 h2 h2) h3 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 61 (* h1 h1) (* h2 h2 
h2) h3 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 149 (* h1 h1) (* h2 h2 h2) h3 
(* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 215 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5
 h5) (* j2 j2 j2 j2)) (* 191 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* j2 j2 
j2)) (* 103 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* j2 j2)) (* 31 (* h1 h1)
 (* h2 h2 h2) h3 (* h5 h5 h5 h5) j2) (* 4 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5 
h5)) (* 35 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 303 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
1118 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 2298 
(* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 2879 (* h1 h1) 
(* h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 2251 (* h1 h1) (* h2 h2 h2) 
h3 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 1072 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) 
h6 (* j2 j2)) (* 284 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) h6 j2) (* 32 (* h1 
h1) (* h2 h2 h2) h3 (* h5 h5 h5) h6) (* 12 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 147 (* h1 h1) (* h2 h2 h2) h3 (* h5
 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 748 (* h1 h1) (* h2 h2 h2) h3 (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2096 (* h1 h1) (* h2 h2 h2) h3 (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3596 (* h1 h1) (* h2 h2 h2) h3 (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 3943 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2)) (* 2776 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* h6 h6)
 (* j2 j2 j2)) (* 1214 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2)) 
(* 300 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* h6 h6) j2) (* 32 (* h1 h1) (* h2 
h2 h2) h3 (* h5 h5) (* h6 h6)) (* 6 (* h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 71 (* h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 338 (* h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 863 (* h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2)) (* 1310 (* h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 
j2 j2)) (* 1221 (* h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 
686 (* h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 213 (* h1 h1) (* 
h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2)) (* 28 (* h1 h1) (* h2 h2 h2) h3 h5 (* h6
 h6 h6) j2) (* 2 (* h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 14 (* h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 40 (* h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 60 
(* h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 50 (* h1 h1) 
(* h2 h2 h2) h3 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 22 (* h1 h1) (* h2 h2 h2) h3
 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 4 (* h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6 h6) 
(* j2 j2)) (* 9 (* h1 h1) (* h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 63 (* h1 h1) (* h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2
)) (* 182 (* h1 h1) (* h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
283 (* h1 h1) (* h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 257 (* h1 
h1) (* h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 137 (* h1 h1) (* h2 h2 
h2) (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 40 (* h1 h1) (* h2 h2 h2) (* h4 h4) (* 
h5 h5) h6 j2) (* 5 (* h1 h1) (* h2 h2 h2) (* h4 h4) (* h5 h5) h6) (* 9 (* h1 h1)
 (* h2 h2 h2) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 54 (* h1 h1) 
(* h2 h2 h2) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 130 (* h1 h1) (* 
h2 h2 h2) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 162 (* h1 h1) (* h2 h2 
h2) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 111 (* h1 h1) (* h2 h2 h2) (* h4 
h4) h5 (* h6 h6) (* j2 j2 j2)) (* 40 (* h1 h1) (* h2 h2 h2) (* h4 h4) h5 (* h6 
h6) (* j2 j2)) (* 6 (* h1 h1) (* h2 h2 h2) (* h4 h4) h5 (* h6 h6) j2) (* 6 (* h1
 h1) (* h2 h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 51 (* h1 h1
) (* h2 h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 183 (* h1 h1) (* 
h2 h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 365 (* h1 h1) (* h2 h2 h2
) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 445 (* h1 h1) (* h2 h2 h2) h4 (* h5 
h5 h5) h6 (* j2 j2 j2 j2)) (* 341 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5 h5) h6 (* 
j2 j2 j2)) (* 161 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2)) (* 43 (* 
h1 h1) (* h2 h2 h2) h4 (* h5 h5 h5) h6 j2) (* 5 (* h1 h1) (* h2 h2 h2) h4 (* h5 
h5 h5) h6) (* 12 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 99 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 345 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 671 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2))
 (* 803 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 609 
(* h1 h1) (* h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 287 (* h1 h1) (* 
h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 77 (* h1 h1) (* h2 h2 h2) h4 (* 
h5 h5) (* h6 h6) j2) (* 9 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5) (* h6 h6)) (* 6 
(* h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 45 (* 
h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 141 (* h1 h1
) (* h2 h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 241 (* h1 h1) (* h2 
h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 244 (* h1 h1) (* h2 h2 h2) h4 
h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 147 (* h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6 h6
) (* j2 j2 j2)) (* 49 (* h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2)) (* 7 
(* h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6 h6) j2) (* (* h1 h1) (* h2 h2 h2) (* h5 h5
 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 8 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 28 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5 h5) h6
 (* j2 j2 j2 j2 j2 j2)) (* 56 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5 h5) h6 (* j2 j2
 j2 j2 j2)) (* 70 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 
56 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 28 (* h1 h1) (* h2
 h2 h2) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 8 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5 h5
) h6 j2) (* (* h1 h1) (* h2 h2 h2) (* h5 h5 h5 h5) h6) (* 3 (* h1 h1) (* h2 h2 
h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 31 (* h1 h1) (* h2
 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 137 (* h1 h1) (* 
h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 343 (* h1 h1) (* 
h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 539 (* h1 h1) (* h2 
h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 553 (* h1 h1) (* h2 h2 h2) 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 371 (* h1 h1) (* h2 h2 h2) (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2)) (* 157 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5) (* h6 h6)
 (* j2 j2)) (* 38 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5) (* h6 h6) j2) (* 4 (* h1 
h1) (* h2 h2 h2) (* h5 h5 h5) (* h6 h6)) (* 3 (* h1 h1) (* h2 h2 h2) (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 31 (* h1 h1) (* h2 h2 h2) (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 137 (* h1 h1) (* h2 h2 h2) (* 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 343 (* h1 h1) (* h2 h2 h2) (* 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 539 (* h1 h1) (* h2 h2 h2) (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 553 (* h1 h1) (* h2 h2 h2) (* h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2)) (* 371 (* h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2)) (* 157 (* h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2)) 
(* 38 (* h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6 h6) j2) (* 4 (* h1 h1) (* h2 h2 
h2) (* h5 h5) (* h6 h6 h6)) (* (* h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 7 (* h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 21 (* h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 35 (* h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
35 (* h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 21 (* h1 h1) 
(* h2 h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 7 (* h1 h1) (* h2 h2 h2) h5 (* 
h6 h6 h6 h6) (* j2 j2)) (* (* h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6 h6) j2) (* 32 
(* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 520 
(* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 3400 (* 
h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 11912 (* h1 h1)
 (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 24664 (* h1 h1) (* h2 h2
) (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2)) (* 30992 (* h1 h1) (* h2 h2) (* h3 h3 
h3 h3) h4 h5 (* j2 j2 j2)) (* 23072 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h5 
(* j2 j2)) (* 9280 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h5 j2) (* 1536 (* h1 
h1) (* h2 h2) (* h3 h3 h3 h3) h4 h5) (* 64 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) 
h4 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 752 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4
 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 3744 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h6 
(* j2 j2 j2 j2 j2 j2)) (* 10224 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 
j2 j2 j2 j2)) (* 16512 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2)
) (* 15744 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2)) (* 8192 (* h1
 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2)) (* 1792 (* h1 h1) (* h2 h2) (* 
h3 h3 h3 h3) h4 h6 j2) (* 8 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 168 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1424 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h5 
h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 6400 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h5 
h5) (* j2 j2 j2 j2 j2 j2)) (* 16952 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h5 h5
) (* j2 j2 j2 j2 j2)) (* 27640 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* 
j2 j2 j2 j2)) (* 27888 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2
)) (* 16864 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2)) (* 5568 (* 
h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) j2) (* 768 (* h1 h1) (* h2 h2) (* h3 
h3 h3 h3) (* h5 h5)) (* 136 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 1560 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 
j2 j2 j2 j2 j2)) (* 7592 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 
j2 j2 j2)) (* 20392 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2)
) (* 32912 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 32512 
(* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2)) (* 19072 (* h1 h1) (* h2
 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2)) (* 6016 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3
) h5 h6 j2) (* 768 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 h6) (* 32 (* h1 h1) 
(* h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 416 (* h1
 h1) (* h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2336 
(* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 7392 
(* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 14400 
(* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 17664 (* h1
 h1) (* h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 13312 (* h1 h1) (* 
h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2)) (* 5632 (* h1 h1) (* h2 h2) (* h3
 h3 h3 h3) (* h6 h6) (* j2 j2)) (* 1024 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* 
h6 h6) j2) (* 24 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 392 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 
j2 j2 j2)) (* 2624 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 
j2 j2)) (* 9440 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)
) (* 19992 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 
25496 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 19056 (* h1
 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2)) (* 7584 (* h1 h1) (* h2 h2) 
(* h3 h3 h3) (* h4 h4) h5 j2) (* 1216 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4)
 h5) (* 48 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2
 j2)) (* 592 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 
j2)) (* 3072 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2)
) (* 8688 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 
14448 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2)) (* 14112 
(* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2)) (* 7488 (* h1 h1) 
(* h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2)) (* 1664 (* h1 h1) (* h2 h2) (* h3
 h3 h3) (* h4 h4) h6 j2) (* 12 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 278 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h5 h5
) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2514 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h5
 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 11752 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* 
h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 31920 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h5
 h5) (* j2 j2 j2 j2 j2)) (* 53030 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) 
(* j2 j2 j2 j2)) (* 54450 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2
 j2)) (* 33564 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2)) (* 11328
 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) j2) (* 1600 (* h1 h1) (* h2 h2) 
(* h3 h3 h3) h4 (* h5 h5)) (* 48 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2
 j2 j2 j2 j2 j2 j2 j2 j2)) (* 900 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 6660 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 h6 (* 
j2 j2 j2 j2 j2 j2 j2)) (* 26616 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 
j2 j2 j2 j2 j2)) (* 64328 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 
j2 j2)) (* 98004 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 
94004 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 54384 (* h1 h1)
 (* h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2)) (* 16976 (* h1 h1) (* h2 h2) (* h3 
h3 h3) h4 h5 h6 j2) (* 2112 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 h6) (* 48 (* 
h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
680 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 4104 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 13776 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 28104 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
35640 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 27408 
(* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2)) (* 11680 (* h1 h1) 
(* h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2)) (* 2112 (* h1 h1) (* h2 h2) (* h3
 h3 h3) h4 (* h6 h6) j2) (* 8 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 160 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5 h5
) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1273 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5
 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 5287 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5
 h5) (* j2 j2 j2 j2 j2 j2)) (* 12793 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5 
h5) (* j2 j2 j2 j2 j2)) (* 18985 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) 
(* j2 j2 j2 j2)) (* 17486 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2
 j2)) (* 9720 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2)) (* 2976 
(* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) j2) (* 384 (* h1 h1) (* h2 h2) (* 
h3 h3 h3) (* h5 h5 h5)) (* 78 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1368 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 9104 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 31912 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5
 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 66612 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 
h5) h6 (* j2 j2 j2 j2 j2)) (* 87048 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) 
h6 (* j2 j2 j2 j2)) (* 71714 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2
 j2 j2)) (* 35996 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2)) (* 
9968 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) h6 j2) (* 1152 (* h1 h1) (* h2 
h2) (* h3 h3 h3) (* h5 h5) h6) (* 188 (* h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2308 (* h1 h1) (* h2 h2) (* h3 h3 h3) h5 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 12296 (* h1 h1) (* h2 h2) (* h3 h3 h3)
 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 37228 (* h1 h1) (* h2 h2) (* h3 h3 h3
) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 70384 (* h1 h1) (* h2 h2) (* h3 h3 h3) 
h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 85824 (* h1 h1) (* h2 h2) (* h3 h3 h3) h5 
(* h6 h6) (* j2 j2 j2 j2)) (* 67100 (* h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* h6 h6
) (* j2 j2 j2)) (* 32144 (* h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2)
) (* 8432 (* h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* h6 h6) j2) (* 896 (* h1 h1) (* 
h2 h2) (* h3 h3 h3) h5 (* h6 h6)) (* 32 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 384 (* h1 h1) (* h2 h2) (* h3 h3 h3) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1976 (* h1 h1) (* h2 h2) (* h3 h3 
h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 5688 (* h1 h1) (* h2 h2) (* h3 h3 
h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 10008 (* h1 h1) (* h2 h2) (* h3 h3 h3
) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 11016 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* 
h6 h6 h6) (* j2 j2 j2 j2)) (* 7408 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6 h6)
 (* j2 j2 j2)) (* 2784 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6 h6) (* j2 j2)) 
(* 448 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6 h6) j2) (* 12 (* h1 h1) (* h2 
h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 162 (* h1 h1) (* h2 
h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 840 (* h1 h1) (* h2 h2) 
(* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 2196 (* h1 h1) (* h2 h2) (* h3 
h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 3144 (* h1 h1) (* h2 h2) (* h3 h3) (* h4
 h4 h4) h5 (* j2 j2 j2)) (* 2466 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 
(* j2 j2)) (* 972 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 j2) (* 144 (* h1
 h1) (* h2 h2) (* h3 h3) (* h4 h4 h4) h5) (* 24 (* h1 h1) (* h2 h2) (* h3 h3) 
(* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 228 (* h1 h1) (* h2 h2) (* h3 h3) 
(* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 876 (* h1 h1) (* h2 h2) (* h3 h3) (* 
h4 h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 1740 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4 
h4) h6 (* j2 j2 j2 j2)) (* 1884 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4 h4) h6 
(* j2 j2 j2)) (* 1056 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4 h4) h6 (* j2 j2)) 
(* 240 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4 h4) h6 j2) (* 24 (* h1 h1) (* h2 
h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 368 (* h1 h1) 
(* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 2263 (* h1 
h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 7308 (* h1
 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 13630 (* h1 
h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 15128 (* h1 h1) 
(* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 9803 (* h1 h1) (* h2 h2
) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 3396 (* h1 h1) (* h2 h2) (* h3 h3)
 (* h4 h4) (* h5 h5) j2) (* 480 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5
)) (* 96 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 1110 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 
j2)) (* 5484 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)
) (* 15000 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 
24566 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 24306 
(* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 13898 (* h1 h1) 
(* h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 4044 (* h1 h1) (* h2 h2) (* h3
 h3) (* h4 h4) h5 h6 j2) (* 416 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 h6) 
(* 48 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 544 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 2544 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2
 j2 j2)) (* 6336 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 
j2 j2)) (* 9024 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2
)) (* 7296 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 
3072 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2)) (* 512 (* h1 
h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) j2) (* 6 (* h1 h1) (* h2 h2) (* h3 
h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 133 (* h1 h1) (* h2 h2) 
(* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1127 (* h1 h1) (* h2 
h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 4817 (* h1 h1) (* h2 
h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 11711 (* h1 h1) (* h2 h2
) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 17122 (* h1 h1) (* h2 h2) (* 
h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 15292 (* h1 h1) (* h2 h2) (* h3 h3) 
h4 (* h5 h5 h5) (* j2 j2 j2)) (* 8144 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5 
h5) (* j2 j2)) (* 2368 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) j2) (* 288 
(* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5 h5)) (* 54 (* h1 h1) (* h2 h2) (* h3 
h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 894 (* h1 h1) (* h2 h2) 
(* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 5869 (* h1 h1) (* h2 
h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 20772 (* h1 h1) (* h2
 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 44296 (* h1 h1) (* h2 
h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 59369 (* h1 h1) (* h2 h2) 
(* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 50115 (* h1 h1) (* h2 h2) (* h3 h3
) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 25667 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 
h5) h6 (* j2 j2)) (* 7200 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) h6 j2) (* 
832 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) h6) (* 96 (* h1 h1) (* h2 h2) (* 
h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1226 (* h1 h1) (* h2 
h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6810 (* h1 h1) (* 
h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 21446 (* h1 h1) 
(* h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 41822 (* h1 h1) 
(* h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 51838 (* h1 h1) (* h2
 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 40344 (* h1 h1) (* h2 h2) (* 
h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 18678 (* h1 h1) (* h2 h2) (* h3 h3) h4 
h5 (* h6 h6) (* j2 j2)) (* 4516 (* h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* h6 h6) j2
) (* 400 (* h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* h6 h6)) (* 24 (* h1 h1) (* h2 h2
) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 316 (* h1 h1) (* 
h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1740 (* h1 h1) 
(* h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 5224 (* h1 h1) 
(* h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 9328 (* h1 h1) (* 
h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 10108 (* h1 h1) (* h2 h2
) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 6460 (* h1 h1) (* h2 h2) (* h3 
h3) h4 (* h6 h6 h6) (* j2 j2 j2)) (* 2208 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h6
 h6 h6) (* j2 j2)) (* 304 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6 h6) j2) (* 2
 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 38 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2))
 (* 281 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 1057 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 
2268 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 2940 
(* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 2341 (* h1 h1)
 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 1117 (* h1 h1) (* h2 h2) 
(* h3 h3) (* h5 h5 h5 h5) (* j2 j2)) (* 292 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 
h5 h5 h5) j2) (* 32 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5 h5)) (* 39 (* h1 
h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 649 
(* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
3985 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
12688 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
23806 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 27784
 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 20394 (* h1 
h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 9139 (* h1 h1) (* h2 h2
) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2)) (* 2276 (* h1 h1) (* h2 h2) (* h3 h3) (* 
h5 h5 h5) h6 j2) (* 240 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) h6) (* 209 
(* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 2256 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 10554 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 28029 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 46481 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2)) (* 49814 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* 
j2 j2 j2 j2)) (* 34412 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 
j2 j2)) (* 14717 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) 
(* 3512 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) j2) (* 352 (* h1 h1) 
(* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6)) (* 102 (* h1 h1) (* h2 h2) (* h3 h3) h5
 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1124 (* h1 h1) (* h2 h2) (* h3 
h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 5336 (* h1 h1) (* h2 h2) (* 
h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 14288 (* h1 h1) (* h2 h2) 
(* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 23704 (* h1 h1) (* h2 h2) 
(* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 25150 (* h1 h1) (* h2 h2) (* h3
 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 16942 (* h1 h1) (* h2 h2) (* h3 h3) h5 
(* h6 h6 h6) (* j2 j2 j2)) (* 6902 (* h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6 h6)
 (* j2 j2)) (* 1508 (* h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6 h6) j2) (* 128 (* 
h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6 h6)) (* 8 (* h1 h1) (* h2 h2) (* h3 h3) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 88 (* h1 h1) (* h2 h2) (* h3 
h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 408 (* h1 h1) (* h2 h2) (* 
h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1040 (* h1 h1) (* h2 h2) (* 
h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1592 (* h1 h1) (* h2 h2) (* h3 
h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1496 (* h1 h1) (* h2 h2) (* h3 h3) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 840 (* h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 
h6 h6) (* j2 j2 j2)) (* 256 (* h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6 h6) (* j2 
j2)) (* 32 (* h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6 h6) j2) (* 6 (* h1 h1) (* 
h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 75 (* h1 h1) (* h2
 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 348 (* h1 h1) (* h2 h2)
 h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 785 (* h1 h1) (* h2 h2) h3 (* 
h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 935 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) 
(* h5 h5) (* j2 j2 j2)) (* 584 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* 
j2 j2)) (* 171 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) j2) (* 16 (* h1 h1)
 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5)) (* 30 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) 
h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 239 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) h5 h6
 (* j2 j2 j2 j2 j2 j2)) (* 760 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) h5 h6 (* j2 
j2 j2 j2 j2)) (* 1226 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2))
 (* 1046 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 439 (* h1 h1
) (* h2 h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2)) (* 68 (* h1 h1) (* h2 h2) h3 (* h4 
h4 h4) h5 h6 j2) (* 12 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) (* h6 h6) (* j2 j2 j2
 j2 j2 j2 j2)) (* 90 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 258 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 354 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 
234 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) (* h6 h6) (* j2 j2 j2)) (* 60 (* h1 h1) 
(* h2 h2) h3 (* h4 h4 h4) (* h6 h6) (* j2 j2)) (* 6 (* h1 h1) (* h2 h2) h3 (* h4
 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 86 (* h1 h1) (* h2 h2) h3 (* 
h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 484 (* h1 h1) (* h2 h2) h3 (* 
h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1399 (* h1 h1) (* h2 h2) h3 (* h4 
h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 2293 (* h1 h1) (* h2 h2) h3 (* h4 h4) 
(* h5 h5 h5) (* j2 j2 j2 j2)) (* 2207 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5 
h5) (* j2 j2 j2)) (* 1229 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2
)) (* 364 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) j2) (* 44 (* h1 h1) (* 
h2 h2) h3 (* h4 h4) (* h5 h5 h5)) (* 48 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 507 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2266 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 5551 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 
h5) h6 (* j2 j2 j2 j2 j2)) (* 8042 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) h6
 (* j2 j2 j2 j2)) (* 6940 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2
 j2)) (* 3402 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 828 
(* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) h6 j2) (* 68 (* h1 h1) (* h2 h2) h3 
(* h4 h4) (* h5 h5) h6) (* 54 (* h1 h1) (* h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 539 (* h1 h1) (* h2 h2) h3 (* h4 h4) h5 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 2190 (* h1 h1) (* h2 h2) h3 (* h4 h4) h5 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 4677 (* h1 h1) (* h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* 
j2 j2 j2 j2 j2)) (* 5640 (* h1 h1) (* h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 
j2 j2)) (* 3798 (* h1 h1) (* h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 
1290 (* h1 h1) (* h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 160 (* h1 h1) 
(* h2 h2) h3 (* h4 h4) h5 (* h6 h6) j2) (* 12 (* h1 h1) (* h2 h2) h3 (* h4 h4) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 112 (* h1 h1) (* h2 h2) h3 (* h4 h4
) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 418 (* h1 h1) (* h2 h2) h3 (* h4 h4)
 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 790 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 790 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h6 h6 
h6) (* j2 j2 j2 j2)) (* 394 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h6 h6 h6) (* j2 
j2 j2)) (* 76 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h6 h6 h6) (* j2 j2)) (* 4 (* 
h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 53 (* h1 
h1) (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 263 (* h1 h1) 
(* h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 666 (* h1 h1) (* h2 h2
) h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 966 (* h1 h1) (* h2 h2) h3 h4 (* 
h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 833 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5 h5) 
(* j2 j2 j2)) (* 419 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2)) (* 112
 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5 h5) j2) (* 12 (* h1 h1) (* h2 h2) h3 h4 
(* h5 h5 h5 h5)) (* 12 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 201 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2
 j2 j2 j2 j2)) (* 1272 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2)) (* 4230 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2)) (* 8330 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
10189 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 7788 (* h1 
h1) (* h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 3596 (* h1 h1) (* h2 h2) h3
 h4 (* h5 h5 h5) h6 (* j2 j2)) (* 910 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) h6 
j2) (* 96 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) h6) (* 48 (* h1 h1) (* h2 h2) 
h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 565 (* h1 h1) (* h2
 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2879 (* h1 h1) 
(* h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 8269 (* h1 h1) 
(* h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 14609 (* h1 h1) 
(* h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 16302 (* h1 h1) (* h2
 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 11364 (* h1 h1) (* h2 h2) h3 
h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 4700 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5)
 (* h6 h6) (* j2 j2)) (* 1020 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* h6 h6) j2) 
(* 84 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* h6 h6)) (* 24 (* h1 h1) (* h2 h2) 
h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 289 (* h1 h1) (* h2 h2)
 h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1431 (* h1 h1) (* h2 h2) 
h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3817 (* h1 h1) (* h2 h2) h3 
h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 5997 (* h1 h1) (* h2 h2) h3 h4 h5 
(* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 5668 (* h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6 
h6) (* j2 j2 j2 j2)) (* 3124 (* h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 
j2)) (* 902 (* h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2)) (* 100 (* h1 h1
) (* h2 h2) h3 h4 h5 (* h6 h6 h6) j2) (* 8 (* h1 h1) (* h2 h2) h3 h4 (* h6 h6 h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 62 (* h1 h1) (* h2 h2) h3 h4 (* h6 h6 h6 h6
) (* j2 j2 j2 j2 j2 j2 j2)) (* 190 (* h1 h1) (* h2 h2) h3 h4 (* h6 h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 294 (* h1 h1) (* h2 h2) h3 h4 (* h6 h6 h6 h6) (* j2 j2 j2
 j2 j2)) (* 242 (* h1 h1) (* h2 h2) h3 h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 
100 (* h1 h1) (* h2 h2) h3 h4 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 16 (* h1 h1) (* 
h2 h2) h3 h4 (* h6 h6 h6 h6) (* j2 j2)) (* 19 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5
 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 171 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 644 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2)) (* 1332 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2)) (* 1659 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 
j2)) (* 1275 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 590 (* 
h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 150 (* h1 h1) (* h2 h2) h3 
(* h5 h5 h5 h5) h6 j2) (* 16 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) h6) (* 47 
(* h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 495 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 2229 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 5630 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 8798 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
8827 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 5685 (* 
h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 2264 (* h1 h1) (* h2
 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 505 (* h1 h1) (* h2 h2) h3 (* h5 h5
 h5) (* h6 h6) j2) (* 48 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* h6 h6)) (* 51 
(* h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 521 (* h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 2275 (* h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 5569 (* h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 8416 (* h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
8127 (* h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 4995 (* 
h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 1871 (* h1 h1) (* h2
 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 383 (* h1 h1) (* h2 h2) h3 (* h5 h5
) (* h6 h6 h6) j2) (* 32 (* h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6 h6)) (* 4 (* 
h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 45 (* 
h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 205 (* h1
 h1) (* h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 497 (* h1 h1) 
(* h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 706 (* h1 h1) (* h2 h2
) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 603 (* h1 h1) (* h2 h2) h3 h5 (* 
h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 301 (* h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6 h6) 
(* j2 j2 j2)) (* 79 (* h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2)) (* 8 
(* h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6 h6) j2) (* 6 (* h1 h1) (* h2 h2) (* h4 h4 
h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 45 (* h1 h1) (* h2 h2) (* h4 h4 h4
) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 131 (* h1 h1) (* h2 h2) (* h4 h4 h4) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 190 (* h1 h1) (* h2 h2) (* h4 h4 h4) (* h5 
h5) h6 (* j2 j2 j2 j2)) (* 146 (* h1 h1) (* h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* 
j2 j2 j2)) (* 58 (* h1 h1) (* h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 11 
(* h1 h1) (* h2 h2) (* h4 h4 h4) (* h5 h5) h6 j2) (* (* h1 h1) (* h2 h2) (* h4 
h4 h4) (* h5 h5) h6) (* 6 (* h1 h1) (* h2 h2) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2
 j2 j2 j2 j2 j2)) (* 39 (* h1 h1) (* h2 h2) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 95 (* h1 h1) (* h2 h2) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2
 j2)) (* 110 (* h1 h1) (* h2 h2) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 
63 (* h1 h1) (* h2 h2) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 17 (* h1 h1) 
(* h2 h2) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2)) (* 2 (* h1 h1) (* h2 h2) (* h4 h4
 h4) h5 (* h6 h6) j2) (* 6 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 56 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2
 j2 j2 j2 j2 j2 j2)) (* 211 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2)) (* 423 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2)) (* 500 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2))
 (* 363 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 162 (* h1
 h1) (* h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 42 (* h1 h1) (* h2 h2) 
(* h4 h4) (* h5 h5 h5) h6 j2) (* 5 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5 h5) h6
) (* 12 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 112 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 419 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 823 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2)) (* 929 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)
) (* 614 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 229 
(* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 43 (* h1 h1) (* 
h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) j2) (* 3 (* h1 h1) (* h2 h2) (* h4 h4) (* 
h5 h5) (* h6 h6)) (* 6 (* h1 h1) (* h2 h2) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 50 (* h1 h1) (* h2 h2) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 166 (* h1 h1) (* h2 h2) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 281 (* h1 h1) (* h2 h2) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 
j2 j2)) (* 261 (* h1 h1) (* h2 h2) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) 
(* 133 (* h1 h1) (* h2 h2) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 35 (* h1 
h1) (* h2 h2) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2)) (* 4 (* h1 h1) (* h2 h2) (* 
h4 h4) h5 (* h6 h6 h6) j2) (* 4 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 33 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2)) (* 114 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2
 j2 j2)) (* 217 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) 
(* 250 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 179 (* h1 
h1) (* h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 78 (* h1 h1) (* h2 h2) h4 
(* h5 h5 h5 h5) h6 (* j2 j2)) (* 19 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5 h5) h6 j2
) (* 2 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5 h5) h6) (* 6 (* h1 h1) (* h2 h2) h4 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 67 (* h1 h1) (* h2 h2)
 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 310 (* h1 h1) (* h2 
h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 787 (* h1 h1) (* h2 
h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1224 (* h1 h1) (* h2 h2)
 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1226 (* h1 h1) (* h2 h2) h4 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 802 (* h1 h1) (* h2 h2) h4 (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2)) (* 335 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5) (* h6 h6)
 (* j2 j2)) (* 82 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5) (* h6 h6) j2) (* 9 (* h1 
h1) (* h2 h2) h4 (* h5 h5 h5) (* h6 h6)) (* 6 (* h1 h1) (* h2 h2) h4 (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 67 (* h1 h1) (* h2 h2) h4 (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 308 (* h1 h1) (* h2 h2) h4 (* 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 770 (* h1 h1) (* h2 h2) h4 (* 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1162 (* h1 h1) (* h2 h2) h4 (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1102 (* h1 h1) (* h2 h2) h4 (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2)) (* 656 (* h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2)) (* 234 (* h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2)
) (* 44 (* h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6 h6) j2) (* 3 (* h1 h1) (* h2 
h2) h4 (* h5 h5) (* h6 h6 h6)) (* 4 (* h1 h1) (* h2 h2) h4 h5 (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 29 (* h1 h1) (* h2 h2) h4 h5 (* h6 h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 85 (* h1 h1) (* h2 h2) h4 h5 (* h6 h6 h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 132 (* h1 h1) (* h2 h2) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2
)) (* 118 (* h1 h1) (* h2 h2) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 61 (* h1
 h1) (* h2 h2) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 17 (* h1 h1) (* h2 h2) h4 
h5 (* h6 h6 h6 h6) (* j2 j2)) (* 2 (* h1 h1) (* h2 h2) h4 h5 (* h6 h6 h6 h6) j2)
 (* 2 (* h1 h1) (* h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 20 (* h1 h1) (* h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2
 j2)) (* 86 (* h1 h1) (* h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 210 (* h1 h1) (* h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2))
 (* 322 (* h1 h1) (* h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 322
 (* h1 h1) (* h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 210 (* h1 h1)
 (* h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 86 (* h1 h1) (* h2 h2) (* 
h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 20 (* h1 h1) (* h2 h2) (* h5 h5 h5 h5) (* 
h6 h6) j2) (* 2 (* h1 h1) (* h2 h2) (* h5 h5 h5 h5) (* h6 h6)) (* 4 (* h1 h1) 
(* h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 40 (* h1 
h1) (* h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 172 (* 
h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 420 (* 
h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 644 (* h1 
h1) (* h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 644 (* h1 h1) (* 
h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 420 (* h1 h1) (* h2 h2) (* 
h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 172 (* h1 h1) (* h2 h2) (* h5 h5 h5) (* 
h6 h6 h6) (* j2 j2)) (* 40 (* h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6 h6) j2) (* 
4 (* h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6 h6)) (* 2 (* h1 h1) (* h2 h2) (* h5 
h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 20 (* h1 h1) (* h2 h2) 
(* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 85 (* h1 h1) (* h2 h2)
 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 203 (* h1 h1) (* h2 h2) 
(* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 301 (* h1 h1) (* h2 h2) (* 
h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 287 (* h1 h1) (* h2 h2) (* h5 h5) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 175 (* h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 
h6 h6) (* j2 j2 j2)) (* 65 (* h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 
j2)) (* 13 (* h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6 h6) j2) (* (* h1 h1) (* h2 
h2) (* h5 h5) (* h6 h6 h6 h6)) (* 24 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h5 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 384 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h5 
(* j2 j2 j2 j2 j2 j2 j2)) (* 2528 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h5 (* 
j2 j2 j2 j2 j2 j2)) (* 8976 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 
j2 j2 j2)) (* 18760 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) 
(* 23440 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 16800 (* h1 
h1) h2 (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2)) (* 6080 (* h1 h1) h2 (* h3 h3 h3 
h3) (* h4 h4) h5 j2) (* 768 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h5) (* 48 (* 
h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 592 (* h1
 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 3088 (* h1 h1)
 h2 (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 8816 (* h1 h1) h2 (* 
h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 14848 (* h1 h1) h2 (* h3 h3 h3 
h3) (* h4 h4) h6 (* j2 j2 j2 j2)) (* 14720 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4
) h6 (* j2 j2 j2)) (* 7936 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2)) 
(* 1792 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h6 j2) (* 12 (* h1 h1) h2 (* h3 
h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 244 (* h1 h1) h2 (* h3
 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2072 (* h1 h1) h2 (* h3 
h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 9644 (* h1 h1) h2 (* h3 h3 
h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 27052 (* h1 h1) h2 (* h3 h3 h3 h3)
 h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 47216 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h5
 h5) (* j2 j2 j2 j2)) (* 50944 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 
j2 j2)) (* 32512 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2)) (* 11072 
(* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h5 h5) j2) (* 1536 (* h1 h1) h2 (* h3 h3 h3 
h3) h4 (* h5 h5)) (* 48 (* h1 h1) h2 (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 832 (* h1 h1) h2 (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 6144 (* h1 h1) h2 (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 25312 (* h1 h1) h2 (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 63776 
(* h1 h1) h2 (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 101008 (* h1 h1) h2
 (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 99104 (* h1 h1) h2 (* h3 h3 h3 h3)
 h4 h5 h6 (* j2 j2 j2)) (* 56640 (* h1 h1) h2 (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2)
) (* 16256 (* h1 h1) h2 (* h3 h3 h3 h3) h4 h5 h6 j2) (* 1536 (* h1 h1) h2 (* h3 
h3 h3 h3) h4 h5 h6) (* 48 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 672 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 4064 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 13808 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 28672 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 36992 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 28672 (* 
h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2)) (* 12032 (* h1 h1) h2 (* h3
 h3 h3 h3) h4 (* h6 h6) (* j2 j2)) (* 2048 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6
 h6) j2) (* 2 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 46 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 432 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 2154 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 6230
 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 10768 (* h1 h1
) h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 11088 (* h1 h1) h2 (* h3 
h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2)) (* 6576 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 
h5 h5) (* j2 j2)) (* 2048 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5 h5) j2) (* 256 
(* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5 h5)) (* 72 (* h1 h1) h2 (* h3 h3 h3 h3) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1168 (* h1 h1) h2 (* h3 h3 h3 h3
) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 7852 (* h1 h1) h2 (* h3 h3 h3 h3)
 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 28832 (* h1 h1) h2 (* h3 h3 h3 h3) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 63696 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 
h5) h6 (* j2 j2 j2 j2 j2)) (* 87476 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) h6 
(* j2 j2 j2 j2)) (* 74224 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2)
) (* 37200 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2)) (* 9856 (* h1 h1
) h2 (* h3 h3 h3 h3) (* h5 h5) h6 j2) (* 1024 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5
 h5) h6) (* 144 (* h1 h1) h2 (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 1952 (* h1 h1) h2 (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 11400 (* h1 h1) h2 (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 37456 (* h1 h1) h2 (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)
) (* 75792 (* h1 h1) h2 (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
97064 (* h1 h1) h2 (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 77648 (* h1 
h1) h2 (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 36640 (* h1 h1) h2 (* h3 h3
 h3 h3) h5 (* h6 h6) (* j2 j2)) (* 8896 (* h1 h1) h2 (* h3 h3 h3 h3) h5 (* h6 h6
) j2) (* 768 (* h1 h1) h2 (* h3 h3 h3 h3) h5 (* h6 h6)) (* 16 (* h1 h1) h2 (* h3
 h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 208 (* h1 h1) h2 (* 
h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1152 (* h1 h1) h2 (* 
h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3536 (* h1 h1) h2 (* h3 
h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6544 (* h1 h1) h2 (* h3 h3 h3 
h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 7424 (* h1 h1) h2 (* h3 h3 h3 h3) (* h6 
h6 h6) (* j2 j2 j2 j2)) (* 4992 (* h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 
j2 j2)) (* 1792 (* h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2)) (* 256 (* 
h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6 h6) j2) (* 24 (* h1 h1) h2 (* h3 h3 h3) (* h4
 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 328 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 
h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 1760 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h5 
(* j2 j2 j2 j2 j2)) (* 4848 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 
j2 j2)) (* 7376 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 6096 
(* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2)) (* 2432 (* h1 h1) h2 (* h3 
h3 h3) (* h4 h4 h4) h5 j2) (* 320 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h5) (* 
48 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 480 
(* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 1968 (* h1 
h1) h2 (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 4224 (* h1 h1) h2 (* 
h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2)) (* 4992 (* h1 h1) h2 (* h3 h3 h3) (* 
h4 h4 h4) h6 (* j2 j2 j2)) (* 3072 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h6 (* 
j2 j2)) (* 768 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h6 j2) (* 42 (* h1 h1) h2 
(* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 656 (* h1 h1) 
h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 4192 (* h1 h1) 
h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 14380 (* h1 h1) h2
 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 28974 (* h1 h1) h2 (* 
h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 34924 (* h1 h1) h2 (* h3 h3 h3
) (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 24304 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4)
 (* h5 h5) (* j2 j2)) (* 8768 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) j2) 
(* 1216 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h5 h5)) (* 156 (* h1 h1) h2 (* h3
 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1964 (* h1 h1) h2 (* h3 
h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 10600 (* h1 h1) h2 (* h3 h3 
h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 31756 (* h1 h1) h2 (* h3 h3 h3) 
(* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 57008 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4)
 h5 h6 (* j2 j2 j2 j2)) (* 61564 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 h6 (* j2
 j2 j2)) (* 37808 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 11312 
(* h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 h6 j2) (* 1024 (* h1 h1) h2 (* h3 h3 h3) 
(* h4 h4) h5 h6) (* 96 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 1112 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2
 j2 j2 j2 j2 j2)) (* 5400 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2
 j2 j2 j2 j2)) (* 14184 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 
j2 j2 j2)) (* 21624 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2
)) (* 18960 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 8736 
(* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2)) (* 1600 (* h1 h1) h2 
(* h3 h3 h3) (* h4 h4) (* h6 h6) j2) (* 12 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5
 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 233 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1870 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 8125 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5 
h5) (* j2 j2 j2 j2 j2 j2)) (* 20985 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5 h5) 
(* j2 j2 j2 j2 j2)) (* 33280 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 
j2 j2)) (* 32311 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2)) (* 
18484 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2)) (* 5648 (* h1 h1) h2 
(* h3 h3 h3) h4 (* h5 h5 h5) j2) (* 704 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5 h5
)) (* 84 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2
)) (* 1408 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 9956 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 38848 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
91964 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 136664 
(* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 126996 (* h1 h1) 
h2 (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 70560 (* h1 h1) h2 (* h3 h3 h3)
 h4 (* h5 h5) h6 (* j2 j2)) (* 20912 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6 
j2) (* 2432 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6) (* 144 (* h1 h1) h2 (* h3
 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2032 (* h1 h1) h2 (* 
h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 12484 (* h1 h1) h2 (* 
h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 43432 (* h1 h1) h2 (* h3 
h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 93368 (* h1 h1) h2 (* h3 h3 h3)
 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 127084 (* h1 h1) h2 (* h3 h3 h3) h4 h5 
(* h6 h6) (* j2 j2 j2 j2)) (* 107704 (* h1 h1) h2 (* h3 h3 h3) h4 h5 (* h6 h6) 
(* j2 j2 j2)) (* 53344 (* h1 h1) h2 (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 
13280 (* h1 h1) h2 (* h3 h3 h3) h4 h5 (* h6 h6) j2) (* 1088 (* h1 h1) h2 (* h3 
h3 h3) h4 h5 (* h6 h6)) (* 48 (* h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2
 j2 j2 j2 j2 j2 j2 j2)) (* 624 (* h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 3472 (* h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 10752 (* h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 20160 (* h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 
j2)) (* 23280 (* h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 
16032 (* h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2)) (* 5952 (* h1 h1) 
h2 (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2)) (* 896 (* h1 h1) h2 (* h3 h3 h3) h4 
(* h6 h6 h6) j2) (* (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 22 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 195 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2
 j2)) (* 903 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) 
(* 2386 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 3727 
(* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 3474 (* h1 h1) h2 
(* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 1884 (* h1 h1) h2 (* h3 h3 h3) (* 
h5 h5 h5 h5) (* j2 j2)) (* 544 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5 h5) j2) (* 
64 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5 h5)) (* 73 (* h1 h1) h2 (* h3 h3 h3) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1119 (* h1 h1) h2 (* h3 h3 h3
) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 7019 (* h1 h1) h2 (* h3 h3 h3)
 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 23826 (* h1 h1) h2 (* h3 h3 h3) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 48489 (* h1 h1) h2 (* h3 h3 h3) (* h5 
h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 61609 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) h6
 (* j2 j2 j2 j2)) (* 48921 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2
)) (* 23356 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2)) (* 6048 (* h1 
h1) h2 (* h3 h3 h3) (* h5 h5 h5) h6 j2) (* 640 (* h1 h1) h2 (* h3 h3 h3) (* h5 
h5 h5) h6) (* 282 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 3510 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 18704 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2
 j2 j2 j2 j2 j2 j2)) (* 56014 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 103954 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2)) (* 123876 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 
j2 j2 j2)) (* 94372 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) 
(* 43928 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 11168 (* h1
 h1) h2 (* h3 h3 h3) (* h5 h5) (* h6 h6) j2) (* 1152 (* h1 h1) h2 (* h3 h3 h3) 
(* h5 h5) (* h6 h6)) (* 164 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 1992 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 10392 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 30480 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 55168 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 
j2)) (* 63504 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 
46028 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 19920 (* h1 h1)
 h2 (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 4528 (* h1 h1) h2 (* h3 h3 h3) h5
 (* h6 h6 h6) j2) (* 384 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6 h6)) (* 8 (* h1 
h1) h2 (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 96 (* h1 
h1) h2 (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 488 (* h1 h1
) h2 (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1368 (* h1 h1) h2
 (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2304 (* h1 h1) h2 (* h3 
h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2376 (* h1 h1) h2 (* h3 h3 h3) (* 
h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 1456 (* h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6 h6) 
(* j2 j2 j2)) (* 480 (* h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2)) (* 64 
(* h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6 h6) j2) (* 6 (* h1 h1) h2 (* h3 h3) (* h4 
h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 64 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4 h4)
 h5 (* j2 j2 j2 j2 j2)) (* 240 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 
j2 j2 j2)) (* 420 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2)) (* 362
 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2)) (* 140 (* h1 h1) h2 (* h3 
h3) (* h4 h4 h4 h4) h5 j2) (* 16 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4 h4) h5) (* 
12 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 84 (* h1 
h1) h2 (* h3 h3) (* h4 h4 h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 228 (* h1 h1) h2 (* 
h3 h3) (* h4 h4 h4 h4) h6 (* j2 j2 j2 j2)) (* 300 (* h1 h1) h2 (* h3 h3) (* h4 
h4 h4 h4) h6 (* j2 j2 j2)) (* 192 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4 h4) h6 (* 
j2 j2)) (* 48 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4 h4) h6 j2) (* 24 (* h1 h1) h2 
(* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 305 (* h1 h1) h2 
(* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1486 (* h1 h1) h2 (* 
h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 3642 (* h1 h1) h2 (* h3 h3)
 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 4852 (* h1 h1) h2 (* h3 h3) (* h4 h4
 h4) (* h5 h5) (* j2 j2 j2)) (* 3487 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) (* h5 
h5) (* j2 j2)) (* 1216 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) j2) (* 144 
(* h1 h1) h2 (* h3 h3) (* h4 h4 h4) (* h5 h5)) (* 96 (* h1 h1) h2 (* h3 h3) (* 
h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 896 (* h1 h1) h2 (* h3 h3) (* h4 h4
 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 3448 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5
 h6 (* j2 j2 j2 j2 j2)) (* 6948 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 
j2 j2 j2)) (* 7716 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 
4544 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2)) (* 1208 (* h1 h1) h2 
(* h3 h3) (* h4 h4 h4) h5 h6 j2) (* 80 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 h6
) (* 48 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 420 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
1452 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2508 
(* h1 h1) h2 (* h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 2244 (* h1 h1)
 h2 (* h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2)) (* 960 (* h1 h1) h2 (* h3 h3)
 (* h4 h4 h4) (* h6 h6) (* j2 j2)) (* 144 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) 
(* h6 h6) j2) (* 21 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2
 j2 j2 j2 j2)) (* 307 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 
j2 j2 j2 j2)) (* 1800 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 
j2 j2 j2)) (* 5545 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 
j2)) (* 9813 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 
10164 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 5974 (* h1 
h1) h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 1800 (* h1 h1) h2 (* h3 h3
) (* h4 h4) (* h5 h5 h5) j2) (* 208 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5 h5
)) (* 135 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 1596 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2)) (* 7988 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)
) (* 21829 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
35171 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 33788 
(* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 18583 (* h1 h1) 
h2 (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 5176 (* h1 h1) h2 (* h3 h3) 
(* h4 h4) (* h5 h5) h6 j2) (* 512 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) h6)
 (* 174 (* h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 1866 (* h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2
)) (* 8426 (* h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 20674 (* h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
29622 (* h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 24746 
(* h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 11320 (* h1 h1) 
h2 (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 2400 (* h1 h1) h2 (* h3 h3) 
(* h4 h4) h5 (* h6 h6) j2) (* 144 (* h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* h6 h6))
 (* 48 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 496 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2))
 (* 2088 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 4588 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
5592 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 3700 (* 
h1 h1) h2 (* h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2)) (* 1200 (* h1 h1) h2 
(* h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2)) (* 144 (* h1 h1) h2 (* h3 h3) (* h4 
h4) (* h6 h6 h6) j2) (* 3 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 55 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 409 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2
 j2 j2 j2)) (* 1611 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 
j2)) (* 3678 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 
5018 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 4094 (* h1 h1
) h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2)) (* 1932 (* h1 h1) h2 (* h3 h3) 
h4 (* h5 h5 h5 h5) (* j2 j2)) (* 480 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5 h5) 
j2) (* 48 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5 h5)) (* 42 (* h1 h1) h2 (* h3 h3
) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 662 (* h1 h1) h2 (* h3 
h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4346 (* h1 h1) h2 (* h3 
h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 15505 (* h1 h1) h2 (* h3 h3)
 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 32986 (* h1 h1) h2 (* h3 h3) h4 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 43352 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 
h5) h6 (* j2 j2 j2 j2)) (* 35210 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) h6 (* j2
 j2 j2)) (* 17025 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2)) (* 4424 
(* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) h6 j2) (* 464 (* h1 h1) h2 (* h3 h3) h4 
(* h5 h5 h5) h6) (* 123 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 1653 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 9517 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 30511 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* h6 h6)
 (* j2 j2 j2 j2 j2 j2)) (* 59618 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* 73181 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2
 j2 j2 j2)) (* 56060 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2))
 (* 25577 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 6180 (* h1
 h1) h2 (* h3 h3) h4 (* h5 h5) (* h6 h6) j2) (* 576 (* h1 h1) h2 (* h3 h3) h4 
(* h5 h5) (* h6 h6)) (* 84 (* h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2
 j2 j2 j2 j2 j2 j2)) (* 1048 (* h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 5620 (* h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 16804 (* h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 30444 (* h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)
) (* 34124 (* h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 23244 
(* h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 9040 (* h1 h1) h2 (* 
h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2)) (* 1736 (* h1 h1) h2 (* h3 h3) h4 h5 (* h6 
h6 h6) j2) (* 112 (* h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6)) (* 12 (* h1 h1) h2 
(* h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 144 (* h1 h1) h2
 (* h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 720 (* h1 h1) h2 
(* h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1944 (* h1 h1) h2 (* 
h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3072 (* h1 h1) h2 (* h3 h3) 
h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2880 (* h1 h1) h2 (* h3 h3) h4 (* h6 
h6 h6 h6) (* j2 j2 j2 j2)) (* 1548 (* h1 h1) h2 (* h3 h3) h4 (* h6 h6 h6 h6) (* 
j2 j2 j2)) (* 432 (* h1 h1) h2 (* h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2)) (* 48 (* 
h1 h1) h2 (* h3 h3) h4 (* h6 h6 h6 h6) j2) (* 18 (* h1 h1) h2 (* h3 h3) (* h5 h5
 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 257 (* h1 h1) h2 (* h3 h3) (* h5 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1476 (* h1 h1) h2 (* h3 h3) (* h5 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 4527 (* h1 h1) h2 (* h3 h3) (* h5 h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 8241 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2)) (* 9304 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 
j2 j2 j2)) (* 6553 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 
2788 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 652 (* h1 h1) h2 
(* h3 h3) (* h5 h5 h5 h5) h6 j2) (* 64 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) h6
) (* 141 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 1619 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 7904 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 21494 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2
 j2 j2)) (* 35868 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 38118 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 
25811 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 10729 (* h1
 h1) h2 (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 2476 (* h1 h1) h2 (* h3 
h3) (* h5 h5 h5) (* h6 h6) j2) (* 240 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* h6 
h6)) (* 171 (* h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 1861 (* h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 8668 (* h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 22678 (* h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2
 j2 j2 j2)) (* 36698 (* h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2)) (* 38028 (* h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) 
(* 25155 (* h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 10185 
(* h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 2268 (* h1 h1) h2 
(* h3 h3) (* h5 h5) (* h6 h6 h6) j2) (* 208 (* h1 h1) h2 (* h3 h3) (* h5 h5) (* 
h6 h6 h6)) (* 42 (* h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 466 (* h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 2188 (* h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 5688 (* h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 8992 (* h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 8928 
(* h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 5534 (* h1 h1) h2 
(* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 2046 (* h1 h1) h2 (* h3 h3) h5 (* 
h6 h6 h6 h6) (* j2 j2)) (* 404 (* h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6 h6) j2) (* 
32 (* h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6 h6)) (* 3 (* h1 h1) h2 h3 (* h4 h4 h4 
h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 29 (* h1 h1) h2 h3 (* h4 h4 h4 h4) (* h5
 h5) (* j2 j2 j2 j2 j2)) (* 92 (* h1 h1) h2 h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 
j2 j2 j2)) (* 126 (* h1 h1) h2 h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 75 
(* h1 h1) h2 h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2)) (* 15 (* h1 h1) h2 h3 (* h4
 h4 h4 h4) (* h5 h5) j2) (* 15 (* h1 h1) h2 h3 (* h4 h4 h4 h4) h5 h6 (* j2 j2 j2
 j2 j2 j2)) (* 84 (* h1 h1) h2 h3 (* h4 h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 
178 (* h1 h1) h2 h3 (* h4 h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 172 (* h1 h1) h2 
h3 (* h4 h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 71 (* h1 h1) h2 h3 (* h4 h4 h4 h4) h5 
h6 (* j2 j2)) (* 8 (* h1 h1) h2 h3 (* h4 h4 h4 h4) h5 h6 j2) (* 6 (* h1 h1) h2 
h3 (* h4 h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 30 (* h1 h1) h2 h3 (* h4 
h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 54 (* h1 h1) h2 h3 (* h4 h4 h4 h4) 
(* h6 h6) (* j2 j2 j2 j2)) (* 42 (* h1 h1) h2 h3 (* h4 h4 h4 h4) (* h6 h6) (* j2
 j2 j2)) (* 12 (* h1 h1) h2 h3 (* h4 h4 h4 h4) (* h6 h6) (* j2 j2)) (* 6 (* h1 
h1) h2 h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 70 (* h1 h1) h2
 h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 302 (* h1 h1) h2 h3 (* 
h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 631 (* h1 h1) h2 h3 (* h4 h4 h4) 
(* h5 h5 h5) (* j2 j2 j2 j2)) (* 681 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5 h5) 
(* j2 j2 j2)) (* 363 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2)) (* 75 
(* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5 h5) j2) (* 48 (* h1 h1) h2 h3 (* h4 h4 h4)
 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 400 (* h1 h1) h2 h3 (* h4 h4 h4) (* 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 1357 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) 
h6 (* j2 j2 j2 j2 j2)) (* 2350 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 
j2 j2 j2)) (* 2151 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 
973 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 175 (* h1 h1) h2 h3 
(* h4 h4 h4) (* h5 h5) h6 j2) (* 8 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) h6) 
(* 54 (* h1 h1) h2 h3 (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 410
 (* h1 h1) h2 h3 (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1205 (* h1 
h1) h2 h3 (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1731 (* h1 h1) h2 h3 
(* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 1247 (* h1 h1) h2 h3 (* h4 h4 h4) 
h5 (* h6 h6) (* j2 j2 j2)) (* 401 (* h1 h1) h2 h3 (* h4 h4 h4) h5 (* h6 h6) (* 
j2 j2)) (* 36 (* h1 h1) h2 h3 (* h4 h4 h4) h5 (* h6 h6) j2) (* 12 (* h1 h1) h2 
h3 (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 84 (* h1 h1) h2 h3 (* 
h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 216 (* h1 h1) h2 h3 (* h4 h4 h4
) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 252 (* h1 h1) h2 h3 (* h4 h4 h4) (* h6 h6 
h6) (* j2 j2 j2 j2)) (* 132 (* h1 h1) h2 h3 (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 
j2)) (* 24 (* h1 h1) h2 h3 (* h4 h4 h4) (* h6 h6 h6) (* j2 j2)) (* 3 (* h1 h1) 
h2 h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 39 (* h1 h1) h2 
h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 195 (* h1 h1) h2 h3 
(* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 489 (* h1 h1) h2 h3 (* h4 h4
) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 670 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 
h5 h5) (* j2 j2 j2 j2)) (* 506 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 
j2 j2)) (* 196 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 30 (* h1 
h1) h2 h3 (* h4 h4) (* h5 h5 h5 h5) j2) (* 39 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5
 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 413 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1832 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2)) (* 4386 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2)) (* 6113 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 
j2)) (* 5011 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 2311 (* 
h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 525 (* h1 h1) h2 h3 (* h4 
h4) (* h5 h5 h5) h6 j2) (* 40 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) h6) (* 87 
(* h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
846 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
3427 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
7481 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 9449 
(* h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 6858 (* h1 h1)
 h2 h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 2656 (* h1 h1) h2 h3 (* h4
 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 458 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5) 
(* h6 h6) j2) (* 24 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* h6 h6)) (* 51 (* h1 
h1) h2 h3 (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 473 (* h1 h1
) h2 h3 (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1757 (* h1 h1) h2
 h3 (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3362 (* h1 h1) h2 h3 (* 
h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 3538 (* h1 h1) h2 h3 (* h4 h4) h5 
(* h6 h6 h6) (* j2 j2 j2 j2)) (* 2004 (* h1 h1) h2 h3 (* h4 h4) h5 (* h6 h6 h6) 
(* j2 j2 j2)) (* 541 (* h1 h1) h2 h3 (* h4 h4) h5 (* h6 h6 h6) (* j2 j2)) (* 48 
(* h1 h1) h2 h3 (* h4 h4) h5 (* h6 h6 h6) j2) (* 6 (* h1 h1) h2 h3 (* h4 h4) (* 
h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 50 (* h1 h1) h2 h3 (* h4 h4) (* h6 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 160 (* h1 h1) h2 h3 (* h4 h4) (* h6 h6 h6
 h6) (* j2 j2 j2 j2 j2 j2)) (* 252 (* h1 h1) h2 h3 (* h4 h4) (* h6 h6 h6 h6) (* 
j2 j2 j2 j2 j2)) (* 206 (* h1 h1) h2 h3 (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2
)) (* 82 (* h1 h1) h2 h3 (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 12 (* h1 h1)
 h2 h3 (* h4 h4) (* h6 h6 h6 h6) (* j2 j2)) (* 6 (* h1 h1) h2 h3 h4 (* h5 h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 86 (* h1 h1) h2 h3 h4 (* h5 h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 505 (* h1 h1) h2 h3 h4 (* h5 h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2)) (* 1589 (* h1 h1) h2 h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2
 j2 j2 j2)) (* 2944 (* h1 h1) h2 h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) 
(* 3332 (* h1 h1) h2 h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 2301 (* h1 h1)
 h2 h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 929 (* h1 h1) h2 h3 h4 (* h5 h5 h5
 h5) h6 (* j2 j2)) (* 196 (* h1 h1) h2 h3 h4 (* h5 h5 h5 h5) h6 j2) (* 16 (* h1 
h1) h2 h3 h4 (* h5 h5 h5 h5) h6) (* 36 (* h1 h1) h2 h3 h4 (* h5 h5 h5) (* h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 436 (* h1 h1) h2 h3 h4 (* h5 h5 h5) (* h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2267 (* h1 h1) h2 h3 h4 (* h5 h5 h5) (* h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2)) (* 6555 (* h1 h1) h2 h3 h4 (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 11518 (* h1 h1) h2 h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2)) (* 12693 (* h1 h1) h2 h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) 
(* 8736 (* h1 h1) h2 h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 3600 (* h1 h1
) h2 h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 799 (* h1 h1) h2 h3 h4 (* h5 h5 
h5) (* h6 h6) j2) (* 72 (* h1 h1) h2 h3 h4 (* h5 h5 h5) (* h6 h6)) (* 42 (* h1 
h1) h2 h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 482 (* h1
 h1) h2 h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2361 (* h1 
h1) h2 h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 6415 (* h1 h1) 
h2 h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 10525 (* h1 h1) h2 h3 
h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 10662 (* h1 h1) h2 h3 h4 (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 6549 (* h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2)) (* 2289 (* h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2)) 
(* 395 (* h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6 h6) j2) (* 24 (* h1 h1) h2 h3 h4 
(* h5 h5) (* h6 h6 h6)) (* 12 (* h1 h1) h2 h3 h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 133 (* h1 h1) h2 h3 h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 604 (* h1 h1) h2 h3 h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 1466 (* h1 h1) h2 h3 h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
2076 (* h1 h1) h2 h3 h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1748 (* h1 h1)
 h2 h3 h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 846 (* h1 h1) h2 h3 h4 h5 (* h6
 h6 h6 h6) (* j2 j2 j2)) (* 211 (* h1 h1) h2 h3 h4 h5 (* h6 h6 h6 h6) (* j2 j2))
 (* 20 (* h1 h1) h2 h3 h4 h5 (* h6 h6 h6 h6) j2) (* 18 (* h1 h1) h2 h3 (* h5 h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 192 (* h1 h1) h2 h3 (* h5 h5
 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 865 (* h1 h1) h2 h3 (* h5 h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2165 (* h1 h1) h2 h3 (* h5 h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3329 (* h1 h1) h2 h3 (* h5 h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2)) (* 3270 (* h1 h1) h2 h3 (* h5 h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2)) (* 2055 (* h1 h1) h2 h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) 
(* 797 (* h1 h1) h2 h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 173 (* h1 h1) h2 
h3 (* h5 h5 h5 h5) (* h6 h6) j2) (* 16 (* h1 h1) h2 h3 (* h5 h5 h5 h5) (* h6 h6)
) (* 41 (* h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 422 (* h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 1845 (* h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
4510 (* h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6812 
(* h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 6606 (* h1 h1) 
h2 h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 4117 (* h1 h1) h2 h3 (* h5 
h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 1590 (* h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6 
h6) (* j2 j2)) (* 345 (* h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6 h6) j2) (* 32 (* h1 
h1) h2 h3 (* h5 h5 h5) (* h6 h6 h6)) (* 21 (* h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 214 (* h1 h1) h2 h3 (* h5 h5) (* h6 h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 917 (* h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6
 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2170 (* h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2)) (* 3128 (* h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 
j2 j2 j2 j2)) (* 2846 (* h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2))
 (* 1629 (* h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 562 (* h1 h1
) h2 h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 105 (* h1 h1) h2 h3 (* h5 h5) 
(* h6 h6 h6 h6) j2) (* 8 (* h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6 h6)) (* 3 (* h1 
h1) h2 (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 15 (* h1 h1) h2 
(* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 26 (* h1 h1) h2 (* h4 h4 h4 
h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 18 (* h1 h1) h2 (* h4 h4 h4 h4) (* h5 h5) 
h6 (* j2 j2 j2)) (* 4 (* h1 h1) h2 (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 3 
(* h1 h1) h2 (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 12 (* h1 h1)
 h2 (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 16 (* h1 h1) h2 (* h4 h4
 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 8 (* h1 h1) h2 (* h4 h4 h4 h4) h5 (* h6
 h6) (* j2 j2 j2)) (* (* h1 h1) h2 (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2)) (* 6 
(* h1 h1) h2 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 42 (* h1 
h1) h2 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 113 (* h1 h1) h2 
(* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 147 (* h1 h1) h2 (* h4 h4 h4
) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 95 (* h1 h1) h2 (* h4 h4 h4) (* h5 h5 h5) 
h6 (* j2 j2 j2)) (* 27 (* h1 h1) h2 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 2
 (* h1 h1) h2 (* h4 h4 h4) (* h5 h5 h5) h6 j2) (* 12 (* h1 h1) h2 (* h4 h4 h4) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 81 (* h1 h1) h2 (* h4 h4 h4) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 206 (* h1 h1) h2 (* h4 h4 h4) (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 246 (* h1 h1) h2 (* h4 h4 h4) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2)) (* 139 (* h1 h1) h2 (* h4 h4 h4) (* h5 h5) (* h6 h6) 
(* j2 j2 j2)) (* 33 (* h1 h1) h2 (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 
3 (* h1 h1) h2 (* h4 h4 h4) (* h5 h5) (* h6 h6) j2) (* 6 (* h1 h1) h2 (* h4 h4 
h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 36 (* h1 h1) h2 (* h4 h4 h4) h5
 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 75 (* h1 h1) h2 (* h4 h4 h4) h5 (* h6 h6
 h6) (* j2 j2 j2 j2 j2)) (* 66 (* h1 h1) h2 (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 
j2 j2 j2)) (* 24 (* h1 h1) h2 (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 3 
(* h1 h1) h2 (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2)) (* 3 (* h1 h1) h2 (* h4 h4)
 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 25 (* h1 h1) h2 (* h4 h4) 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 82 (* h1 h1) h2 (* h4 h4) (* h5 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 137 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5 h5
) h6 (* j2 j2 j2 j2 j2)) (* 126 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 
j2 j2 j2)) (* 64 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 17 
(* h1 h1) h2 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 2 (* h1 h1) h2 (* h4 h4)
 (* h5 h5 h5 h5) h6 j2) (* 12 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 103 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 354 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 636 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2)) (* 652 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2)) (* 388 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 
129 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 21 (* h1 h1) h2 
(* h4 h4) (* h5 h5 h5) (* h6 h6) j2) (* (* h1 h1) h2 (* h4 h4) (* h5 h5 h5) (* 
h6 h6)) (* 12 (* h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 100 (* h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 328 (* h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 546 (* h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 496 (* h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 245 (* 
h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 62 (* h1 h1) h2 (* 
h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 7 (* h1 h1) h2 (* h4 h4) (* h5 h5) 
(* h6 h6 h6) j2) (* 3 (* h1 h1) h2 (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 22 (* h1 h1) h2 (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 60 (* h1 h1) h2 (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 78 (* h1 h1) h2 (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 51 (* h1 
h1) h2 (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 16 (* h1 h1) h2 (* h4 h4
) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 2 (* h1 h1) h2 (* h4 h4) h5 (* h6 h6 h6 h6
) (* j2 j2)) (* 3 (* h1 h1) h2 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2 j2)) (* 30 (* h1 h1) h2 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 125 (* h1 h1) h2 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 285 (* h1 h1) h2 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
394 (* h1 h1) h2 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 345 (* h1 
h1) h2 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 193 (* h1 h1) h2 h4 (* 
h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 67 (* h1 h1) h2 h4 (* h5 h5 h5 h5) (* h6
 h6) (* j2 j2)) (* 13 (* h1 h1) h2 h4 (* h5 h5 h5 h5) (* h6 h6) j2) (* (* h1 h1)
 h2 h4 (* h5 h5 h5 h5) (* h6 h6)) (* 6 (* h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 60 (* h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 250 (* h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 572 (* h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2)) (* 797 (* h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2)) (* 706 (* h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 400
 (* h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 140 (* h1 h1) h2 h4 
(* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 27 (* h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6
 h6) j2) (* 2 (* h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6 h6)) (* 3 (* h1 h1) h2 h4 
(* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 30 (* h1 h1) h2 h4 
(* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 122 (* h1 h1) h2 h4 
(* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 265 (* h1 h1) h2 h4 (* h5
 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 339 (* h1 h1) h2 h4 (* h5 h5) (* 
h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 264 (* h1 h1) h2 h4 (* h5 h5) (* h6 h6 h6 h6
) (* j2 j2 j2 j2)) (* 124 (* h1 h1) h2 h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)
) (* 33 (* h1 h1) h2 h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 4 (* h1 h1) h2 
h4 (* h5 h5) (* h6 h6 h6 h6) j2) (* (* h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 10 (* h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 43 (* h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 105 (* h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2
 j2 j2 j2 j2)) (* 161 (* h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2)) (* 161 (* h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 105 
(* h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 43 (* h1 h1) h2 (* h5
 h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 10 (* h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6 
h6) j2) (* (* h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6 h6)) (* (* h1 h1) h2 (* h5 h5 
h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 10 (* h1 h1) h2 (* h5 h5 
h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 43 (* h1 h1) h2 (* h5 h5 h5)
 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 105 (* h1 h1) h2 (* h5 h5 h5) (* 
h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 161 (* h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6
 h6) (* j2 j2 j2 j2 j2)) (* 161 (* h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 
j2 j2 j2)) (* 105 (* h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 43 
(* h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 10 (* h1 h1) h2 (* h5 h5
 h5) (* h6 h6 h6 h6) j2) (* (* h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6 h6)) (* 8 (* 
h1 h1) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 104 (* h1 h1
) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 536 (* h1 h1) (* h3 
h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 1416 (* h1 h1) (* h3 h3 h3 h3) 
(* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 2032 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4 h4) 
h5 (* j2 j2 j2)) (* 1504 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2)) 
(* 448 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4 h4) h5 j2) (* 16 (* h1 h1) (* h3 h3 h3
 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 160 (* h1 h1) (* h3 h3 h3 h3) 
(* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 656 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4
 h4) h6 (* j2 j2 j2 j2 j2)) (* 1408 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4 h4) h6 
(* j2 j2 j2 j2)) (* 1664 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2))
 (* 1024 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2)) (* 256 (* h1 h1) 
(* h3 h3 h3 h3) (* h4 h4 h4) h6 j2) (* 8 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) (* 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 144 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) 
(* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1048 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) 
(* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 4000 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) (* 
h5 h5) (* j2 j2 j2 j2 j2)) (* 8672 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5)
 (* j2 j2 j2 j2)) (* 10688 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 
j2 j2)) (* 6912 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 1792
 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) j2) (* 32 (* h1 h1) (* h3 h3 h3 
h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 504 (* h1 h1) (* h3 h3 h3 h3
) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 3208 (* h1 h1) (* h3 h3 h3 h3) 
(* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 10832 (* h1 h1) (* h3 h3 h3 h3) (* h4 
h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 21120 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 h6
 (* j2 j2 j2 j2)) (* 23968 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2
)) (* 14912 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 4224 (* h1 
h1) (* h3 h3 h3 h3) (* h4 h4) h5 h6 j2) (* 256 (* h1 h1) (* h3 h3 h3 h3) (* h4 
h4) h5 h6) (* 32 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 384 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 1920 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 5152 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)
) (* 7936 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 6912
 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 3072 (* h1 h1) 
(* h3 h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2)) (* 512 (* h1 h1) (* h3 h3 h3 h3) 
(* h4 h4) (* h6 h6) j2) (* 2 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 42 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 364 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2
 j2 j2 j2 j2)) (* 1686 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 
j2 j2)) (* 4518 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) 
(* 7080 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 6224 (* h1
 h1) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2)) (* 2736 (* h1 h1) (* h3 h3 h3
 h3) h4 (* h5 h5 h5) (* j2 j2)) (* 448 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5 h5)
 j2) (* 12 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 256 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 2256 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 10792 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
30700 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 53340 (* 
h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 55792 (* h1 h1) (* h3
 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 33136 (* h1 h1) (* h3 h3 h3 h3) h4 
(* h5 h5) h6 (* j2 j2)) (* 9792 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) h6 j2) 
(* 1024 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) h6) (* 24 (* h1 h1) (* h3 h3 h3 
h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 448 (* h1 h1) (* h3 h3 h3
 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3456 (* h1 h1) (* h3 h3 h3 
h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 14464 (* h1 h1) (* h3 h3 h3 h3)
 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 36008 (* h1 h1) (* h3 h3 h3 h3) h4 h5
 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 54696 (* h1 h1) (* h3 h3 h3 h3) h4 h5 (* h6 h6
) (* j2 j2 j2 j2)) (* 49776 (* h1 h1) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 
j2)) (* 25440 (* h1 h1) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 6336 (* h1
 h1) (* h3 h3 h3 h3) h4 h5 (* h6 h6) j2) (* 512 (* h1 h1) (* h3 h3 h3 h3) h4 h5 
(* h6 h6)) (* 16 (* h1 h1) (* h3 h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 208 (* h1 h1) (* h3 h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 1152 (* h1 h1) (* h3 h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 3536 (* h1 h1) (* h3 h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 6544 (* h1 h1) (* h3 h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 7424 
(* h1 h1) (* h3 h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 4992 (* h1 h1) (* 
h3 h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2)) (* 1792 (* h1 h1) (* h3 h3 h3 h3) h4 
(* h6 h6 h6) (* j2 j2)) (* 256 (* h1 h1) (* h3 h3 h3 h3) h4 (* h6 h6 h6) j2) (* 
12 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
224 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
1716 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 7024
 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 16764 (* h1
 h1) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 23928 (* h1 h1) (* 
h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 20256 (* h1 h1) (* h3 h3 h3 h3)
 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 9824 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5 h5) h6
 (* j2 j2)) (* 2496 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5 h5) h6 j2) (* 256 (* h1 
h1) (* h3 h3 h3 h3) (* h5 h5 h5) h6) (* 48 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 776 (* h1 h1) (* h3 h3 h3 h3) (* h5
 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 5200 (* h1 h1) (* h3 h3 h3 h3) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 19048 (* h1 h1) (* h3 h3 h3 h3)
 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 42048 (* h1 h1) (* h3 h3 h3 h3) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 57848 (* h1 h1) (* h3 h3 h3 h3) (* h5
 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 49360 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5) (* 
h6 h6) (* j2 j2 j2)) (* 25056 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* 
j2 j2)) (* 6848 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) j2) (* 768 (* h1 
h1) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6)) (* 48 (* h1 h1) (* h3 h3 h3 h3) h5 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 656 (* h1 h1) (* h3 h3 h3 h3) h5 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3824 (* h1 h1) (* h3 h3 h3 h3) h5 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 12400 (* h1 h1) (* h3 h3 h3 h3) h5 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 24464 (* h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6 
h6) (* j2 j2 j2 j2 j2)) (* 30192 (* h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2
 j2 j2 j2)) (* 23104 (* h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 
10496 (* h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 2560 (* h1 h1) (* 
h3 h3 h3 h3) h5 (* h6 h6 h6) j2) (* 256 (* h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6 h6
)) (* 4 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 44 
(* h1 h1) (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 180 (* h1 h1) 
(* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 348 (* h1 h1) (* h3 h3 h3) 
(* h4 h4 h4 h4) h5 (* j2 j2 j2)) (* 320 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4 h4) 
h5 (* j2 j2)) (* 112 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4 h4) h5 j2) (* 8 (* h1 h1
) (* h3 h3 h3) (* h4 h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 64 (* h1 h1) (* h3 
h3 h3) (* h4 h4 h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 200 (* h1 h1) (* h3 h3 h3) (* 
h4 h4 h4 h4) h6 (* j2 j2 j2 j2)) (* 304 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4 h4) 
h6 (* j2 j2 j2)) (* 224 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4 h4) h6 (* j2 j2)) (* 
64 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4 h4) h6 j2) (* 14 (* h1 h1) (* h3 h3 h3) 
(* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 182 (* h1 h1) (* h3 h3 h3) 
(* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 944 (* h1 h1) (* h3 h3 h3) (* 
h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 2526 (* h1 h1) (* h3 h3 h3) (* h4 h4 
h4) (* h5 h5) (* j2 j2 j2 j2)) (* 3670 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h5
 h5) (* j2 j2 j2)) (* 2716 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 
j2)) (* 784 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) j2) (* 52 (* h1 h1) 
(* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 552 (* h1 h1) (* h3
 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 2444 (* h1 h1) (* h3 h3 h3)
 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 5716 (* h1 h1) (* h3 h3 h3) (* h4 h4 
h4) h5 h6 (* j2 j2 j2 j2)) (* 7388 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* 
j2 j2 j2)) (* 5008 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2)) (* 1456 
(* h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 h6 j2) (* 64 (* h1 h1) (* h3 h3 h3) (* h4
 h4 h4) h5 h6) (* 32 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 304 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 1160 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 2248 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 
2288 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2)) (* 1120 (* h1 
h1) (* h3 h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2)) (* 192 (* h1 h1) (* h3 h3 h3)
 (* h4 h4 h4) (* h6 h6) j2) (* 8 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 137 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5
) (* j2 j2 j2 j2 j2 j2 j2)) (* 931 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5)
 (* j2 j2 j2 j2 j2 j2)) (* 3239 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) 
(* j2 j2 j2 j2 j2)) (* 6227 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 
j2 j2 j2)) (* 6622 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) 
(* 3612 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 784 (* h1 h1
) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) j2) (* 56 (* h1 h1) (* h3 h3 h3) (* h4 h4)
 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 828 (* h1 h1) (* h3 h3 h3) (* h4 
h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 4958 (* h1 h1) (* h3 h3 h3) (* h4 
h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 15926 (* h1 h1) (* h3 h3 h3) (* h4 h4
) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 29986 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* 
h5 h5) h6 (* j2 j2 j2 j2)) (* 33300 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) 
h6 (* j2 j2 j2)) (* 20464 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2
)) (* 5856 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 j2) (* 448 (* h1 h1) 
(* h3 h3 h3) (* h4 h4) (* h5 h5) h6) (* 96 (* h1 h1) (* h3 h3 h3) (* h4 h4) h5 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1148 (* h1 h1) (* h3 h3 h3) (* h4 h4) 
h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 5868 (* h1 h1) (* h3 h3 h3) (* h4 h4) 
h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 16536 (* h1 h1) (* h3 h3 h3) (* h4 h4) h5
 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 27504 (* h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* 
h6 h6) (* j2 j2 j2 j2)) (* 26748 (* h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) 
(* j2 j2 j2)) (* 14112 (* h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2)) 
(* 3376 (* h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) j2) (* 192 (* h1 h1) (* h3
 h3 h3) (* h4 h4) h5 (* h6 h6)) (* 32 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 344 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1528 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3608 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h6 h6 
h6) (* j2 j2 j2 j2 j2)) (* 4840 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h6 h6 h6) 
(* j2 j2 j2 j2)) (* 3632 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 
j2)) (* 1376 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2)) (* 192 (* 
h1 h1) (* h3 h3 h3) (* h4 h4) (* h6 h6 h6) j2) (* (* h1 h1) (* h3 h3 h3) h4 (* 
h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 20 (* h1 h1) (* h3 h3 h3) h4 (* 
h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 163 (* h1 h1) (* h3 h3 h3) h4 (* h5
 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 699 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 
h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1704 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5 h5) 
(* j2 j2 j2 j2 j2)) (* 2391 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 
j2 j2)) (* 1870 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2)) (* 740 
(* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2)) (* 112 (* h1 h1) (* h3 h3 
h3) h4 (* h5 h5 h5 h5) j2) (* 13 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2
 j2 j2 j2 j2 j2 j2 j2 j2)) (* 258 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 2110 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2)) (* 9285 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2)) (* 23938 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2)) (* 37050 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 
34098 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 17812 (* h1 h1)
 (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2)) (* 4688 (* h1 h1) (* h3 h3 h3) h4 
(* h5 h5 h5) h6 j2) (* 448 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) h6) (* 42 (* 
h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
752 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 5482 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 21448 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 49896 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
71758 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 63486 
(* h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 32724 (* h1 h1) 
(* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 8640 (* h1 h1) (* h3 h3 h3) h4
 (* h5 h5) (* h6 h6) j2) (* 832 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6)) 
(* 44 (* h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 608 (* h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 3688 (* h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
12672 (* h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 26632 
(* h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 34720 (* h1 h1)
 (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 27412 (* h1 h1) (* h3 h3 h3
) h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 12288 (* h1 h1) (* h3 h3 h3) h4 h5 (* h6 
h6 h6) (* j2 j2)) (* 2704 (* h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6 h6) j2) (* 192 
(* h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6 h6)) (* 8 (* h1 h1) (* h3 h3 h3) h4 (* h6 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 96 (* h1 h1) (* h3 h3 h3) h4 (* h6 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 488 (* h1 h1) (* h3 h3 h3) h4 (* h6 h6
 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1368 (* h1 h1) (* h3 h3 h3) h4 (* h6 h6 h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 2304 (* h1 h1) (* h3 h3 h3) h4 (* h6 h6 h6 h6) (* 
j2 j2 j2 j2 j2)) (* 2376 (* h1 h1) (* h3 h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 
j2)) (* 1456 (* h1 h1) (* h3 h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 480 (* 
h1 h1) (* h3 h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2)) (* 64 (* h1 h1) (* h3 h3 h3) 
h4 (* h6 h6 h6 h6) j2) (* 6 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 106 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2
 j2 j2 j2 j2 j2 j2)) (* 758 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2)) (* 2854 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2)) (* 6186 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2))
 (* 7974 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 6144 (* 
h1 h1) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 2752 (* h1 h1) (* h3 h3 
h3) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 656 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5 h5) 
h6 j2) (* 64 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5 h5) h6) (* 54 (* h1 h1) (* h3 h3
 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 798 (* h1 h1) (* 
h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4870 (* h1 h1) 
(* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 16126 (* h1 h1)
 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 32014 (* h1 h1) 
(* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 39654 (* h1 h1) (* h3
 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 30680 (* h1 h1) (* h3 h3 h3) 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 14288 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5
) (* h6 h6) (* j2 j2)) (* 3632 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) j2)
 (* 384 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6)) (* 96 (* h1 h1) (* h3 h3 
h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1204 (* h1 h1) (* 
h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6412 (* h1 h1) 
(* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 19092 (* h1 h1)
 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 35140 (* h1 h1) 
(* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 41468 (* h1 h1) (* h3
 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 31220 (* h1 h1) (* h3 h3 h3) 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 14352 (* h1 h1) (* h3 h3 h3) (* h5 h5) 
(* h6 h6 h6) (* j2 j2)) (* 3632 (* h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) j2
) (* 384 (* h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6)) (* 24 (* h1 h1) (* h3 h3
 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 304 (* h1 h1) (* h3 
h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1632 (* h1 h1) (* h3 
h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4848 (* h1 h1) (* h3 h3 
h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 8736 (* h1 h1) (* h3 h3 h3) h5 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 9856 (* h1 h1) (* h3 h3 h3) h5 (* h6 h6 
h6 h6) (* j2 j2 j2 j2)) (* 6936 (* h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 
j2 j2)) (* 2928 (* h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2)) (* 672 (* 
h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6 h6) j2) (* 64 (* h1 h1) (* h3 h3 h3) h5 (* h6
 h6 h6 h6)) (* 4 (* h1 h1) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2
 j2)) (* 41 (* h1 h1) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) 
(* 151 (* h1 h1) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 253 (* 
h1 h1) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 195 (* h1 h1) (* h3 
h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2)) (* 56 (* h1 h1) (* h3 h3) (* h4 h4 h4 
h4) (* h5 h5) j2) (* 16 (* h1 h1) (* h3 h3) (* h4 h4 h4 h4) h5 h6 (* j2 j2 j2 j2
 j2 j2)) (* 116 (* h1 h1) (* h3 h3) (* h4 h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) 
(* 316 (* h1 h1) (* h3 h3) (* h4 h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 400 (* h1 
h1) (* h3 h3) (* h4 h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 232 (* h1 h1) (* h3 h3) (* 
h4 h4 h4 h4) h5 h6 (* j2 j2)) (* 48 (* h1 h1) (* h3 h3) (* h4 h4 h4 h4) h5 h6 j2
) (* 8 (* h1 h1) (* h3 h3) (* h4 h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
48 (* h1 h1) (* h3 h3) (* h4 h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 104 (* 
h1 h1) (* h3 h3) (* h4 h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 96 (* h1 h1) (* 
h3 h3) (* h4 h4 h4 h4) (* h6 h6) (* j2 j2 j2)) (* 32 (* h1 h1) (* h3 h3) (* h4 
h4 h4 h4) (* h6 h6) (* j2 j2)) (* 7 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5
) (* j2 j2 j2 j2 j2 j2 j2)) (* 84 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2)) (* 393 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* 
j2 j2 j2 j2 j2)) (* 927 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 
j2 j2)) (* 1154 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 
711 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2)) (* 168 (* h1 h1) 
(* h3 h3) (* h4 h4 h4) (* h5 h5 h5) j2) (* 45 (* h1 h1) (* h3 h3) (* h4 h4 h4) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 447 (* h1 h1) (* h3 h3) (* h4 h4 h4) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 1827 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* 
h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 3841 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5)
 h6 (* j2 j2 j2 j2)) (* 4308 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2
 j2 j2)) (* 2460 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 604
 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 j2) (* 32 (* h1 h1) (* h3 h3) (* 
h4 h4 h4) (* h5 h5) h6) (* 58 (* h1 h1) (* h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 510 (* h1 h1) (* h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 1782 (* h1 h1) (* h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 
j2 j2 j2 j2)) (* 3104 (* h1 h1) (* h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 
j2)) (* 2778 (* h1 h1) (* h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 1180
 (* h1 h1) (* h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2)) (* 176 (* h1 h1) (* h3
 h3) (* h4 h4 h4) h5 (* h6 h6) j2) (* 16 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 124 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 364 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h6 h6 
h6) (* j2 j2 j2 j2 j2)) (* 496 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h6 h6 h6) (* 
j2 j2 j2 j2)) (* 304 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2))
 (* 64 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h6 h6 h6) (* j2 j2)) (* 2 (* h1 h1) 
(* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 32 (* h1 h1)
 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 198 (* h1 h1) 
(* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 606 (* h1 h1) (* 
h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 984 (* h1 h1) (* h3 h3) 
(* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 846 (* h1 h1) (* h3 h3) (* h4 h4) 
(* h5 h5 h5 h5) (* j2 j2 j2)) (* 356 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5 
h5) (* j2 j2)) (* 56 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) j2) (* 28 (* 
h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 386 
(* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2109 
(* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 6054 (* 
h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 9944 (* h1 h1)
 (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 9406 (* h1 h1) (* h3 h3
) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 4880 (* h1 h1) (* h3 h3) (* h4 h4) 
(* h5 h5 h5) h6 (* j2 j2)) (* 1208 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6
 j2) (* 96 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6) (* 82 (* h1 h1) (* h3 
h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 913 (* h1 h1) 
(* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4338 (* h1 
h1) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 11207 (* 
h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 16755 (* 
h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 14404 (* h1 
h1) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 6699 (* h1 h1) (* 
h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 1456 (* h1 h1) (* h3 h3) (* 
h4 h4) (* h5 h5) (* h6 h6) j2) (* 96 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* 
h6 h6)) (* 56 (* h1 h1) (* h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 564 (* h1 h1) (* h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 2402 (* h1 h1) (* h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 5464 (* h1 h1) (* h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 6936 (* h1 h1) (* h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 4756 
(* h1 h1) (* h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 1616 (* h1 h1) 
(* h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2)) (* 208 (* h1 h1) (* h3 h3) (* h4 
h4) h5 (* h6 h6 h6) j2) (* 8 (* h1 h1) (* h3 h3) (* h4 h4) (* h6 h6 h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 72 (* h1 h1) (* h3 h3) (* h4 h4) (* h6 h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 256 (* h1 h1) (* h3 h3) (* h4 h4) (* h6 h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 456 (* h1 h1) (* h3 h3) (* h4 h4) (* h6 h6 h6 h6) (* j2 
j2 j2 j2 j2)) (* 424 (* h1 h1) (* h3 h3) (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 
j2)) (* 192 (* h1 h1) (* h3 h3) (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 32 
(* h1 h1) (* h3 h3) (* h4 h4) (* h6 h6 h6 h6) (* j2 j2)) (* 3 (* h1 h1) (* h3 h3
) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 58 (* h1 h1) (* h3 h3
) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 450 (* h1 h1) (* h3 h3) 
h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1825 (* h1 h1) (* h3 h3) h4 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 4187 (* h1 h1) (* h3 h3) h4 (* h5 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 5554 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) 
h6 (* j2 j2 j2 j2)) (* 4258 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 
j2)) (* 1821 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 392 (* h1 
h1) (* h3 h3) h4 (* h5 h5 h5 h5) h6 j2) (* 32 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5
 h5) h6) (* 21 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 355 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 2402 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 8564 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 17834 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2
 j2 j2)) (* 22632 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2))
 (* 17509 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 7923 
(* h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 1884 (* h1 h1) (* h3
 h3) h4 (* h5 h5 h5) (* h6 h6) j2) (* 176 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5) 
(* h6 h6)) (* 36 (* h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2 j2)) (* 485 (* h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 2817 (* h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 9071 (* h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 17495 (* h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2
 j2 j2)) (* 20609 (* h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2))
 (* 14643 (* h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 5974 
(* h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 1244 (* h1 h1) (* h3
 h3) h4 (* h5 h5) (* h6 h6 h6) j2) (* 96 (* h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 
h6 h6)) (* 12 (* h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 150 (* h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2
 j2)) (* 802 (* h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2))
 (* 2338 (* h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
3970 (* h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 3954 (* h1
 h1) (* h3 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 2246 (* h1 h1) (* h3 h3
) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 668 (* h1 h1) (* h3 h3) h4 h5 (* h6 h6 
h6 h6) (* j2 j2)) (* 80 (* h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6 h6) j2) (* 12 (* 
h1 h1) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
170 (* h1 h1) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 972 (* h1 h1) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 2952 (* h1 h1) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
5268 (* h1 h1) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 5768 
(* h1 h1) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 3900 (* h1 h1)
 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 1578 (* h1 h1) (* h3 h3) 
(* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 348 (* h1 h1) (* h3 h3) (* h5 h5 h5 h5) 
(* h6 h6) j2) (* 32 (* h1 h1) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6)) (* 48 (* h1 
h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 554 
(* h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
2700 (* h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
7316 (* h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
12184 (* h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 12936
 (* h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 8740 (* h1 h1
) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 3614 (* h1 h1) (* h3 h3) 
(* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 828 (* h1 h1) (* h3 h3) (* h5 h5 h5) (* 
h6 h6 h6) j2) (* 80 (* h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6)) (* 24 (* h1 
h1) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 280 
(* h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
1376 (* h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
3728 (* h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
6128 (* h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 6336 
(* h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 4120 (* h1 h1)
 (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 1624 (* h1 h1) (* h3 h3) 
(* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 352 (* h1 h1) (* h3 h3) (* h5 h5) (* h6 
h6 h6 h6) j2) (* 32 (* h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6)) (* (* h1 h1) 
h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 9 (* h1 h1) h3 (* h4 
h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 27 (* h1 h1) h3 (* h4 h4 h4 h4) 
(* h5 h5 h5) (* j2 j2 j2 j2)) (* 33 (* h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5 h5) 
(* j2 j2 j2)) (* 14 (* h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2)) (* 8 
(* h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 50 (* h1 h1)
 h3 (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 112 (* h1 h1) h3 (* h4 
h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 104 (* h1 h1) h3 (* h4 h4 h4 h4) (* 
h5 h5) h6 (* j2 j2 j2)) (* 34 (* h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2
)) (* 9 (* h1 h1) h3 (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 44 
(* h1 h1) h3 (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 75 (* h1 h1) h3
 (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 52 (* h1 h1) h3 (* h4 h4 h4 h4
) h5 (* h6 h6) (* j2 j2 j2)) (* 12 (* h1 h1) h3 (* h4 h4 h4 h4) h5 (* h6 h6) (* 
j2 j2)) (* 2 (* h1 h1) h3 (* h4 h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 8 (* h1 h1) h3 (* h4 h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 10 (* h1 
h1) h3 (* h4 h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 4 (* h1 h1) h3 (* h4 h4 
h4 h4) (* h6 h6 h6) (* j2 j2 j2)) (* (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 10 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 
j2 j2 j2 j2 j2)) (* 36 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 
j2)) (* 60 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 47 (* 
h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 14 (* h1 h1) h3 (* h4 h4
 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 13 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 112 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2
 j2 j2 j2 j2 j2)) (* 391 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2)) (* 675 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 572
 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 204 (* h1 h1) h3 (* 
h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 15 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5
) h6 j2) (* 29 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 226 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 686 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 1009 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 731 
(* h1 h1) h3 (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 226 (* h1 h1) h3 
(* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 16 (* h1 h1) h3 (* h4 h4 h4) (* 
h5 h5) (* h6 h6) j2) (* 17 (* h1 h1) h3 (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2
 j2 j2 j2 j2)) (* 116 (* h1 h1) h3 (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 294 (* h1 h1) h3 (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
336 (* h1 h1) h3 (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 173 (* h1 h1) 
h3 (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 32 (* h1 h1) h3 (* h4 h4 h4) h5
 (* h6 h6 h6) (* j2 j2)) (* 2 (* h1 h1) h3 (* h4 h4 h4) (* h6 h6 h6 h6) (* j2 j2
 j2 j2 j2 j2 j2)) (* 10 (* h1 h1) h3 (* h4 h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2
 j2 j2)) (* 18 (* h1 h1) h3 (* h4 h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
14 (* h1 h1) h3 (* h4 h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 4 (* h1 h1) h3 
(* h4 h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 4 (* h1 h1) h3 (* h4 h4) (* h5 h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 51 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 243 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2)) (* 563 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2
 j2 j2 j2 j2)) (* 685 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2))
 (* 440 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 137 (* h1 h1)
 h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 15 (* h1 h1) h3 (* h4 h4) (* h5 
h5 h5 h5) h6 j2) (* 24 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 239 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 995 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 2223 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2)) (* 2831 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) 
(* 2012 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 728 (* h1
 h1) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 108 (* h1 h1) h3 (* h4 h4
) (* h5 h5 h5) (* h6 h6) j2) (* 4 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6))
 (* 28 (* h1 h1) h3 (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 254 (* h1 h1) h3 (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2))
 (* 966 (* h1 h1) h3 (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
1939 (* h1 h1) h3 (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2143 
(* h1 h1) h3 (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1273 (* h1 h1)
 h3 (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 365 (* h1 h1) h3 (* h4 h4)
 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 36 (* h1 h1) h3 (* h4 h4) (* h5 h5) (* h6 
h6 h6) j2) (* 8 (* h1 h1) h3 (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 67 (* h1 h1) h3 (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 217 (* h1 h1) h3 (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 346
 (* h1 h1) h3 (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 289 (* h1 h1) 
h3 (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 121 (* h1 h1) h3 (* h4 h4) 
h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 20 (* h1 h1) h3 (* h4 h4) h5 (* h6 h6 h6 h6)
 (* j2 j2)) (* 3 (* h1 h1) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 47 (* h1 h1) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 289 (* h1 h1) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2
)) (* 911 (* h1 h1) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
1623 (* h1 h1) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1706 (* h1
 h1) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 1060 (* h1 h1) h3 h4 
(* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 372 (* h1 h1) h3 h4 (* h5 h5 h5 h5) 
(* h6 h6) (* j2 j2)) (* 65 (* h1 h1) h3 h4 (* h5 h5 h5 h5) (* h6 h6) j2) (* 4 
(* h1 h1) h3 h4 (* h5 h5 h5 h5) (* h6 h6)) (* 11 (* h1 h1) h3 h4 (* h5 h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 130 (* h1 h1) h3 h4 (* h5 h5 h5)
 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 667 (* h1 h1) h3 h4 (* h5 h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1902 (* h1 h1) h3 h4 (* h5 h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3244 (* h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2)) (* 3374 (* h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2)) (* 2107 (* h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 
746 (* h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 131 (* h1 h1) h3 h4 
(* h5 h5 h5) (* h6 h6 h6) j2) (* 8 (* h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6 h6)) 
(* 6 (* h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 69 (* h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
336 (* h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 884 
(* h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1350 (* h1 
h1) h3 h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1220 (* h1 h1) h3 h4 
(* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 638 (* h1 h1) h3 h4 (* h5 h5) (* 
h6 h6 h6 h6) (* j2 j2 j2)) (* 177 (* h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6 h6) (* 
j2 j2)) (* 20 (* h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6 h6) j2) (* 6 (* h1 h1) h3 
(* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 64 (* h1 h1) h3 
(* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 286 (* h1 h1) h3 
(* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 704 (* h1 h1) h3 (* h5
 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1056 (* h1 h1) h3 (* h5 h5 h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1004 (* h1 h1) h3 (* h5 h5 h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2)) (* 606 (* h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 
j2 j2)) (* 224 (* h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 46 (* h1 
h1) h3 (* h5 h5 h5 h5) (* h6 h6 h6) j2) (* 4 (* h1 h1) h3 (* h5 h5 h5 h5) (* h6 
h6 h6)) (* 6 (* h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 64 (* h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 286 (* h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 704 (* h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1056 
(* h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1004 (* h1 h1) 
h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 606 (* h1 h1) h3 (* h5 h5 h5
) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 224 (* h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6 h6)
 (* j2 j2)) (* 46 (* h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6 h6) j2) (* 4 (* h1 h1) 
h3 (* h5 h5 h5) (* h6 h6 h6 h6)) (* (* h1 h1) (* h4 h4 h4 h4) (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 5 (* h1 h1) (* h4 h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2)) (* 8 (* h1 h1) (* h4 h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 4 
(* h1 h1) (* h4 h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 2 (* h1 h1) (* h4 h4 
h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 8 (* h1 h1) (* h4 h4 h4 h4)
 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 10 (* h1 h1) (* h4 h4 h4 h4) (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2)) (* 4 (* h1 h1) (* h4 h4 h4 h4) (* h5 h5) (* h6 h6
) (* j2 j2 j2)) (* (* h1 h1) (* h4 h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 3 (* h1 h1) (* h4 h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2 (* 
h1 h1) (* h4 h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* (* h1 h1) (* h4 h4 h4
) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 6 (* h1 h1) (* h4 h4 h4) (* h5
 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 13 (* h1 h1) (* h4 h4 h4) (* h5 h5 h5 h5
) h6 (* j2 j2 j2 j2 j2)) (* 12 (* h1 h1) (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 
j2 j2 j2)) (* 4 (* h1 h1) (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 4 (* 
h1 h1) (* h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 26 (* h1
 h1) (* h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 63 (* h1 h1) 
(* h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 68 (* h1 h1) (* h4 h4
 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 29 (* h1 h1) (* h4 h4 h4) (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2)) (* 2 (* h1 h1) (* h4 h4 h4) (* h5 h5 h5) (* h6 h6
) (* j2 j2)) (* 4 (* h1 h1) (* h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 23 (* h1 h1) (* h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2
 j2)) (* 46 (* h1 h1) (* h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 37 (* h1 h1) (* h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 10 (* h1
 h1) (* h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* (* h1 h1) (* h4 h4 h4)
 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1) (* h4 h4 h4) h5 (* 
h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 5 (* h1 h1) (* h4 h4 h4) h5 (* h6 h6 h6 
h6) (* j2 j2 j2 j2 j2)) (* 2 (* h1 h1) (* h4 h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 
j2 j2)) (* 2 (* h1 h1) (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 16 (* h1 h1) (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2
 j2)) (* 49 (* h1 h1) (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2))
 (* 73 (* h1 h1) (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 55 
(* h1 h1) (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 19 (* h1 h1) 
(* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 2 (* h1 h1) (* h4 h4) (* h5
 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 4 (* h1 h1) (* h4 h4) (* h5 h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 31 (* h1 h1) (* h4 h4) (* h5 h5 h5) (* h6 h6
 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 94 (* h1 h1) (* h4 h4) (* h5 h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 141 (* h1 h1) (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2)) (* 108 (* h1 h1) (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2)) (* 38 (* h1 h1) (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 
4 (* h1 h1) (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 2 (* h1 h1) (* h4 
h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 14 (* h1 h1) (* h4
 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 37 (* h1 h1) (* h4 
h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 46 (* h1 h1) (* h4 h4) 
(* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 27 (* h1 h1) (* h4 h4) (* h5 h5
) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 6 (* h1 h1) (* h4 h4) (* h5 h5) (* h6 h6 
h6 h6) (* j2 j2 j2)) (* (* h1 h1) h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 9 (* h1 h1) h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 33 (* h1 h1) h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 64 (* h1 h1) h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 71 (* h1 h1) h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 45 (* h1 
h1) h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 15 (* h1 h1) h4 (* h5 h5
 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 2 (* h1 h1) h4 (* h5 h5 h5 h5) (* h6 h6 h6
) (* j2 j2)) (* (* h1 h1) h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 9 (* h1 h1) h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 33 (* h1 h1) h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 64 (* h1 h1) h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 71 
(* h1 h1) h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 45 (* h1 h1) h4
 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 15 (* h1 h1) h4 (* h5 h5 h5) 
(* h6 h6 h6 h6) (* j2 j2 j2)) (* 2 (* h1 h1) h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* 
j2 j2)) (* 8 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 120 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 688 h1
 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 2064 h1 (* h2 h2 
h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 3624 h1 (* h2 h2 h2 h2) (* h3 
h3 h3) h4 h5 (* j2 j2 j2 j2)) (* 3864 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 (* 
j2 j2 j2)) (* 2464 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2)) (* 864 h1 
(* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 j2) (* 128 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4
 h5) (* 16 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 160 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 672 h1
 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2)) (* 1536 h1 (* h2 h2 
h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 2064 h1 (* h2 h2 h2 h2) (* h3 
h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 1632 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h6 (* 
j2 j2 j2)) (* 704 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2)) (* 128 h1 (* 
h2 h2 h2 h2) (* h3 h3 h3) h4 h6 j2) (* 2 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 
h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 40 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 
h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 310 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5
) (* j2 j2 j2 j2 j2 j2 j2)) (* 1220 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) 
(* j2 j2 j2 j2 j2 j2)) (* 2766 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 
j2 j2 j2 j2)) (* 3840 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2))
 (* 3322 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2)) (* 1748 h1 (* 
h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2)) (* 512 h1 (* h2 h2 h2 h2) (* h3 
h3 h3) (* h5 h5) j2) (* 64 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5)) (* 40 h1 
(* h2 h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 376 h1 (* h2 
h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1504 h1 (* h2 h2 h2 h2
) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 3344 h1 (* h2 h2 h2 h2) (* h3 h3 
h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 4520 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h5 h6 (* 
j2 j2 j2 j2)) (* 3800 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2)) (* 
1936 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2)) (* 544 h1 (* h2 h2 h2 h2) 
(* h3 h3 h3) h5 h6 j2) (* 64 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h5 h6) (* 8 h1 (* 
h2 h2 h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 88 h1 (* 
h2 h2 h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 416 h1 (* h2
 h2 h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1104 h1 (* h2 h2 
h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1800 h1 (* h2 h2 h2 h2) 
(* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1848 h1 (* h2 h2 h2 h2) (* h3 h3 
h3) (* h6 h6) (* j2 j2 j2 j2)) (* 1168 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h6 h6)
 (* j2 j2 j2)) (* 416 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2)) (* 64
 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h6 h6) j2) (* 6 h1 (* h2 h2 h2 h2) (* h3 h3)
 (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 78 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4
 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 360 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 
(* j2 j2 j2 j2 j2)) (* 828 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2
 j2)) (* 1062 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 774 h1 
(* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2)) (* 300 h1 (* h2 h2 h2 h2) (* 
h3 h3) (* h4 h4) h5 j2) (* 48 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5) (* 12 
h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 96 h1 (* 
h2 h2 h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 312 h1 (* h2 h2 h2
 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 528 h1 (* h2 h2 h2 h2) (* h3 
h3) (* h4 h4) h6 (* j2 j2 j2 j2)) (* 492 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) 
h6 (* j2 j2 j2)) (* 240 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2)) (* 
48 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h6 j2) (* 8 h1 (* h2 h2 h2 h2) (* h3 
h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 112 h1 (* h2 h2 h2 h2) (* h3 h3
) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 584 h1 (* h2 h2 h2 h2) (* h3 h3) h4 
(* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1584 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 
h5) (* j2 j2 j2 j2 j2)) (* 2520 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 
j2 j2 j2)) (* 2448 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 
1432 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2)) (* 464 h1 (* h2 h2 h2 
h2) (* h3 h3) h4 (* h5 h5) j2) (* 64 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5)) 
(* 24 h1 (* h2 h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 240 
h1 (* h2 h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1040 h1 (* h2
 h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 2536 h1 (* h2 h2 h2 h2) 
(* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 3784 h1 (* h2 h2 h2 h2) (* h3 h3) h4 
h5 h6 (* j2 j2 j2 j2)) (* 3520 h1 (* h2 h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2
)) (* 1984 h1 (* h2 h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2)) (* 616 h1 (* h2 h2 
h2 h2) (* h3 h3) h4 h5 h6 j2) (* 80 h1 (* h2 h2 h2 h2) (* h3 h3) h4 h5 h6) (* 16
 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 144 
h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 544 h1 
(* h2 h2 h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1120 h1 (* h2 
h2 h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1360 h1 (* h2 h2 h2 h2) 
(* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 976 h1 (* h2 h2 h2 h2) (* h3 h3) h4 
(* h6 h6) (* j2 j2 j2)) (* 384 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 
j2)) (* 64 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h6 h6) j2) (* h1 (* h2 h2 h2 h2) 
(* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 19 h1 (* h2 h2 h2 h2) 
(* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 137 h1 (* h2 h2 h2 h2) 
(* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 491 h1 (* h2 h2 h2 h2) (* h3
 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1011 h1 (* h2 h2 h2 h2) (* h3 h3) 
(* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 1281 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 
h5) (* j2 j2 j2 j2)) (* 1019 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 
j2)) (* 497 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2)) (* 136 h1 (* h2
 h2 h2 h2) (* h3 h3) (* h5 h5 h5) j2) (* 16 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 
h5 h5)) (* h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 54 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 413 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
1454 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 2943 h1
 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 3706 h1 (* h2 h2 
h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 2959 h1 (* h2 h2 h2 h2) (* h3 
h3) (* h5 h5) h6 (* j2 j2 j2)) (* 1458 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) h6
 (* j2 j2)) (* 404 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) h6 j2) (* 48 h1 (* h2 
h2 h2 h2) (* h3 h3) (* h5 h5) h6) (* 8 h1 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 92 h1 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 466 h1 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 1354 h1 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 2472 h1 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 
j2 j2 j2)) (* 2928 h1 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) 
(* 2242 h1 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 1066 h1 (* h2
 h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2)) (* 284 h1 (* h2 h2 h2 h2) (* h3 h3)
 h5 (* h6 h6) j2) (* 32 h1 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6)) (* 4 h1 (* h2
 h2 h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 40 h1 (* h2
 h2 h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 172 h1 (* h2 
h2 h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 416 h1 (* h2 h2 h2
 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 620 h1 (* h2 h2 h2 h2) (* 
h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 584 h1 (* h2 h2 h2 h2) (* h3 h3) (* 
h6 h6 h6) (* j2 j2 j2 j2)) (* 340 h1 (* h2 h2 h2 h2) (* h3 h3) (* h6 h6 h6) (* 
j2 j2 j2)) (* 112 h1 (* h2 h2 h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2)) (* 16 h1 
(* h2 h2 h2 h2) (* h3 h3) (* h6 h6 h6) j2) (* 3 h1 (* h2 h2 h2 h2) h3 (* h4 h4) 
(* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 36 h1 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 
h5) (* j2 j2 j2 j2 j2 j2)) (* 147 h1 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* 
j2 j2 j2 j2 j2)) (* 300 h1 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2
)) (* 345 h1 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 228 h1 (* 
h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2)) (* 81 h1 (* h2 h2 h2 h2) h3 (* h4
 h4) (* h5 h5) j2) (* 12 h1 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5)) (* 13 h1 (* 
h2 h2 h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 87 h1 (* h2 h2 h2 
h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 240 h1 (* h2 h2 h2 h2) h3 (* h4
 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 350 h1 (* h2 h2 h2 h2) h3 (* h4 h4) h5 h6 (* 
j2 j2 j2 j2)) (* 285 h1 (* h2 h2 h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2)) (* 123 
h1 (* h2 h2 h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2)) (* 22 h1 (* h2 h2 h2 h2) h3 (* 
h4 h4) h5 h6 j2) (* 6 h1 (* h2 h2 h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 36 h1 (* h2 h2 h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)
) (* 84 h1 (* h2 h2 h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 96 h1 
(* h2 h2 h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 54 h1 (* h2 h2 h2 h2)
 h3 (* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 12 h1 (* h2 h2 h2 h2) h3 (* h4 h4) (* 
h6 h6) (* j2 j2)) (* 2 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 26 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2))
 (* 122 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 298 h1 
(* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 430 h1 (* h2 h2 h2 h2)
 h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 382 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5
) (* j2 j2 j2)) (* 206 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2)) (* 62 h1
 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) j2) (* 8 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5 
h5)) (* 12 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 109 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 428 h1
 (* h2 h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 945 h1 (* h2 h2 h2
 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 1280 h1 (* h2 h2 h2 h2) h3 h4 (* 
h5 h5) h6 (* j2 j2 j2 j2)) (* 1087 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 
j2 j2)) (* 564 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2)) (* 163 h1 (* h2 
h2 h2 h2) h3 h4 (* h5 h5) h6 j2) (* 20 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5) h6) 
(* 14 h1 (* h2 h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 112 
h1 (* h2 h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 374 h1 (* h2 
h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 680 h1 (* h2 h2 h2 h2) h3
 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 730 h1 (* h2 h2 h2 h2) h3 h4 h5 (* h6 h6
) (* j2 j2 j2 j2)) (* 464 h1 (* h2 h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2)) 
(* 162 h1 (* h2 h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2)) (* 24 h1 (* h2 h2 h2 h2)
 h3 h4 h5 (* h6 h6) j2) (* 4 h1 (* h2 h2 h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 28 h1 (* h2 h2 h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 80 h1 (* h2 h2 h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
120 h1 (* h2 h2 h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 100 h1 (* h2 h2
 h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 44 h1 (* h2 h2 h2 h2) h3 h4 (* h6
 h6 h6) (* j2 j2 j2)) (* 8 h1 (* h2 h2 h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2)) (* 
11 h1 (* h2 h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 87 h1 
(* h2 h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 299 h1 (* h2 h2 
h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 583 h1 (* h2 h2 h2 h2) h3 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 705 h1 (* h2 h2 h2 h2) h3 (* h5 h5 h5) h6
 (* j2 j2 j2 j2)) (* 541 h1 (* h2 h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 
257 h1 (* h2 h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2)) (* 69 h1 (* h2 h2 h2 h2) h3
 (* h5 h5 h5) h6 j2) (* 8 h1 (* h2 h2 h2 h2) h3 (* h5 h5 h5) h6) (* 4 h1 (* h2 
h2 h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 45 h1 (* h2 
h2 h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 212 h1 (* h2 h2
 h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 559 h1 (* h2 h2 h2 
h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 918 h1 (* h2 h2 h2 h2) h3 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 979 h1 (* h2 h2 h2 h2) h3 (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2)) (* 680 h1 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6) (* 
j2 j2 j2)) (* 297 h1 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2)) (* 74 h1 
(* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6) j2) (* 8 h1 (* h2 h2 h2 h2) h3 (* h5 h5) 
(* h6 h6)) (* 2 h1 (* h2 h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
 j2)) (* 21 h1 (* h2 h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 90 h1 (* h2 h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 211 h1 
(* h2 h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 300 h1 (* h2 h2 h2 
h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 267 h1 (* h2 h2 h2 h2) h3 h5 (* h6
 h6 h6) (* j2 j2 j2 j2)) (* 146 h1 (* h2 h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 
j2)) (* 45 h1 (* h2 h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2)) (* 6 h1 (* h2 h2 h2 
h2) h3 h5 (* h6 h6 h6) j2) (* 3 h1 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2)) (* 19 h1 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 
j2 j2 j2)) (* 51 h1 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) 
(* 75 h1 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 65 h1 (* h2 
h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 33 h1 (* h2 h2 h2 h2) (* h4 h4
) (* h5 h5) h6 (* j2 j2)) (* 9 h1 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5) h6 j2) (* 
h1 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5) h6) (* 3 h1 (* h2 h2 h2 h2) (* h4 h4) h5 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 16 h1 (* h2 h2 h2 h2) (* h4 h4) h5 (* h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 35 h1 (* h2 h2 h2 h2) (* h4 h4) h5 (* h6 h6) (* j2
 j2 j2 j2 j2)) (* 40 h1 (* h2 h2 h2 h2) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) 
(* 25 h1 (* h2 h2 h2 h2) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 8 h1 (* h2 h2 
h2 h2) (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* h1 (* h2 h2 h2 h2) (* h4 h4) h5 (* 
h6 h6) j2) (* 2 h1 (* h2 h2 h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 15 h1 (* h2 h2 h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 49 
h1 (* h2 h2 h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 91 h1 (* h2 h2 
h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 105 h1 (* h2 h2 h2 h2) h4 (* h5
 h5 h5) h6 (* j2 j2 j2 j2)) (* 77 h1 (* h2 h2 h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2
 j2)) (* 35 h1 (* h2 h2 h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2)) (* 9 h1 (* h2 h2 h2
 h2) h4 (* h5 h5 h5) h6 j2) (* h1 (* h2 h2 h2 h2) h4 (* h5 h5 h5) h6) (* 4 h1 
(* h2 h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 29 h1 (* 
h2 h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 92 h1 (* h2 h2 
h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 167 h1 (* h2 h2 h2 h2) 
h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 190 h1 (* h2 h2 h2 h2) h4 (* h5 h5
) (* h6 h6) (* j2 j2 j2 j2)) (* 139 h1 (* h2 h2 h2 h2) h4 (* h5 h5) (* h6 h6) 
(* j2 j2 j2)) (* 64 h1 (* h2 h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 17 
h1 (* h2 h2 h2 h2) h4 (* h5 h5) (* h6 h6) j2) (* 2 h1 (* h2 h2 h2 h2) h4 (* h5 
h5) (* h6 h6)) (* 2 h1 (* h2 h2 h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 13 h1 (* h2 h2 h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 36 h1 (* h2 h2 h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 55 h1 (* 
h2 h2 h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 50 h1 (* h2 h2 h2 h2) h4 
h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 27 h1 (* h2 h2 h2 h2) h4 h5 (* h6 h6 h6) (* 
j2 j2 j2)) (* 8 h1 (* h2 h2 h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2)) (* h1 (* h2 h2 
h2 h2) h4 h5 (* h6 h6 h6) j2) (* h1 (* h2 h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2 j2)) (* 9 h1 (* h2 h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 36 h1 (* h2 h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 84 h1 (* h2 h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 126 h1 (* h2 h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
126 h1 (* h2 h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 84 h1 (* h2 h2
 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 36 h1 (* h2 h2 h2 h2) (* h5 h5 
h5) (* h6 h6) (* j2 j2)) (* 9 h1 (* h2 h2 h2 h2) (* h5 h5 h5) (* h6 h6) j2) (* 
h1 (* h2 h2 h2 h2) (* h5 h5 h5) (* h6 h6)) (* h1 (* h2 h2 h2 h2) (* h5 h5) (* h6
 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 9 h1 (* h2 h2 h2 h2) (* h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 36 h1 (* h2 h2 h2 h2) (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 84 h1 (* h2 h2 h2 h2) (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 126 h1 (* h2 h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2
 j2 j2 j2)) (* 126 h1 (* h2 h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) 
(* 84 h1 (* h2 h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 36 h1 (* h2 h2 
h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 9 h1 (* h2 h2 h2 h2) (* h5 h5) (* h6
 h6 h6) j2) (* h1 (* h2 h2 h2 h2) (* h5 h5) (* h6 h6 h6)) (* 16 h1 (* h2 h2 h2) 
(* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 256 h1 (* h2 h2 h2) (* h3 
h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 1600 h1 (* h2 h2 h2) (* h3 h3 h3 h3
) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 5280 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 (* 
j2 j2 j2 j2 j2)) (* 10224 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2))
 (* 12000 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2)) (* 8384 h1 (* h2 
h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2)) (* 3200 h1 (* h2 h2 h2) (* h3 h3 h3 h3) 
h4 h5 j2) (* 512 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5) (* 32 h1 (* h2 h2 h2) 
(* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 352 h1 (* h2 h2 h2) (* h3 
h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1632 h1 (* h2 h2 h2) (* h3 h3 h3 h3
) h4 h6 (* j2 j2 j2 j2 j2 j2)) (* 4128 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h6 (* 
j2 j2 j2 j2 j2)) (* 6144 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2)) 
(* 5376 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2)) (* 2560 h1 (* h2 h2 
h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2)) (* 512 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 
h6 j2) (* 4 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2
 j2)) (* 84 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 696 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 2984 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 7428
 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 11316 h1 (* h2
 h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 10688 h1 (* h2 h2 h2) (* 
h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2)) (* 6096 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* 
h5 h5) (* j2 j2)) (* 1920 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) j2) (* 256 
h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5)) (* 80 h1 (* h2 h2 h2) (* h3 h3 h3 h3)
 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 832 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h5 h6
 (* j2 j2 j2 j2 j2 j2 j2)) (* 3680 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 
j2 j2 j2 j2 j2)) (* 9024 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2
)) (* 13392 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 12288 h1 
(* h2 h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2)) (* 6784 h1 (* h2 h2 h2) (* h3 
h3 h3 h3) h5 h6 (* j2 j2)) (* 2048 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h5 h6 j2) (* 
256 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h5 h6) (* 16 h1 (* h2 h2 h2) (* h3 h3 h3 h3)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 192 h1 (* h2 h2 h2) (* h3 h3 h3 h3
) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 992 h1 (* h2 h2 h2) (* h3 h3 h3 h3) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2880 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 5136 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* 5760 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 
j2 j2)) (* 3968 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2)) (* 1536 
h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2)) (* 256 h1 (* h2 h2 h2) (* 
h3 h3 h3 h3) (* h6 h6) j2) (* 16 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 256 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 
j2 j2 j2 j2 j2 j2)) (* 1640 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 
j2 j2 j2 j2)) (* 5576 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 
j2)) (* 11096 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 
13304 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 9424 h1 (* h2 
h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2)) (* 3616 h1 (* h2 h2 h2) (* h3 h3 h3)
 (* h4 h4) h5 j2) (* 576 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5) (* 32 h1 (* 
h2 h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 368 h1 (* h2
 h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1776 h1 (* h2 h2 
h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 4656 h1 (* h2 h2 h2) (* 
h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 7152 h1 (* h2 h2 h2) (* h3 h3 h3) 
(* h4 h4) h6 (* j2 j2 j2 j2)) (* 6432 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h6 
(* j2 j2 j2)) (* 3136 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2)) (* 
640 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h6 j2) (* 8 h1 (* h2 h2 h2) (* h3 h3 
h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 180 h1 (* h2 h2 h2) (* h3 h3
 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1556 h1 (* h2 h2 h2) (* h3 h3 
h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 6800 h1 (* h2 h2 h2) (* h3 h3 h3) 
h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 17088 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* 
h5 h5) (* j2 j2 j2 j2 j2)) (* 26244 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) 
(* j2 j2 j2 j2)) (* 25060 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2)
) (* 14520 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2)) (* 4672 h1 (* h2
 h2 h2) (* h3 h3 h3) h4 (* h5 h5) j2) (* 640 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* 
h5 h5)) (* 32 h1 (* h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 572 h1 (* h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 3984 h1 (* h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 14924
 h1 (* h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 33852 h1 (* h2 
h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 48696 h1 (* h2 h2 h2) (* h3 
h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 44596 h1 (* h2 h2 h2) (* h3 h3 h3) h4 h5 h6 
(* j2 j2 j2)) (* 25072 h1 (* h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2)) (* 7824 
h1 (* h2 h2 h2) (* h3 h3 h3) h4 h5 h6 j2) (* 1024 h1 (* h2 h2 h2) (* h3 h3 h3) 
h4 h5 h6) (* 32 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 416 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 2304 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 7104 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 13344 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 15648 
h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 11200 h1 (* h2 h2 
h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2)) (* 4480 h1 (* h2 h2 h2) (* h3 h3 h3)
 h4 (* h6 h6) (* j2 j2)) (* 768 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6) j2) 
(* 4 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 79 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
603 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 2338 
h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 5262 h1 (* 
h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 7311 h1 (* h2 h2 h2) 
(* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 6371 h1 (* h2 h2 h2) (* h3 h3 h3) 
(* h5 h5 h5) (* j2 j2 j2)) (* 3392 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* 
j2 j2)) (* 1008 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) j2) (* 128 h1 (* h2 h2
 h2) (* h3 h3 h3) (* h5 h5 h5)) (* 54 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 906 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6
 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 5590 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 18116 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2)) (* 35158 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 
j2 j2 j2)) (* 43102 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) 
(* 33694 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 16276 h1 (* 
h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2)) (* 4416 h1 (* h2 h2 h2) (* h3 h3 
h3) (* h5 h5) h6 j2) (* 512 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6) (* 124 h1
 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1404 
h1 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6948 
h1 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 19704 h1 
(* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 35236 h1 (* h2 
h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 41116 h1 (* h2 h2 h2) 
(* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 31212 h1 (* h2 h2 h2) (* h3 h3 h3)
 h5 (* h6 h6) (* j2 j2 j2)) (* 14800 h1 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) 
(* j2 j2)) (* 3952 h1 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) j2) (* 448 h1 (* h2
 h2 h2) (* h3 h3 h3) h5 (* h6 h6)) (* 16 h1 (* h2 h2 h2) (* h3 h3 h3) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 176 h1 (* h2 h2 h2) (* h3 h3 h3) (* h6 h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 832 h1 (* h2 h2 h2) (* h3 h3 h3) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2208 h1 (* h2 h2 h2) (* h3 h3 h3) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 3600 h1 (* h2 h2 h2) (* h3 h3 h3) (* h6 h6 h6) (* j2 
j2 j2 j2 j2)) (* 3696 h1 (* h2 h2 h2) (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2))
 (* 2336 h1 (* h2 h2 h2) (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2)) (* 832 h1 (* h2
 h2 h2) (* h3 h3 h3) (* h6 h6 h6) (* j2 j2)) (* 128 h1 (* h2 h2 h2) (* h3 h3 h3)
 (* h6 h6 h6) j2) (* 8 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 
j2 j2 j2)) (* 108 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2
)) (* 548 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 1404 
h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 1996 h1 (* h2 h2 
h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 1592 h1 (* h2 h2 h2) (* h3 h3) 
(* h4 h4 h4) h5 (* j2 j2)) (* 664 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 j2) 
(* 112 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5) (* 16 h1 (* h2 h2 h2) (* h3 h3
) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 144 h1 (* h2 h2 h2) (* h3 h3) (* 
h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 528 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4
) h6 (* j2 j2 j2 j2 j2)) (* 1008 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h6 (* j2
 j2 j2 j2)) (* 1056 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2)) (* 
576 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h6 (* j2 j2)) (* 128 h1 (* h2 h2 h2) 
(* h3 h3) (* h4 h4 h4) h6 j2) (* 16 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5
) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 240 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 
h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1409 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 
h5) (* j2 j2 j2 j2 j2 j2)) (* 4306 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5)
 (* j2 j2 j2 j2 j2)) (* 7628 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2
 j2 j2 j2)) (* 8130 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2)) 
(* 5139 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 1772 h1 (* 
h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) j2) (* 256 h1 (* h2 h2 h2) (* h3 h3) (* 
h4 h4) (* h5 h5)) (* 64 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2
 j2 j2 j2 j2)) (* 694 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 
j2 j2 j2)) (* 3236 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 
j2)) (* 8434 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 
13366 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 13108 h1 (* 
h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 7710 h1 (* h2 h2 h2) (* h3 
h3) (* h4 h4) h5 h6 (* j2 j2)) (* 2460 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6
 j2) (* 320 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6) (* 32 h1 (* h2 h2 h2) (* 
h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 336 h1 (* h2 h2 h2) 
(* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1460 h1 (* h2 h2 h2) 
(* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3404 h1 (* h2 h2 h2) (* 
h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 4604 h1 (* h2 h2 h2) (* h3 h3)
 (* h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 3620 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4
) (* h6 h6) (* j2 j2 j2)) (* 1536 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) 
(* j2 j2)) (* 272 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) j2) (* 4 h1 (* 
h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 86 h1 (* 
h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 695 h1 (* h2
 h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 2769 h1 (* h2 h2 
h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 6270 h1 (* h2 h2 h2) (* 
h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 8652 h1 (* h2 h2 h2) (* h3 h3) h4 
(* h5 h5 h5) (* j2 j2 j2 j2)) (* 7439 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) 
(* j2 j2 j2)) (* 3901 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2)) (* 
1144 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) j2) (* 144 h1 (* h2 h2 h2) (* h3 
h3) h4 (* h5 h5 h5)) (* 36 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2
 j2 j2 j2 j2 j2 j2)) (* 573 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 3545 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2)) (* 11813 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 
j2 j2 j2)) (* 23920 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)
) (* 30881 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 25567 
h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 13117 h1 (* h2 h2 h2)
 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 3780 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5
 h5) h6 j2) (* 464 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6) (* 64 h1 (* h2 h2 
h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 758 h1 (* h2 h2
 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3928 h1 (* h2 h2 
h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 11658 h1 (* h2 h2 h2)
 (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 21762 h1 (* h2 h2 h2) (* h3
 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 26384 h1 (* h2 h2 h2) (* h3 h3) h4 
h5 (* h6 h6) (* j2 j2 j2 j2)) (* 20670 h1 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6)
 (* j2 j2 j2)) (* 10024 h1 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 
2704 h1 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) j2) (* 304 h1 (* h2 h2 h2) (* h3 
h3) h4 h5 (* h6 h6)) (* 16 h1 (* h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2
 j2 j2 j2 j2 j2 j2)) (* 192 h1 (* h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 968 h1 (* h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2
 j2 j2 j2 j2)) (* 2688 h1 (* h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 4512 h1 (* h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 4704 h1 (* h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 2984 h1 
(* h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2)) (* 1056 h1 (* h2 h2 h2) (* 
h3 h3) h4 (* h6 h6 h6) (* j2 j2)) (* 160 h1 (* h2 h2 h2) (* h3 h3) h4 (* h6 h6 
h6) j2) (* h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 19 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 137 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
491 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1011 h1 
(* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 1281 h1 (* h2 h2 
h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 1019 h1 (* h2 h2 h2) (* h3 h3)
 (* h5 h5 h5 h5) (* j2 j2 j2)) (* 497 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) 
(* j2 j2)) (* 136 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) j2) (* 16 h1 (* h2 
h2 h2) (* h3 h3) (* h5 h5 h5 h5)) (* 27 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 428 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5)
 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2416 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 7115 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 12563 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* 14082 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)
) (* 10138 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 4551 h1 
(* h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2)) (* 1160 h1 (* h2 h2 h2) (* h3 
h3) (* h5 h5 h5) h6 j2) (* 128 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6) (* 142
 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 1401 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 6082 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2
)) (* 15252 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2))
 (* 24334 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
25581 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 17682 h1
 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 7726 h1 (* h2 h2 h2
) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 1928 h1 (* h2 h2 h2) (* h3 h3) (* 
h5 h5) (* h6 h6) j2) (* 208 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6)) (* 66
 h1 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
668 h1 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
2960 h1 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 7534
 h1 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 12126 h1 
(* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 12776 h1 (* h2 h2 
h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 8788 h1 (* h2 h2 h2) (* h3 h3)
 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 3790 h1 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6)
 (* j2 j2)) (* 924 h1 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) j2) (* 96 h1 (* h2 
h2 h2) (* h3 h3) h5 (* h6 h6 h6)) (* 4 h1 (* h2 h2 h2) (* h3 h3) (* h6 h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 40 h1 (* h2 h2 h2) (* h3 h3) (* h6 h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 172 h1 (* h2 h2 h2) (* h3 h3) (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 416 h1 (* h2 h2 h2) (* h3 h3) (* h6 h6 h6 h6) (* j2
 j2 j2 j2 j2 j2)) (* 620 h1 (* h2 h2 h2) (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 
j2 j2)) (* 584 h1 (* h2 h2 h2) (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 340
 h1 (* h2 h2 h2) (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 112 h1 (* h2 h2 h2) 
(* h3 h3) (* h6 h6 h6 h6) (* j2 j2)) (* 16 h1 (* h2 h2 h2) (* h3 h3) (* h6 h6 h6
 h6) j2) (* 4 h1 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)
) (* 50 h1 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 227 
h1 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 510 h1 (* h2 h2
 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 632 h1 (* h2 h2 h2) h3 (* h4 
h4 h4) (* h5 h5) (* j2 j2 j2)) (* 440 h1 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) 
(* j2 j2)) (* 161 h1 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) j2) (* 24 h1 (* h2 
h2 h2) h3 (* h4 h4 h4) (* h5 h5)) (* 20 h1 (* h2 h2 h2) h3 (* h4 h4 h4) h5 h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 150 h1 (* h2 h2 h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2 
j2 j2 j2 j2)) (* 458 h1 (* h2 h2 h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) 
(* 728 h1 (* h2 h2 h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 636 h1 (* h2 h2
 h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 290 h1 (* h2 h2 h2) h3 (* h4 h4 h4) 
h5 h6 (* j2 j2)) (* 54 h1 (* h2 h2 h2) h3 (* h4 h4 h4) h5 h6 j2) (* 8 h1 (* h2 
h2 h2) h3 (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 56 h1 (* h2 h2 h2)
 h3 (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 152 h1 (* h2 h2 h2) h3 (* 
h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 200 h1 (* h2 h2 h2) h3 (* h4 h4 h4) 
(* h6 h6) (* j2 j2 j2 j2)) (* 128 h1 (* h2 h2 h2) h3 (* h4 h4 h4) (* h6 h6) (* 
j2 j2 j2)) (* 32 h1 (* h2 h2 h2) h3 (* h4 h4 h4) (* h6 h6) (* j2 j2)) (* 4 h1 
(* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 56 h1 (* 
h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 300 h1 (* h2 h2
 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 824 h1 (* h2 h2 h2) h3 
(* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 1304 h1 (* h2 h2 h2) h3 (* h4 h4) 
(* h5 h5 h5) (* j2 j2 j2 j2)) (* 1240 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) 
(* j2 j2 j2)) (* 700 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 216
 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) j2) (* 28 h1 (* h2 h2 h2) h3 (* h4 h4
) (* h5 h5 h5)) (* 32 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 315 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2
 j2 j2)) (* 1330 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)
) (* 3128 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 4460 
h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 3931 h1 (* h2 h2 
h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 2082 h1 (* h2 h2 h2) h3 (* h4 h4)
 (* h5 h5) h6 (* j2 j2)) (* 602 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 j2) 
(* 72 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6) (* 36 h1 (* h2 h2 h2) h3 (* h4 
h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 331 h1 (* h2 h2 h2) h3 (* h4 h4
) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1250 h1 (* h2 h2 h2) h3 (* h4 h4) h5
 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2526 h1 (* h2 h2 h2) h3 (* h4 h4) h5 (* h6 
h6) (* j2 j2 j2 j2 j2)) (* 2962 h1 (* h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 
j2 j2 j2)) (* 2021 h1 (* h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 
744 h1 (* h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 114 h1 (* h2 h2 h2) 
h3 (* h4 h4) h5 (* h6 h6) j2) (* 8 h1 (* h2 h2 h2) h3 (* h4 h4) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 68 h1 (* h2 h2 h2) h3 (* h4 h4) (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 232 h1 (* h2 h2 h2) h3 (* h4 h4) (* h6 h6 h6) (* j2 j2 j2
 j2 j2 j2)) (* 408 h1 (* h2 h2 h2) h3 (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2))
 (* 392 h1 (* h2 h2 h2) h3 (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 196 h1 (* 
h2 h2 h2) h3 (* h4 h4) (* h6 h6 h6) (* j2 j2 j2)) (* 40 h1 (* h2 h2 h2) h3 (* h4
 h4) (* h6 h6 h6) (* j2 j2)) (* 2 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2
 j2 j2 j2 j2 j2 j2)) (* 26 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 
j2 j2 j2)) (* 122 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) 
(* 298 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 430 h1 (* h2
 h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 382 h1 (* h2 h2 h2) h3 h4 (* 
h5 h5 h5 h5) (* j2 j2 j2)) (* 206 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2
)) (* 62 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) j2) (* 8 h1 (* h2 h2 h2) h3 h4 
(* h5 h5 h5 h5)) (* 8 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2
 j2 j2 j2)) (* 127 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2
 j2)) (* 750 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
2340 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 4391 h1 (* 
h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 5223 h1 (* h2 h2 h2) h3 
h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 3972 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5) 
h6 (* j2 j2 j2)) (* 1870 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2)) (* 495
 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5) h6 j2) (* 56 h1 (* h2 h2 h2) h3 h4 (* h5 h5 
h5) h6) (* 32 h1 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 347 h1 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2
 j2)) (* 1647 h1 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 4470 h1 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
7615 h1 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 8419 h1 
(* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 6025 h1 (* h2 h2 h2) 
h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 2684 h1 (* h2 h2 h2) h3 h4 (* h5 h5) 
(* h6 h6) (* j2 j2)) (* 673 h1 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) j2) (* 72 
h1 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6)) (* 16 h1 (* h2 h2 h2) h3 h4 h5 (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 175 h1 (* h2 h2 h2) h3 h4 h5 (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 795 h1 (* h2 h2 h2) h3 h4 h5 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 1977 h1 (* h2 h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2
 j2 j2 j2 j2)) (* 2964 h1 (* h2 h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2))
 (* 2757 h1 (* h2 h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1559 h1 (* h2
 h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 491 h1 (* h2 h2 h2) h3 h4 h5 (* 
h6 h6 h6) (* j2 j2)) (* 66 h1 (* h2 h2 h2) h3 h4 h5 (* h6 h6 h6) j2) (* 4 h1 (* 
h2 h2 h2) h3 h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 28 h1 (* h2 h2 
h2) h3 h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 80 h1 (* h2 h2 h2) h3 h4 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 120 h1 (* h2 h2 h2) h3 h4 (* h6 h6 h6 
h6) (* j2 j2 j2 j2 j2)) (* 100 h1 (* h2 h2 h2) h3 h4 (* h6 h6 h6 h6) (* j2 j2 j2
 j2)) (* 44 h1 (* h2 h2 h2) h3 h4 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 8 h1 (* h2 h2
 h2) h3 h4 (* h6 h6 h6 h6) (* j2 j2)) (* 11 h1 (* h2 h2 h2) h3 (* h5 h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 87 h1 (* h2 h2 h2) h3 (* h5 h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2)) (* 299 h1 (* h2 h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2)) (* 583 h1 (* h2 h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
705 h1 (* h2 h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 541 h1 (* h2 h2 h2
) h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 257 h1 (* h2 h2 h2) h3 (* h5 h5 h5 h5) 
h6 (* j2 j2)) (* 69 h1 (* h2 h2 h2) h3 (* h5 h5 h5 h5) h6 j2) (* 8 h1 (* h2 h2 
h2) h3 (* h5 h5 h5 h5) h6) (* 31 h1 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2 j2)) (* 295 h1 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 1222 h1 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 2901 h1 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 4358 h1 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2)) (* 4301 h1 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 
2790 h1 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 1147 h1 (* h2 h2
 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 271 h1 (* h2 h2 h2) h3 (* h5 h5 h5)
 (* h6 h6) j2) (* 28 h1 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6)) (* 33 h1 (* h2 
h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 306 h1 (* h2
 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1239 h1 (* h2 
h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2880 h1 (* h2 h2 
h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4239 h1 (* h2 h2 h2) h3 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 4098 h1 (* h2 h2 h2) h3 (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2)) (* 2601 h1 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2)) (* 1044 h1 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 
240 h1 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) j2) (* 24 h1 (* h2 h2 h2) h3 (* h5
 h5) (* h6 h6 h6)) (* 2 h1 (* h2 h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 21 h1 (* h2 h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 90 h1 (* h2 h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 211 h1 (* h2 h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 300 h1 
(* h2 h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 267 h1 (* h2 h2 h2) h3
 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 146 h1 (* h2 h2 h2) h3 h5 (* h6 h6 h6 h6
) (* j2 j2 j2)) (* 45 h1 (* h2 h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2)) (* 6 h1 
(* h2 h2 h2) h3 h5 (* h6 h6 h6 h6) j2) (* 4 h1 (* h2 h2 h2) (* h4 h4 h4) (* h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 28 h1 (* h2 h2 h2) (* h4 h4 h4) (* h5 h5) h6
 (* j2 j2 j2 j2 j2 j2)) (* 79 h1 (* h2 h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2
 j2 j2 j2)) (* 117 h1 (* h2 h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) 
(* 98 h1 (* h2 h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 46 h1 (* h2 h2 
h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 11 h1 (* h2 h2 h2) (* h4 h4 h4) (* 
h5 h5) h6 j2) (* h1 (* h2 h2 h2) (* h4 h4 h4) (* h5 h5) h6) (* 4 h1 (* h2 h2 h2)
 (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 24 h1 (* h2 h2 h2) (* h4
 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 56 h1 (* h2 h2 h2) (* h4 h4 h4) 
h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 65 h1 (* h2 h2 h2) (* h4 h4 h4) h5 (* h6 h6)
 (* j2 j2 j2 j2)) (* 39 h1 (* h2 h2 h2) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2)) 
(* 11 h1 (* h2 h2 h2) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2)) (* h1 (* h2 h2 h2) 
(* h4 h4 h4) h5 (* h6 h6) j2) (* 4 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 34 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2)) (* 119 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2
 j2 j2 j2)) (* 227 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2))
 (* 260 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 184 h1 (* 
h2 h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 79 h1 (* h2 h2 h2) (* h4 h4
) (* h5 h5 h5) h6 (* j2 j2)) (* 19 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5) h6 j2)
 (* 2 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5) h6) (* 8 h1 (* h2 h2 h2) (* h4 h4) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 68 h1 (* h2 h2 h2) (* h4 h4)
 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 236 h1 (* h2 h2 h2) (* h4 h4) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 443 h1 (* h2 h2 h2) (* h4 h4) (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 495 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2)) (* 338 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) 
(* j2 j2 j2)) (* 138 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) 
(* 31 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) j2) (* 3 h1 (* h2 h2 h2) (* 
h4 h4) (* h5 h5) (* h6 h6)) (* 4 h1 (* h2 h2 h2) (* h4 h4) h5 (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 30 h1 (* h2 h2 h2) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2
 j2 j2 j2 j2 j2)) (* 91 h1 (* h2 h2 h2) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2
 j2 j2)) (* 146 h1 (* h2 h2 h2) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 134 h1 (* h2 h2 h2) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 70 h1 (* h2
 h2 h2) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 19 h1 (* h2 h2 h2) (* h4 h4) 
h5 (* h6 h6 h6) (* j2 j2)) (* 2 h1 (* h2 h2 h2) (* h4 h4) h5 (* h6 h6 h6) j2) 
(* 2 h1 (* h2 h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 15 h1
 (* h2 h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 49 h1 (* h2 h2 
h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 91 h1 (* h2 h2 h2) h4 (* h5 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 105 h1 (* h2 h2 h2) h4 (* h5 h5 h5 h5) h6 
(* j2 j2 j2 j2)) (* 77 h1 (* h2 h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 35
 h1 (* h2 h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 9 h1 (* h2 h2 h2) h4 (* h5 
h5 h5 h5) h6 j2) (* h1 (* h2 h2 h2) h4 (* h5 h5 h5 h5) h6) (* 4 h1 (* h2 h2 h2) 
h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 40 h1 (* h2 h2 h2) 
h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 168 h1 (* h2 h2 h2) h4
 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 396 h1 (* h2 h2 h2) h4 (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 584 h1 (* h2 h2 h2) h4 (* h5 h5 h5
) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 564 h1 (* h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6)
 (* j2 j2 j2 j2)) (* 360 h1 (* h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2))
 (* 148 h1 (* h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 36 h1 (* h2 h2 
h2) h4 (* h5 h5 h5) (* h6 h6) j2) (* 4 h1 (* h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6)
) (* 4 h1 (* h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (* 40 h1 (* h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 167 h1 (* h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
389 h1 (* h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 563 h1 
(* h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 529 h1 (* h2 h2 h2
) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 325 h1 (* h2 h2 h2) h4 (* h5 h5)
 (* h6 h6 h6) (* j2 j2 j2)) (* 127 h1 (* h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* 
j2 j2)) (* 29 h1 (* h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6) j2) (* 3 h1 (* h2 h2 h2)
 h4 (* h5 h5) (* h6 h6 h6)) (* 2 h1 (* h2 h2 h2) h4 h5 (* h6 h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 13 h1 (* h2 h2 h2) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 36 h1 (* h2 h2 h2) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 55 h1 (* h2 h2 h2) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 50 h1 (* h2 
h2 h2) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 27 h1 (* h2 h2 h2) h4 h5 (* h6 
h6 h6 h6) (* j2 j2 j2)) (* 8 h1 (* h2 h2 h2) h4 h5 (* h6 h6 h6 h6) (* j2 j2)) 
(* h1 (* h2 h2 h2) h4 h5 (* h6 h6 h6 h6) j2) (* h1 (* h2 h2 h2) (* h5 h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 9 h1 (* h2 h2 h2) (* h5 h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 36 h1 (* h2 h2 h2) (* h5 h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 84 h1 (* h2 h2 h2) (* h5 h5 h5 h5) (* h6 h6)
 (* j2 j2 j2 j2 j2 j2)) (* 126 h1 (* h2 h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2)) (* 126 h1 (* h2 h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) 
(* 84 h1 (* h2 h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 36 h1 (* h2 h2 
h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 9 h1 (* h2 h2 h2) (* h5 h5 h5 h5) 
(* h6 h6) j2) (* h1 (* h2 h2 h2) (* h5 h5 h5 h5) (* h6 h6)) (* 2 h1 (* h2 h2 h2)
 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 18 h1 (* h2 h2 h2)
 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 72 h1 (* h2 h2 h2) 
(* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 168 h1 (* h2 h2 h2) (* h5
 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 252 h1 (* h2 h2 h2) (* h5 h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 252 h1 (* h2 h2 h2) (* h5 h5 h5) (* h6 h6 h6
) (* j2 j2 j2 j2)) (* 168 h1 (* h2 h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)
) (* 72 h1 (* h2 h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 18 h1 (* h2 h2 
h2) (* h5 h5 h5) (* h6 h6 h6) j2) (* 2 h1 (* h2 h2 h2) (* h5 h5 h5) (* h6 h6 h6)
) (* h1 (* h2 h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 9 h1 (* h2 h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
36 h1 (* h2 h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 84 h1 
(* h2 h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 126 h1 (* h2 h2
 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 126 h1 (* h2 h2 h2) (* h5 
h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 84 h1 (* h2 h2 h2) (* h5 h5) (* h6 h6 h6
 h6) (* j2 j2 j2)) (* 36 h1 (* h2 h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) 
(* 9 h1 (* h2 h2 h2) (* h5 h5) (* h6 h6 h6 h6) j2) (* h1 (* h2 h2 h2) (* h5 h5) 
(* h6 h6 h6 h6)) (* 24 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 392 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2
 j2 j2)) (* 2600 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)
) (* 9272 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 19552
 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 24992 h1 (* h2 h2
) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 18880 h1 (* h2 h2) (* h3 h3 h3 
h3) (* h4 h4) h5 (* j2 j2)) (* 7680 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 j2
) (* 1280 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5) (* 48 h1 (* h2 h2) (* h3 h3
 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 576 h1 (* h2 h2) (* h3 h3 
h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2928 h1 (* h2 h2) (* h3 h3 h3 
h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 8160 h1 (* h2 h2) (* h3 h3 h3 h3) (* 
h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 13440 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h6
 (* j2 j2 j2 j2)) (* 13056 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2
)) (* 6912 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2)) (* 1536 h1 (* h2
 h2) (* h3 h3 h3 h3) (* h4 h4) h6 j2) (* 12 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 252 h1 (* h2 h2) (* h3 h3 h3 h3) h4 
(* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2152 h1 (* h2 h2) (* h3 h3 h3 h3) h4 
(* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 9816 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* 
h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 26476 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5)
 (* j2 j2 j2 j2 j2)) (* 43964 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2
 j2 j2)) (* 45088 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 
27632 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2)) (* 9216 h1 (* h2 h2) 
(* h3 h3 h3 h3) h4 (* h5 h5) j2) (* 1280 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 
h5)) (* 48 h1 (* h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (* 824 h1 (* h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
5928 h1 (* h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 23600 h1
 (* h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 57448 h1 (* h2 h2)
 (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 88712 h1 (* h2 h2) (* h3 h3 h3 
h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 86800 h1 (* h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* 
j2 j2 j2)) (* 51744 h1 (* h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2)) (* 16960 h1
 (* h2 h2) (* h3 h3 h3 h3) h4 h5 h6 j2) (* 2304 h1 (* h2 h2) (* h3 h3 h3 h3) h4 
h5 h6) (* 48 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 640 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2
 j2)) (* 3680 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 11904 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
23664 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 29568 h1 
(* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 22656 h1 (* h2 h2) 
(* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2)) (* 9728 h1 (* h2 h2) (* h3 h3 h3 h3) 
h4 (* h6 h6) (* j2 j2)) (* 1792 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6) j2) 
(* 2 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 48 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
460 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 2272 
h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 6322 h1 (* 
h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 10400 h1 (* h2 h2) 
(* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 10304 h1 (* h2 h2) (* h3 h3 h3 
h3) (* h5 h5 h5) (* j2 j2 j2)) (* 6032 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5)
 (* j2 j2)) (* 1920 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) j2) (* 256 h1 (* 
h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5)) (* 76 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5
) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1220 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 7900 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 27628 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5)
 h6 (* j2 j2 j2 j2 j2 j2)) (* 58072 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 
(* j2 j2 j2 j2 j2)) (* 76496 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 
j2 j2)) (* 63360 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 
31872 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2)) (* 8832 h1 (* h2 h2) 
(* h3 h3 h3 h3) (* h5 h5) h6 j2) (* 1024 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) 
h6) (* 152 h1 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 1912 h1 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 10432 h1 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 32336 h1 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
62616 h1 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 78360 h1 
(* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 63184 h1 (* h2 h2) 
(* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 31520 h1 (* h2 h2) (* h3 h3 h3 h3)
 h5 (* h6 h6) (* j2 j2)) (* 8768 h1 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) j2) 
(* 1024 h1 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6)) (* 16 h1 (* h2 h2) (* h3 h3 
h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 192 h1 (* h2 h2) (* h3 h3
 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 992 h1 (* h2 h2) (* h3 h3 
h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2880 h1 (* h2 h2) (* h3 h3 h3 
h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 5136 h1 (* h2 h2) (* h3 h3 h3 h3) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 5760 h1 (* h2 h2) (* h3 h3 h3 h3) (* h6 h6 h6) 
(* j2 j2 j2 j2)) (* 3968 h1 (* h2 h2) (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2))
 (* 1536 h1 (* h2 h2) (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2)) (* 256 h1 (* h2 h2
) (* h3 h3 h3 h3) (* h6 h6 h6) j2) (* 24 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) 
h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 336 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 
(* j2 j2 j2 j2 j2 j2)) (* 1808 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 
j2 j2 j2 j2)) (* 4976 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2))
 (* 7640 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 6560 h1 (* 
h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2)) (* 2912 h1 (* h2 h2) (* h3 h3 h3)
 (* h4 h4 h4) h5 j2) (* 512 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5) (* 48 h1 
(* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 464 h1 (* h2
 h2) (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 1840 h1 (* h2 h2) 
(* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 3824 h1 (* h2 h2) (* h3 h3 
h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2)) (* 4384 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 
h4) h6 (* j2 j2 j2)) (* 2624 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2)
) (* 640 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h6 j2) (* 42 h1 (* h2 h2) (* h3 
h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 660 h1 (* h2 h2) (* 
h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 4152 h1 (* h2 h2) (* 
h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 13828 h1 (* h2 h2) (* h3
 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 26870 h1 (* h2 h2) (* h3 h3 
h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 31352 h1 (* h2 h2) (* h3 h3 h3) (* 
h4 h4) (* h5 h5) (* j2 j2 j2)) (* 21528 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* 
h5 h5) (* j2 j2)) (* 7968 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) j2) (* 
1216 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5)) (* 156 h1 (* h2 h2) (* h3 h3
 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1888 h1 (* h2 h2) (* h3 h3 
h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 9800 h1 (* h2 h2) (* h3 h3 h3) 
(* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 28296 h1 (* h2 h2) (* h3 h3 h3) (* h4 
h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 49324 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6
 (* j2 j2 j2 j2)) (* 52680 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2
)) (* 33280 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 11168 h1 (* 
h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 j2) (* 1472 h1 (* h2 h2) (* h3 h3 h3) (* h4 
h4) h5 h6) (* 96 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 1056 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2
 j2 j2 j2)) (* 4872 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2
 j2 j2)) (* 12192 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 17832 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 
15216 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 7008 h1 (* 
h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2)) (* 1344 h1 (* h2 h2) (* h3 h3
 h3) (* h4 h4) (* h6 h6) j2) (* 12 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 239 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1909 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 8032 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* 
j2 j2 j2 j2 j2 j2)) (* 19784 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 
j2 j2 j2)) (* 29921 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) 
(* 28055 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2)) (* 15840 h1 (* 
h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2)) (* 4912 h1 (* h2 h2) (* h3 h3 h3)
 h4 (* h5 h5 h5) j2) (* 640 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5)) (* 84 h1 
(* h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1390 
h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 9508 
h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 35414 h1 
(* h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 79786 h1 (* h2 
h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 113536 h1 (* h2 h2) (* 
h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 102478 h1 (* h2 h2) (* h3 h3 h3) 
h4 (* h5 h5) h6 (* j2 j2 j2)) (* 56652 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6
 (* j2 j2)) (* 17376 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 j2) (* 2240 h1 
(* h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6) (* 144 h1 (* h2 h2) (* h3 h3 h3) h4 h5 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1936 h1 (* h2 h2) (* h3 h3 h3) h4 
h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 11280 h1 (* h2 h2) (* h3 h3 h3) h4 
h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 37264 h1 (* h2 h2) (* h3 h3 h3) h4 h5 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 76632 h1 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 
h6) (* j2 j2 j2 j2 j2)) (* 101264 h1 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* 
j2 j2 j2 j2)) (* 85464 h1 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) 
(* 44032 h1 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 12384 h1 (* h2 
h2) (* h3 h3 h3) h4 h5 (* h6 h6) j2) (* 1408 h1 (* h2 h2) (* h3 h3 h3) h4 h5 (* 
h6 h6)) (* 48 h1 (* h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 592 h1 (* h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2
 j2)) (* 3120 h1 (* h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 9168 h1 (* h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
16416 h1 (* h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 18336 h1 
(* h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 12480 h1 (* h2 h2) 
(* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2)) (* 4736 h1 (* h2 h2) (* h3 h3 h3) h4 
(* h6 h6 h6) (* j2 j2)) (* 768 h1 (* h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6) j2) (* 
h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 23 
h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 208 h1
 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 950 h1 (* 
h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2397 h1 (* h2 h2) 
(* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 3567 h1 (* h2 h2) (* h3 h3 
h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 3218 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 
h5 h5) (* j2 j2 j2)) (* 1732 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2)
) (* 512 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) j2) (* 64 h1 (* h2 h2) (* h3 
h3 h3) (* h5 h5 h5 h5)) (* 77 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2
 j2 j2 j2 j2 j2 j2 j2)) (* 1159 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 6923 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2)) (* 22141 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2)) (* 42626 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2)) (* 51852 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 
40126 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 19112 h1 (* h2 
h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2)) (* 5088 h1 (* h2 h2) (* h3 h3 h3) 
(* h5 h5 h5) h6 j2) (* 576 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6) (* 298 h1 
(* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
3434 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 17066 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2))
 (* 48176 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 85302 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
98274 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 73574 h1
 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 34420 h1 (* h2 h2) 
(* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 9088 h1 (* h2 h2) (* h3 h3 h3) 
(* h5 h5) (* h6 h6) j2) (* 1024 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6)) 
(* 172 h1 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (* 1916 h1 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 9280 h1 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
25624 h1 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 44396 
h1 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 49964 h1 (* h2 
h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 36424 h1 (* h2 h2) (* h3 h3
 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 16512 h1 (* h2 h2) (* h3 h3 h3) h5 (* h6 
h6 h6) (* j2 j2)) (* 4192 h1 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) j2) (* 448 
h1 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6)) (* 8 h1 (* h2 h2) (* h3 h3 h3) (* h6 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 88 h1 (* h2 h2) (* h3 h3 h3) (* h6 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 416 h1 (* h2 h2) (* h3 h3 h3) (* h6 h6
 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1104 h1 (* h2 h2) (* h3 h3 h3) (* h6 h6 h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 1800 h1 (* h2 h2) (* h3 h3 h3) (* h6 h6 h6 h6) (* 
j2 j2 j2 j2 j2)) (* 1848 h1 (* h2 h2) (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 
j2)) (* 1168 h1 (* h2 h2) (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 416 h1 
(* h2 h2) (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2)) (* 64 h1 (* h2 h2) (* h3 h3 h3
) (* h6 h6 h6 h6) j2) (* 6 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2
 j2 j2 j2)) (* 68 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) 
(* 264 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 480 h1 (* 
h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2)) (* 442 h1 (* h2 h2) (* h3 h3) 
(* h4 h4 h4 h4) h5 (* j2 j2)) (* 196 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 
j2) (* 32 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5) (* 12 h1 (* h2 h2) (* h3 h3
) (* h4 h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 84 h1 (* h2 h2) (* h3 h3) (* h4 
h4 h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 228 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) 
h6 (* j2 j2 j2 j2)) (* 300 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) h6 (* j2 j2 j2
)) (* 192 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) h6 (* j2 j2)) (* 48 h1 (* h2 h2
) (* h3 h3) (* h4 h4 h4 h4) h6 j2) (* 24 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 311 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* 
h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1506 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 
h5) (* j2 j2 j2 j2 j2)) (* 3666 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) 
(* j2 j2 j2 j2)) (* 4958 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 
j2)) (* 3771 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 1500 h1
 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) j2) (* 240 h1 (* h2 h2) (* h3 h3) 
(* h4 h4 h4) (* h5 h5)) (* 96 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2
 j2 j2 j2 j2 j2)) (* 862 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 
j2 j2 j2)) (* 3226 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2))
 (* 6432 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 7246 h1 
(* h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 4494 h1 (* h2 h2) (* h3 
h3) (* h4 h4 h4) h5 h6 (* j2 j2)) (* 1348 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) h5
 h6 j2) (* 128 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6) (* 48 h1 (* h2 h2) (* 
h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 404 h1 (* h2 h2) (* 
h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1356 h1 (* h2 h2) (* h3 
h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2300 h1 (* h2 h2) (* h3 h3) 
(* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 2052 h1 (* h2 h2) (* h3 h3) (* h4 h4 
h4) (* h6 h6) (* j2 j2 j2)) (* 896 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h6 h6)
 (* j2 j2)) (* 144 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h6 h6) j2) (* 21 h1 
(* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 309 
h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1783 
h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 5352 h1 
(* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 9261 h1 (* h2 
h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 9563 h1 (* h2 h2) (* h3
 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 5799 h1 (* h2 h2) (* h3 h3) (* h4 
h4) (* h5 h5 h5) (* j2 j2)) (* 1896 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5
) j2) (* 256 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5)) (* 135 h1 (* h2 h2) 
(* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1524 h1 (* h2 
h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 7313 h1 (* h2 
h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 19299 h1 (* h2 h2
) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 30528 h1 (* h2 h2) (* 
h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 29593 h1 (* h2 h2) (* h3 h3) 
(* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 17120 h1 (* h2 h2) (* h3 h3) (* h4 h4) 
(* h5 h5) h6 (* j2 j2)) (* 5368 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 j2
) (* 688 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6) (* 174 h1 (* h2 h2) (* 
h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1748 h1 (* h2 h2) 
(* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 7478 h1 (* h2 h2) 
(* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 17628 h1 (* h2 h2) 
(* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 24770 h1 (* h2 h2) (* h3
 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 20940 h1 (* h2 h2) (* h3 h3) (* 
h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 10154 h1 (* h2 h2) (* h3 h3) (* h4 h4) h5 
(* h6 h6) (* j2 j2)) (* 2452 h1 (* h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6) j2) 
(* 192 h1 (* h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6)) (* 48 h1 (* h2 h2) (* h3 
h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 468 h1 (* h2 h2) (* 
h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1872 h1 (* h2 h2) (* 
h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3960 h1 (* h2 h2) (* h3 
h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 4752 h1 (* h2 h2) (* h3 h3) 
(* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 3204 h1 (* h2 h2) (* h3 h3) (* h4 h4)
 (* h6 h6 h6) (* j2 j2 j2)) (* 1104 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h6 h6 h6
) (* j2 j2)) (* 144 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h6 h6 h6) j2) (* 3 h1 
(* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 57 h1 
(* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 426 h1 
(* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1640 h1 (* 
h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 3627 h1 (* h2 h2) 
(* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 4869 h1 (* h2 h2) (* h3 h3) 
h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 4032 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 
h5 h5) (* j2 j2 j2)) (* 2010 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2)
) (* 552 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) j2) (* 64 h1 (* h2 h2) (* h3 
h3) h4 (* h5 h5 h5 h5)) (* 42 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2
 j2 j2 j2 j2 j2 j2 j2)) (* 653 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 4138 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2)) (* 14090 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2)) (* 28757 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2)) (* 36870 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 
29915 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 14871 h1 (* h2 
h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2)) (* 4112 h1 (* h2 h2) (* h3 h3) h4 
(* h5 h5 h5) h6 j2) (* 480 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6) (* 123 h1 
(* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
1572 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 8553 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 26055 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 49060 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
59284 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 45970 h1
 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 22007 h1 (* h2 h2) 
(* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 5868 h1 (* h2 h2) (* h3 h3) h4 
(* h5 h5) (* h6 h6) j2) (* 656 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6)) 
(* 84 h1 (* h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 988 h1 (* h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 4986 h1 (* h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
14116 h1 (* h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 24598 
h1 (* h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 27194 h1 (* h2 
h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 18888 h1 (* h2 h2) (* h3 h3
) h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 7806 h1 (* h2 h2) (* h3 h3) h4 h5 (* h6 h6
 h6) (* j2 j2)) (* 1676 h1 (* h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) j2) (* 128 h1 
(* h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6)) (* 12 h1 (* h2 h2) (* h3 h3) h4 (* h6 h6
 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 136 h1 (* h2 h2) (* h3 h3) h4 (* h6 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 644 h1 (* h2 h2) (* h3 h3) h4 (* h6 h6
 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1664 h1 (* h2 h2) (* h3 h3) h4 (* h6 h6 h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 2564 h1 (* h2 h2) (* h3 h3) h4 (* h6 h6 h6 h6) (* 
j2 j2 j2 j2 j2)) (* 2408 h1 (* h2 h2) (* h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 
j2)) (* 1340 h1 (* h2 h2) (* h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 400 h1 
(* h2 h2) (* h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2)) (* 48 h1 (* h2 h2) (* h3 h3) 
h4 (* h6 h6 h6 h6) j2) (* 19 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 268 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2
 j2 j2 j2 j2 j2 j2)) (* 1470 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2)) (* 4281 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2)) (* 7475 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2))
 (* 8238 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 5784 h1 
(* h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 2509 h1 (* h2 h2) (* h3 
h3) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 612 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) 
h6 j2) (* 64 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6) (* 149 h1 (* h2 h2) (* 
h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1573 h1 (* h2 
h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 7142 h1 (* 
h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 18354 h1 
(* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 29497 h1 
(* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 30801 h1 (* h2
 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 20916 h1 (* h2 h2) (* 
h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 8904 h1 (* h2 h2) (* h3 h3) (* h5
 h5 h5) (* h6 h6) (* j2 j2)) (* 2152 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 
h6) j2) (* 224 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6)) (* 180 h1 (* h2 h2
) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1779 h1 
(* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 7668 
h1 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 18948
 h1 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 29592 
h1 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 30271 h1 
(* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 20248 h1 (* h2 h2
) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 8514 h1 (* h2 h2) (* h3 h3) 
(* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 2032 h1 (* h2 h2) (* h3 h3) (* h5 h5) (* h6
 h6 h6) j2) (* 208 h1 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6)) (* 44 h1 (* h2
 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 442 h1 (* 
h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1918 h1 (* 
h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4716 h1 (* h2 
h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 7232 h1 (* h2 h2) (* 
h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 7154 h1 (* h2 h2) (* h3 h3) h5 
(* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 4542 h1 (* h2 h2) (* h3 h3) h5 (* h6 h6 h6 
h6) (* j2 j2 j2)) (* 1768 h1 (* h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2)) 
(* 376 h1 (* h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) j2) (* 32 h1 (* h2 h2) (* h3 h3
) h5 (* h6 h6 h6 h6)) (* 3 h1 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2
 j2 j2 j2)) (* 31 h1 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) 
(* 103 h1 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 155 h1 (* 
h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 114 h1 (* h2 h2) h3 (* h4 
h4 h4 h4) (* h5 h5) (* j2 j2)) (* 38 h1 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) 
j2) (* 4 h1 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5)) (* 15 h1 (* h2 h2) h3 (* h4 
h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 84 h1 (* h2 h2) h3 (* h4 h4 h4 h4) h5 
h6 (* j2 j2 j2 j2 j2)) (* 182 h1 (* h2 h2) h3 (* h4 h4 h4 h4) h5 h6 (* j2 j2 j2 
j2)) (* 188 h1 (* h2 h2) h3 (* h4 h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 91 h1 (* h2 
h2) h3 (* h4 h4 h4 h4) h5 h6 (* j2 j2)) (* 16 h1 (* h2 h2) h3 (* h4 h4 h4 h4) h5
 h6 j2) (* 6 h1 (* h2 h2) h3 (* h4 h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 30 h1 (* h2 h2) h3 (* h4 h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 54 h1 (* 
h2 h2) h3 (* h4 h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 42 h1 (* h2 h2) h3 (* h4
 h4 h4 h4) (* h6 h6) (* j2 j2 j2)) (* 12 h1 (* h2 h2) h3 (* h4 h4 h4 h4) (* h6 
h6) (* j2 j2)) (* 6 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 
j2 j2)) (* 72 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) 
(* 312 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 668 h1 
(* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 786 h1 (* h2 h2) h3 
(* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 516 h1 (* h2 h2) h3 (* h4 h4 h4) (* 
h5 h5 h5) (* j2 j2)) (* 176 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) j2) (* 24 
h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5)) (* 48 h1 (* h2 h2) h3 (* h4 h4 h4) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 383 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5
 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 1271 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6
 (* j2 j2 j2 j2 j2)) (* 2227 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 
j2 j2)) (* 2179 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 1154 
h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 286 h1 (* h2 h2) h3 (* 
h4 h4 h4) (* h5 h5) h6 j2) (* 20 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6) (* 
54 h1 (* h2 h2) h3 (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 389 h1
 (* h2 h2) h3 (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1108 h1 (* h2 
h2) h3 (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1589 h1 (* h2 h2) h3 (* 
h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 1192 h1 (* h2 h2) h3 (* h4 h4 h4) h5 
(* h6 h6) (* j2 j2 j2)) (* 428 h1 (* h2 h2) h3 (* h4 h4 h4) h5 (* h6 h6) (* j2 
j2)) (* 52 h1 (* h2 h2) h3 (* h4 h4 h4) h5 (* h6 h6) j2) (* 12 h1 (* h2 h2) h3 
(* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 80 h1 (* h2 h2) h3 (* h4 
h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 200 h1 (* h2 h2) h3 (* h4 h4 h4) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 232 h1 (* h2 h2) h3 (* h4 h4 h4) (* h6 h6 h6
) (* j2 j2 j2 j2)) (* 124 h1 (* h2 h2) h3 (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2)
) (* 24 h1 (* h2 h2) h3 (* h4 h4 h4) (* h6 h6 h6) (* j2 j2)) (* 3 h1 (* h2 h2) 
h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 40 h1 (* h2 h2) h3 
(* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 203 h1 (* h2 h2) h3 (* h4
 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 528 h1 (* h2 h2) h3 (* h4 h4) (* 
h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 789 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5
) (* j2 j2 j2 j2)) (* 704 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)
) (* 369 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 104 h1 (* h2 h2
) h3 (* h4 h4) (* h5 h5 h5 h5) j2) (* 12 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 
h5)) (* 39 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 394 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
1687 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 3960 h1
 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 5555 h1 (* h2 h2)
 h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 4760 h1 (* h2 h2) h3 (* h4 h4)
 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 2427 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6
 (* j2 j2)) (* 670 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 j2) (* 76 h1 (* h2 
h2) h3 (* h4 h4) (* h5 h5 h5) h6) (* 87 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 787 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3027 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6402 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2)) (* 8047 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6)
 (* j2 j2 j2 j2)) (* 6057 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2
 j2)) (* 2595 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 546 h1
 (* h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) j2) (* 36 h1 (* h2 h2) h3 (* h4 h4) 
(* h5 h5) (* h6 h6)) (* 51 h1 (* h2 h2) h3 (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 440 h1 (* h2 h2) h3 (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 1546 h1 (* h2 h2) h3 (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 2863 h1 (* h2 h2) h3 (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 3004 h1 (* h2 h2) h3 (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1765 h1 
(* h2 h2) h3 (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 523 h1 (* h2 h2) h3 (* 
h4 h4) h5 (* h6 h6 h6) (* j2 j2)) (* 56 h1 (* h2 h2) h3 (* h4 h4) h5 (* h6 h6 h6
) j2) (* 6 h1 (* h2 h2) h3 (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 48 h1 (* h2 h2) h3 (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
150 h1 (* h2 h2) h3 (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 234 h1 
(* h2 h2) h3 (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 192 h1 (* h2 h2) 
h3 (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 78 h1 (* h2 h2) h3 (* h4 h4) 
(* h6 h6 h6 h6) (* j2 j2 j2)) (* 12 h1 (* h2 h2) h3 (* h4 h4) (* h6 h6 h6 h6) 
(* j2 j2)) (* 6 h1 (* h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2
 j2)) (* 85 h1 (* h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 484 h1 (* h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1478 
h1 (* h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 2713 h1 (* h2 h2
) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 3141 h1 (* h2 h2) h3 h4 (* h5 
h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 2310 h1 (* h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* 
j2 j2 j2)) (* 1044 h1 (* h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 263 h1 
(* h2 h2) h3 h4 (* h5 h5 h5 h5) h6 j2) (* 28 h1 (* h2 h2) h3 h4 (* h5 h5 h5 h5) 
h6) (* 36 h1 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 412 h1 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 2026 h1 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 5594 h1 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 9552
 h1 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 10464 h1 (* h2
 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 7354 h1 (* h2 h2) h3 h4 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 3194 h1 (* h2 h2) h3 h4 (* h5 h5 h5) (* 
h6 h6) (* j2 j2)) (* 776 h1 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) j2) (* 80 h1 
(* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6)) (* 42 h1 (* h2 h2) h3 h4 (* h5 h5) (* h6
 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 452 h1 (* h2 h2) h3 h4 (* h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2081 h1 (* h2 h2) h3 h4 (* h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 5364 h1 (* h2 h2) h3 h4 (* h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 8498 h1 (* h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2)) (* 8532 h1 (* h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2)) (* 5377 h1 (* h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 2016 
h1 (* h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 394 h1 (* h2 h2) h3 h4 
(* h5 h5) (* h6 h6 h6) j2) (* 28 h1 (* h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6)) (* 
12 h1 (* h2 h2) h3 h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 124 
h1 (* h2 h2) h3 h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 531 h1 (* 
h2 h2) h3 h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1234 h1 (* h2 h2) 
h3 h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1706 h1 (* h2 h2) h3 h4 h5 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1436 h1 (* h2 h2) h3 h4 h5 (* h6 h6 h6 h6
) (* j2 j2 j2 j2)) (* 715 h1 (* h2 h2) h3 h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2)) 
(* 190 h1 (* h2 h2) h3 h4 h5 (* h6 h6 h6 h6) (* j2 j2)) (* 20 h1 (* h2 h2) h3 h4
 h5 (* h6 h6 h6 h6) j2) (* 19 h1 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2
 j2 j2 j2 j2 j2 j2 j2)) (* 184 h1 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 768 h1 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2
 j2 j2 j2 j2 j2)) (* 1824 h1 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 2726 h1 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2))
 (* 2664 h1 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 1704 h1 
(* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 688 h1 (* h2 h2) h3 (* 
h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 159 h1 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 
h6) j2) (* 16 h1 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6)) (* 43 h1 (* h2 h2) h3 
(* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 399 h1 (* h2 h2) h3
 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1609 h1 (* h2 h2) h3 
(* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3711 h1 (* h2 h2) h3 (* 
h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 5403 h1 (* h2 h2) h3 (* h5 h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 5153 h1 (* h2 h2) h3 (* h5 h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2)) (* 3219 h1 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 
j2 j2)) (* 1269 h1 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 286 h1 
(* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) j2) (* 28 h1 (* h2 h2) h3 (* h5 h5 h5) 
(* h6 h6 h6)) (* 22 h1 (* h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 201 h1 (* h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 792 h1 (* h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 1771 h1 (* h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2))
 (* 2478 h1 (* h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2247 
h1 (* h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 1316 h1 (* h2 h2) 
h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 477 h1 (* h2 h2) h3 (* h5 h5) (* 
h6 h6 h6 h6) (* j2 j2)) (* 96 h1 (* h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) j2) (* 8
 h1 (* h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6)) (* 3 h1 (* h2 h2) (* h4 h4 h4 h4) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 15 h1 (* h2 h2) (* h4 h4 h4 h4) (* h5 h5)
 h6 (* j2 j2 j2 j2 j2)) (* 28 h1 (* h2 h2) (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2
 j2 j2)) (* 24 h1 (* h2 h2) (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 9 h1 
(* h2 h2) (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* h1 (* h2 h2) (* h4 h4 h4 h4
) (* h5 h5) h6 j2) (* 3 h1 (* h2 h2) (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2
 j2 j2)) (* 12 h1 (* h2 h2) (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
17 h1 (* h2 h2) (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 10 h1 (* h2 h2)
 (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 2 h1 (* h2 h2) (* h4 h4 h4 h4) h5
 (* h6 h6) (* j2 j2)) (* 6 h1 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2
 j2 j2 j2 j2)) (* 40 h1 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2
 j2)) (* 107 h1 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
149 h1 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 116 h1 (* h2 
h2) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 50 h1 (* h2 h2) (* h4 h4 h4) 
(* h5 h5 h5) h6 (* j2 j2)) (* 11 h1 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5) h6 j2) 
(* h1 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5) h6) (* 12 h1 (* h2 h2) (* h4 h4 h4) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 77 h1 (* h2 h2) (* h4 h4 h4) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 194 h1 (* h2 h2) (* h4 h4 h4) (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 245 h1 (* h2 h2) (* h4 h4 h4) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2)) (* 161 h1 (* h2 h2) (* h4 h4 h4) (* h5 h5) (* h6 h6) 
(* j2 j2 j2)) (* 50 h1 (* h2 h2) (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 
5 h1 (* h2 h2) (* h4 h4 h4) (* h5 h5) (* h6 h6) j2) (* 6 h1 (* h2 h2) (* h4 h4 
h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 34 h1 (* h2 h2) (* h4 h4 h4) h5
 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 71 h1 (* h2 h2) (* h4 h4 h4) h5 (* h6 h6
 h6) (* j2 j2 j2 j2 j2)) (* 69 h1 (* h2 h2) (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 
j2 j2 j2)) (* 31 h1 (* h2 h2) (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 5 h1
 (* h2 h2) (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2)) (* 3 h1 (* h2 h2) (* h4 h4) 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 24 h1 (* h2 h2) (* h4 h4) (* 
h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 79 h1 (* h2 h2) (* h4 h4) (* h5 h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 141 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2)) (* 150 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2
 j2 j2)) (* 98 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 39 h1 
(* h2 h2) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 9 h1 (* h2 h2) (* h4 h4) 
(* h5 h5 h5 h5) h6 j2) (* h1 (* h2 h2) (* h4 h4) (* h5 h5 h5 h5) h6) (* 12 h1 
(* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 96 h1
 (* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 316 h1 
(* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 563 h1 (* 
h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 595 h1 (* h2 h2) 
(* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 382 h1 (* h2 h2) (* h4 h4) 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 146 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5) 
(* h6 h6) (* j2 j2)) (* 31 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6) j2) (* 
3 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6)) (* 12 h1 (* h2 h2) (* h4 h4) 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 93 h1 (* h2 h2) (* h4 h4)
 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 292 h1 (* h2 h2) (* h4 h4) 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 485 h1 (* h2 h2) (* h4 h4) (* 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 460 h1 (* h2 h2) (* h4 h4) (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2)) (* 247 h1 (* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2)) (* 68 h1 (* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2))
 (* 7 h1 (* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6 h6) j2) (* 3 h1 (* h2 h2) (* h4 
h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 21 h1 (* h2 h2) (* h4 h4)
 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 57 h1 (* h2 h2) (* h4 h4) h5 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 78 h1 (* h2 h2) (* h4 h4) h5 (* h6 h6 
h6 h6) (* j2 j2 j2 j2 j2)) (* 57 h1 (* h2 h2) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2
 j2 j2 j2)) (* 21 h1 (* h2 h2) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 3 
h1 (* h2 h2) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2)) (* 3 h1 (* h2 h2) h4 (* h5 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 28 h1 (* h2 h2) h4 (* h5 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 111 h1 (* h2 h2) h4 (* h5 h5
 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 248 h1 (* h2 h2) h4 (* h5 h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 347 h1 (* h2 h2) h4 (* h5 h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2)) (* 318 h1 (* h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2)) (* 193 h1 (* h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 
76 h1 (* h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 18 h1 (* h2 h2) h4 
(* h5 h5 h5 h5) (* h6 h6) j2) (* 2 h1 (* h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6)) 
(* 6 h1 (* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 56 h1 (* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
221 h1 (* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 489 
h1 (* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 673 h1 (* h2
 h2) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 601 h1 (* h2 h2) h4 (* 
h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 351 h1 (* h2 h2) h4 (* h5 h5 h5) (* 
h6 h6 h6) (* j2 j2 j2)) (* 131 h1 (* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 
j2)) (* 29 h1 (* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6) j2) (* 3 h1 (* h2 h2) h4 
(* h5 h5 h5) (* h6 h6 h6)) (* 3 h1 (* h2 h2) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 28 h1 (* h2 h2) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 108 h1 (* h2 h2) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2
 j2 j2 j2 j2 j2)) (* 228 h1 (* h2 h2) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 290 h1 (* h2 h2) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 228 h1 (* h2 h2) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 108 h1 (* 
h2 h2) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 28 h1 (* h2 h2) h4 (* h5 h5
) (* h6 h6 h6 h6) (* j2 j2)) (* 3 h1 (* h2 h2) h4 (* h5 h5) (* h6 h6 h6 h6) j2) 
(* h1 (* h2 h2) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
9 h1 (* h2 h2) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 36 
h1 (* h2 h2) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 84 h1 (* 
h2 h2) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 126 h1 (* h2 h2) 
(* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 126 h1 (* h2 h2) (* h5 h5 h5
 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 84 h1 (* h2 h2) (* h5 h5 h5 h5) (* h6 h6 
h6) (* j2 j2 j2)) (* 36 h1 (* h2 h2) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 
9 h1 (* h2 h2) (* h5 h5 h5 h5) (* h6 h6 h6) j2) (* h1 (* h2 h2) (* h5 h5 h5 h5) 
(* h6 h6 h6)) (* h1 (* h2 h2) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 9 h1 (* h2 h2) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 36 h1 (* h2 h2) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 84 h1 (* h2 h2) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 126 
h1 (* h2 h2) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 126 h1 (* h2 h2
) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 84 h1 (* h2 h2) (* h5 h5 h5) 
(* h6 h6 h6 h6) (* j2 j2 j2)) (* 36 h1 (* h2 h2) (* h5 h5 h5) (* h6 h6 h6 h6) 
(* j2 j2)) (* 9 h1 (* h2 h2) (* h5 h5 h5) (* h6 h6 h6 h6) j2) (* h1 (* h2 h2) 
(* h5 h5 h5) (* h6 h6 h6 h6)) (* 16 h1 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 
j2 j2 j2 j2 j2 j2)) (* 224 h1 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 
j2 j2)) (* 1216 h1 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 
3376 h1 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 5184 h1 h2 (* h3 
h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 4352 h1 h2 (* h3 h3 h3 h3) (* h4 h4 
h4) h5 (* j2 j2)) (* 1792 h1 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h5 j2) (* 256 h1 h2
 (* h3 h3 h3 h3) (* h4 h4 h4) h5) (* 32 h1 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 320 h1 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 
j2 j2 j2 j2)) (* 1312 h1 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2)) 
(* 2816 h1 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2)) (* 3328 h1 h2 (* 
h3 h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2)) (* 2048 h1 h2 (* h3 h3 h3 h3) (* h4 
h4 h4) h6 (* j2 j2)) (* 512 h1 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h6 j2) (* 16 h1 
h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 300 h1 h2
 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 2264 h1 h2 (* 
h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 8948 h1 h2 (* h3 h3 
h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 20280 h1 h2 (* h3 h3 h3 h3) 
(* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 26976 h1 h2 (* h3 h3 h3 h3) (* h4 h4) 
(* h5 h5) (* j2 j2 j2)) (* 20512 h1 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2
 j2)) (* 8128 h1 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) j2) (* 1280 h1 h2 (* h3 
h3 h3 h3) (* h4 h4) (* h5 h5)) (* 64 h1 h2 (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 984 h1 h2 (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2
 j2 j2 j2 j2)) (* 6144 h1 h2 (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 
j2)) (* 20448 h1 h2 (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 39528
 h1 h2 (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 44880 h1 h2 (* h3 h3 
h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 28448 h1 h2 (* h3 h3 h3 h3) (* h4 h4) h5
 h6 (* j2 j2)) (* 8640 h1 h2 (* h3 h3 h3 h3) (* h4 h4) h5 h6 j2) (* 768 h1 h2 
(* h3 h3 h3 h3) (* h4 h4) h5 h6) (* 64 h1 h2 (* h3 h3 h3 h3) (* h4 h4) (* h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 752 h1 h2 (* h3 h3 h3 h3) (* h4 h4) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 3696 h1 h2 (* h3 h3 h3 h3) (* h4 h4) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 9792 h1 h2 (* h3 h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 
j2 j2 j2)) (* 14976 h1 h2 (* h3 h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2)) 
(* 13056 h1 h2 (* h3 h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 5888 h1 h2 
(* h3 h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2)) (* 1024 h1 h2 (* h3 h3 h3 h3) (* 
h4 h4) (* h6 h6) j2) (* 4 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 92 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 864 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)
) (* 4308 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 12460 
h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 21536 h1 h2 (* h3 
h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 22176 h1 h2 (* h3 h3 h3 h3) h4 (* 
h5 h5 h5) (* j2 j2 j2)) (* 13152 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2)
) (* 4096 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) j2) (* 512 h1 h2 (* h3 h3 h3 h3)
 h4 (* h5 h5 h5)) (* 24 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 516 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 4476 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 20560 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 55468 
h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 91580 h1 h2 (* h3 
h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 92736 h1 h2 (* h3 h3 h3 h3) h4 (* 
h5 h5) h6 (* j2 j2 j2)) (* 55536 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2)
) (* 17792 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5) h6 j2) (* 2304 h1 h2 (* h3 h3 h3 
h3) h4 (* h5 h5) h6) (* 48 h1 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 872 h1 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 6384 h1 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2
)) (* 25136 h1 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
58952 h1 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 85200 h1 h2 
(* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 75136 h1 h2 (* h3 h3 h3 h3) 
h4 h5 (* h6 h6) (* j2 j2 j2)) (* 38144 h1 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* 
j2 j2)) (* 9600 h1 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6) j2) (* 768 h1 h2 (* h3 h3 
h3 h3) h4 h5 (* h6 h6)) (* 32 h1 h2 (* h3 h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 416 h1 h2 (* h3 h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 2304 h1 h2 (* h3 h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2
 j2)) (* 7072 h1 h2 (* h3 h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
13088 h1 h2 (* h3 h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 14848 h1 h2 
(* h3 h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 9984 h1 h2 (* h3 h3 h3 h3) 
h4 (* h6 h6 h6) (* j2 j2 j2)) (* 3584 h1 h2 (* h3 h3 h3 h3) h4 (* h6 h6 h6) (* 
j2 j2)) (* 512 h1 h2 (* h3 h3 h3 h3) h4 (* h6 h6 h6) j2) (* 22 h1 h2 (* h3 h3 h3
 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 410 h1 h2 (* h3 h3 h3 h3
) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3092 h1 h2 (* h3 h3 h3 h3) (* 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 12302 h1 h2 (* h3 h3 h3 h3) (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 28430 h1 h2 (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2)) (* 39728 h1 h2 (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2))
 (* 33808 h1 h2 (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 17008 h1 h2 (* 
h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2)) (* 4608 h1 h2 (* h3 h3 h3 h3) (* h5 h5 
h5) h6 j2) (* 512 h1 h2 (* h3 h3 h3 h3) (* h5 h5 h5) h6) (* 88 h1 h2 (* h3 h3 h3
 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1356 h1 h2 (* h3 h3 
h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 8612 h1 h2 (* h3 h3 
h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 29848 h1 h2 (* h3 h3 h3 
h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 62476 h1 h2 (* h3 h3 h3 h3) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 82052 h1 h2 (* h3 h3 h3 h3) (* h5 h5)
 (* h6 h6) (* j2 j2 j2 j2)) (* 67632 h1 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) 
(* j2 j2 j2)) (* 33680 h1 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 
9152 h1 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) j2) (* 1024 h1 h2 (* h3 h3 h3 h3)
 (* h5 h5) (* h6 h6)) (* 88 h1 h2 (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 1120 h1 h2 (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 6088 h1 h2 (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2
 j2)) (* 18488 h1 h2 (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
34416 h1 h2 (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 40488 h1 h2 
(* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 29840 h1 h2 (* h3 h3 h3 h3) 
h5 (* h6 h6 h6) (* j2 j2 j2)) (* 13088 h1 h2 (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* 
j2 j2)) (* 3008 h1 h2 (* h3 h3 h3 h3) h5 (* h6 h6 h6) j2) (* 256 h1 h2 (* h3 h3 
h3 h3) h5 (* h6 h6 h6)) (* 8 h1 h2 (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 
j2 j2 j2)) (* 96 h1 h2 (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 
416 h1 h2 (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 856 h1 h2 (* h3 h3
 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2)) (* 880 h1 h2 (* h3 h3 h3) (* h4 h4 h4 h4) 
h5 (* j2 j2)) (* 416 h1 h2 (* h3 h3 h3) (* h4 h4 h4 h4) h5 j2) (* 64 h1 h2 (* h3
 h3 h3) (* h4 h4 h4 h4) h5) (* 16 h1 h2 (* h3 h3 h3) (* h4 h4 h4 h4) h6 (* j2 j2
 j2 j2 j2 j2)) (* 128 h1 h2 (* h3 h3 h3) (* h4 h4 h4 h4) h6 (* j2 j2 j2 j2 j2)) 
(* 400 h1 h2 (* h3 h3 h3) (* h4 h4 h4 h4) h6 (* j2 j2 j2 j2)) (* 608 h1 h2 (* h3
 h3 h3) (* h4 h4 h4 h4) h6 (* j2 j2 j2)) (* 448 h1 h2 (* h3 h3 h3) (* h4 h4 h4 
h4) h6 (* j2 j2)) (* 128 h1 h2 (* h3 h3 h3) (* h4 h4 h4 h4) h6 j2) (* 28 h1 h2 
(* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 384 h1 h2 (* h3
 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2052 h1 h2 (* h3 h3 h3)
 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 5664 h1 h2 (* h3 h3 h3) (* h4 h4 
h4) (* h5 h5) (* j2 j2 j2 j2)) (* 8712 h1 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5)
 (* j2 j2 j2)) (* 7384 h1 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 
3152 h1 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) j2) (* 512 h1 h2 (* h3 h3 h3) (* 
h4 h4 h4) (* h5 h5)) (* 104 h1 h2 (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2
 j2 j2 j2)) (* 1076 h1 h2 (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2))
 (* 4656 h1 h2 (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 10720 h1 
h2 (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 13820 h1 h2 (* h3 h3 h3) 
(* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 9584 h1 h2 (* h3 h3 h3) (* h4 h4 h4) h5 h6 
(* j2 j2)) (* 3056 h1 h2 (* h3 h3 h3) (* h4 h4 h4) h5 h6 j2) (* 256 h1 h2 (* h3 
h3 h3) (* h4 h4 h4) h5 h6) (* 64 h1 h2 (* h3 h3 h3) (* h4 h4 h4) (* h6 h6) (* j2
 j2 j2 j2 j2 j2 j2)) (* 592 h1 h2 (* h3 h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 2208 h1 h2 (* h3 h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 4208 h1 h2 (* h3 h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 4256 
h1 h2 (* h3 h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2)) (* 2112 h1 h2 (* h3 h3 
h3) (* h4 h4 h4) (* h6 h6) (* j2 j2)) (* 384 h1 h2 (* h3 h3 h3) (* h4 h4 h4) (* 
h6 h6) j2) (* 16 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 284 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2
)) (* 1996 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 
7206 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 14658 h1 
h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 17300 h1 h2 (* h3 h3 
h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 11640 h1 h2 (* h3 h3 h3) (* h4 h4) 
(* h5 h5 h5) (* j2 j2)) (* 4096 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) j2) 
(* 576 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5)) (* 112 h1 h2 (* h3 h3 h3) (* 
h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1614 h1 h2 (* h3 h3 h3) (* 
h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 9366 h1 h2 (* h3 h3 h3) (* h4 
h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 28996 h1 h2 (* h3 h3 h3) (* h4 h4) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 52718 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5)
 h6 (* j2 j2 j2 j2)) (* 57614 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2
 j2)) (* 36636 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 12144 h1 
h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 j2) (* 1536 h1 h2 (* h3 h3 h3) (* h4 h4) 
(* h5 h5) h6) (* 192 h1 h2 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 2192 h1 h2 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 10648 h1 h2 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)
) (* 28460 h1 h2 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
45144 h1 h2 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 42612 h1 h2 
(* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 22544 h1 h2 (* h3 h3 h3) 
(* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 5648 h1 h2 (* h3 h3 h3) (* h4 h4) h5 (* h6 
h6) j2) (* 384 h1 h2 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6)) (* 64 h1 h2 (* h3 h3 
h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 672 h1 h2 (* h3 h3 h3
) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2928 h1 h2 (* h3 h3 h3) 
(* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6816 h1 h2 (* h3 h3 h3) (* h4 
h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 9072 h1 h2 (* h3 h3 h3) (* h4 h4) (* h6 
h6 h6) (* j2 j2 j2 j2)) (* 6816 h1 h2 (* h3 h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 
j2 j2)) (* 2624 h1 h2 (* h3 h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2)) (* 384 h1 
h2 (* h3 h3 h3) (* h4 h4) (* h6 h6 h6) j2) (* 2 h1 h2 (* h3 h3 h3) h4 (* h5 h5 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 44 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5 
h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 390 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 1806 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2
 j2 j2 j2 j2)) (* 4772 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2))
 (* 7454 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 6948 h1 h2 
(* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2)) (* 3768 h1 h2 (* h3 h3 h3) h4 (* 
h5 h5 h5 h5) (* j2 j2)) (* 1088 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) j2) (* 128
 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5)) (* 26 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5)
 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 524 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5) h6
 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4197 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2)) (* 17558 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2)) (* 42734 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2))
 (* 63573 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 58318 h1 h2 
(* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 31940 h1 h2 (* h3 h3 h3) h4 (* 
h5 h5 h5) h6 (* j2 j2)) (* 9472 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5) h6 j2) (* 
1152 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5) h6) (* 84 h1 h2 (* h3 h3 h3) h4 (* h5 h5
) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1456 h1 h2 (* h3 h3 h3) h4 (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 9948 h1 h2 (* h3 h3 h3) h4 (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 36236 h1 h2 (* h3 h3 h3) h4 (* h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 79092 h1 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6
 h6) (* j2 j2 j2 j2 j2)) (* 108428 h1 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* 
j2 j2 j2 j2)) (* 93540 h1 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) 
(* 48688 h1 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 13680 h1 h2 (* 
h3 h3 h3) h4 (* h5 h5) (* h6 h6) j2) (* 1536 h1 h2 (* h3 h3 h3) h4 (* h5 h5) (* 
h6 h6)) (* 88 h1 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 1176 h1 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 6724 h1 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 21492
 h1 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 42040 h1 h2 (* 
h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 51676 h1 h2 (* h3 h3 h3) h4 
h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 39300 h1 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6) 
(* j2 j2 j2)) (* 17344 h1 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2)) (* 3792 
h1 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6) j2) (* 256 h1 h2 (* h3 h3 h3) h4 h5 (* h6 
h6 h6)) (* 16 h1 h2 (* h3 h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 192 h1 h2 (* h3 h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 976 h1 h2 (* h3 h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2736 
h1 h2 (* h3 h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4608 h1 h2 (* h3
 h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 4752 h1 h2 (* h3 h3 h3) h4 (* 
h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 2912 h1 h2 (* h3 h3 h3) h4 (* h6 h6 h6 h6) (* 
j2 j2 j2)) (* 960 h1 h2 (* h3 h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2)) (* 128 h1 h2 
(* h3 h3 h3) h4 (* h6 h6 h6 h6) j2) (* 11 h1 h2 (* h3 h3 h3) (* h5 h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 194 h1 h2 (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 1363 h1 h2 (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2
 j2 j2 j2 j2 j2)) (* 4971 h1 h2 (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2)) (* 10424 h1 h2 (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
13231 h1 h2 (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 10306 h1 h2 (* 
h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 4796 h1 h2 (* h3 h3 h3) (* h5 h5 
h5 h5) h6 (* j2 j2)) (* 1216 h1 h2 (* h3 h3 h3) (* h5 h5 h5 h5) h6 j2) (* 128 h1
 h2 (* h3 h3 h3) (* h5 h5 h5 h5) h6) (* 99 h1 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1396 h1 h2 (* h3 h3 h3) (* h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 8001 h1 h2 (* h3 h3 h3) (* h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 24881 h1 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 46970 h1 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* 56287 h1 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2)) (* 42962 h1 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 
20140 h1 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 5248 h1 h2 (* h3 
h3 h3) (* h5 h5 h5) (* h6 h6) j2) (* 576 h1 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 
h6)) (* 176 h1 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
 j2)) (* 2038 h1 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 10112 h1 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 28394 h1 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
49862 h1 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 56748 h1 
h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 41714 h1 h2 (* h3 h3 
h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 18988 h1 h2 (* h3 h3 h3) (* h5 h5) 
(* h6 h6 h6) (* j2 j2)) (* 4816 h1 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) j2) 
(* 512 h1 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6)) (* 44 h1 h2 (* h3 h3 h3) h5 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 516 h1 h2 (* h3 h3 h3) h5 (* 
h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2572 h1 h2 (* h3 h3 h3) h5 (* h6 h6
 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 7144 h1 h2 (* h3 h3 h3) h5 (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 12164 h1 h2 (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 
j2 j2 j2)) (* 13124 h1 h2 (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 
8916 h1 h2 (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 3632 h1 h2 (* h3 h3 
h3) h5 (* h6 h6 h6 h6) (* j2 j2)) (* 784 h1 h2 (* h3 h3 h3) h5 (* h6 h6 h6 h6) 
j2) (* 64 h1 h2 (* h3 h3 h3) h5 (* h6 h6 h6 h6)) (* 8 h1 h2 (* h3 h3) (* h4 h4 
h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 88 h1 h2 (* h3 h3) (* h4 h4 h4 h4) 
(* h5 h5) (* j2 j2 j2 j2 j2)) (* 338 h1 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) 
(* j2 j2 j2 j2)) (* 606 h1 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2)) 
(* 544 h1 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2)) (* 228 h1 h2 (* h3 
h3) (* h4 h4 h4 h4) (* h5 h5) j2) (* 32 h1 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5
)) (* 32 h1 h2 (* h3 h3) (* h4 h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 228 h1 
h2 (* h3 h3) (* h4 h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 620 h1 h2 (* h3 h3) 
(* h4 h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 800 h1 h2 (* h3 h3) (* h4 h4 h4 h4) h5
 h6 (* j2 j2 j2)) (* 488 h1 h2 (* h3 h3) (* h4 h4 h4 h4) h5 h6 (* j2 j2)) (* 112
 h1 h2 (* h3 h3) (* h4 h4 h4 h4) h5 h6 j2) (* 16 h1 h2 (* h3 h3) (* h4 h4 h4 h4)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 96 h1 h2 (* h3 h3) (* h4 h4 h4 h4) (* h6 h6
) (* j2 j2 j2 j2 j2)) (* 208 h1 h2 (* h3 h3) (* h4 h4 h4 h4) (* h6 h6) (* j2 j2 
j2 j2)) (* 192 h1 h2 (* h3 h3) (* h4 h4 h4 h4) (* h6 h6) (* j2 j2 j2)) (* 64 h1 
h2 (* h3 h3) (* h4 h4 h4 h4) (* h6 h6) (* j2 j2)) (* 14 h1 h2 (* h3 h3) (* h4 h4
 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 178 h1 h2 (* h3 h3) (* h4 h4 h4) 
(* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 860 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5
 h5) (* j2 j2 j2 j2 j2)) (* 2112 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2
 j2 j2 j2)) (* 2846 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 
2102 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2)) (* 784 h1 h2 (* h3 h3)
 (* h4 h4 h4) (* h5 h5 h5) j2) (* 112 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5))
 (* 90 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
865 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 3438 h1 
h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 7124 h1 h2 (* h3 
h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 8191 h1 h2 (* h3 h3) (* h4 h4 
h4) (* h5 h5) h6 (* j2 j2 j2)) (* 5122 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) h6
 (* j2 j2)) (* 1536 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 j2) (* 144 h1 h2 
(* h3 h3) (* h4 h4 h4) (* h5 h5) h6) (* 116 h1 h2 (* h3 h3) (* h4 h4 h4) h5 (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 966 h1 h2 (* h3 h3) (* h4 h4 h4) h5 (* h6 h6
) (* j2 j2 j2 j2 j2 j2)) (* 3232 h1 h2 (* h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2
 j2 j2 j2 j2)) (* 5496 h1 h2 (* h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)
) (* 4934 h1 h2 (* h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 2172 h1 h2 
(* h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2)) (* 352 h1 h2 (* h3 h3) (* h4 h4 
h4) h5 (* h6 h6) j2) (* 32 h1 h2 (* h3 h3) (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2
 j2 j2 j2 j2)) (* 240 h1 h2 (* h3 h3) (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 688 h1 h2 (* h3 h3) (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
928 h1 h2 (* h3 h3) (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 576 h1 h2 (* 
h3 h3) (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2)) (* 128 h1 h2 (* h3 h3) (* h4 h4 
h4) (* h6 h6 h6) (* j2 j2)) (* 4 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 67 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2
 j2 j2 j2 j2 j2)) (* 434 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 
j2 j2 j2)) (* 1402 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2))
 (* 2484 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 2511 h1 
h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 1430 h1 h2 (* h3 h3) (* 
h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 420 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 
h5) j2) (* 48 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5)) (* 56 h1 h2 (* h3 h3) 
(* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 751 h1 h2 (* h3 h3) 
(* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 3978 h1 h2 (* h3 h3) (* 
h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 11085 h1 h2 (* h3 h3) (* h4 h4)
 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 17988 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5
 h5) h6 (* j2 j2 j2 j2)) (* 17485 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* 
j2 j2 j2)) (* 9923 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 2976 
h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 j2) (* 352 h1 h2 (* h3 h3) (* h4 h4) 
(* h5 h5 h5) h6) (* 164 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 1728 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 7722 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 18855 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2
 j2 j2 j2)) (* 27206 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2)) (* 23479 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 
11602 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 2872 h1 h2 (* 
h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) j2) (* 240 h1 h2 (* h3 h3) (* h4 h4) (* h5 
h5) (* h6 h6)) (* 112 h1 h2 (* h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 1068 h1 h2 (* h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 4264 h1 h2 (* h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 9104 h1 h2 (* h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
11080 h1 h2 (* h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 7604 h1 h2 
(* h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 2688 h1 h2 (* h3 h3) (* h4 
h4) h5 (* h6 h6 h6) (* j2 j2)) (* 368 h1 h2 (* h3 h3) (* h4 h4) h5 (* h6 h6 h6) 
j2) (* 16 h1 h2 (* h3 h3) (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2))
 (* 140 h1 h2 (* h3 h3) (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
488 h1 h2 (* h3 h3) (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 860 h1 
h2 (* h3 h3) (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 800 h1 h2 (* h3 h3
) (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 368 h1 h2 (* h3 h3) (* h4 h4) 
(* h6 h6 h6 h6) (* j2 j2 j2)) (* 64 h1 h2 (* h3 h3) (* h4 h4) (* h6 h6 h6 h6) 
(* j2 j2)) (* 6 h1 h2 (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2
 j2)) (* 117 h1 h2 (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 891 h1 h2 (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 3462 
h1 h2 (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 7665 h1 h2 (* h3
 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 10220 h1 h2 (* h3 h3) h4 (* h5
 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 8326 h1 h2 (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* 
j2 j2 j2)) (* 4029 h1 h2 (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 1052 h1 
h2 (* h3 h3) h4 (* h5 h5 h5 h5) h6 j2) (* 112 h1 h2 (* h3 h3) h4 (* h5 h5 h5 h5)
 h6) (* 42 h1 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 686 h1 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 4330 h1 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 14401 h1 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
28549 h1 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 35469 h1 
h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 27771 h1 h2 (* h3 h3)
 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 13208 h1 h2 (* h3 h3) h4 (* h5 h5 h5
) (* h6 h6) (* j2 j2)) (* 3440 h1 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) j2) (* 
368 h1 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6)) (* 72 h1 h2 (* h3 h3) h4 (* h5 h5
) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 923 h1 h2 (* h3 h3) h4 (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4969 h1 h2 (* h3 h3) h4 (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 14782 h1 h2 (* h3 h3) h4 (* h5 h5)
 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 26753 h1 h2 (* h3 h3) h4 (* h5 h5) (* h6
 h6 h6) (* j2 j2 j2 j2 j2)) (* 30483 h1 h2 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2)) (* 21752 h1 h2 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)
) (* 9262 h1 h2 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 2080 h1 h2 (* 
h3 h3) h4 (* h5 h5) (* h6 h6 h6) j2) (* 176 h1 h2 (* h3 h3) h4 (* h5 h5) (* h6 
h6 h6)) (* 24 h1 h2 (* h3 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 286 h1 h2 (* h3 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 1420 h1 h2 (* h3 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3818 
h1 h2 (* h3 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6070 h1 h2 (* h3
 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 5844 h1 h2 (* h3 h3) h4 h5 (* 
h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 3326 h1 h2 (* h3 h3) h4 h5 (* h6 h6 h6 h6) (* 
j2 j2 j2)) (* 1020 h1 h2 (* h3 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2)) (* 128 h1 h2
 (* h3 h3) h4 h5 (* h6 h6 h6 h6) j2) (* 22 h1 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 295 h1 h2 (* h3 h3) (* h5 h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1591 h1 h2 (* h3 h3) (* h5 h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4609 h1 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 8032 h1 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2)) (* 8829 h1 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2)) (* 6163 h1 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 2643 h1 
h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 632 h1 h2 (* h3 h3) (* h5 
h5 h5 h5) (* h6 h6) j2) (* 64 h1 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6)) (* 88 
h1 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 931
 h1 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4231 
h1 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 10905 h1 
h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 17602 h1 h2 (* 
h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 18449 h1 h2 (* h3 h3) 
(* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 12535 h1 h2 (* h3 h3) (* h5 h5 h5)
 (* h6 h6 h6) (* j2 j2 j2)) (* 5307 h1 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) 
(* j2 j2)) (* 1264 h1 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) j2) (* 128 h1 h2 
(* h3 h3) (* h5 h5 h5) (* h6 h6 h6)) (* 44 h1 h2 (* h3 h3) (* h5 h5) (* h6 h6 h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 466 h1 h2 (* h3 h3) (* h5 h5) (* h6 h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2110 h1 h2 (* h3 h3) (* h5 h5) (* h6 h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 5378 h1 h2 (* h3 h3) (* h5 h5) (* h6 h6 h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 8516 h1 h2 (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* 
j2 j2 j2 j2 j2)) (* 8686 h1 h2 (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 
j2)) (* 5694 h1 h2 (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 2302 h1 
h2 (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 516 h1 h2 (* h3 h3) (* h5 
h5) (* h6 h6 h6 h6) j2) (* 48 h1 h2 (* h3 h3) (* h5 h5) (* h6 h6 h6 h6)) (* 2 h1
 h2 h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 20 h1 h2 h3 (* h4 
h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 65 h1 h2 h3 (* h4 h4 h4 h4) (* h5 
h5 h5) (* j2 j2 j2 j2)) (* 93 h1 h2 h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2)
) (* 61 h1 h2 h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2)) (* 15 h1 h2 h3 (* h4 h4
 h4 h4) (* h5 h5 h5) j2) (* 16 h1 h2 h3 (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2
 j2 j2 j2)) (* 98 h1 h2 h3 (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
224 h1 h2 h3 (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 234 h1 h2 h3 (* h4
 h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 108 h1 h2 h3 (* h4 h4 h4 h4) (* h5 h5) 
h6 (* j2 j2)) (* 16 h1 h2 h3 (* h4 h4 h4 h4) (* h5 h5) h6 j2) (* 18 h1 h2 h3 (* 
h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 86 h1 h2 h3 (* h4 h4 h4 h4) 
h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 148 h1 h2 h3 (* h4 h4 h4 h4) h5 (* h6 h6) 
(* j2 j2 j2 j2)) (* 108 h1 h2 h3 (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 
28 h1 h2 h3 (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2)) (* 4 h1 h2 h3 (* h4 h4 h4 h4
) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 16 h1 h2 h3 (* h4 h4 h4 h4) (* h6 h6 h6
) (* j2 j2 j2 j2 j2)) (* 20 h1 h2 h3 (* h4 h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2
)) (* 8 h1 h2 h3 (* h4 h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2)) (* 2 h1 h2 h3 (* h4 
h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 22 h1 h2 h3 (* h4 h4 h4) (* 
h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 85 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5 h5) 
(* j2 j2 j2 j2 j2)) (* 158 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)
) (* 154 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 76 h1 h2 h3 (* 
h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 15 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5 h5)
 j2) (* 26 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
217 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 748 h1 h2 h3
 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 1334 h1 h2 h3 (* h4 h4 h4) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 1298 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5) h6 
(* j2 j2 j2)) (* 665 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 152 h1 
h2 h3 (* h4 h4 h4) (* h5 h5 h5) h6 j2) (* 8 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5) 
h6) (* 58 h1 h2 h3 (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 425 h1 h2 h3 (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1244 
h1 h2 h3 (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1840 h1 h2 h3 
(* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 1422 h1 h2 h3 (* h4 h4 h4) 
(* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 523 h1 h2 h3 (* h4 h4 h4) (* h5 h5) (* h6 
h6) (* j2 j2)) (* 64 h1 h2 h3 (* h4 h4 h4) (* h5 h5) (* h6 h6) j2) (* 34 h1 h2 
h3 (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 217 h1 h2 h3 (* h4 
h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 524 h1 h2 h3 (* h4 h4 h4) h5 
(* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 600 h1 h2 h3 (* h4 h4 h4) h5 (* h6 h6 h6) 
(* j2 j2 j2 j2)) (* 323 h1 h2 h3 (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 
64 h1 h2 h3 (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2)) (* 4 h1 h2 h3 (* h4 h4 h4) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 20 h1 h2 h3 (* h4 h4 h4) (* h6 h6 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 36 h1 h2 h3 (* h4 h4 h4) (* h6 h6 h6 h6) (* j2 
j2 j2 j2 j2)) (* 28 h1 h2 h3 (* h4 h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 8 
h1 h2 h3 (* h4 h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 8 h1 h2 h3 (* h4 h4) (* 
h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 99 h1 h2 h3 (* h4 h4) (* h5 h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 467 h1 h2 h3 (* h4 h4) (* h5 h5 h5 h5) h6
 (* j2 j2 j2 j2 j2 j2)) (* 1117 h1 h2 h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 
j2 j2 j2)) (* 1508 h1 h2 h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 
1183 h1 h2 h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 521 h1 h2 h3 (* h4 
h4) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 113 h1 h2 h3 (* h4 h4) (* h5 h5 h5 h5) h6 
j2) (* 8 h1 h2 h3 (* h4 h4) (* h5 h5 h5 h5) h6) (* 48 h1 h2 h3 (* h4 h4) (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 452 h1 h2 h3 (* h4 h4) (* h5 h5
 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1794 h1 h2 h3 (* h4 h4) (* h5 h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3881 h1 h2 h3 (* h4 h4) (* h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2)) (* 4949 h1 h2 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2)) (* 3753 h1 h2 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 
1613 h1 h2 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 342 h1 h2 h3 (* h4 
h4) (* h5 h5 h5) (* h6 h6) j2) (* 24 h1 h2 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6)) 
(* 56 h1 h2 h3 (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
478 h1 h2 h3 (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1706 
h1 h2 h3 (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3254 h1 h2 
h3 (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 3544 h1 h2 h3 (* h4 
h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 2176 h1 h2 h3 (* h4 h4) (* h5 h5)
 (* h6 h6 h6) (* j2 j2 j2)) (* 682 h1 h2 h3 (* h4 h4) (* h5 h5) (* h6 h6 h6) (* 
j2 j2)) (* 80 h1 h2 h3 (* h4 h4) (* h5 h5) (* h6 h6 h6) j2) (* 16 h1 h2 h3 (* h4
 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 125 h1 h2 h3 (* h4 h4) 
h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 384 h1 h2 h3 (* h4 h4) h5 (* h6 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 600 h1 h2 h3 (* h4 h4) h5 (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2)) (* 504 h1 h2 h3 (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)
) (* 215 h1 h2 h3 (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 36 h1 h2 h3 (* 
h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2)) (* 6 h1 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 91 h1 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 525 h1 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 1570 h1 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2
 j2)) (* 2757 h1 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2995 
h1 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 2027 h1 h2 h3 h4 (* h5
 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 824 h1 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6) 
(* j2 j2)) (* 181 h1 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6) j2) (* 16 h1 h2 h3 h4 
(* h5 h5 h5 h5) (* h6 h6)) (* 22 h1 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 250 h1 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 1203 h1 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2
 j2 j2)) (* 3212 h1 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 5240 h1 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 5406 h1 h2 
h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 3511 h1 h2 h3 h4 (* h5 h5 h5
) (* h6 h6 h6) (* j2 j2 j2)) (* 1372 h1 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2
 j2)) (* 288 h1 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6) j2) (* 24 h1 h2 h3 h4 (* h5 
h5 h5) (* h6 h6 h6)) (* 12 h1 h2 h3 h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 131 h1 h2 h3 h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 591 h1 h2 h3 h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 1441 h1 h2 h3 h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2086 
h1 h2 h3 h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1841 h1 h2 h3 h4 
(* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 967 h1 h2 h3 h4 (* h5 h5) (* h6 h6
 h6 h6) (* j2 j2 j2)) (* 275 h1 h2 h3 h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) 
(* 32 h1 h2 h3 h4 (* h5 h5) (* h6 h6 h6 h6) j2) (* 11 h1 h2 h3 (* h5 h5 h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 107 h1 h2 h3 (* h5 h5 h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 446 h1 h2 h3 (* h5 h5 h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1053 h1 h2 h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 1558 h1 h2 h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2
 j2)) (* 1501 h1 h2 h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 942 h1 
h2 h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 371 h1 h2 h3 (* h5 h5 h5 h5)
 (* h6 h6 h6) (* j2 j2)) (* 83 h1 h2 h3 (* h5 h5 h5 h5) (* h6 h6 h6) j2) (* 8 h1
 h2 h3 (* h5 h5 h5 h5) (* h6 h6 h6)) (* 11 h1 h2 h3 (* h5 h5 h5) (* h6 h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 107 h1 h2 h3 (* h5 h5 h5) (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 446 h1 h2 h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 1053 h1 h2 h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2
 j2 j2)) (* 1558 h1 h2 h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
1501 h1 h2 h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 942 h1 h2 h3 (* 
h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 371 h1 h2 h3 (* h5 h5 h5) (* h6 h6 h6
 h6) (* j2 j2)) (* 83 h1 h2 h3 (* h5 h5 h5) (* h6 h6 h6 h6) j2) (* 8 h1 h2 h3 
(* h5 h5 h5) (* h6 h6 h6 h6)) (* 2 h1 h2 (* h4 h4 h4 h4) (* h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2)) (* 10 h1 h2 (* h4 h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2))
 (* 18 h1 h2 (* h4 h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 14 h1 h2 (* h4 
h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 4 h1 h2 (* h4 h4 h4 h4) (* h5 h5 h5) 
h6 (* j2 j2)) (* 4 h1 h2 (* h4 h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 16 h1 h2 (* h4 h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 22 
h1 h2 (* h4 h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 12 h1 h2 (* h4 h4 
h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 2 h1 h2 (* h4 h4 h4 h4) (* h5 h5) 
(* h6 h6) (* j2 j2)) (* 2 h1 h2 (* h4 h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 6 h1 h2 (* h4 h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 5 h1 
h2 (* h4 h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* h1 h2 (* h4 h4 h4 h4) h5 
(* h6 h6 h6) (* j2 j2 j2)) (* 2 h1 h2 (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2)) (* 12 h1 h2 (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2)) (* 28 h1 h2 (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 32 h1 h2
 (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 18 h1 h2 (* h4 h4 h4) (* h5
 h5 h5 h5) h6 (* j2 j2 j2)) (* 4 h1 h2 (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2)
) (* 8 h1 h2 (* h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 50
 h1 h2 (* h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 123 h1 h2 
(* h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 151 h1 h2 (* h4 h4 h4
) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 95 h1 h2 (* h4 h4 h4) (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2)) (* 27 h1 h2 (* h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2
)) (* 2 h1 h2 (* h4 h4 h4) (* h5 h5 h5) (* h6 h6) j2) (* 8 h1 h2 (* h4 h4 h4) 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 44 h1 h2 (* h4 h4 h4) (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 90 h1 h2 (* h4 h4 h4) (* h5 h5) (* h6
 h6 h6) (* j2 j2 j2 j2 j2)) (* 86 h1 h2 (* h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2)) (* 38 h1 h2 (* h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 6
 h1 h2 (* h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 2 h1 h2 (* h4 h4 h4) h5
 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 8 h1 h2 (* h4 h4 h4) h5 (* h6 h6 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 11 h1 h2 (* h4 h4 h4) h5 (* h6 h6 h6 h6) (* j2 
j2 j2 j2 j2)) (* 6 h1 h2 (* h4 h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* h1 
h2 (* h4 h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 4 h1 h2 (* h4 h4) (* h5 h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 31 h1 h2 (* h4 h4) (* h5 h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 97 h1 h2 (* h4 h4) (* h5 h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 160 h1 h2 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6
) (* j2 j2 j2 j2 j2)) (* 150 h1 h2 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2)) (* 79 h1 h2 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 21 h1 
h2 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 2 h1 h2 (* h4 h4) (* h5 h5 
h5 h5) (* h6 h6) j2) (* 8 h1 h2 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 60 h1 h2 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 184 h1 h2 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2
)) (* 300 h1 h2 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 280 
h1 h2 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 148 h1 h2 (* h4 h4
) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 40 h1 h2 (* h4 h4) (* h5 h5 h5) (* 
h6 h6 h6) (* j2 j2)) (* 4 h1 h2 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) j2) (* 4 h1 
h2 (* h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 27 h1 h2 
(* h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 72 h1 h2 (* h4 
h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 98 h1 h2 (* h4 h4) (* h5
 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 72 h1 h2 (* h4 h4) (* h5 h5) (* h6 
h6 h6 h6) (* j2 j2 j2 j2)) (* 27 h1 h2 (* h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2
 j2 j2)) (* 4 h1 h2 (* h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 2 h1 h2 h4
 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 18 h1 h2 h4 (* 
h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 68 h1 h2 h4 (* h5 h5 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 142 h1 h2 h4 (* h5 h5 h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 180 h1 h2 h4 (* h5 h5 h5 h5) (* h6 h6 h6)
 (* j2 j2 j2 j2 j2)) (* 142 h1 h2 h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2
)) (* 68 h1 h2 h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 18 h1 h2 h4 (* 
h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 2 h1 h2 h4 (* h5 h5 h5 h5) (* h6 h6 h6) 
j2) (* 2 h1 h2 h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 18 h1 h2 h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 68 
h1 h2 h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 142 h1 h2 h4 
(* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 180 h1 h2 h4 (* h5 h5 h5)
 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 142 h1 h2 h4 (* h5 h5 h5) (* h6 h6 h6 h6
) (* j2 j2 j2 j2)) (* 68 h1 h2 h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 
18 h1 h2 h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 2 h1 h2 h4 (* h5 h5 h5) 
(* h6 h6 h6 h6) j2) (* 4 h1 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 
j2 j2 j2 j2)) (* 64 h1 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 
j2)) (* 396 h1 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 
1208 h1 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 1920 h1 (* h3
 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 1504 h1 (* h3 h3 h3 h3) (* h4
 h4 h4) (* h5 h5) (* j2 j2)) (* 448 h1 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) j2
) (* 16 h1 (* h3 h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 208 
h1 (* h3 h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 1024 h1 (* h3 h3
 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 2496 h1 (* h3 h3 h3 h3) (* h4 
h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 3200 h1 (* h3 h3 h3 h3) (* h4 h4 h4) h5 h6 (* 
j2 j2 j2)) (* 2048 h1 (* h3 h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2)) (* 512 h1 
(* h3 h3 h3 h3) (* h4 h4 h4) h5 h6 j2) (* 16 h1 (* h3 h3 h3 h3) (* h4 h4 h4) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 144 h1 (* h3 h3 h3 h3) (* h4 h4 h4) (* h6 h6
) (* j2 j2 j2 j2 j2 j2)) (* 512 h1 (* h3 h3 h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 
j2 j2 j2 j2)) (* 896 h1 (* h3 h3 h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2)) 
(* 768 h1 (* h3 h3 h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2)) (* 256 h1 (* h3 
h3 h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2)) (* 2 h1 (* h3 h3 h3 h3) (* h4 h4) 
(* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 40 h1 (* h3 h3 h3 h3) (* h4 h4) (* 
h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 318 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5
 h5) (* j2 j2 j2 j2 j2 j2)) (* 1284 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) 
(* j2 j2 j2 j2 j2)) (* 2808 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 
j2 j2)) (* 3312 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 1952 
h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 448 h1 (* h3 h3 h3 h3) 
(* h4 h4) (* h5 h5 h5) j2) (* 12 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 236 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2)) (* 1840 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 
j2 j2 j2 j2)) (* 7360 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 
j2)) (* 16400 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 
20512 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 13568 h1 (* h3 
h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 3968 h1 (* h3 h3 h3 h3) (* h4 h4)
 (* h5 h5) h6 j2) (* 256 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6) (* 24 h1 (* 
h3 h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 392 h1 (* h3
 h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2472 h1 (* h3 h3 
h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 7944 h1 (* h3 h3 h3 h3) 
(* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 14096 h1 (* h3 h3 h3 h3) (* h4 h4)
 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 13728 h1 (* h3 h3 h3 h3) (* h4 h4) h5 (* h6 h6
) (* j2 j2 j2)) (* 6720 h1 (* h3 h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 
1280 h1 (* h3 h3 h3 h3) (* h4 h4) h5 (* h6 h6) j2) (* 16 h1 (* h3 h3 h3 h3) (* 
h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 160 h1 (* h3 h3 h3 h3) (* h4
 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 656 h1 (* h3 h3 h3 h3) (* h4 h4) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1408 h1 (* h3 h3 h3 h3) (* h4 h4) (* h6 
h6 h6) (* j2 j2 j2 j2 j2)) (* 1664 h1 (* h3 h3 h3 h3) (* h4 h4) (* h6 h6 h6) (* 
j2 j2 j2 j2)) (* 1024 h1 (* h3 h3 h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2)) 
(* 256 h1 (* h3 h3 h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2)) (* 26 h1 (* h3 h3 h3
 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 434 h1 (* h3 h3 h3 h3) 
h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2866 h1 (* h3 h3 h3 h3) h4 (* h5
 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 9644 h1 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2)) (* 17832 h1 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 
j2)) (* 18352 h1 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 10208 h1 
(* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2)) (* 2752 h1 (* h3 h3 h3 h3) h4 (* 
h5 h5 h5) h6 j2) (* 256 h1 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6) (* 104 h1 (* h3 
h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1444 h1 (* h3 
h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 8004 h1 (* h3 h3 
h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 23316 h1 (* h3 h3 h3 h3)
 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 38984 h1 (* h3 h3 h3 h3) h4 (* h5
 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 37984 h1 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 
h6) (* j2 j2 j2)) (* 20704 h1 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2)) 
(* 5568 h1 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) j2) (* 512 h1 (* h3 h3 h3 h3) 
h4 (* h5 h5) (* h6 h6)) (* 104 h1 (* h3 h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 1104 h1 (* h3 h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 4848 h1 (* h3 h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 11352 h1 (* h3 h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 15216 h1 
(* h3 h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 11616 h1 (* h3 h3 h3 h3) 
h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 4672 h1 (* h3 h3 h3 h3) h4 h5 (* h6 h6 h6) 
(* j2 j2)) (* 768 h1 (* h3 h3 h3 h3) h4 h5 (* h6 h6 h6) j2) (* 72 h1 (* h3 h3 h3
 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 960 h1 (* h3 h3 h3 
h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4928 h1 (* h3 h3 h3 h3) 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 12936 h1 (* h3 h3 h3 h3) (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 19232 h1 (* h3 h3 h3 h3) (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2)) (* 16800 h1 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2)) (* 8512 h1 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 
2304 h1 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) j2) (* 256 h1 (* h3 h3 h3 h3) (* 
h5 h5 h5) (* h6 h6)) (* 144 h1 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 1488 h1 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 6400 h1 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 14928 h1 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)
) (* 20624 h1 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 17280 
h1 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 8576 h1 (* h3 h3 h3 
h3) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 2304 h1 (* h3 h3 h3 h3) (* h5 h5) (* h6
 h6 h6) j2) (* 256 h1 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6)) (* 2 h1 (* h3 h3 
h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 28 h1 (* h3 h3 h3) (* h4
 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 142 h1 (* h3 h3 h3) (* h4 h4 h4 h4) 
(* h5 h5) (* j2 j2 j2 j2)) (* 320 h1 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* 
j2 j2 j2)) (* 320 h1 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2)) (* 112 h1
 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) j2) (* 8 h1 (* h3 h3 h3) (* h4 h4 h4 h4)
 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 88 h1 (* h3 h3 h3) (* h4 h4 h4 h4) h5 h6 (* j2 
j2 j2 j2 j2)) (* 336 h1 (* h3 h3 h3) (* h4 h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 
576 h1 (* h3 h3 h3) (* h4 h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 448 h1 (* h3 h3 h3) 
(* h4 h4 h4 h4) h5 h6 (* j2 j2)) (* 128 h1 (* h3 h3 h3) (* h4 h4 h4 h4) h5 h6 j2
) (* 8 h1 (* h3 h3 h3) (* h4 h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 56 h1
 (* h3 h3 h3) (* h4 h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 144 h1 (* h3 h3 
h3) (* h4 h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 160 h1 (* h3 h3 h3) (* h4 h4 
h4 h4) (* h6 h6) (* j2 j2 j2)) (* 64 h1 (* h3 h3 h3) (* h4 h4 h4 h4) (* h6 h6) 
(* j2 j2)) (* 4 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 
j2)) (* 60 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 
340 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 924 h1 (* 
h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 1280 h1 (* h3 h3 h3) (* 
h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 864 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 
h5 h5) (* j2 j2)) (* 224 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) j2) (* 28 h1 
(* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 354 h1 (* h3
 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 1750 h1 (* h3 h3 h3)
 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 4478 h1 (* h3 h3 h3) (* h4 h4 
h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 6240 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5)
 h6 (* j2 j2 j2)) (* 4448 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) 
(* 1328 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 j2) (* 64 h1 (* h3 h3 h3) (* 
h4 h4 h4) (* h5 h5) h6) (* 48 h1 (* h3 h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2
 j2 j2 j2 j2 j2)) (* 464 h1 (* h3 h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 1872 h1 (* h3 h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2))
 (* 3916 h1 (* h3 h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 4320 h1 
(* h3 h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 2288 h1 (* h3 h3 h3) (* 
h4 h4 h4) h5 (* h6 h6) (* j2 j2)) (* 448 h1 (* h3 h3 h3) (* h4 h4 h4) h5 (* h6 
h6) j2) (* 16 h1 (* h3 h3 h3) (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 128 h1 (* h3 h3 h3) (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 400
 h1 (* h3 h3 h3) (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 608 h1 (* h3 
h3 h3) (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 448 h1 (* h3 h3 h3) (* h4 
h4 h4) (* h6 h6 h6) (* j2 j2 j2)) (* 128 h1 (* h3 h3 h3) (* h4 h4 h4) (* h6 h6 
h6) (* j2 j2)) (* h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 19 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2
)) (* 141 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 
519 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 1008 h1 (* 
h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 1044 h1 (* h3 h3 h3) (* 
h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 544 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 
h5 h5) (* j2 j2)) (* 112 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) j2) (* 13 h1 
(* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 237 h1 
(* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1690 h1 (* 
h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 6058 h1 (* h3 h3 
h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 11820 h1 (* h3 h3 h3) (* h4
 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 12760 h1 (* h3 h3 h3) (* h4 h4) (* h5 
h5 h5) h6 (* j2 j2 j2)) (* 7328 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 
j2)) (* 1920 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 j2) (* 128 h1 (* h3 h3 h3
) (* h4 h4) (* h5 h5 h5) h6) (* 42 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 658 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3932 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 12030 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6
) (* j2 j2 j2 j2 j2)) (* 20894 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* 
j2 j2 j2 j2)) (* 21000 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2
)) (* 11536 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 2928 h1 
(* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) j2) (* 192 h1 (* h3 h3 h3) (* h4 h4) 
(* h5 h5) (* h6 h6)) (* 44 h1 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 484 h1 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 2316 h1 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 6028 h1 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 8936 h1 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 7376 h1 
(* h3 h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 3104 h1 (* h3 h3 h3) (* 
h4 h4) h5 (* h6 h6 h6) (* j2 j2)) (* 512 h1 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6 
h6) j2) (* 8 h1 (* h3 h3 h3) (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 72 h1 (* h3 h3 h3) (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 264 h1 (* h3 h3 h3) (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 504 
h1 (* h3 h3 h3) (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 528 h1 (* h3 h3
 h3) (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 288 h1 (* h3 h3 h3) (* h4 h4)
 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 64 h1 (* h3 h3 h3) (* h4 h4) (* h6 h6 h6 h6) 
(* j2 j2)) (* 13 h1 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 204 h1 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
1242 h1 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 3771 h1 (* 
h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 6196 h1 (* h3 h3 h3) h4 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 5700 h1 (* h3 h3 h3) h4 (* h5 h5 h5 h5) 
h6 (* j2 j2 j2)) (* 2880 h1 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 720
 h1 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 j2) (* 64 h1 (* h3 h3 h3) h4 (* h5 h5 h5 
h5) h6) (* 117 h1 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2
 j2)) (* 1466 h1 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 7220 h1 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
18435 h1 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 26988 h1 
(* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 23256 h1 (* h3 h3 h3)
 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 11424 h1 (* h3 h3 h3) h4 (* h5 h5 h5
) (* h6 h6) (* j2 j2)) (* 2848 h1 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) j2) (* 
256 h1 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6)) (* 208 h1 (* h3 h3 h3) h4 (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2026 h1 (* h3 h3 h3) h4 (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 8304 h1 (* h3 h3 h3) h4 (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 18748 h1 (* h3 h3 h3) h4 (* h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2)) (* 25366 h1 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2)) (* 20736 h1 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)
) (* 9760 h1 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 2320 h1 (* h3 
h3 h3) h4 (* h5 h5) (* h6 h6 h6) j2) (* 192 h1 (* h3 h3 h3) h4 (* h5 h5) (* h6 
h6 h6)) (* 52 h1 (* h3 h3 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2))
 (* 500 h1 (* h3 h3 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1976 
h1 (* h3 h3 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4148 h1 (* h3 h3
 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 4988 h1 (* h3 h3 h3) h4 h5 (* 
h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 3440 h1 (* h3 h3 h3) h4 h5 (* h6 h6 h6 h6) (* 
j2 j2 j2)) (* 1264 h1 (* h3 h3 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2)) (* 192 h1 
(* h3 h3 h3) h4 h5 (* h6 h6 h6 h6) j2) (* 36 h1 (* h3 h3 h3) (* h5 h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 444 h1 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6
 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2056 h1 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6)
 (* j2 j2 j2 j2 j2 j2)) (* 4820 h1 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2)) (* 6444 h1 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2))
 (* 5128 h1 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 2400 h1 (* 
h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 608 h1 (* h3 h3 h3) (* h5 h5 
h5 h5) (* h6 h6) j2) (* 64 h1 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6)) (* 180 h1 
(* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1572 h1 
(* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 5744 h1 (* 
h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 11572 h1 (* h3 h3 
h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 14100 h1 (* h3 h3 h3) (* h5
 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 10640 h1 (* h3 h3 h3) (* h5 h5 h5) (* 
h6 h6 h6) (* j2 j2 j2)) (* 4848 h1 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 
j2)) (* 1216 h1 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) j2) (* 128 h1 (* h3 h3 h3
) (* h5 h5 h5) (* h6 h6 h6)) (* 72 h1 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 672 h1 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2
 j2 j2 j2 j2 j2 j2)) (* 2600 h1 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 5464 h1 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 
j2)) (* 6848 h1 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 5256 
h1 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 2416 h1 (* h3 h3 h3) 
(* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 608 h1 (* h3 h3 h3) (* h5 h5) (* h6 h6 
h6 h6) j2) (* 64 h1 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6)) (* h1 (* h3 h3) (* 
h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 13 h1 (* h3 h3) (* h4 h4 h4 
h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 59 h1 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5
 h5) (* j2 j2 j2 j2)) (* 113 h1 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 
j2)) (* 94 h1 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2)) (* 28 h1 (* h3 
h3) (* h4 h4 h4 h4) (* h5 h5 h5) j2) (* 9 h1 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5)
 h6 (* j2 j2 j2 j2 j2 j2)) (* 87 h1 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) h6 (* j2
 j2 j2 j2 j2)) (* 280 h1 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2))
 (* 384 h1 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 228 h1 (* h3 
h3) (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 48 h1 (* h3 h3) (* h4 h4 h4 h4) 
(* h5 h5) h6 j2) (* 16 h1 (* h3 h3) (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 100 h1 (* h3 h3) (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
220 h1 (* h3 h3) (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 200 h1 (* h3 
h3) (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 64 h1 (* h3 h3) (* h4 h4 h4 h4
) h5 (* h6 h6) (* j2 j2)) (* 4 h1 (* h3 h3) (* h4 h4 h4 h4) (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 20 h1 (* h3 h3) (* h4 h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 
j2)) (* 32 h1 (* h3 h3) (* h4 h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 16 h1 
(* h3 h3) (* h4 h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2)) (* h1 (* h3 h3) (* h4 h4 h4
) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 14 h1 (* h3 h3) (* h4 h4 h4) (* 
h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 72 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 
h5) (* j2 j2 j2 j2 j2)) (* 172 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 
j2 j2 j2)) (* 207 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 122
 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 28 h1 (* h3 h3) (* h4 
h4 h4) (* h5 h5 h5 h5) j2) (* 14 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2
 j2 j2 j2 j2 j2 j2)) (* 163 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2)) (* 724 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2
)) (* 1634 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 1949 h1
 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 1182 h1 (* h3 h3) (* h4
 h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 308 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5)
 h6 j2) (* 16 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6) (* 41 h1 (* h3 h3) (* 
h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 376 h1 (* h3 h3) (* 
h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1418 h1 (* h3 h3) (* h4 
h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2644 h1 (* h3 h3) (* h4 h4 h4)
 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 2498 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5
) (* h6 h6) (* j2 j2 j2)) (* 1108 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5) (* h6 h6) 
(* j2 j2)) (* 176 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5) (* h6 h6) j2) (* 28 h1 (* 
h3 h3) (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 218 h1 (* h3 h3
) (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 674 h1 (* h3 h3) (* h4 
h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 978 h1 (* h3 h3) (* h4 h4 h4) h5 
(* h6 h6 h6) (* j2 j2 j2 j2)) (* 628 h1 (* h3 h3) (* h4 h4 h4) h5 (* h6 h6 h6) 
(* j2 j2 j2)) (* 144 h1 (* h3 h3) (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2)) (* 4 
h1 (* h3 h3) (* h4 h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 24 h1 (* 
h3 h3) (* h4 h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 52 h1 (* h3 h3) 
(* h4 h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 48 h1 (* h3 h3) (* h4 h4 h4)
 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 16 h1 (* h3 h3) (* h4 h4 h4) (* h6 h6 h6 h6
) (* j2 j2 j2)) (* 3 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 53 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2
 j2)) (* 356 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 1156 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 1962 h1
 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 1820 h1 (* h3 h3) 
(* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 908 h1 (* h3 h3) (* h4 h4) (* h5 
h5 h5 h5) h6 (* j2 j2)) (* 216 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 j2) (* 
16 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6) (* 21 h1 (* h3 h3) (* h4 h4) (* h5
 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 308 h1 (* h3 h3) (* h4 h4) (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1674 h1 (* h3 h3) (* h4 h4) (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4556 h1 (* h3 h3) (* h4 h4) (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 6978 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5)
 (* h6 h6) (* j2 j2 j2 j2)) (* 6155 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6
) (* j2 j2 j2)) (* 2990 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2))
 (* 692 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) j2) (* 48 h1 (* h3 h3) (* 
h4 h4) (* h5 h5 h5) (* h6 h6)) (* 36 h1 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 385 h1 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1766 h1 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4241 h1 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2)) (* 5596 h1 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2)) (* 4032 h1 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 
j2)) (* 1468 h1 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 208 h1 
(* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6 h6) j2) (* 12 h1 (* h3 h3) (* h4 h4) h5 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 114 h1 (* h3 h3) (* h4 h4) h5 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 446 h1 (* h3 h3) (* h4 h4) h5 (* h6
 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 874 h1 (* h3 h3) (* h4 h4) h5 (* h6 h6 h6 
h6) (* j2 j2 j2 j2 j2)) (* 878 h1 (* h3 h3) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 
j2 j2 j2)) (* 428 h1 (* h3 h3) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 80 
h1 (* h3 h3) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2)) (* 26 h1 (* h3 h3) h4 (* h5
 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 309 h1 (* h3 h3) h4 (* h5 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1403 h1 (* h3 h3) h4 (* h5 h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3238 h1 (* h3 h3) h4 (* h5 h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 4251 h1 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2)) (* 3295 h1 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2))
 (* 1478 h1 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 348 h1 (* h3 h3
) h4 (* h5 h5 h5 h5) (* h6 h6) j2) (* 32 h1 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 
h6)) (* 104 h1 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 909 h1 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 3329 h1 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6718
 h1 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 8127 h1 (* h3 
h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 5971 h1 (* h3 h3) h4 (* h5 
h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 2562 h1 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 
h6) (* j2 j2)) (* 572 h1 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) j2) (* 48 h1 (* 
h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6)) (* 52 h1 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 454 h1 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1602 h1 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 2964 h1 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 
j2 j2 j2 j2)) (* 3122 h1 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2))
 (* 1882 h1 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 604 h1 (* h3
 h3) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 80 h1 (* h3 h3) h4 (* h5 h5) (* 
h6 h6 h6 h6) j2) (* 36 h1 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 300 h1 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2
 j2 j2)) (* 1036 h1 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)
) (* 1960 h1 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2236 
h1 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1580 h1 (* h3 h3) 
(* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 676 h1 (* h3 h3) (* h5 h5 h5 h5) 
(* h6 h6 h6) (* j2 j2)) (* 160 h1 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) j2) (* 
16 h1 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6)) (* 36 h1 (* h3 h3) (* h5 h5 h5) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 300 h1 (* h3 h3) (* h5 h5 h5) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1036 h1 (* h3 h3) (* h5 h5 h5) (* 
h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1960 h1 (* h3 h3) (* h5 h5 h5) (* h6 h6 
h6 h6) (* j2 j2 j2 j2 j2)) (* 2236 h1 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* 
j2 j2 j2 j2)) (* 1580 h1 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) 
(* 676 h1 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 160 h1 (* h3 h3) 
(* h5 h5 h5) (* h6 h6 h6 h6) j2) (* 16 h1 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6)
) (* 2 h1 h3 (* h4 h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 18 h1 h3 
(* h4 h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 49 h1 h3 (* h4 h4 h4 h4) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 50 h1 h3 (* h4 h4 h4 h4) (* h5 h5 h5) h6 (* 
j2 j2 j2)) (* 17 h1 h3 (* h4 h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 8 h1 h3 (* 
h4 h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 42 h1 h3 (* h4 h4 h4 
h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 73 h1 h3 (* h4 h4 h4 h4) (* h5 h5
) (* h6 h6) (* j2 j2 j2 j2)) (* 51 h1 h3 (* h4 h4 h4 h4) (* h5 h5) (* h6 h6) (* 
j2 j2 j2)) (* 12 h1 h3 (* h4 h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 4 h1 h3
 (* h4 h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 17 h1 h3 (* h4 h4 h4 
h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 21 h1 h3 (* h4 h4 h4 h4) h5 (* h6 h6 
h6) (* j2 j2 j2 j2)) (* 8 h1 h3 (* h4 h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2)) 
(* 2 h1 h3 (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 20 h1 h3
 (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 67 h1 h3 (* h4 h4 h4)
 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 99 h1 h3 (* h4 h4 h4) (* h5 h5 h5 h5)
 h6 (* j2 j2 j2 j2)) (* 67 h1 h3 (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) 
(* 17 h1 h3 (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 12 h1 h3 (* h4 h4 h4) 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 92 h1 h3 (* h4 h4 h4) (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 290 h1 h3 (* h4 h4 h4) (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 451 h1 h3 (* h4 h4 h4) (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2)) (* 344 h1 h3 (* h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) 
(* 111 h1 h3 (* h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 8 h1 h3 (* h4 h4 
h4) (* h5 h5 h5) (* h6 h6) j2) (* 14 h1 h3 (* h4 h4 h4) (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 95 h1 h3 (* h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 251 h1 h3 (* h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2
 j2)) (* 300 h1 h3 (* h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 162 
h1 h3 (* h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 32 h1 h3 (* h4 h4 h4)
 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 4 h1 h3 (* h4 h4 h4) h5 (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 21 h1 h3 (* h4 h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 38 h1 h3 (* h4 h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 29 h1 h3 (* h4 h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 8 h1 h3 (* h4 h4
 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 3 h1 h3 (* h4 h4) (* h5 h5 h5 h5) (* h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 40 h1 h3 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6
) (* j2 j2 j2 j2 j2 j2 j2)) (* 187 h1 h3 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 409 h1 h3 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2
 j2 j2)) (* 468 h1 h3 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 
283 h1 h3 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 82 h1 h3 (* h4 h4
) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 8 h1 h3 (* h4 h4) (* h5 h5 h5 h5) (* 
h6 h6) j2) (* 11 h1 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 99 h1 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 386 h1 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 789
 h1 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 888 h1 h3 (* 
h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 540 h1 h3 (* h4 h4) (* h5 
h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 159 h1 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6 
h6) (* j2 j2)) (* 16 h1 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) j2) (* 6 h1 h3 
(* h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 51 h1 h3 (* 
h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 176 h1 h3 (* h4 h4
) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 298 h1 h3 (* h4 h4) (* h5 
h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 262 h1 h3 (* h4 h4) (* h5 h5) (* h6 
h6 h6 h6) (* j2 j2 j2 j2)) (* 115 h1 h3 (* h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* 
j2 j2 j2)) (* 20 h1 h3 (* h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 13 h1 
h3 h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 99 h1 h3 h4 
(* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 303 h1 h3 h4 (* h5 h5 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 490 h1 h3 h4 (* h5 h5 h5 h5) (* h6
 h6 h6) (* j2 j2 j2 j2 j2)) (* 455 h1 h3 h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2)) (* 243 h1 h3 h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 69 h1 
h3 h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 8 h1 h3 h4 (* h5 h5 h5 h5) (* 
h6 h6 h6) j2) (* 13 h1 h3 h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 99 h1 h3 h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 303 h1 h3 h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 490 h1 h3
 h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 455 h1 h3 h4 (* h5 h5 h5
) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 243 h1 h3 h4 (* h5 h5 h5) (* h6 h6 h6 h6) 
(* j2 j2 j2)) (* 69 h1 h3 h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 8 h1 h3 
h4 (* h5 h5 h5) (* h6 h6 h6 h6) j2) (* h1 (* h4 h4 h4 h4) (* h5 h5 h5) (* h6 h6)
 (* j2 j2 j2 j2 j2 j2)) (* 4 h1 (* h4 h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2)) (* 5 h1 (* h4 h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 2 
h1 (* h4 h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* h1 (* h4 h4 h4 h4) 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3 h1 (* h4 h4 h4 h4) (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2 h1 (* h4 h4 h4 h4) (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2)) (* h1 (* h4 h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 5 h1 (* h4 h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 9 h1 (* h4 h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 7 h1 (* h4
 h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 2 h1 (* h4 h4 h4) (* h5 h5
 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 2 h1 (* h4 h4 h4) (* h5 h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 10 h1 (* h4 h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 18 h1 (* h4 h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2)) (* 14 h1 (* h4 h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 4 h1 
(* h4 h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* h1 (* h4 h4 h4) (* h5 h5
) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4 h1 (* h4 h4 h4) (* h5 h5) (* h6
 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 5 h1 (* h4 h4 h4) (* h5 h5) (* h6 h6 h6 h6)
 (* j2 j2 j2 j2 j2)) (* 2 h1 (* h4 h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 
j2)) (* h1 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 6 h1 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 14 
h1 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 16 h1 (* h4 
h4) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 9 h1 (* h4 h4) (* h5 h5 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 2 h1 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6 
h6) (* j2 j2 j2)) (* h1 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 6 h1 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 14 h1 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
16 h1 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 9 h1 (* h4 
h4) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 2 h1 (* h4 h4) (* h5 h5 h5)
 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 4 (* h2 h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 60 (* h2 h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* 
j2 j2 j2 j2 j2 j2 j2)) (* 344 (* h2 h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2
 j2 j2 j2 j2)) (* 1032 (* h2 h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 
j2)) (* 1812 (* h2 h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 1932 
(* h2 h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 1232 (* h2 h2 h2 h2) 
(* h3 h3 h3) (* h4 h4) h5 (* j2 j2)) (* 432 (* h2 h2 h2 h2) (* h3 h3 h3) (* h4 
h4) h5 j2) (* 64 (* h2 h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5) (* 8 (* h2 h2 h2 h2)
 (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 80 (* h2 h2 h2 h2) 
(* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 336 (* h2 h2 h2 h2) (* h3
 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 768 (* h2 h2 h2 h2) (* h3 h3 h3) 
(* h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 1032 (* h2 h2 h2 h2) (* h3 h3 h3) (* h4 h4) 
h6 (* j2 j2 j2 j2)) (* 816 (* h2 h2 h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2
)) (* 352 (* h2 h2 h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2)) (* 64 (* h2 h2 h2
 h2) (* h3 h3 h3) (* h4 h4) h6 j2) (* 2 (* h2 h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5
) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 40 (* h2 h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5
) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 310 (* h2 h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 1220 (* h2 h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* 
j2 j2 j2 j2 j2 j2)) (* 2766 (* h2 h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 
j2 j2 j2)) (* 3840 (* h2 h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) 
(* 3322 (* h2 h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 1748 (* h2 h2
 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2)) (* 512 (* h2 h2 h2 h2) (* h3 h3 h3)
 h4 (* h5 h5) j2) (* 64 (* h2 h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5)) (* 8 (* h2 h2
 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 128 (* h2 h2 h2
 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 808 (* h2 h2 h2 h2) 
(* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2752 (* h2 h2 h2 h2) (* h3 h3
 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 5688 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 
h6 (* j2 j2 j2 j2 j2)) (* 7488 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2
 j2)) (* 6328 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 3328 (* h2 
h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2)) (* 992 (* h2 h2 h2 h2) (* h3 h3 h3) 
h4 h5 h6 j2) (* 128 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 h6) (* 8 (* h2 h2 h2 h2) 
(* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 88 (* h2 h2 h2 h2) 
(* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 416 (* h2 h2 h2 h2) 
(* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1104 (* h2 h2 h2 h2) (* 
h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1800 (* h2 h2 h2 h2) (* h3 h3 
h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1848 (* h2 h2 h2 h2) (* h3 h3 h3) h4 (* 
h6 h6) (* j2 j2 j2 j2)) (* 1168 (* h2 h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 
j2 j2)) (* 416 (* h2 h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2)) (* 64 (* h2 
h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6) j2) (* 14 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5
 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 204 (* h2 h2 h2 h2) (* h3 h3 h3) (* 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1134 (* h2 h2 h2 h2) (* h3 h3 h3) (* 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 3356 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 
h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 5994 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 
(* j2 j2 j2 j2 j2)) (* 6804 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 
j2 j2)) (* 4954 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 2244 
(* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2)) (* 576 (* h2 h2 h2 h2) (* 
h3 h3 h3) (* h5 h5) h6 j2) (* 64 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6) (* 
28 (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
296 (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
1364 (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3600
 (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6004 (* h2 
h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 6568 (* h2 h2 h2 h2) 
(* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 4716 (* h2 h2 h2 h2) (* h3 h3 h3) 
h5 (* h6 h6) (* j2 j2 j2)) (* 2144 (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* 
j2 j2)) (* 560 (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) j2) (* 64 (* h2 h2 h2 
h2) (* h3 h3 h3) h5 (* h6 h6)) (* 2 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 
(* j2 j2 j2 j2 j2 j2 j2)) (* 26 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 
j2 j2 j2 j2 j2)) (* 120 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2
 j2)) (* 276 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 354 
(* h2 h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 258 (* h2 h2 h2 h2) 
(* h3 h3) (* h4 h4 h4) h5 (* j2 j2)) (* 100 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4 
h4) h5 j2) (* 16 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5) (* 4 (* h2 h2 h2 h2)
 (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 32 (* h2 h2 h2 h2) (* h3
 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 104 (* h2 h2 h2 h2) (* h3 h3) (* 
h4 h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 176 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4 h4) 
h6 (* j2 j2 j2 j2)) (* 164 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2
)) (* 80 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4 h4) h6 (* j2 j2)) (* 16 (* h2 h2 h2 
h2) (* h3 h3) (* h4 h4 h4) h6 j2) (* 4 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) (* h5
 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 56 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) (* 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 292 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) (* 
h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 792 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 
h5) (* j2 j2 j2 j2 j2)) (* 1260 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) 
(* j2 j2 j2 j2)) (* 1224 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 
j2)) (* 716 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 232 (* 
h2 h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) j2) (* 32 (* h2 h2 h2 h2) (* h3 h3) 
(* h4 h4) (* h5 h5)) (* 16 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 154 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 
j2 j2 j2 j2)) (* 646 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2
 j2)) (* 1536 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 
2252 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 2074 (* h2 h2
 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 1166 (* h2 h2 h2 h2) (* h3 h3
) (* h4 h4) h5 h6 (* j2 j2)) (* 364 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 j2
) (* 48 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6) (* 8 (* h2 h2 h2 h2) (* h3 h3
) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 72 (* h2 h2 h2 h2) (* h3 
h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 272 (* h2 h2 h2 h2) (* h3 
h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 560 (* h2 h2 h2 h2) (* h3 h3) 
(* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 680 (* h2 h2 h2 h2) (* h3 h3) (* h4 
h4) (* h6 h6) (* j2 j2 j2 j2)) (* 488 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) (* h6 
h6) (* j2 j2 j2)) (* 192 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2)
) (* 32 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) j2) (* (* h2 h2 h2 h2) (* 
h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 19 (* h2 h2 h2 h2) (* 
h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 137 (* h2 h2 h2 h2) (* h3
 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 491 (* h2 h2 h2 h2) (* h3 h3) 
h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1011 (* h2 h2 h2 h2) (* h3 h3) h4 (* 
h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 1281 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) 
(* j2 j2 j2 j2)) (* 1019 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2))
 (* 497 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2)) (* 136 (* h2 h2 h2 
h2) (* h3 h3) h4 (* h5 h5 h5) j2) (* 16 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5
)) (* 9 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 132 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 745 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
2268 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 4219 
(* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 5044 (* h2 h2 
h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 3907 (* h2 h2 h2 h2) (* h3 
h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 1900 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5)
 h6 (* j2 j2)) (* 528 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 j2) (* 64 (* h2 
h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6) (* 16 (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 168 (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 786 (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* h6
 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2142 (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6)
 (* j2 j2 j2 j2 j2 j2)) (* 3728 (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 
j2 j2 j2 j2)) (* 4276 (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2))
 (* 3218 (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 1526 (* h2 
h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 412 (* h2 h2 h2 h2) (* h3 h3) 
h4 h5 (* h6 h6) j2) (* 48 (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6)) (* 4 (* h2 
h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 40 (* h2 
h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 172 (* h2 h2
 h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 416 (* h2 h2 h2 
h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 620 (* h2 h2 h2 h2) (* 
h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 584 (* h2 h2 h2 h2) (* h3 h3) h4 
(* h6 h6 h6) (* j2 j2 j2 j2)) (* 340 (* h2 h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6) 
(* j2 j2 j2)) (* 112 (* h2 h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2)) (* 16 
(* h2 h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6) j2) (* 7 (* h2 h2 h2 h2) (* h3 h3) (* 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 95 (* h2 h2 h2 h2) (* h3 h3) (* 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 479 (* h2 h2 h2 h2) (* h3 h3) (* h5
 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1287 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 2101 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2)) (* 2197 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 
j2 j2)) (* 1485 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 629 
(* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2)) (* 152 (* h2 h2 h2 h2) (* 
h3 h3) (* h5 h5 h5) h6 j2) (* 16 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6) (* 
35 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (* 314 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 1253 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2
)) (* 2916 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 4357 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
4330 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 2859 (* 
h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 1208 (* h2 h2 h2 h2)
 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 296 (* h2 h2 h2 h2) (* h3 h3) (* h5
 h5) (* h6 h6) j2) (* 32 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6)) (* 14 
(* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 134
 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 562 
(* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1358 (* 
h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2086 (* h2 h2 
h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2114 (* h2 h2 h2 h2) (* 
h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1414 (* h2 h2 h2 h2) (* h3 h3) h5 (* 
h6 h6 h6) (* j2 j2 j2)) (* 602 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 
j2)) (* 148 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) j2) (* 16 (* h2 h2 h2 h2) 
(* h3 h3) h5 (* h6 h6 h6)) (* (* h2 h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2
 j2 j2 j2 j2 j2)) (* 12 (* h2 h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2
 j2 j2)) (* 49 (* h2 h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 
100 (* h2 h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 115 (* h2 h2 
h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 76 (* h2 h2 h2 h2) h3 (* h4 h4
 h4) (* h5 h5) (* j2 j2)) (* 27 (* h2 h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) j2) 
(* 4 (* h2 h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5)) (* 5 (* h2 h2 h2 h2) h3 (* h4 h4
 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 33 (* h2 h2 h2 h2) h3 (* h4 h4 h4) h5 h6
 (* j2 j2 j2 j2 j2 j2)) (* 90 (* h2 h2 h2 h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 
j2 j2)) (* 130 (* h2 h2 h2 h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 105 (* 
h2 h2 h2 h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 45 (* h2 h2 h2 h2) h3 (* h4 
h4 h4) h5 h6 (* j2 j2)) (* 8 (* h2 h2 h2 h2) h3 (* h4 h4 h4) h5 h6 j2) (* 2 (* 
h2 h2 h2 h2) h3 (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 12 (* h2 h2 
h2 h2) h3 (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 28 (* h2 h2 h2 h2) h3
 (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 32 (* h2 h2 h2 h2) h3 (* h4 h4 h4
) (* h6 h6) (* j2 j2 j2 j2)) (* 18 (* h2 h2 h2 h2) h3 (* h4 h4 h4) (* h6 h6) (* 
j2 j2 j2)) (* 4 (* h2 h2 h2 h2) h3 (* h4 h4 h4) (* h6 h6) (* j2 j2)) (* (* h2 h2
 h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 13 (* h2 h2 h2
 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 61 (* h2 h2 h2 h2) 
h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 149 (* h2 h2 h2 h2) h3 (* h4
 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 215 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 
h5 h5) (* j2 j2 j2 j2)) (* 191 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 
j2 j2)) (* 103 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 31 (* h2 
h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) j2) (* 4 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 
h5 h5)) (* 8 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 69 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 262 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 567 
(* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 760 (* h2 h2 h2
 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 643 (* h2 h2 h2 h2) h3 (* h4 
h4) (* h5 h5) h6 (* j2 j2 j2)) (* 334 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 
(* j2 j2)) (* 97 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 j2) (* 12 (* h2 h2 h2
 h2) h3 (* h4 h4) (* h5 h5) h6) (* 9 (* h2 h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 71 (* h2 h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 236 (* h2 h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2
 j2 j2 j2 j2)) (* 430 (* h2 h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 465 (* h2 h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 299 
(* h2 h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 106 (* h2 h2 h2 h2) 
h3 (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 16 (* h2 h2 h2 h2) h3 (* h4 h4) h5 (* h6
 h6) j2) (* 2 (* h2 h2 h2 h2) h3 (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 14 (* h2 h2 h2 h2) h3 (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 40 (* h2 h2 h2 h2) h3 (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 60 (* 
h2 h2 h2 h2) h3 (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 50 (* h2 h2 h2 h2)
 h3 (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 22 (* h2 h2 h2 h2) h3 (* h4 h4) 
(* h6 h6 h6) (* j2 j2 j2)) (* 4 (* h2 h2 h2 h2) h3 (* h4 h4) (* h6 h6 h6) (* j2 
j2)) (* 2 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 28 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 148 
(* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 420 (* h2 h2 
h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 728 (* h2 h2 h2 h2) h3 h4
 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 812 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) 
h6 (* j2 j2 j2 j2)) (* 588 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2)) 
(* 268 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2)) (* 70 (* h2 h2 h2 h2) h3
 h4 (* h5 h5 h5) h6 j2) (* 8 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) h6) (* 8 (* h2 
h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 76 (* h2 
h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 325 (* h2 h2
 h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 814 (* h2 h2 h2 
h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1307 (* h2 h2 h2 h2) h3 
h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1388 (* h2 h2 h2 h2) h3 h4 (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2)) (* 971 (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) 
(* j2 j2 j2)) (* 430 (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 109
 (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) j2) (* 12 (* h2 h2 h2 h2) h3 h4 (* h5
 h5) (* h6 h6)) (* 4 (* h2 h2 h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 37 (* h2 h2 h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 146 (* h2 h2 h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
323 (* h2 h2 h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 440 (* h2 h2
 h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 379 (* h2 h2 h2 h2) h3 h4 
h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 202 (* h2 h2 h2 h2) h3 h4 h5 (* h6 h6 h6) 
(* j2 j2 j2)) (* 61 (* h2 h2 h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2)) (* 8 (* h2 
h2 h2 h2) h3 h4 h5 (* h6 h6 h6) j2) (* 7 (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 60 (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 228 (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6
) (* j2 j2 j2 j2 j2 j2 j2)) (* 504 (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 714 (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2
 j2 j2)) (* 672 (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 
420 (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 168 (* h2 h2 h2 
h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 39 (* h2 h2 h2 h2) h3 (* h5 h5 h5) 
(* h6 h6) j2) (* 4 (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6)) (* 7 (* h2 h2 h2 
h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 60 (* h2 h2 h2 
h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 228 (* h2 h2 h2 h2
) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 504 (* h2 h2 h2 h2) h3 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 714 (* h2 h2 h2 h2) h3 (* h5 h5
) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 672 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2)) (* 420 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 
j2)) (* 168 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 39 (* h2 h2 
h2 h2) h3 (* h5 h5) (* h6 h6 h6) j2) (* 4 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6 
h6)) (* (* h2 h2 h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 6
 (* h2 h2 h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 15 (* h2 h2
 h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 20 (* h2 h2 h2 h2) (* 
h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 15 (* h2 h2 h2 h2) (* h4 h4 h4) (* h5
 h5) h6 (* j2 j2 j2)) (* 6 (* h2 h2 h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) 
(* (* h2 h2 h2 h2) (* h4 h4 h4) (* h5 h5) h6 j2) (* (* h2 h2 h2 h2) (* h4 h4 h4)
 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 5 (* h2 h2 h2 h2) (* h4 h4 h4) h5 (* 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 10 (* h2 h2 h2 h2) (* h4 h4 h4) h5 (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* 10 (* h2 h2 h2 h2) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 
j2)) (* 5 (* h2 h2 h2 h2) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* (* h2 h2 h2
 h2) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2)) (* (* h2 h2 h2 h2) (* h4 h4) (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 7 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 21 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2)) (* 35 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2)) (* 35 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 21 
(* h2 h2 h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 7 (* h2 h2 h2 h2) (* 
h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* (* h2 h2 h2 h2) (* h4 h4) (* h5 h5 h5) h6 
j2) (* 2 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 14 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2
)) (* 42 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 70 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 70 
(* h2 h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 42 (* h2 h2 h2
 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 14 (* h2 h2 h2 h2) (* h4 h4)
 (* h5 h5) (* h6 h6) (* j2 j2)) (* 2 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 
h6) j2) (* (* h2 h2 h2 h2) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 6 (* h2 h2 h2 h2) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 15
 (* h2 h2 h2 h2) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 20 (* h2 h2
 h2 h2) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 15 (* h2 h2 h2 h2) (* 
h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 6 (* h2 h2 h2 h2) (* h4 h4) h5 (* h6 
h6 h6) (* j2 j2 j2)) (* (* h2 h2 h2 h2) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2)) (* 
(* h2 h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8 
(* h2 h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 28 (* 
h2 h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 56 (* h2 h2 
h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 70 (* h2 h2 h2 h2) h4
 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 56 (* h2 h2 h2 h2) h4 (* h5 h5 h5
) (* h6 h6) (* j2 j2 j2 j2)) (* 28 (* h2 h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2)) (* 8 (* h2 h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* (* h2 h2
 h2 h2) h4 (* h5 h5 h5) (* h6 h6) j2) (* (* h2 h2 h2 h2) h4 (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8 (* h2 h2 h2 h2) h4 (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 28 (* h2 h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2)) (* 56 (* h2 h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2)) (* 70 (* h2 h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2
 j2)) (* 56 (* h2 h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 28 (* 
h2 h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 8 (* h2 h2 h2 h2) h4 (* 
h5 h5) (* h6 h6 h6) (* j2 j2)) (* (* h2 h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6) j2) 
(* 8 (* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
128 (* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 800 
(* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 2640 (* h2 
h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 5112 (* h2 h2 h2) (* 
h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 6000 (* h2 h2 h2) (* h3 h3 h3 h3) 
(* h4 h4) h5 (* j2 j2 j2)) (* 4192 (* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* 
j2 j2)) (* 1600 (* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 j2) (* 256 (* h2 h2 h2
) (* h3 h3 h3 h3) (* h4 h4) h5) (* 16 (* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 176 (* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 816 (* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4) h6 (* j2
 j2 j2 j2 j2 j2)) (* 2064 (* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 
j2 j2)) (* 3072 (* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2)) (* 
2688 (* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2)) (* 1280 (* h2 h2 h2
) (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2)) (* 256 (* h2 h2 h2) (* h3 h3 h3 h3) 
(* h4 h4) h6 j2) (* 4 (* h2 h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 84 (* h2 h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 696 (* h2 h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2
 j2 j2)) (* 2984 (* h2 h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)
) (* 7428 (* h2 h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 11316
 (* h2 h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 10688 (* h2 h2 h2
) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 6096 (* h2 h2 h2) (* h3 h3 h3 h3
) h4 (* h5 h5) (* j2 j2)) (* 1920 (* h2 h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) j2) 
(* 256 (* h2 h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5)) (* 16 (* h2 h2 h2) (* h3 h3 h3
 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 272 (* h2 h2 h2) (* h3 h3 h3 h3
) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1856 (* h2 h2 h2) (* h3 h3 h3 h3) h4 
h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 6880 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 h6 
(* j2 j2 j2 j2 j2 j2)) (* 15504 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 
j2 j2 j2)) (* 22224 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 
20384 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 11584 (* h2 h2 h2) 
(* h3 h3 h3 h3) h4 h5 h6 (* j2 j2)) (* 3712 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 
h6 j2) (* 512 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 h6) (* 16 (* h2 h2 h2) (* h3 h3
 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 192 (* h2 h2 h2) (* h3 
h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 992 (* h2 h2 h2) (* h3 h3
 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2880 (* h2 h2 h2) (* h3 h3 h3 
h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 5136 (* h2 h2 h2) (* h3 h3 h3 h3) h4 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 5760 (* h2 h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6) 
(* j2 j2 j2 j2)) (* 3968 (* h2 h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2))
 (* 1536 (* h2 h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2)) (* 256 (* h2 h2 h2
) (* h3 h3 h3 h3) h4 (* h6 h6) j2) (* 28 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 436 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5)
 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2648 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 8600 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 16812 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* 20772 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)
) (* 16352 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 7952 (* h2
 h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2)) (* 2176 (* h2 h2 h2) (* h3 h3 h3
 h3) (* h5 h5) h6 j2) (* 256 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6) (* 56 
(* h2 h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 648
 (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3264 
(* h2 h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 9392 (* 
h2 h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 17016 (* h2 h2 
h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 20136 (* h2 h2 h2) (* h3
 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 15568 (* h2 h2 h2) (* h3 h3 h3 h3) 
h5 (* h6 h6) (* j2 j2 j2)) (* 7584 (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* 
j2 j2)) (* 2112 (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) j2) (* 256 (* h2 h2 h2
) (* h3 h3 h3 h3) h5 (* h6 h6)) (* 8 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 
(* j2 j2 j2 j2 j2 j2 j2)) (* 112 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2
 j2 j2 j2 j2 j2)) (* 576 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 
j2 j2)) (* 1488 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 
2136 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 1728 (* h2 h2 h2
) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2)) (* 736 (* h2 h2 h2) (* h3 h3 h3) (* h4
 h4 h4) h5 j2) (* 128 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5) (* 16 (* h2 h2 
h2) (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 144 (* h2 h2 h2) 
(* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 528 (* h2 h2 h2) (* h3 h3
 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 1008 (* h2 h2 h2) (* h3 h3 h3) (* h4
 h4 h4) h6 (* j2 j2 j2 j2)) (* 1056 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4 h4) h6 
(* j2 j2 j2)) (* 576 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2)) (* 128
 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4 h4) h6 j2) (* 14 (* h2 h2 h2) (* h3 h3 h3) 
(* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 214 (* h2 h2 h2) (* h3 h3 h3
) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1256 (* h2 h2 h2) (* h3 h3 h3
) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 3852 (* h2 h2 h2) (* h3 h3 h3) 
(* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 6894 (* h2 h2 h2) (* h3 h3 h3) (* h4 
h4) (* h5 h5) (* j2 j2 j2 j2)) (* 7470 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) (* h5
 h5) (* j2 j2 j2)) (* 4828 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 
j2)) (* 1712 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) j2) (* 256 (* h2 h2 
h2) (* h3 h3 h3) (* h4 h4) (* h5 h5)) (* 52 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) 
h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 588 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5
 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2852 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 
(* j2 j2 j2 j2 j2 j2)) (* 7724 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 
j2 j2 j2 j2)) (* 12728 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)
) (* 13016 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 8032 (* h2
 h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 2720 (* h2 h2 h2) (* h3 h3 h3
) (* h4 h4) h5 h6 j2) (* 384 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6) (* 32 
(* h2 h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
320 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
1344 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
3072 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 4128 
(* h2 h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 3264 (* h2 h2 
h2) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 1408 (* h2 h2 h2) (* h3 h3
 h3) (* h4 h4) (* h6 h6) (* j2 j2)) (* 256 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) 
(* h6 h6) j2) (* 4 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 79 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 603 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2
 j2)) (* 2338 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) 
(* 5262 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 7311 
(* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 6371 (* h2 h2 h2) 
(* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2)) (* 3392 (* h2 h2 h2) (* h3 h3 h3) h4 
(* h5 h5 h5) (* j2 j2)) (* 1008 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) j2) 
(* 128 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5)) (* 28 (* h2 h2 h2) (* h3 h3 h3
) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 456 (* h2 h2 h2) (* h3 h3 
h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2940 (* h2 h2 h2) (* h3 h3 
h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 10216 (* h2 h2 h2) (* h3 h3 h3)
 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 21492 (* h2 h2 h2) (* h3 h3 h3) h4 
(* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 28728 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5)
 h6 (* j2 j2 j2 j2)) (* 24596 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2
 j2)) (* 13080 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 3936 (* 
h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 j2) (* 512 (* h2 h2 h2) (* h3 h3 h3) h4 
(* h5 h5) h6) (* 48 (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 600 (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 3272 (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 10192 (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)
) (* 19936 (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
25336 (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 20872 (* h2 
h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 10720 (* h2 h2 h2) (* h3 h3
 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 3104 (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6
) j2) (* 384 (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6)) (* 16 (* h2 h2 h2) (* h3
 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 176 (* h2 h2 h2) (* 
h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 832 (* h2 h2 h2) (* h3
 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2208 (* h2 h2 h2) (* h3 h3 
h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3600 (* h2 h2 h2) (* h3 h3 h3) h4 
(* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 3696 (* h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6 
h6) (* j2 j2 j2 j2)) (* 2336 (* h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 
j2)) (* 832 (* h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2)) (* 128 (* h2 h2
 h2) (* h3 h3 h3) h4 (* h6 h6 h6) j2) (* 28 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 401 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5
 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2187 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 6402 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2)) (* 11402 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2)) (* 12989 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 
j2)) (* 9535 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 4368 (* 
h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2)) (* 1136 (* h2 h2 h2) (* h3 h3 
h3) (* h5 h5 h5) h6 j2) (* 128 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6) (* 112
 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 1170 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 5350 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2
)) (* 14064 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2))
 (* 23436 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
25682 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 18510 
(* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 8460 (* h2 h2 h2)
 (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 2224 (* h2 h2 h2) (* h3 h3 h3) 
(* h5 h5) (* h6 h6) j2) (* 256 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6)) 
(* 56 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 592 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 2728 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
7200 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 12008 
(* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 13136 (* h2 h2 
h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 9432 (* h2 h2 h2) (* h3 h3 
h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 4288 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6 
h6) (* j2 j2)) (* 1120 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) j2) (* 128 (* 
h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6)) (* 2 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4 
h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 24 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 
(* j2 j2 j2 j2 j2)) (* 96 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 
j2)) (* 180 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2)) (* 174 (* h2
 h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2)) (* 84 (* h2 h2 h2) (* h3 h3) (* 
h4 h4 h4 h4) h5 j2) (* 16 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5) (* 4 (* h2 
h2 h2) (* h3 h3) (* h4 h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 28 (* h2 h2 h2) 
(* h3 h3) (* h4 h4 h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 76 (* h2 h2 h2) (* h3 h3) 
(* h4 h4 h4 h4) h6 (* j2 j2 j2 j2)) (* 100 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4 h4
) h6 (* j2 j2 j2)) (* 64 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4 h4) h6 (* j2 j2)) 
(* 16 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4 h4) h6 j2) (* 8 (* h2 h2 h2) (* h3 h3) 
(* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 103 (* h2 h2 h2) (* h3 h3) 
(* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 470 (* h2 h2 h2) (* h3 h3) (* 
h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 1076 (* h2 h2 h2) (* h3 h3) (* h4 h4 
h4) (* h5 h5) (* j2 j2 j2 j2)) (* 1382 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) (* h5
 h5) (* j2 j2 j2)) (* 1013 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 
j2)) (* 396 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) j2) (* 64 (* h2 h2 h2)
 (* h3 h3) (* h4 h4 h4) (* h5 h5)) (* 32 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 268 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 
(* j2 j2 j2 j2 j2 j2)) (* 948 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2
 j2 j2 j2)) (* 1828 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) 
(* 2060 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 1344 (* h2 h2
 h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2)) (* 464 (* h2 h2 h2) (* h3 h3) (* h4
 h4 h4) h5 h6 j2) (* 64 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6) (* 16 (* h2 
h2 h2) (* h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 124 (* h2 
h2 h2) (* h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 388 (* h2 h2 
h2) (* h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 628 (* h2 h2 h2) (* 
h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 556 (* h2 h2 h2) (* h3 h3) (* 
h4 h4 h4) (* h6 h6) (* j2 j2 j2)) (* 256 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) (* 
h6 h6) (* j2 j2)) (* 48 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) (* h6 h6) j2) (* 7 
(* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
100 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
535 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1484
 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 2405 (* h2
 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 2372 (* h2 h2 h2) 
(* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 1405 (* h2 h2 h2) (* h3 h3) 
(* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 460 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 
h5 h5) j2) (* 64 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5)) (* 45 (* h2 h2 
h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 473 (* h2 
h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2117 (* h2 
h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 5278 (* h2 h2 
h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 8023 (* h2 h2 h2) 
(* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 7613 (* h2 h2 h2) (* h3 h3)
 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 4399 (* h2 h2 h2) (* h3 h3) (* h4 h4) 
(* h5 h5) h6 (* j2 j2)) (* 1412 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 j2
) (* 192 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6) (* 58 (* h2 h2 h2) (* h3
 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 530 (* h2 h2 h2) (* 
h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2100 (* h2 h2 h2) (* 
h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4700 (* h2 h2 h2) (* h3 
h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 6466 (* h2 h2 h2) (* h3 h3) 
(* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 5562 (* h2 h2 h2) (* h3 h3) (* h4 h4)
 h5 (* h6 h6) (* j2 j2 j2)) (* 2896 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6
) (* j2 j2)) (* 824 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6) j2) (* 96 (* 
h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6)) (* 16 (* h2 h2 h2) (* h3 h3) (* h4 
h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 140 (* h2 h2 h2) (* h3 h3) (* 
h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 512 (* h2 h2 h2) (* h3 h3) (* 
h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1016 (* h2 h2 h2) (* h3 h3) (* h4 
h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1184 (* h2 h2 h2) (* h3 h3) (* h4 h4) 
(* h6 h6 h6) (* j2 j2 j2 j2)) (* 812 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h6 h6 
h6) (* j2 j2 j2)) (* 304 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2)
) (* 48 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h6 h6 h6) j2) (* (* h2 h2 h2) (* h3 
h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 19 (* h2 h2 h2) (* h3 
h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 137 (* h2 h2 h2) (* h3 h3
) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 491 (* h2 h2 h2) (* h3 h3) h4 
(* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1011 (* h2 h2 h2) (* h3 h3) h4 (* h5 
h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 1281 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) 
(* j2 j2 j2 j2)) (* 1019 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2))
 (* 497 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2)) (* 136 (* h2 h2 h2)
 (* h3 h3) h4 (* h5 h5 h5 h5) j2) (* 16 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5
)) (* 14 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2
)) (* 214 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2))
 (* 1270 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
4038 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 7778 
(* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 9554 (* h2 h2 
h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 7554 (* h2 h2 h2) (* h3 h3)
 h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 3730 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5)
 h6 (* j2 j2)) (* 1048 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 j2) (* 128 (* 
h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6) (* 41 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5
) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 489 (* h2 h2 h2) (* h3 h3) h4 (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2494 (* h2 h2 h2) (* h3 h3) h4 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 7209 (* h2 h2 h2) (* h3 h3) h4 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 13077 (* h2 h2 h2) (* h3 h3) h4 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 15471 (* h2 h2 h2) (* h3 h3) h4 (* h5
 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 11944 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* 
h6 h6) (* j2 j2 j2)) (* 5799 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2
 j2)) (* 1604 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) j2) (* 192 (* h2 h2 
h2) (* h3 h3) h4 (* h5 h5) (* h6 h6)) (* 28 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 300 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6
 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1408 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3792 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 6444 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* 
j2 j2 j2 j2 j2)) (* 7148 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 
j2)) (* 5160 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 2328 (* 
h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2)) (* 592 (* h2 h2 h2) (* h3 h3) 
h4 h5 (* h6 h6 h6) j2) (* 64 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6)) (* 4 (* 
h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 40 (* 
h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 172 (* h2
 h2 h2) (* h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 416 (* h2 h2 
h2) (* h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 620 (* h2 h2 h2) (* 
h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 584 (* h2 h2 h2) (* h3 h3) h4 
(* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 340 (* h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6 h6
) (* j2 j2 j2)) (* 112 (* h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2)) (* 
16 (* h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6 h6) j2) (* 7 (* h2 h2 h2) (* h3 h3) (* 
h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 95 (* h2 h2 h2) (* h3 h3) (* 
h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 479 (* h2 h2 h2) (* h3 h3) (* h5
 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1287 (* h2 h2 h2) (* h3 h3) (* h5 h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 2101 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2)) (* 2197 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 
j2 j2 j2)) (* 1485 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 
629 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 152 (* h2 h2 h2) (* 
h3 h3) (* h5 h5 h5 h5) h6 j2) (* 16 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6) 
(* 56 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 529 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 2202 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 5303 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 8144 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 8271 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 5554 
(* h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 2377 (* h2 h2 h2)
 (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 588 (* h2 h2 h2) (* h3 h3) (* h5
 h5 h5) (* h6 h6) j2) (* 64 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6)) (* 63
 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 575 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 2331 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 5503 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 8329 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
8373 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 5585 (* 
h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 2381 (* h2 h2 h2) 
(* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 588 (* h2 h2 h2) (* h3 h3) (* h5 
h5) (* h6 h6 h6) j2) (* 64 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6)) (* 14 
(* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 134
 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 562 
(* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1358 (* 
h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2086 (* h2 h2 
h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2114 (* h2 h2 h2) (* h3 
h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 1414 (* h2 h2 h2) (* h3 h3) h5 (* h6 
h6 h6 h6) (* j2 j2 j2)) (* 602 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 
j2)) (* 148 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) j2) (* 16 (* h2 h2 h2) (* 
h3 h3) h5 (* h6 h6 h6 h6)) (* (* h2 h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2
 j2 j2 j2 j2)) (* 11 (* h2 h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2
)) (* 38 (* h2 h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 62 (* h2 
h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 53 (* h2 h2 h2) h3 (* h4 h4
 h4 h4) (* h5 h5) (* j2 j2)) (* 23 (* h2 h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) j2)
 (* 4 (* h2 h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5)) (* 5 (* h2 h2 h2) h3 (* h4 h4 
h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 28 (* h2 h2 h2) h3 (* h4 h4 h4 h4) h5 h6 
(* j2 j2 j2 j2 j2)) (* 62 (* h2 h2 h2) h3 (* h4 h4 h4 h4) h5 h6 (* j2 j2 j2 j2))
 (* 68 (* h2 h2 h2) h3 (* h4 h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 37 (* h2 h2 h2) h3
 (* h4 h4 h4 h4) h5 h6 (* j2 j2)) (* 8 (* h2 h2 h2) h3 (* h4 h4 h4 h4) h5 h6 j2)
 (* 2 (* h2 h2 h2) h3 (* h4 h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 10 (* 
h2 h2 h2) h3 (* h4 h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 18 (* h2 h2 h2) h3
 (* h4 h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 14 (* h2 h2 h2) h3 (* h4 h4 h4 h4
) (* h6 h6) (* j2 j2 j2)) (* 4 (* h2 h2 h2) h3 (* h4 h4 h4 h4) (* h6 h6) (* j2 
j2)) (* 2 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 24 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 98 (* 
h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 200 (* h2 h2 h2) 
h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 230 (* h2 h2 h2) h3 (* h4 h4 h4
) (* h5 h5 h5) (* j2 j2 j2)) (* 152 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) 
(* j2 j2)) (* 54 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) j2) (* 8 (* h2 h2 h2)
 h3 (* h4 h4 h4) (* h5 h5 h5)) (* 16 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 118 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2
 j2 j2 j2 j2 j2)) (* 372 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 
j2 j2)) (* 644 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 656
 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 390 (* h2 h2 h2) h3 
(* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 124 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 
h5) h6 j2) (* 16 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6) (* 18 (* h2 h2 h2) 
h3 (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 118 (* h2 h2 h2) h3 
(* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 317 (* h2 h2 h2) h3 (* h4 h4
 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 447 (* h2 h2 h2) h3 (* h4 h4 h4) h5 (* 
h6 h6) (* j2 j2 j2 j2)) (* 349 (* h2 h2 h2) h3 (* h4 h4 h4) h5 (* h6 h6) (* j2 
j2 j2)) (* 143 (* h2 h2 h2) h3 (* h4 h4 h4) h5 (* h6 h6) (* j2 j2)) (* 24 (* h2 
h2 h2) h3 (* h4 h4 h4) h5 (* h6 h6) j2) (* 4 (* h2 h2 h2) h3 (* h4 h4 h4) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 24 (* h2 h2 h2) h3 (* h4 h4 h4) (* h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2)) (* 56 (* h2 h2 h2) h3 (* h4 h4 h4) (* h6 h6 h6) (* j2 j2
 j2 j2 j2)) (* 64 (* h2 h2 h2) h3 (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 
36 (* h2 h2 h2) h3 (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2)) (* 8 (* h2 h2 h2) h3 
(* h4 h4 h4) (* h6 h6 h6) (* j2 j2)) (* (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5
) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 13 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 61 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 
j2 j2 j2 j2 j2)) (* 149 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2
 j2)) (* 215 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 191 
(* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 103 (* h2 h2 h2) h3 
(* h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 31 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5
 h5) j2) (* 4 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5)) (* 13 (* h2 h2 h2) h3 
(* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 121 (* h2 h2 h2) h3 
(* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 484 (* h2 h2 h2) h3 (* h4
 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 1084 (* h2 h2 h2) h3 (* h4 h4) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 1485 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 
h5) h6 (* j2 j2 j2 j2)) (* 1273 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 
j2 j2)) (* 666 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 194 (* h2
 h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 j2) (* 24 (* h2 h2 h2) h3 (* h4 h4) (* h5 
h5 h5) h6) (* 29 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 236 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 843 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 1714 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)
) (* 2155 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 1704
 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 821 (* h2 h2 h2)
 h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 218 (* h2 h2 h2) h3 (* h4 h4) 
(* h5 h5) (* h6 h6) j2) (* 24 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6)) (* 
17 (* h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 131
 (* h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 425 (* 
h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 754 (* h2 h2 h2
) h3 (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 791 (* h2 h2 h2) h3 (* h4 
h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 491 (* h2 h2 h2) h3 (* h4 h4) h5 (* h6 
h6 h6) (* j2 j2 j2)) (* 167 (* h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6 h6) (* j2 j2))
 (* 24 (* h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6 h6) j2) (* 2 (* h2 h2 h2) h3 (* h4 
h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 14 (* h2 h2 h2) h3 (* h4 h4)
 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 40 (* h2 h2 h2) h3 (* h4 h4) (* h6
 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 60 (* h2 h2 h2) h3 (* h4 h4) (* h6 h6 h6 h6
) (* j2 j2 j2 j2 j2)) (* 50 (* h2 h2 h2) h3 (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 
j2 j2)) (* 22 (* h2 h2 h2) h3 (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 4 (* h2
 h2 h2) h3 (* h4 h4) (* h6 h6 h6 h6) (* j2 j2)) (* 2 (* h2 h2 h2) h3 h4 (* h5 h5
 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 28 (* h2 h2 h2) h3 h4 (* h5 h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 148 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) h6
 (* j2 j2 j2 j2 j2 j2 j2)) (* 420 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2
 j2 j2 j2 j2)) (* 728 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) 
(* 812 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 588 (* h2 h2 h2
) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 268 (* h2 h2 h2) h3 h4 (* h5 h5 h5 
h5) h6 (* j2 j2)) (* 70 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) h6 j2) (* 8 (* h2 h2 
h2) h3 h4 (* h5 h5 h5 h5) h6) (* 12 (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 126 (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 578 (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 1518 (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 2514 (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2)) (* 2722 (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) 
(* 1926 (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 858 (* h2 h2 
h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 218 (* h2 h2 h2) h3 h4 (* h5 h5 
h5) (* h6 h6) j2) (* 24 (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6)) (* 14 (* h2 
h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 136 (* h2
 h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 582 (* h2 
h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1436 (* h2 h2 
h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2246 (* h2 h2 h2) h3 
h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2304 (* h2 h2 h2) h3 h4 (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1546 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2)) (* 652 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2)) 
(* 156 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) j2) (* 16 (* h2 h2 h2) h3 h4 
(* h5 h5) (* h6 h6 h6)) (* 4 (* h2 h2 h2) h3 h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 37 (* h2 h2 h2) h3 h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 146 (* h2 h2 h2) h3 h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 323 (* h2 h2 h2) h3 h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 440 
(* h2 h2 h2) h3 h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 379 (* h2 h2 h2) h3
 h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 202 (* h2 h2 h2) h3 h4 h5 (* h6 h6 h6
 h6) (* j2 j2 j2)) (* 61 (* h2 h2 h2) h3 h4 h5 (* h6 h6 h6 h6) (* j2 j2)) (* 8 
(* h2 h2 h2) h3 h4 h5 (* h6 h6 h6 h6) j2) (* 7 (* h2 h2 h2) h3 (* h5 h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 60 (* h2 h2 h2) h3 (* h5 h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 228 (* h2 h2 h2) h3 (* h5 h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 504 (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* h6
 h6) (* j2 j2 j2 j2 j2 j2)) (* 714 (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2)) (* 672 (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2
)) (* 420 (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 168 (* h2 
h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 39 (* h2 h2 h2) h3 (* h5 h5 h5
 h5) (* h6 h6) j2) (* 4 (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6)) (* 14 (* h2 
h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 120 (* h2
 h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 456 (* h2 
h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1008 (* h2 h2 
h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1428 (* h2 h2 h2) h3 
(* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1344 (* h2 h2 h2) h3 (* h5 h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 840 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6 
h6) (* j2 j2 j2)) (* 336 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) 
(* 78 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) j2) (* 8 (* h2 h2 h2) h3 (* h5 
h5 h5) (* h6 h6 h6)) (* 7 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 60 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 228 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2
 j2 j2 j2)) (* 504 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 714 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 672
 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 420 (* h2 h2 h2) 
h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 168 (* h2 h2 h2) h3 (* h5 h5) (* 
h6 h6 h6 h6) (* j2 j2)) (* 39 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) j2) (* 4
 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6)) (* (* h2 h2 h2) (* h4 h4 h4 h4) (* 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 5 (* h2 h2 h2) (* h4 h4 h4 h4) (* h5 h5) h6 
(* j2 j2 j2 j2 j2)) (* 10 (* h2 h2 h2) (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 
j2)) (* 10 (* h2 h2 h2) (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 5 (* h2 h2
 h2) (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* (* h2 h2 h2) (* h4 h4 h4 h4) (* 
h5 h5) h6 j2) (* (* h2 h2 h2) (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)
) (* 4 (* h2 h2 h2) (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 6 (* h2 
h2 h2) (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 4 (* h2 h2 h2) (* h4 h4 
h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* (* h2 h2 h2) (* h4 h4 h4 h4) h5 (* h6 h6) 
(* j2 j2)) (* 2 (* h2 h2 h2) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2)) (* 12 (* h2 h2 h2) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
30 (* h2 h2 h2) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 40 (* h2 h2 
h2) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 30 (* h2 h2 h2) (* h4 h4 h4
) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 12 (* h2 h2 h2) (* h4 h4 h4) (* h5 h5 h5) h6 
(* j2 j2)) (* 2 (* h2 h2 h2) (* h4 h4 h4) (* h5 h5 h5) h6 j2) (* 4 (* h2 h2 h2) 
(* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 23 (* h2 h2 h2) 
(* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 55 (* h2 h2 h2) (* h4
 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 70 (* h2 h2 h2) (* h4 h4 h4) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 50 (* h2 h2 h2) (* h4 h4 h4) (* h5 h5) 
(* h6 h6) (* j2 j2 j2)) (* 19 (* h2 h2 h2) (* h4 h4 h4) (* h5 h5) (* h6 h6) (* 
j2 j2)) (* 3 (* h2 h2 h2) (* h4 h4 h4) (* h5 h5) (* h6 h6) j2) (* 2 (* h2 h2 h2)
 (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 10 (* h2 h2 h2) (* h4
 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 20 (* h2 h2 h2) (* h4 h4 h4) 
h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 20 (* h2 h2 h2) (* h4 h4 h4) h5 (* h6 h6 
h6) (* j2 j2 j2 j2)) (* 10 (* h2 h2 h2) (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2
)) (* 2 (* h2 h2 h2) (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2)) (* (* h2 h2 h2) (* 
h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 7 (* h2 h2 h2) (* h4 
h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 21 (* h2 h2 h2) (* h4 h4) 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 35 (* h2 h2 h2) (* h4 h4) (* h5 h5 
h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 35 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5 h5) h6 
(* j2 j2 j2 j2)) (* 21 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) 
(* 7 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2)) (* (* h2 h2 h2) (* h4 
h4) (* h5 h5 h5 h5) h6 j2) (* 4 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 28 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2)) (* 84 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 140 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2)) (* 140 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2)) (* 84 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 28 
(* h2 h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 4 (* h2 h2 h2) (* h4
 h4) (* h5 h5 h5) (* h6 h6) j2) (* 4 (* h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 27 (* h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6
 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 78 (* h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 125 (* h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2)) (* 120 (* h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2)) (* 69 (* h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 
22 (* h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 3 (* h2 h2 h2) 
(* h4 h4) (* h5 h5) (* h6 h6 h6) j2) (* (* h2 h2 h2) (* h4 h4) h5 (* h6 h6 h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6 (* h2 h2 h2) (* h4 h4) h5 (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 15 (* h2 h2 h2) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 20 (* h2 h2 h2) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 
j2)) (* 15 (* h2 h2 h2) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 6 (* h2
 h2 h2) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* (* h2 h2 h2) (* h4 h4) h5 
(* h6 h6 h6 h6) (* j2 j2)) (* (* h2 h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2
 j2 j2 j2 j2 j2 j2 j2)) (* 8 (* h2 h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 28 (* h2 h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 56 (* h2 h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 70 (* h2 h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 56 
(* h2 h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 28 (* h2 h2 h2) h4
 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 8 (* h2 h2 h2) h4 (* h5 h5 h5 h5) 
(* h6 h6) (* j2 j2)) (* (* h2 h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6) j2) (* 2 (* h2
 h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 16 (* h2
 h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 56 (* h2 h2
 h2) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 112 (* h2 h2 h2) 
h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 140 (* h2 h2 h2) h4 (* h5
 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 112 (* h2 h2 h2) h4 (* h5 h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2)) (* 56 (* h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2
 j2 j2)) (* 16 (* h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 2 (* h2 
h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6) j2) (* (* h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8 (* h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 28 (* h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2)) (* 56 (* h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2
 j2 j2 j2 j2 j2)) (* 70 (* h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2
 j2)) (* 56 (* h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 28 (* 
h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 8 (* h2 h2 h2) h4 (* h5 
h5) (* h6 h6 h6 h6) (* j2 j2)) (* (* h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6 h6) j2) 
(* 8 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 120 
(* h2 h2) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 680 (* h2 h2
) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 1960 (* h2 h2) (* h3 h3
 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 3152 (* h2 h2) (* h3 h3 h3 h3) (* h4
 h4 h4) h5 (* j2 j2 j2)) (* 2848 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2
 j2)) (* 1344 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4 h4) h5 j2) (* 256 (* h2 h2) (* 
h3 h3 h3 h3) (* h4 h4 h4) h5) (* 16 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4 h4) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 160 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4 h4) h6 (* j2
 j2 j2 j2 j2 j2)) (* 656 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 
j2 j2)) (* 1408 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2)) (* 
1664 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2)) (* 1024 (* h2 h2) 
(* h3 h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2)) (* 256 (* h2 h2) (* h3 h3 h3 h3) (* 
h4 h4 h4) h6 j2) (* 8 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 152 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 
j2 j2 j2 j2 j2)) (* 1128 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 
j2 j2 j2 j2)) (* 4264 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 
j2 j2)) (* 9104 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) 
(* 11392 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 8256 (* 
h2 h2) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 3200 (* h2 h2) (* h3 h3
 h3 h3) (* h4 h4) (* h5 h5) j2) (* 512 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) (* h5
 h5)) (* 32 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 480 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 2888 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 9280
 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 17576 (* h2 h2
) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 20176 (* h2 h2) (* h3 h3 
h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 13728 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4
) h5 h6 (* j2 j2)) (* 5056 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 h6 j2) (* 768 
(* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 h6) (* 32 (* h2 h2) (* h3 h3 h3 h3) (* h4
 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 352 (* h2 h2) (* h3 h3 h3 h3) (* 
h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1632 (* h2 h2) (* h3 h3 h3 h3) (* 
h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4128 (* h2 h2) (* h3 h3 h3 h3) (* h4 
h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 6144 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) 
(* h6 h6) (* j2 j2 j2 j2)) (* 5376 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) (* h6 h6)
 (* j2 j2 j2)) (* 2560 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2)) 
(* 512 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) (* h6 h6) j2) (* 2 (* h2 h2) (* h3 h3
 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 48 (* h2 h2) (* h3 h3
 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 460 (* h2 h2) (* h3 h3 
h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 2272 (* h2 h2) (* h3 h3 h3 
h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 6322 (* h2 h2) (* h3 h3 h3 h3) h4 
(* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 10400 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5 
h5) (* j2 j2 j2 j2)) (* 10304 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2
 j2)) (* 6032 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2)) (* 1920 (* h2
 h2) (* h3 h3 h3 h3) h4 (* h5 h5 h5) j2) (* 256 (* h2 h2) (* h3 h3 h3 h3) h4 (* 
h5 h5 h5)) (* 12 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 264 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 2272 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2)) (* 10040 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 25668 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 40128 
(* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 38928 (* h2 h2) 
(* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 22848 (* h2 h2) (* h3 h3 h3 h3)
 h4 (* h5 h5) h6 (* j2 j2)) (* 7424 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) h6 j2
) (* 1024 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) h6) (* 24 (* h2 h2) (* h3 h3 h3
 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 432 (* h2 h2) (* h3 h3 
h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3032 (* h2 h2) (* h3 h3 
h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 11400 (* h2 h2) (* h3 h3 h3 
h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 25824 (* h2 h2) (* h3 h3 h3 h3) h4
 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 36936 (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* h6
 h6) (* j2 j2 j2 j2)) (* 33552 (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 
j2 j2)) (* 18720 (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 5824 
(* h2 h2) (* h3 h3 h3 h3) h4 h5 (* h6 h6) j2) (* 768 (* h2 h2) (* h3 h3 h3 h3) 
h4 h5 (* h6 h6)) (* 16 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 192 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2
 j2 j2 j2 j2)) (* 992 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 2880 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 5136 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
5760 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 3968 (* h2 h2
) (* h3 h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2)) (* 1536 (* h2 h2) (* h3 h3 h3 h3
) h4 (* h6 h6 h6) (* j2 j2)) (* 256 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6 h6) j2
) (* 14 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 260 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 1880 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
6956 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 14874 
(* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 19488 (* h2 h2)
 (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 15904 (* h2 h2) (* h3 h3 h3
 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 7888 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5
) h6 (* j2 j2)) (* 2176 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) h6 j2) (* 256 (* 
h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) h6) (* 56 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5
) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 816 (* h2 h2) (* h3 h3 h3 h3) (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4816 (* h2 h2) (* h3 h3 h3 h3) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 15488 (* h2 h2) (* h3 h3 h3 h3)
 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 30328 (* h2 h2) (* h3 h3 h3 h3) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 37840 (* h2 h2) (* h3 h3 h3 h3) (* h5
 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 30272 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* 
h6 h6) (* j2 j2 j2)) (* 15040 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* 
j2 j2)) (* 4224 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) j2) (* 512 (* h2 
h2) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6)) (* 56 (* h2 h2) (* h3 h3 h3 h3) h5 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 648 (* h2 h2) (* h3 h3 h3 h3) h5 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3264 (* h2 h2) (* h3 h3 h3 h3) h5 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 9392 (* h2 h2) (* h3 h3 h3 h3) h5 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 17016 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6 
h6) (* j2 j2 j2 j2 j2)) (* 20136 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2
 j2 j2 j2)) (* 15568 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 
7584 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 2112 (* h2 h2) (* 
h3 h3 h3 h3) h5 (* h6 h6 h6) j2) (* 256 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6 h6
)) (* 4 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 52 
(* h2 h2) (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 236 (* h2 h2) 
(* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 508 (* h2 h2) (* h3 h3 h3) 
(* h4 h4 h4 h4) h5 (* j2 j2 j2)) (* 560 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4 h4) 
h5 (* j2 j2)) (* 304 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4 h4) h5 j2) (* 64 (* h2 
h2) (* h3 h3 h3) (* h4 h4 h4 h4) h5) (* 8 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4 h4)
 h6 (* j2 j2 j2 j2 j2 j2)) (* 64 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4 h4) h6 (* j2
 j2 j2 j2 j2)) (* 200 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4 h4) h6 (* j2 j2 j2 j2))
 (* 304 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4 h4) h6 (* j2 j2 j2)) (* 224 (* h2 h2)
 (* h3 h3 h3) (* h4 h4 h4 h4) h6 (* j2 j2)) (* 64 (* h2 h2) (* h3 h3 h3) (* h4 
h4 h4 h4) h6 j2) (* 14 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2
 j2 j2 j2 j2)) (* 200 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 
j2 j2 j2)) (* 1056 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 
j2)) (* 2796 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 
4098 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 3372 (* h2 
h2) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 1456 (* h2 h2) (* h3 h3 h3
) (* h4 h4 h4) (* h5 h5) j2) (* 256 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5
)) (* 52 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
524 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 2188 (* 
h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 4884 (* h2 h2) (* 
h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 6256 (* h2 h2) (* h3 h3 h3) (* 
h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 4560 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 h6 
(* j2 j2)) (* 1728 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 h6 j2) (* 256 (* h2 h2
) (* h3 h3 h3) (* h4 h4 h4) h5 h6) (* 32 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 280 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 992 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* h6 
h6) (* j2 j2 j2 j2 j2)) (* 1816 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* h6 h6) 
(* j2 j2 j2 j2)) (* 1808 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 
j2)) (* 928 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2)) (* 192 (* 
h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* h6 h6) j2) (* 8 (* h2 h2) (* h3 h3 h3) (* h4
 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 143 (* h2 h2) (* h3 h3 h3) (* 
h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 977 (* h2 h2) (* h3 h3 h3) (* 
h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 3331 (* h2 h2) (* h3 h3 h3) (* h4 
h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 6387 (* h2 h2) (* h3 h3 h3) (* h4 h4) 
(* h5 h5 h5) (* j2 j2 j2 j2)) (* 7222 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5 
h5) (* j2 j2 j2)) (* 4780 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2
)) (* 1712 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) j2) (* 256 (* h2 h2) 
(* h3 h3 h3) (* h4 h4) (* h5 h5 h5)) (* 56 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 786 (* h2 h2) (* h3 h3 h3) (* h4 h4) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 4342 (* h2 h2) (* h3 h3 h3) (* h4 h4) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 12776 (* h2 h2) (* h3 h3 h3) (* h4 h4) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 22258 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5
 h5) h6 (* j2 j2 j2 j2)) (* 23690 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 
(* j2 j2 j2)) (* 15092 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2)) 
(* 5264 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 j2) (* 768 (* h2 h2) (* h3
 h3 h3) (* h4 h4) (* h5 h5) h6) (* 96 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1028 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4708 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 12004 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* h6
 h6) (* j2 j2 j2 j2 j2)) (* 18556 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) 
(* j2 j2 j2 j2)) (* 17704 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2
 j2)) (* 10096 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 3104 
(* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) j2) (* 384 (* h2 h2) (* h3 h3 h3) 
(* h4 h4) h5 (* h6 h6)) (* 32 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 312 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 1272 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 2808 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2)) (* 3624 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 
j2 j2)) (* 2736 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2)) (* 
1120 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2)) (* 192 (* h2 h2) 
(* h3 h3 h3) (* h4 h4) (* h6 h6 h6) j2) (* (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5
 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 23 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5
 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 208 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5 
h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 950 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2)) (* 2397 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 
j2 j2 j2 j2)) (* 3567 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2))
 (* 3218 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2)) (* 1732 (* h2 
h2) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2)) (* 512 (* h2 h2) (* h3 h3 h3) h4 
(* h5 h5 h5 h5) j2) (* 64 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5 h5)) (* 13 (* h2
 h2) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 269 (* 
h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2122 (* 
h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 8390 (* h2 
h2) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 19165 (* h2 h2) 
(* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 27013 (* h2 h2) (* h3 h3 
h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 23916 (* h2 h2) (* h3 h3 h3) h4 (* h5
 h5 h5) h6 (* j2 j2 j2)) (* 12968 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* 
j2 j2)) (* 3936 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) h6 j2) (* 512 (* h2 h2) 
(* h3 h3 h3) h4 (* h5 h5 h5) h6) (* 42 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 726 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4716 (* h2 h2) (* h3 h3 h3) h4 (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 16302 (* h2 h2) (* h3 h3 h3) h4 (* h5
 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 34060 (* h2 h2) (* h3 h3 h3) h4 (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 45248 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2)) (* 38502 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6
) (* j2 j2 j2)) (* 20308 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2)
) (* 6032 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) j2) (* 768 (* h2 h2) (* 
h3 h3 h3) h4 (* h5 h5) (* h6 h6)) (* 44 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 556 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3016 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 9224 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 17532 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 
j2 j2 j2 j2)) (* 21468 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)
) (* 16912 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 8240 (* h2
 h2) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2)) (* 2240 (* h2 h2) (* h3 h3 h3) 
h4 h5 (* h6 h6 h6) j2) (* 256 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6 h6)) (* 8 
(* h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 88 
(* h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 416 
(* h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1104 (* 
h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1800 (* h2 h2) 
(* h3 h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1848 (* h2 h2) (* h3 h3 
h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 1168 (* h2 h2) (* h3 h3 h3) h4 (* h6 
h6 h6 h6) (* j2 j2 j2)) (* 416 (* h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6 h6) (* j2 
j2)) (* 64 (* h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6 h6) j2) (* 7 (* h2 h2) (* h3 h3
 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 123 (* h2 h2) (* h3 
h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 824 (* h2 h2) (* h3 h3
 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2770 (* h2 h2) (* h3 h3 h3)
 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 5375 (* h2 h2) (* h3 h3 h3) (* h5 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 6431 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) 
h6 (* j2 j2 j2 j2)) (* 4834 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 
j2)) (* 2228 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 576 (* h2 
h2) (* h3 h3 h3) (* h5 h5 h5 h5) h6 j2) (* 64 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5
 h5) h6) (* 63 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 841 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 4380 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 12446 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2
 j2 j2 j2 j2)) (* 21799 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2)) (* 24685 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2
)) (* 18174 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 8412 
(* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 2224 (* h2 h2) (* h3
 h3 h3) (* h5 h5 h5) (* h6 h6) j2) (* 256 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) 
(* h6 h6)) (* 112 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 1170 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 5350 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 14064 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2)) (* 23436 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2)) (* 25682 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2
 j2)) (* 18510 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 
8460 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 2224 (* h2 h2) 
(* h3 h3 h3) (* h5 h5) (* h6 h6 h6) j2) (* 256 (* h2 h2) (* h3 h3 h3) (* h5 h5) 
(* h6 h6 h6)) (* 28 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 296 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 1364 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 3600 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2))
 (* 6004 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 6568 
(* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 4716 (* h2 h2) (* 
h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 2144 (* h2 h2) (* h3 h3 h3) h5 (* 
h6 h6 h6 h6) (* j2 j2)) (* 560 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6 h6) j2) (* 
64 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6 h6)) (* 4 (* h2 h2) (* h3 h3) (* h4 h4 
h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 47 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4
) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 183 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) (* h5
 h5) (* j2 j2 j2 j2)) (* 341 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2
 j2 j2)) (* 333 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2)) (* 164 
(* h2 h2) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) j2) (* 32 (* h2 h2) (* h3 h3) (* 
h4 h4 h4 h4) (* h5 h5)) (* 16 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 h6 (* j2 j2
 j2 j2 j2 j2)) (* 112 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 h6 (* j2 j2 j2 j2 
j2)) (* 304 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 400 
(* h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 256 (* h2 h2) (* h3 
h3) (* h4 h4 h4 h4) h5 h6 (* j2 j2)) (* 64 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) 
h5 h6 j2) (* 8 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 48 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
104 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 96 (* h2 
h2) (* h3 h3) (* h4 h4 h4 h4) (* h6 h6) (* j2 j2 j2)) (* 32 (* h2 h2) (* h3 h3) 
(* h4 h4 h4 h4) (* h6 h6) (* j2 j2)) (* 7 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5
 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 93 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 
h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 442 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5 
h5) (* j2 j2 j2 j2 j2)) (* 1042 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) 
(* j2 j2 j2 j2)) (* 1363 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 
j2)) (* 1009 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2)) (* 396 (* 
h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) j2) (* 64 (* h2 h2) (* h3 h3) (* h4 
h4 h4) (* h5 h5 h5)) (* 45 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2)) (* 417 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 
j2 j2 j2 j2 j2)) (* 1570 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 
j2 j2 j2)) (* 3149 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)
) (* 3655 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 2456 
(* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 880 (* h2 h2) (* h3 
h3) (* h4 h4 h4) (* h5 h5) h6 j2) (* 128 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 
h5) h6) (* 58 (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2
 j2)) (* 448 (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)
) (* 1410 (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
2316 (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 2096 (* 
h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 992 (* h2 h2) (* h3 
h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2)) (* 192 (* h2 h2) (* h3 h3) (* h4 h4 h4)
 h5 (* h6 h6) j2) (* 16 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 112 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 304 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 
j2 j2)) (* 400 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2)) 
(* 256 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2)) (* 64 (* h2 
h2) (* h3 h3) (* h4 h4 h4) (* h6 h6 h6) (* j2 j2)) (* 2 (* h2 h2) (* h3 h3) (* 
h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 34 (* h2 h2) (* h3 h3) 
(* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 216 (* h2 h2) (* h3 h3) 
(* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 668 (* h2 h2) (* h3 h3) (* 
h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 1154 (* h2 h2) (* h3 h3) (* h4 h4)
 (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 1178 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5
 h5 h5) (* j2 j2 j2)) (* 708 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2
 j2)) (* 232 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) j2) (* 32 (* h2 h2) 
(* h3 h3) (* h4 h4) (* h5 h5 h5 h5)) (* 28 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 365 (* h2 h2) (* h3 h3) (* h4 h4) (* 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1834 (* h2 h2) (* h3 h3) (* h4 h4) (* 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 4891 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 
h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 7735 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5)
 h6 (* j2 j2 j2 j2)) (* 7504 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2
 j2 j2)) (* 4383 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 
1412 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 j2) (* 192 (* h2 h2) (* h3 h3
) (* h4 h4) (* h5 h5 h5) h6) (* 82 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 808 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3383 (* h2 h2) (* h3 h3) (* h4 h4) (* h5
 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 7871 (* h2 h2) (* h3 h3) (* h4 h4) (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 11149 (* h2 h2) (* h3 h3) (* h4 h4) (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 9845 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5
) (* h6 h6) (* j2 j2 j2)) (* 5278 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 
h6) (* j2 j2)) (* 1560 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) j2) (* 
192 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6)) (* 56 (* h2 h2) (* h3 h3)
 (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 492 (* h2 h2) (* h3 
h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1820 (* h2 h2) (* h3 
h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3676 (* h2 h2) (* h3 h3)
 (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 4380 (* h2 h2) (* h3 h3) (* h4
 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 3080 (* h2 h2) (* h3 h3) (* h4 h4) h5 
(* h6 h6 h6) (* j2 j2 j2)) (* 1184 (* h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6 h6)
 (* j2 j2)) (* 192 (* h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6 h6) j2) (* 8 (* h2 
h2) (* h3 h3) (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 64 (* h2
 h2) (* h3 h3) (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 208 (* h2 
h2) (* h3 h3) (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 352 (* h2 h2) 
(* h3 h3) (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 328 (* h2 h2) (* h3 
h3) (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 160 (* h2 h2) (* h3 h3) (* h4 
h4) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 32 (* h2 h2) (* h3 h3) (* h4 h4) (* h6 h6 
h6 h6) (* j2 j2)) (* 3 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 60 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 451 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2
 j2 j2)) (* 1668 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)
) (* 3529 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 4588 
(* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 3745 (* h2 h2) (* 
h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 1876 (* h2 h2) (* h3 h3) h4 (* h5 
h5 h5 h5) h6 (* j2 j2)) (* 528 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) h6 j2) (* 
64 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) h6) (* 21 (* h2 h2) (* h3 h3) h4 (* h5
 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 342 (* h2 h2) (* h3 h3) h4 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2037 (* h2 h2) (* h3 h3) 
h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 6435 (* h2 h2) (* h3 h3) 
h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 12311 (* h2 h2) (* h3 h3) h4
 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 15032 (* h2 h2) (* h3 h3) h4 (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 11811 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5
) (* h6 h6) (* j2 j2 j2)) (* 5783 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) 
(* j2 j2)) (* 1604 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) j2) (* 192 (* 
h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6)) (* 36 (* h2 h2) (* h3 h3) h4 (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 438 (* h2 h2) (* h3 h3) h4 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2225 (* h2 h2) (* h3 h3) 
h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 6304 (* h2 h2) (* h3 h3) 
h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 11090 (* h2 h2) (* h3 h3) h4
 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 12634 (* h2 h2) (* h3 h3) h4 (* 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 9345 (* h2 h2) (* h3 h3) h4 (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2)) (* 4328 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6)
 (* j2 j2)) (* 1136 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) j2) (* 128 (* 
h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6)) (* 12 (* h2 h2) (* h3 h3) h4 h5 (* 
h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 132 (* h2 h2) (* h3 h3) h4 h5 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 608 (* h2 h2) (* h3 h3) h4 h5 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1544 (* h2 h2) (* h3 h3) h4 h5 (* 
h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2380 (* h2 h2) (* h3 h3) h4 h5 (* h6 h6 
h6 h6) (* j2 j2 j2 j2 j2)) (* 2292 (* h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6 h6) (* 
j2 j2 j2 j2)) (* 1352 (* h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2)) 
(* 448 (* h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2)) (* 64 (* h2 h2) (* 
h3 h3) h4 h5 (* h6 h6 h6 h6) j2) (* 14 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 176 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 866 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5
) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2316 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5
) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3802 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 4024 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2)) (* 2766 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2
 j2 j2)) (* 1196 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 296
 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) j2) (* 32 (* h2 h2) (* h3 h3) (* 
h5 h5 h5 h5) (* h6 h6)) (* 56 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 529 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2202 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6
 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 5303 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6
 h6) (* j2 j2 j2 j2 j2 j2)) (* 8144 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6
) (* j2 j2 j2 j2 j2)) (* 8271 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2)) (* 5554 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)
) (* 2377 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 588 (* h2 
h2) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) j2) (* 64 (* h2 h2) (* h3 h3) (* h5 h5 
h5) (* h6 h6 h6)) (* 28 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 261 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 1078 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 2587 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 3972 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* 
j2 j2 j2 j2 j2)) (* 4043 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 
j2 j2)) (* 2726 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 
1173 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 292 (* h2 h2) 
(* h3 h3) (* h5 h5) (* h6 h6 h6 h6) j2) (* 32 (* h2 h2) (* h3 h3) (* h5 h5) (* 
h6 h6 h6 h6)) (* (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)
) (* 11 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 38 (* 
h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 62 (* h2 h2) h3 (* h4
 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 53 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 
h5 h5) (* j2 j2)) (* 23 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5 h5) j2) (* 4 (* h2
 h2) h3 (* h4 h4 h4 h4) (* h5 h5 h5)) (* 8 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5
) h6 (* j2 j2 j2 j2 j2 j2)) (* 48 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) h6 (* 
j2 j2 j2 j2 j2)) (* 112 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2
)) (* 128 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 72 (* h2 h2
) h3 (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 16 (* h2 h2) h3 (* h4 h4 h4 h4) 
(* h5 h5) h6 j2) (* 9 (* h2 h2) h3 (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 42 (* h2 h2) h3 (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
73 (* h2 h2) h3 (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 56 (* h2 h2) h3
 (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 16 (* h2 h2) h3 (* h4 h4 h4 h4) 
h5 (* h6 h6) (* j2 j2)) (* 2 (* h2 h2) h3 (* h4 h4 h4 h4) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 8 (* h2 h2) h3 (* h4 h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2))
 (* 10 (* h2 h2) h3 (* h4 h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 4 (* h2 h2)
 h3 (* h4 h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2)) (* (* h2 h2) h3 (* h4 h4 h4) (* 
h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 12 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 
h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 49 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5 h5) 
(* j2 j2 j2 j2 j2)) (* 100 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2
 j2)) (* 115 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 76 (* h2
 h2) h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 27 (* h2 h2) h3 (* h4 h4 h4) 
(* h5 h5 h5 h5) j2) (* 4 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5 h5)) (* 13 (* h2 
h2) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 105 (* h2 h2) 
h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 350 (* h2 h2) h3 (* h4
 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 626 (* h2 h2) h3 (* h4 h4 h4) (* 
h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 649 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) h6 
(* j2 j2 j2)) (* 389 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 124
 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) h6 j2) (* 16 (* h2 h2) h3 (* h4 h4 h4) 
(* h5 h5 h5) h6) (* 29 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2
 j2 j2 j2 j2)) (* 195 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 539 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 785 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 
636 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 272 (* h2 h2)
 h3 (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 48 (* h2 h2) h3 (* h4 h4 h4) 
(* h5 h5) (* h6 h6) j2) (* 17 (* h2 h2) h3 (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2
 j2 j2 j2 j2 j2)) (* 99 (* h2 h2) h3 (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2
 j2 j2)) (* 227 (* h2 h2) h3 (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 257 (* h2 h2) h3 (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 144 (* h2 
h2) h3 (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 32 (* h2 h2) h3 (* h4 h4 h4
) h5 (* h6 h6 h6) (* j2 j2)) (* 2 (* h2 h2) h3 (* h4 h4 h4) (* h6 h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 10 (* h2 h2) h3 (* h4 h4 h4) (* h6 h6 h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 18 (* h2 h2) h3 (* h4 h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)
) (* 14 (* h2 h2) h3 (* h4 h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 4 (* h2 h2
) h3 (* h4 h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 4 (* h2 h2) h3 (* h4 h4) (* 
h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 48 (* h2 h2) h3 (* h4 h4) (* h5 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 217 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5
 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 517 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) h6 
(* j2 j2 j2 j2 j2)) (* 730 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2
 j2)) (* 634 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 333 (* 
h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 97 (* h2 h2) h3 (* h4 h4) 
(* h5 h5 h5 h5) h6 j2) (* 12 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) h6) (* 24 
(* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
209 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
783 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1644
 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2110 (* h2
 h2) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 1689 (* h2 h2) h3 
(* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 819 (* h2 h2) h3 (* h4 h4) (* 
h5 h5 h5) (* h6 h6) (* j2 j2)) (* 218 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* h6 
h6) j2) (* 24 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6)) (* 28 (* h2 h2) h3 
(* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 218 (* h2 h2) 
h3 (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 720 (* h2 h2) 
h3 (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1308 (* h2 h2) h3 
(* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1412 (* h2 h2) h3 (* h4 
h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 906 (* h2 h2) h3 (* h4 h4) (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2)) (* 320 (* h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6 
h6) (* j2 j2)) (* 48 (* h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6 h6) j2) (* 8 (* 
h2 h2) h3 (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 56 (* h2 
h2) h3 (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 160 (* h2 h2) 
h3 (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 240 (* h2 h2) h3 (* h4
 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 200 (* h2 h2) h3 (* h4 h4) h5 (* 
h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 88 (* h2 h2) h3 (* h4 h4) h5 (* h6 h6 h6 h6) 
(* j2 j2 j2)) (* 16 (* h2 h2) h3 (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2)) (* 3 
(* h2 h2) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 45 
(* h2 h2) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 244 
(* h2 h2) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 699 (* h2
 h2) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1212 (* h2 h2) h3
 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1343 (* h2 h2) h3 h4 (* h5 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 960 (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* 
h6 h6) (* j2 j2 j2)) (* 429 (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2))
 (* 109 (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* h6 h6) j2) (* 12 (* h2 h2) h3 h4 (* 
h5 h5 h5 h5) (* h6 h6)) (* 11 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2
 j2 j2 j2 j2 j2 j2 j2)) (* 117 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 531 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2
 j2 j2 j2 j2 j2)) (* 1361 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 2181 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2))
 (* 2271 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1537 (* 
h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 651 (* h2 h2) h3 h4 (* 
h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 156 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6 
h6) j2) (* 16 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6 h6)) (* 6 (* h2 h2) h3 h4 
(* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 60 (* h2 h2) h3 h4 
(* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 250 (* h2 h2) h3 h4 
(* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 576 (* h2 h2) h3 h4 (* h5
 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 810 (* h2 h2) h3 h4 (* h5 h5) (* 
h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 716 (* h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6 h6
) (* j2 j2 j2 j2)) (* 390 (* h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)
) (* 120 (* h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 16 (* h2 h2) h3
 h4 (* h5 h5) (* h6 h6 h6 h6) j2) (* 7 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 60 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 228 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 504 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2)) (* 714 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2)) (* 672 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 420
 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 168 (* h2 h2) h3 (* 
h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 39 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6
 h6) j2) (* 4 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6 h6)) (* 7 (* h2 h2) h3 (* h5
 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 60 (* h2 h2) h3 (* h5
 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 228 (* h2 h2) h3 (* h5 
h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 504 (* h2 h2) h3 (* h5 h5 h5
) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 714 (* h2 h2) h3 (* h5 h5 h5) (* h6 
h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 672 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6 h6) 
(* j2 j2 j2 j2)) (* 420 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) 
(* 168 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 39 (* h2 h2) h3 
(* h5 h5 h5) (* h6 h6 h6 h6) j2) (* 4 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6 h6))
 (* (* h2 h2) (* h4 h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 5 (* h2 
h2) (* h4 h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 10 (* h2 h2) (* h4 h4
 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 10 (* h2 h2) (* h4 h4 h4 h4) (* h5 
h5 h5) h6 (* j2 j2 j2)) (* 5 (* h2 h2) (* h4 h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2)
) (* (* h2 h2) (* h4 h4 h4 h4) (* h5 h5 h5) h6 j2) (* 2 (* h2 h2) (* h4 h4 h4 h4
) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 8 (* h2 h2) (* h4 h4 h4 h4) (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 12 (* h2 h2) (* h4 h4 h4 h4) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2)) (* 8 (* h2 h2) (* h4 h4 h4 h4) (* h5 h5) (* h6 h6) 
(* j2 j2 j2)) (* 2 (* h2 h2) (* h4 h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 
(* h2 h2) (* h4 h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3 (* h2 h2) 
(* h4 h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 3 (* h2 h2) (* h4 h4 h4 
h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* (* h2 h2) (* h4 h4 h4 h4) h5 (* h6 h6 h6
) (* j2 j2 j2)) (* (* h2 h2) (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 6 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 15 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 20 (* h2 
h2) (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 15 (* h2 h2) (* h4 h4 h4
) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 6 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5 h5) 
h6 (* j2 j2)) (* (* h2 h2) (* h4 h4 h4) (* h5 h5 h5 h5) h6 j2) (* 4 (* h2 h2) 
(* h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 23 (* h2 h2) 
(* h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 55 (* h2 h2) (* h4
 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 70 (* h2 h2) (* h4 h4 h4) 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 50 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5
) (* h6 h6) (* j2 j2 j2)) (* 19 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5) (* h6 h6) 
(* j2 j2)) (* 3 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5) (* h6 h6) j2) (* 4 (* h2 h2)
 (* h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 20 (* h2 h2) 
(* h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 40 (* h2 h2) (* h4
 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 40 (* h2 h2) (* h4 h4 h4) 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 20 (* h2 h2) (* h4 h4 h4) (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2)) (* 4 (* h2 h2) (* h4 h4 h4) (* h5 h5) (* h6 h6 h6) 
(* j2 j2)) (* (* h2 h2) (* h4 h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 4 (* h2 h2) (* h4 h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6 (* 
h2 h2) (* h4 h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 4 (* h2 h2) (* h4 
h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* (* h2 h2) (* h4 h4 h4) h5 (* h6 h6
 h6 h6) (* j2 j2 j2)) (* 2 (* h2 h2) (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 14 (* h2 h2) (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2
 j2 j2 j2 j2 j2 j2)) (* 42 (* h2 h2) (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 70 (* h2 h2) (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2
 j2 j2)) (* 70 (* h2 h2) (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) 
(* 42 (* h2 h2) (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 14 (* h2 h2
) (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 2 (* h2 h2) (* h4 h4) (* h5 
h5 h5 h5) (* h6 h6) j2) (* 4 (* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 27 (* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 78 (* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2)) (* 125 (* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2)) (* 120 (* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2))
 (* 69 (* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 22 (* h2 
h2) (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 3 (* h2 h2) (* h4 h4) (* 
h5 h5 h5) (* h6 h6 h6) j2) (* 2 (* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 12 (* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2)) (* 30 (* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 40 (* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2
 j2 j2 j2 j2)) (* 30 (* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 
j2)) (* 12 (* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 2 (* 
h2 h2) (* h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* (* h2 h2) h4 (* h5 h5 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8 (* h2 h2) h4 (* h5 h5 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 28 (* h2 h2) h4 (* h5 h5 h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 56 (* h2 h2) h4 (* h5 h5 h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 70 (* h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2)) (* 56 (* h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2
 j2 j2)) (* 28 (* h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 8 (* 
h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* (* h2 h2) h4 (* h5 h5 h5 h5
) (* h6 h6 h6) j2) (* (* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 8 (* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 28 (* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 56 (* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 70 (* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 56 (* h2 
h2) h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 28 (* h2 h2) h4 (* h5 h5
 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 8 (* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6 h6
) (* j2 j2)) (* (* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6 h6) j2) (* 4 h2 (* h3 h3 
h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 72 h2 (* h3 h3 h3 h3)
 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 492 h2 (* h3 h3 h3 h3) (* h4 
h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 1640 h2 (* h3 h3 h3 h3) (* h4 h4 h4) (* 
h5 h5) (* j2 j2 j2 j2)) (* 2912 h2 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 
j2 j2)) (* 2784 h2 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 1344 h2 
(* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) j2) (* 256 h2 (* h3 h3 h3 h3) (* h4 h4 h4
) (* h5 h5)) (* 16 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2
)) (* 208 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 1024 
h2 (* h3 h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 2496 h2 (* h3 h3 h3
 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 3200 h2 (* h3 h3 h3 h3) (* h4 h4 h4)
 h5 h6 (* j2 j2 j2)) (* 2048 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2)) 
(* 512 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h5 h6 j2) (* 16 h2 (* h3 h3 h3 h3) (* h4 
h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 144 h2 (* h3 h3 h3 h3) (* h4 h4 h4
) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 512 h2 (* h3 h3 h3 h3) (* h4 h4 h4) (* h6 
h6) (* j2 j2 j2 j2 j2)) (* 896 h2 (* h3 h3 h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 
j2 j2 j2)) (* 768 h2 (* h3 h3 h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2)) (* 256
 h2 (* h3 h3 h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2)) (* 2 h2 (* h3 h3 h3 h3) 
(* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 44 h2 (* h3 h3 h3 h3) (* 
h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 382 h2 (* h3 h3 h3 h3) (* h4 h4
) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1676 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5
 h5 h5) (* j2 j2 j2 j2 j2)) (* 4008 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) 
(* j2 j2 j2 j2)) (* 5392 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2))
 (* 4064 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 1600 h2 (* h3 
h3 h3 h3) (* h4 h4) (* h5 h5 h5) j2) (* 256 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 
h5 h5)) (* 12 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 240 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 1840 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 7076
 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 15192 h2 (* h3
 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 18912 h2 (* h3 h3 h3 h3) 
(* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 13472 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5
 h5) h6 (* j2 j2)) (* 5056 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 j2) (* 768 
h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6) (* 24 h2 (* h3 h3 h3 h3) (* h4 h4) h5
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 384 h2 (* h3 h3 h3 h3) (* h4 h4) h5 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2264 h2 (* h3 h3 h3 h3) (* h4 h4) h5 (* 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6736 h2 (* h3 h3 h3 h3) (* h4 h4) h5 (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* 11168 h2 (* h3 h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 
j2 j2)) (* 10432 h2 (* h3 h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 5120
 h2 (* h3 h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 1024 h2 (* h3 h3 h3 h3)
 (* h4 h4) h5 (* h6 h6) j2) (* 16 h2 (* h3 h3 h3 h3) (* h4 h4) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 160 h2 (* h3 h3 h3 h3) (* h4 h4) (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2 j2)) (* 656 h2 (* h3 h3 h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 1408 h2 (* h3 h3 h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 
j2)) (* 1664 h2 (* h3 h3 h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1024 
h2 (* h3 h3 h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2)) (* 256 h2 (* h3 h3 h3 h3
) (* h4 h4) (* h6 h6 h6) (* j2 j2)) (* 24 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 424 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2)) (* 2840 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2
 j2 j2)) (* 9368 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
17104 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 18176 h2 (* h3 
h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 11200 h2 (* h3 h3 h3 h3) h4 (* h5 
h5 h5) h6 (* j2 j2)) (* 3712 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 j2) (* 512 h2
 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6) (* 96 h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1320 h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 7048 h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 19720 h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2)) (* 32152 h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)
) (* 31600 h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 18400 h2 
(* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 5824 h2 (* h3 h3 h3 h3) h4 
(* h5 h5) (* h6 h6) j2) (* 768 h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6)) (* 96 
h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 928 h2 (* 
h3 h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3744 h2 (* h3 h3 h3
 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 8160 h2 (* h3 h3 h3 h3) h4 h5 
(* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 10368 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6 h6) 
(* j2 j2 j2 j2)) (* 7680 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 
3072 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2)) (* 512 h2 (* h3 h3 h3 h3) 
h4 h5 (* h6 h6 h6) j2) (* 84 h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 1028 h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 4788 h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 11628 h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)
) (* 16520 h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 14272 
h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 7392 h2 (* h3 h3 h3 
h3) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 2112 h2 (* h3 h3 h3 h3) (* h5 h5 h5) 
(* h6 h6) j2) (* 256 h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6)) (* 168 h2 (* h3 
h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1552 h2 (* h3 
h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 6096 h2 (* h3 h3 
h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 13312 h2 (* h3 h3 h3 h3)
 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 17704 h2 (* h3 h3 h3 h3) (* h5 h5
) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 14704 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2)) (* 7456 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2)) 
(* 2112 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) j2) (* 256 h2 (* h3 h3 h3 h3) 
(* h5 h5) (* h6 h6 h6)) (* 2 h2 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 
j2 j2 j2 j2)) (* 32 h2 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)
) (* 182 h2 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 456 h2 
(* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 544 h2 (* h3 h3 h3) (* 
h4 h4 h4 h4) (* h5 h5) (* j2 j2)) (* 304 h2 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 
h5) j2) (* 64 h2 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5)) (* 8 h2 (* h3 h3 h3) 
(* h4 h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 88 h2 (* h3 h3 h3) (* h4 h4 h4 
h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 336 h2 (* h3 h3 h3) (* h4 h4 h4 h4) h5 h6 (* j2
 j2 j2 j2)) (* 576 h2 (* h3 h3 h3) (* h4 h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 448 h2
 (* h3 h3 h3) (* h4 h4 h4 h4) h5 h6 (* j2 j2)) (* 128 h2 (* h3 h3 h3) (* h4 h4 
h4 h4) h5 h6 j2) (* 8 h2 (* h3 h3 h3) (* h4 h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 56 h2 (* h3 h3 h3) (* h4 h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
144 h2 (* h3 h3 h3) (* h4 h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 160 h2 (* h3 
h3 h3) (* h4 h4 h4 h4) (* h6 h6) (* j2 j2 j2)) (* 64 h2 (* h3 h3 h3) (* h4 h4 h4
 h4) (* h6 h6) (* j2 j2)) (* 4 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 
j2 j2 j2 j2 j2 j2)) (* 68 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 
j2 j2 j2)) (* 428 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) 
(* 1276 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 2000 h2 
(* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 1696 h2 (* h3 h3 h3) (* 
h4 h4 h4) (* h5 h5 h5) (* j2 j2)) (* 736 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 
h5) j2) (* 128 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5)) (* 28 h2 (* h3 h3 h3) 
(* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 360 h2 (* h3 h3 h3) (* h4
 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 1744 h2 (* h3 h3 h3) (* h4 h4 h4)
 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 4300 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5)
 h6 (* j2 j2 j2 j2)) (* 5896 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 
j2)) (* 4480 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 1728 h2 (* 
h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 j2) (* 256 h2 (* h3 h3 h3) (* h4 h4 h4) (* 
h5 h5) h6) (* 48 h2 (* h3 h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 452 h2 (* h3 h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
1716 h2 (* h3 h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 3344 h2 
(* h3 h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 3504 h2 (* h3 h3 h3) 
(* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 1856 h2 (* h3 h3 h3) (* h4 h4 h4) h5 
(* h6 h6) (* j2 j2)) (* 384 h2 (* h3 h3 h3) (* h4 h4 h4) h5 (* h6 h6) j2) (* 16 
h2 (* h3 h3 h3) (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 128 h2 
(* h3 h3 h3) (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 400 h2 (* h3 h3
 h3) (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 608 h2 (* h3 h3 h3) (* h4 
h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 448 h2 (* h3 h3 h3) (* h4 h4 h4) (* h6 
h6 h6) (* j2 j2 j2)) (* 128 h2 (* h3 h3 h3) (* h4 h4 h4) (* h6 h6 h6) (* j2 j2))
 (* h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 21
 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 171 h2 
(* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 687 h2 (* h3 h3
 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 1468 h2 (* h3 h3 h3) (* h4
 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 1764 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5
 h5 h5) (* j2 j2 j2)) (* 1200 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2
)) (* 432 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) j2) (* 64 h2 (* h3 h3 h3) 
(* h4 h4) (* h5 h5 h5 h5)) (* 13 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 243 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2)) (* 1696 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2)) (* 5794 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2)) (* 11024 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 
12264 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 7904 h2 (* h3 
h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 2720 h2 (* h3 h3 h3) (* h4 h4) 
(* h5 h5 h5) h6 j2) (* 384 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6) (* 42 h2 
(* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 642 
h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3540 
h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 10102 h2
 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 16838 h2 (* 
h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 16908 h2 (* h3 h3 h3
) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 9952 h2 (* h3 h3 h3) (* h4 h4) 
(* h5 h5) (* h6 h6) (* j2 j2)) (* 3104 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6
 h6) j2) (* 384 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6)) (* 44 h2 (* h3 h3
 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 468 h2 (* h3 h3 
h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2068 h2 (* h3 h3 h3) 
(* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4908 h2 (* h3 h3 h3) (* h4 
h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 6736 h2 (* h3 h3 h3) (* h4 h4) h5 (* 
h6 h6 h6) (* j2 j2 j2 j2)) (* 5328 h2 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* 
j2 j2 j2)) (* 2240 h2 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2)) (* 384 
h2 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6 h6) j2) (* 8 h2 (* h3 h3 h3) (* h4 h4) (* 
h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 72 h2 (* h3 h3 h3) (* h4 h4) (* h6 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 264 h2 (* h3 h3 h3) (* h4 h4) (* h6 h6 h6
 h6) (* j2 j2 j2 j2 j2 j2)) (* 504 h2 (* h3 h3 h3) (* h4 h4) (* h6 h6 h6 h6) (* 
j2 j2 j2 j2 j2)) (* 528 h2 (* h3 h3 h3) (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2
)) (* 288 h2 (* h3 h3 h3) (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 64 h2 (* h3
 h3 h3) (* h4 h4) (* h6 h6 h6 h6) (* j2 j2)) (* 12 h2 (* h3 h3 h3) h4 (* h5 h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 200 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5)
 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1232 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2)) (* 3640 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2
 j2)) (* 5956 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 5728 h2 
(* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 3232 h2 (* h3 h3 h3) h4 (* 
h5 h5 h5 h5) h6 (* j2 j2)) (* 992 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 j2) (* 
128 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6) (* 108 h2 (* h3 h3 h3) h4 (* h5 h5 h5
) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1352 h2 (* h3 h3 h3) h4 (* h5 h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 6306 h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 15456 h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6)
 (* j2 j2 j2 j2 j2)) (* 22382 h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2
 j2 j2)) (* 19844 h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 
10576 h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 3104 h2 (* h3 h3 
h3) h4 (* h5 h5 h5) (* h6 h6) j2) (* 384 h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 
h6)) (* 192 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 1720 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 6664 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
14536 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 19416 h2 
(* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 16160 h2 (* h3 h3 h3)
 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 8128 h2 (* h3 h3 h3) h4 (* h5 h5) 
(* h6 h6 h6) (* j2 j2)) (* 2240 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) j2) 
(* 256 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6)) (* 48 h2 (* h3 h3 h3) h4 h5 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 416 h2 (* h3 h3 h3) h4 h5 (* h6 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1504 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6 h6
) (* j2 j2 j2 j2 j2 j2)) (* 2944 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2 
j2 j2 j2)) (* 3376 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 
2272 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 832 h2 (* h3 h3 h3) 
h4 h5 (* h6 h6 h6 h6) (* j2 j2)) (* 128 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6 h6) j2
) (* 42 h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 472 h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
1964 h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4280 h2
 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 5514 h2 (* h3 h3 
h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 4368 h2 (* h3 h3 h3) (* h5 h5 
h5 h5) (* h6 h6) (* j2 j2 j2)) (* 2096 h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6)
 (* j2 j2)) (* 560 h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) j2) (* 64 h2 (* h3 
h3 h3) (* h5 h5 h5 h5) (* h6 h6)) (* 210 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1604 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 5356 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 10192 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2)) (* 12066 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)
) (* 9084 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 4240 h2 (* 
h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 1120 h2 (* h3 h3 h3) (* h5 h5 
h5) (* h6 h6 h6) j2) (* 128 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6)) (* 84 h2 
(* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 692 h2 
(* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2440 h2 (* 
h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4824 h2 (* h3 h3 
h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 5860 h2 (* h3 h3 h3) (* h5 
h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 4484 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 
h6 h6) (* j2 j2 j2)) (* 2112 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)
) (* 560 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) j2) (* 64 h2 (* h3 h3 h3) (* 
h5 h5) (* h6 h6 h6 h6)) (* h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2
 j2 j2 j2)) (* 15 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) 
(* 77 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 165 h2 (* h3
 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 170 h2 (* h3 h3) (* h4 h4 h4 
h4) (* h5 h5 h5) (* j2 j2)) (* 84 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) j2) 
(* 16 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5)) (* 9 h2 (* h3 h3) (* h4 h4 h4 
h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 89 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5
 h5) h6 (* j2 j2 j2 j2 j2)) (* 278 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) h6 (* 
j2 j2 j2 j2)) (* 390 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 
256 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 64 h2 (* h3 h3) (* 
h4 h4 h4 h4) (* h5 h5) h6 j2) (* 16 h2 (* h3 h3) (* h4 h4 h4 h4) h5 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 96 h2 (* h3 h3) (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 
j2 j2 j2)) (* 208 h2 (* h3 h3) (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 
192 h2 (* h3 h3) (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 64 h2 (* h3 h3) 
(* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2)) (* 4 h2 (* h3 h3) (* h4 h4 h4 h4) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 20 h2 (* h3 h3) (* h4 h4 h4 h4) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2)) (* 32 h2 (* h3 h3) (* h4 h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 
j2)) (* 16 h2 (* h3 h3) (* h4 h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2)) (* h2 (* h3 
h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 16 h2 (* h3 h3) 
(* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 92 h2 (* h3 h3) (* h4 h4 
h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 242 h2 (* h3 h3) (* h4 h4 h4) (* h5 
h5 h5 h5) (* j2 j2 j2 j2)) (* 335 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* 
j2 j2 j2)) (* 254 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 100 h2
 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) j2) (* 16 h2 (* h3 h3) (* h4 h4 h4) (* 
h5 h5 h5 h5)) (* 14 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 166 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 720 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 1582 h2 
(* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 1934 h2 (* h3 h3) (* 
h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 1320 h2 (* h3 h3) (* h4 h4 h4) (* h5 
h5 h5) h6 (* j2 j2)) (* 464 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 j2) (* 64 
h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6) (* 41 h2 (* h3 h3) (* h4 h4 h4) (* h5
 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 365 h2 (* h3 h3) (* h4 h4 h4) (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1263 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2201 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) (* h6
 h6) (* j2 j2 j2 j2)) (* 2062 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) (* h6 h6) (* 
j2 j2 j2)) (* 992 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 
192 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) (* h6 h6) j2) (* 28 h2 (* h3 h3) (* h4 
h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 208 h2 (* h3 h3) (* h4 h4 h4
) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 588 h2 (* h3 h3) (* h4 h4 h4) h5 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 792 h2 (* h3 h3) (* h4 h4 h4) h5 (* h6 h6 h6) 
(* j2 j2 j2 j2)) (* 512 h2 (* h3 h3) (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2)) 
(* 128 h2 (* h3 h3) (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2)) (* 4 h2 (* h3 h3) 
(* h4 h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 24 h2 (* h3 h3) (* h4 
h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 52 h2 (* h3 h3) (* h4 h4 h4) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 48 h2 (* h3 h3) (* h4 h4 h4) (* h6 h6 h6 
h6) (* j2 j2 j2 j2)) (* 16 h2 (* h3 h3) (* h4 h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2
)) (* 3 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 54 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 355
 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 1113 h2 (* 
h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 1924 h2 (* h3 h3) (* 
h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 1945 h2 (* h3 h3) (* h4 h4) (* h5 
h5 h5 h5) h6 (* j2 j2 j2)) (* 1146 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* 
j2 j2)) (* 364 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 j2) (* 48 h2 (* h3 h3) 
(* h4 h4) (* h5 h5 h5 h5) h6) (* 21 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 300 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1491 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 3839 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6)
 (* j2 j2 j2 j2 j2)) (* 5792 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2
 j2 j2 j2)) (* 5289 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) 
(* 2852 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 824 h2 (* h3
 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) j2) (* 96 h2 (* h3 h3) (* h4 h4) (* h5 h5 
h5) (* h6 h6)) (* 36 h2 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 366 h2 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 1519 h2 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 3326 h2 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2)) (* 4179 h2 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) 
(* 3034 h2 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 1184 h2 
(* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 192 h2 (* h3 h3) (* h4 
h4) (* h5 h5) (* h6 h6 h6) j2) (* 12 h2 (* h3 h3) (* h4 h4) h5 (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 108 h2 (* h3 h3) (* h4 h4) h5 (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 380 h2 (* h3 h3) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2
 j2 j2 j2 j2 j2)) (* 676 h2 (* h3 h3) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 
j2 j2)) (* 648 h2 (* h3 h3) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 320
 h2 (* h3 h3) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 64 h2 (* h3 h3) (* 
h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2)) (* 24 h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 282 h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1222 h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 2768 h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2)) (* 3700 h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2))
 (* 3034 h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 1502 h2 (* 
h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 412 h2 (* h3 h3) h4 (* h5 h5 
h5 h5) (* h6 h6) j2) (* 48 h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6)) (* 96 h2 
(* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 764 h2 
(* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2664 h2 (* 
h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 5272 h2 (* h3 h3) 
h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 6432 h2 (* h3 h3) h4 (* h5 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 4924 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 
h6 h6) (* j2 j2 j2)) (* 2296 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)
) (* 592 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) j2) (* 64 h2 (* h3 h3) h4 (* 
h5 h5 h5) (* h6 h6 h6)) (* 48 h2 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2
 j2 j2 j2 j2 j2 j2)) (* 370 h2 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 1192 h2 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 2092 h2 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2))
 (* 2168 h2 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 1330 h2 
(* h3 h3) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 448 h2 (* h3 h3) h4 (* 
h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 64 h2 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6 h6
) j2) (* 42 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 304 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 958 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1716 
h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1910 h2 (* h3 
h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1352 h2 (* h3 h3) (* h5 h5 
h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 594 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 
h6) (* j2 j2)) (* 148 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) j2) (* 16 h2 (* 
h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6)) (* 42 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 304 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 958 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 1716 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 
j2 j2 j2 j2)) (* 1910 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2))
 (* 1352 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 594 h2 (* h3
 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 148 h2 (* h3 h3) (* h5 h5 h5) 
(* h6 h6 h6 h6) j2) (* 16 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6)) (* 2 h2 h3 
(* h4 h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 18 h2 h3 (* h4 h4 h4 
h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 50 h2 h3 (* h4 h4 h4 h4) (* h5 h5 h5)
 h6 (* j2 j2 j2 j2)) (* 62 h2 h3 (* h4 h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) 
(* 36 h2 h3 (* h4 h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 8 h2 h3 (* h4 h4 h4 h4
) (* h5 h5 h5) h6 j2) (* 8 h2 h3 (* h4 h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2
 j2 j2 j2)) (* 40 h2 h3 (* h4 h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 72 h2 h3 (* h4 h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 56 h2 h3 (* 
h4 h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 16 h2 h3 (* h4 h4 h4 h4) (* h5
 h5) (* h6 h6) (* j2 j2)) (* 4 h2 h3 (* h4 h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2
 j2 j2 j2)) (* 15 h2 h3 (* h4 h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
19 h2 h3 (* h4 h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 8 h2 h3 (* h4 h4 h4
 h4) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 2 h2 h3 (* h4 h4 h4) (* h5 h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 20 h2 h3 (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2)) (* 68 h2 h3 (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) 
(* 112 h2 h3 (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 98 h2 h3 (* h4 
h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 44 h2 h3 (* h4 h4 h4) (* h5 h5 h5 h5)
 h6 (* j2 j2)) (* 8 h2 h3 (* h4 h4 h4) (* h5 h5 h5 h5) h6 j2) (* 12 h2 h3 (* h4 
h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 89 h2 h3 (* h4 h4 h4)
 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 263 h2 h3 (* h4 h4 h4) (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 399 h2 h3 (* h4 h4 h4) (* h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2)) (* 329 h2 h3 (* h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 
j2 j2)) (* 140 h2 h3 (* h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 24 h2 h3 
(* h4 h4 h4) (* h5 h5 h5) (* h6 h6) j2) (* 14 h2 h3 (* h4 h4 h4) (* h5 h5) (* h6
 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 90 h2 h3 (* h4 h4 h4) (* h5 h5) (* h6 h6 h6
) (* j2 j2 j2 j2 j2 j2)) (* 218 h2 h3 (* h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2)) (* 254 h2 h3 (* h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) 
(* 144 h2 h3 (* h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 32 h2 h3 (* h4
 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 4 h2 h3 (* h4 h4 h4) h5 (* h6 h6 h6
 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 19 h2 h3 (* h4 h4 h4) h5 (* h6 h6 h6 h6) (* j2
 j2 j2 j2 j2 j2)) (* 34 h2 h3 (* h4 h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)
) (* 27 h2 h3 (* h4 h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 8 h2 h3 (* h4 
h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 3 h2 h3 (* h4 h4) (* h5 h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 39 h2 h3 (* h4 h4) (* h5 h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 166 h2 h3 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 350 h2 h3 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2
 j2 j2 j2)) (* 415 h2 h3 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) 
(* 283 h2 h3 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 104 h2 h3 (* 
h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 16 h2 h3 (* h4 h4) (* h5 h5 h5 h5
) (* h6 h6) j2) (* 11 h2 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 95 h2 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 338 h2 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 646 h2 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 719 h2 
h3 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 467 h2 h3 (* h4 h4) 
(* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 164 h2 h3 (* h4 h4) (* h5 h5 h5) (* 
h6 h6 h6) (* j2 j2)) (* 24 h2 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) j2) (* 6 h2
 h3 (* h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 48 h2 h3
 (* h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 148 h2 h3 (* 
h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 232 h2 h3 (* h4 h4) 
(* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 198 h2 h3 (* h4 h4) (* h5 h5) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 88 h2 h3 (* h4 h4) (* h5 h5) (* h6 h6 h6 h6)
 (* j2 j2 j2)) (* 16 h2 h3 (* h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 12 
h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 80 h2 h3 
h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 228 h2 h3 h4 (* h5 
h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 360 h2 h3 h4 (* h5 h5 h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 340 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2)) (* 192 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 
60 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 8 h2 h3 h4 (* h5 h5 h5 h5
) (* h6 h6 h6) j2) (* 12 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 80 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 228 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 360 h2 
h3 h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 340 h2 h3 h4 (* h5 h5 
h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 192 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6 h6
) (* j2 j2 j2)) (* 60 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 8 h2 
h3 h4 (* h5 h5 h5) (* h6 h6 h6 h6) j2) (* h2 (* h4 h4 h4 h4) (* h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 4 h2 (* h4 h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2)) (* 6 h2 (* h4 h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) 
(* 4 h2 (* h4 h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* h2 (* h4 h4 h4 
h4) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* h2 (* h4 h4 h4 h4) (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 3 h2 (* h4 h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2)) (* 3 h2 (* h4 h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) 
(* h2 (* h4 h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* h2 (* h4 h4 h4) 
(* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 5 h2 (* h4 h4 h4) (* h5 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 10 h2 (* h4 h4 h4) (* h5 h5 h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 10 h2 (* h4 h4 h4) (* h5 h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2)) (* 5 h2 (* h4 h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) 
(* h2 (* h4 h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 2 h2 (* h4 h4 h4) (* 
h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 10 h2 (* h4 h4 h4) (* h5 h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 20 h2 (* h4 h4 h4) (* h5 h5 h5) (* h6
 h6 h6) (* j2 j2 j2 j2 j2)) (* 20 h2 (* h4 h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2)) (* 10 h2 (* h4 h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 2
 h2 (* h4 h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* h2 (* h4 h4 h4) (* h5 
h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4 h2 (* h4 h4 h4) (* h5 h5) (* 
h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6 h2 (* h4 h4 h4) (* h5 h5) (* h6 h6 h6 
h6) (* j2 j2 j2 j2 j2)) (* 4 h2 (* h4 h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 
j2 j2)) (* h2 (* h4 h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* h2 (* h4 
h4) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6 h2 (* h4 h4) 
(* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 15 h2 (* h4 h4) (* h5 
h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 20 h2 (* h4 h4) (* h5 h5 h5 h5)
 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 15 h2 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6 h6
) (* j2 j2 j2 j2)) (* 6 h2 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) 
(* h2 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* h2 (* h4 h4) (* h5 h5
 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6 h2 (* h4 h4) (* h5 h5 h5)
 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 15 h2 (* h4 h4) (* h5 h5 h5) (* h6
 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 20 h2 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6 h6
) (* j2 j2 j2 j2 j2)) (* 15 h2 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 
j2 j2)) (* 6 h2 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* h2 (* h4
 h4) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 20 (* h3 h3 h3 h3) (* h4 h4 h4) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 216 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5
) h6 (* j2 j2 j2 j2 j2)) (* 800 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 
j2 j2 j2)) (* 1312 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 
960 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 256 (* h3 h3 h3 h3) 
(* h4 h4 h4) (* h5 h5) h6 j2) (* 40 (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 272 (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2
 j2 j2 j2)) (* 672 (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) 
(* 704 (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 256 (* h3 h3 
h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2)) (* 10 (* h3 h3 h3 h3) (* h4 h4) (* 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 148 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5
 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 792 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2)) (* 1904 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 
j2 j2)) (* 2208 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 1216 
(* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 256 (* h3 h3 h3 h3) (* 
h4 h4) (* h5 h5 h5) h6 j2) (* 40 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 472 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 2032 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2)) (* 4224 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2)) (* 4544 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 
2432 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 512 (* h3 h3 h3
 h3) (* h4 h4) (* h5 h5) (* h6 h6) j2) (* 40 (* h3 h3 h3 h3) (* h4 h4) h5 (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 312 (* h3 h3 h3 h3) (* h4 h4) h5 (* h6 h6 h6
) (* j2 j2 j2 j2 j2 j2)) (* 944 (* h3 h3 h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 
j2 j2 j2 j2)) (* 1376 (* h3 h3 h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2))
 (* 960 (* h3 h3 h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 256 (* h3 h3 
h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2)) (* 60 (* h3 h3 h3 h3) h4 (* h5 h5 h5
) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 628 (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2264 (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* 3840 (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2)) (* 3360 (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 1472 
(* h3 h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 256 (* h3 h3 h3 h3) h4 
(* h5 h5 h5) (* h6 h6) j2) (* 120 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 896 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2
 j2 j2 j2 j2)) (* 2680 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2)) (* 4112 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 3424 
(* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 1472 (* h3 h3 h3 h3) 
h4 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 256 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 
h6 h6) j2) (* 10 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) 
(* 88 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 224 (* h3 h3
 h3) (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 208 (* h3 h3 h3) (* h4 h4 h4 
h4) (* h5 h5) h6 (* j2 j2)) (* 64 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) h6 j2) 
(* 20 (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 96 (* h3 
h3 h3) (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 144 (* h3 h3 h3) (* h4 
h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 64 (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* h6
 h6) (* j2 j2)) (* 20 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2)) (* 196 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
624 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 864 (* h3 h3 
h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 544 (* h3 h3 h3) (* h4 h4 h4) 
(* h5 h5 h5) h6 (* j2 j2)) (* 128 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 j2) 
(* 80 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
504 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1252 
(* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 1520 (* h3 h3 
h3) (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 880 (* h3 h3 h3) (* h4 h4 
h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 192 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) 
(* h6 h6) j2) (* 40 (* h3 h3 h3) (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 232 (* h3 h3 h3) (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 480
 (* h3 h3 h3) (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 416 (* h3 h3 h3) 
(* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 128 (* h3 h3 h3) (* h4 h4 h4) h5 
(* h6 h6 h6) (* j2 j2)) (* 5 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2)) (* 69 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2)) (* 332 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
684 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 688 (* h3 h3 
h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 336 (* h3 h3 h3) (* h4 h4) (* 
h5 h5 h5 h5) h6 (* j2 j2)) (* 64 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 j2) 
(* 45 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 471 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
1718 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 3036 
(* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 2832 (* h3 h3 
h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 1344 (* h3 h3 h3) (* h4 h4
) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 256 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) 
(* h6 h6) j2) (* 80 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2
 j2 j2 j2)) (* 574 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 1718 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)
) (* 2728 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 2384
 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 1072 (* h3 h3 h3
) (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 192 (* h3 h3 h3) (* h4 h4) (* 
h5 h5) (* h6 h6 h6) j2) (* 20 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2
 j2 j2 j2 j2 j2)) (* 136 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 356 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 448 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 272 (* h3 
h3 h3) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 64 (* h3 h3 h3) (* h4 h4) 
h5 (* h6 h6 h6 h6) (* j2 j2)) (* 30 (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 284 (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2
 j2 j2 j2 j2 j2)) (* 878 (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2)) (* 1296 (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 
1008 (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 400 (* h3 h3 h3)
 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 64 (* h3 h3 h3) h4 (* h5 h5 h5 h5) 
(* h6 h6) j2) (* 150 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2
 j2 j2)) (* 880 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2))
 (* 2158 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2820 
(* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 2064 (* h3 h3 h3) 
h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 800 (* h3 h3 h3) h4 (* h5 h5 h5) 
(* h6 h6 h6) (* j2 j2)) (* 128 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) j2) (* 
60 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 388 
(* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1012 (* h3 
h3 h3) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1372 (* h3 h3 h3) h4 
(* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 1024 (* h3 h3 h3) h4 (* h5 h5) (* 
h6 h6 h6 h6) (* j2 j2 j2)) (* 400 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6 h6) (* 
j2 j2)) (* 64 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6 h6) j2) (* 5 (* h3 h3) (* h4
 h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 39 (* h3 h3) (* h4 h4 h4 h4) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 78 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) h6
 (* j2 j2 j2)) (* 60 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 16 
(* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) h6 j2) (* 25 (* h3 h3) (* h4 h4 h4 h4) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 85 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5
) (* h6 h6) (* j2 j2 j2 j2)) (* 92 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* h6 h6)
 (* j2 j2 j2)) (* 32 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) 
(* 10 (* h3 h3) (* h4 h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 28 (* h3 
h3) (* h4 h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 16 (* h3 h3) (* h4 h4 h4
 h4) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 5 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2)) (* 44 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* 117 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) 
(* 138 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 76 (* h3 h3) 
(* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 16 (* h3 h3) (* h4 h4 h4) (* h5 h5
 h5 h5) h6 j2) (* 40 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 212 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 454 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 
478 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 244 (* h3 h3)
 (* h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 48 (* h3 h3) (* h4 h4 h4) (* 
h5 h5 h5) (* h6 h6) j2) (* 45 (* h3 h3) (* h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 211 (* h3 h3) (* h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2)) (* 350 (* h3 h3) (* h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2)) (* 248 (* h3 h3) (* h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 64 
(* h3 h3) (* h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 10 (* h3 h3) (* h4 
h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 38 (* h3 h3) (* h4 h4 h4) h5
 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 44 (* h3 h3) (* h4 h4 h4) h5 (* h6 h6 h6
 h6) (* j2 j2 j2 j2)) (* 16 (* h3 h3) (* h4 h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 
j2)) (* 10 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2
)) (* 98 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 322 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 510 
(* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 428 (* h3 h3) 
(* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 184 (* h3 h3) (* h4 h4) (* 
h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 32 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* 
h6 h6) j2) (* 40 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2
 j2 j2)) (* 247 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 652 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 919 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 718 (* 
h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 292 (* h3 h3) (* h4 
h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 48 (* h3 h3) (* h4 h4) (* h5 h5 h5) 
(* h6 h6 h6) j2) (* 20 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2
 j2 j2 j2 j2)) (* 121 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 274 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 
j2)) (* 297 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 
156 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 32 (* h3 h3) 
(* h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 30 (* h3 h3) h4 (* h5 h5 h5 h5
) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 164 (* h3 h3) h4 (* h5 h5 h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 372 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6 h6
) (* j2 j2 j2 j2 j2)) (* 448 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2)) (* 302 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 108 
(* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 16 (* h3 h3) h4 (* h5 h5
 h5 h5) (* h6 h6 h6) j2) (* 30 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 164 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2
 j2 j2 j2)) (* 372 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2))
 (* 448 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 302 (* h3 
h3) h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 108 (* h3 h3) h4 (* h5 h5 
h5) (* h6 h6 h6 h6) (* j2 j2)) (* 16 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6 h6) 
j2) (* 5 h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 14 h3 
(* h4 h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 13 h3 (* h4 h4 h4 h4)
 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 4 h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* h6
 h6) (* j2 j2)) (* 5 h3 (* h4 h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2
)) (* 9 h3 (* h4 h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 4 h3 (* h4
 h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 5 h3 (* h4 h4 h4) (* h5 h5 h5
 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 19 h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2)) (* 27 h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2
 j2 j2 j2)) (* 17 h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 4 
h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 10 h3 (* h4 h4 h4) (* h5
 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 38 h3 (* h4 h4 h4) (* h5 h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 54 h3 (* h4 h4 h4) (* h5 h5 h5) (* h6 h6 h6)
 (* j2 j2 j2 j2)) (* 34 h3 (* h4 h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) 
(* 8 h3 (* h4 h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 5 h3 (* h4 h4 h4) 
(* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 14 h3 (* h4 h4 h4) (* h5 h5)
 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 13 h3 (* h4 h4 h4) (* h5 h5) (* h6 h6 h6
 h6) (* j2 j2 j2 j2)) (* 4 h3 (* h4 h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2
)) (* 5 h3 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
24 h3 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 46 h3 (* 
h4 h4) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 44 h3 (* h4 h4) (* h5
 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 21 h3 (* h4 h4) (* h5 h5 h5 h5) (* 
h6 h6 h6) (* j2 j2 j2)) (* 4 h3 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2)
) (* 5 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 24
 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 46 h3 (* h4
 h4) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 44 h3 (* h4 h4) (* h5 
h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 21 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6
 h6 h6) (* j2 j2 j2)) (* 4 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2)))
 0)))
(check-sat)
(exit)

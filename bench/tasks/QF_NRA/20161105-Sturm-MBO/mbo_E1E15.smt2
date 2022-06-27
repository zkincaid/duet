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
(set-info :instance |E1E15|)
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
(+ (* 1600 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 8320 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 18032 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2 j2 j2)) (* 
21224 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2 j2)) (* 14816 (* 
h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2)) (* 6278 (* h1 h1 h1 h1) 
(* h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2)) (* 1576 (* h1 h1 h1 h1) (* h2 h2 h2) (* 
h3 h3) h5 (* j2 j2)) (* 214 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 j2) (* 12 
(* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5) (* 1600 (* h1 h1 h1 h1) (* h2 h2 h2) 
(* h3 h3) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 7920 (* h1 h1 h1 h1) (* h2 h2 h2) 
(* h3 h3) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 16552 (* h1 h1 h1 h1) (* h2 h2 h2) (* 
h3 h3) h6 (* j2 j2 j2 j2 j2 j2)) (* 19036 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3)
 h6 (* j2 j2 j2 j2 j2)) (* 13162 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h6 (* j2
 j2 j2 j2)) (* 5602 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h6 (* j2 j2 j2)) (* 
1434 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h6 (* j2 j2)) (* 202 (* h1 h1 h1 h1)
 (* h2 h2 h2) (* h3 h3) h6 j2) (* 12 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h6) 
(* 640 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (* 3776 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 9568 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
13664 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 12120 
(* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 6924 (* h1 h1 
h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2)) (* 2546 (* h1 h1 h1 h1) (* h2 
h2 h2) h3 (* h5 h5) (* j2 j2 j2)) (* 580 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h5 
h5) (* j2 j2)) (* 74 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) j2) (* 4 (* h1 h1
 h1 h1) (* h2 h2 h2) h3 (* h5 h5)) (* 1120 (* h1 h1 h1 h1) (* h2 h2 h2) h3 h5 h6
 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 6448 (* h1 h1 h1 h1) (* h2 h2 h2) h3 h5 h6 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 16240 (* h1 h1 h1 h1) (* h2 h2 h2) h3 h5 h6 (* 
j2 j2 j2 j2 j2 j2 j2)) (* 23456 (* h1 h1 h1 h1) (* h2 h2 h2) h3 h5 h6 (* j2 j2 
j2 j2 j2 j2)) (* 21378 (* h1 h1 h1 h1) (* h2 h2 h2) h3 h5 h6 (* j2 j2 j2 j2 j2))
 (* 12729 (* h1 h1 h1 h1) (* h2 h2 h2) h3 h5 h6 (* j2 j2 j2 j2)) (* 4943 (* h1 
h1 h1 h1) (* h2 h2 h2) h3 h5 h6 (* j2 j2 j2)) (* 1205 (* h1 h1 h1 h1) (* h2 h2 
h2) h3 h5 h6 (* j2 j2)) (* 167 (* h1 h1 h1 h1) (* h2 h2 h2) h3 h5 h6 j2) (* 10 
(* h1 h1 h1 h1) (* h2 h2 h2) h3 h5 h6) (* 320 (* h1 h1 h1 h1) (* h2 h2 h2) h3 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1968 (* h1 h1 h1 h1) (* h2 h2 h2) 
h3 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 5256 (* h1 h1 h1 h1) (* h2 h2 h2) 
h3 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 7988 (* h1 h1 h1 h1) (* h2 h2 h2) h3 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 7602 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h6 
h6) (* j2 j2 j2 j2 j2)) (* 4692 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6) (* j2 
j2 j2 j2)) (* 1876 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6) (* j2 j2 j2)) (* 
468 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6) (* j2 j2)) (* 66 (* h1 h1 h1 h1) 
(* h2 h2 h2) h3 (* h6 h6) j2) (* 4 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6)) 
(* 320 (* h1 h1 h1 h1) (* h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 2048 (* h1 h1 h1 h1) (* h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 5808 (* h1 h1 h1 h1) (* h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 9616 (* h1 h1 h1 h1) (* h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2)) (* 10300 (* h1 h1 h1 h1) (* h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 7464 (* h1 h1 h1 h1) (* h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 3709 
(* h1 h1 h1 h1) (* h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 1249 (* h1 h1 h1 
h1) (* h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2)) (* 273 (* h1 h1 h1 h1) (* h2 h2 h2) 
(* h5 h5) h6 (* j2 j2)) (* 35 (* h1 h1 h1 h1) (* h2 h2 h2) (* h5 h5) h6 j2) (* 2
 (* h1 h1 h1 h1) (* h2 h2 h2) (* h5 h5) h6) (* 160 (* h1 h1 h1 h1) (* h2 h2 h2) 
h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1104 (* h1 h1 h1 h1) (* h2 h2
 h2) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3376 (* h1 h1 h1 h1) (* h2 
h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6024 (* h1 h1 h1 h1) (* h2 
h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 6946 (* h1 h1 h1 h1) (* h2 h2 
h2) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 5409 (* h1 h1 h1 h1) (* h2 h2 h2) h5 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 2882 (* h1 h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6) 
(* j2 j2 j2 j2)) (* 1038 (* h1 h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6) (* j2 j2 j2))
 (* 242 (* h1 h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6) (* j2 j2)) (* 33 (* h1 h1 h1 
h1) (* h2 h2 h2) h5 (* h6 h6) j2) (* 2 (* h1 h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6)
) (* 4000 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2 j2 j2 j2 j2))
 (* 22400 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 52400 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2 j2 j2)) (* 
66492 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2 j2)) (* 49764 (* 
h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2)) (* 22388 (* h1 h1 h1 h1)
 (* h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2)) (* 5900 (* h1 h1 h1 h1) (* h2 h2) (* h3
 h3 h3) h5 (* j2 j2)) (* 832 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 j2) (* 48
 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5) (* 4000 (* h1 h1 h1 h1) (* h2 h2) 
(* h3 h3 h3) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 21400 (* h1 h1 h1 h1) (* h2 h2) 
(* h3 h3 h3) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 48300 (* h1 h1 h1 h1) (* h2 h2) (* 
h3 h3 h3) h6 (* j2 j2 j2 j2 j2 j2)) (* 59792 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 
h3) h6 (* j2 j2 j2 j2 j2)) (* 44216 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h6 
(* j2 j2 j2 j2)) (* 19944 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2)
) (* 5356 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h6 (* j2 j2)) (* 784 (* h1 h1 
h1 h1) (* h2 h2) (* h3 h3 h3) h6 j2) (* 48 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3
) h6) (* 1760 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 12144 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 35816 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 
j2)) (* 58956 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2)) 
(* 59354 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 37683 
(* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2)) (* 15015 (* h1 h1 h1 
h1) (* h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2)) (* 3611 (* h1 h1 h1 h1) (* h2 h2) 
(* h3 h3) h4 h5 (* j2 j2)) (* 475 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 j2) 
(* 26 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5) (* 960 (* h1 h1 h1 h1) (* h2 h2
) (* h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 6944 (* h1 h1 h1 h1) (* h2 
h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 21204 (* h1 h1 h1 h1) (* h2 
h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 35882 (* h1 h1 h1 h1) (* h2 h2)
 (* h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2)) (* 37030 (* h1 h1 h1 h1) (* h2 h2) (* h3
 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 24120 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 
h6 (* j2 j2 j2 j2)) (* 9904 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h6 (* j2 j2 
j2)) (* 2474 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h6 (* j2 j2)) (* 342 (* h1 
h1 h1 h1) (* h2 h2) (* h3 h3) h4 h6 j2) (* 20 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3
) h4 h6) (* 2880 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2
 j2 j2 j2 j2)) (* 18272 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 49808 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* j2
 j2 j2 j2 j2 j2 j2)) (* 76424 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* 
j2 j2 j2 j2 j2 j2)) (* 72636 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* j2
 j2 j2 j2 j2)) (* 44306 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 
j2 j2)) (* 17332 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2)) (* 
4186 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* j2 j2)) (* 564 (* h1 h1 h1
 h1) (* h2 h2) (* h3 h3) (* h5 h5) j2) (* 32 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3)
 (* h5 h5)) (* 5360 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 33144 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 89180 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2 
j2 j2 j2)) (* 136962 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2
 j2)) (* 132230 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) 
(* 83132 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 33956 (* 
h1 h1 h1 h1) (* h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2)) (* 8654 (* h1 h1 h1 h1) (* 
h2 h2) (* h3 h3) h5 h6 (* j2 j2)) (* 1242 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h5
 h6 j2) (* 76 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h5 h6) (* 2080 (* h1 h1 h1 h1)
 (* h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 13112 (* h1 h1
 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 36172 (* 
h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 57264 
(* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 57244 
(* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 37376 (* h1
 h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 15876 (* h1 h1 h1 
h1) (* h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2)) (* 4208 (* h1 h1 h1 h1) (* h2 h2
) (* h3 h3) (* h6 h6) (* j2 j2)) (* 628 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* 
h6 h6) j2) (* 40 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6)) (* 320 (* h1 h1 
h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3008 (* 
h1 h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 11872 
(* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 26048 
(* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 35264 (* 
h1 h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 30804 (* h1 h1 
h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 17587 (* h1 h1 h1 h1) 
(* h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2)) (* 6481 (* h1 h1 h1 h1) (* h2 h2) h3 
h4 (* h5 h5) (* j2 j2 j2)) (* 1475 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* 
j2 j2)) (* 187 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) j2) (* 10 (* h1 h1 h1 
h1) (* h2 h2) h3 h4 (* h5 h5)) (* 640 (* h1 h1 h1 h1) (* h2 h2) h3 h4 h5 h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 5096 (* h1 h1 h1 h1) (* h2 h2) h3 h4 h5 h6 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 17716 (* h1 h1 h1 h1) (* h2 h2) h3 h4 h5 h6 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 35442 (* h1 h1 h1 h1) (* h2 h2) h3 h4 h5 h6 (* 
j2 j2 j2 j2 j2 j2 j2)) (* 45177 (* h1 h1 h1 h1) (* h2 h2) h3 h4 h5 h6 (* j2 j2 
j2 j2 j2 j2)) (* 38300 (* h1 h1 h1 h1) (* h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2 j2))
 (* 21836 (* h1 h1 h1 h1) (* h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2)) (* 8252 (* h1 
h1 h1 h1) (* h2 h2) h3 h4 h5 h6 (* j2 j2 j2)) (* 1975 (* h1 h1 h1 h1) (* h2 h2) 
h3 h4 h5 h6 (* j2 j2)) (* 270 (* h1 h1 h1 h1) (* h2 h2) h3 h4 h5 h6 j2) (* 16 
(* h1 h1 h1 h1) (* h2 h2) h3 h4 h5 h6) (* 240 (* h1 h1 h1 h1) (* h2 h2) h3 h4 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1556 (* h1 h1 h1 h1) (* h2 h2) h3 
h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4374 (* h1 h1 h1 h1) (* h2 h2) h3 
h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 6976 (* h1 h1 h1 h1) (* h2 h2) h3 h4 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6934 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h6 
h6) (* j2 j2 j2 j2 j2)) (* 4440 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6) (* j2 
j2 j2 j2)) (* 1826 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2)) (* 
464 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6) (* j2 j2)) (* 66 (* h1 h1 h1 h1) 
(* h2 h2) h3 h4 (* h6 h6) j2) (* 4 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6)) 
(* 640 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (* 4256 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 12080 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
19152 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 18644 
(* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 11534 (* h1 h1 
h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 4528 (* h1 h1 h1 h1) (* h2 
h2) h3 (* h5 h5 h5) (* j2 j2 j2)) (* 1086 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5 
h5) (* j2 j2)) (* 144 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) j2) (* 8 (* h1 
h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5)) (* 2080 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 14432 (* h1 h1 h1 h1) (* h2 h2) h3 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 44360 (* h1 h1 h1 h1) (* h2 h2) 
h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 79668 (* h1 h1 h1 h1) (* h2 h2) 
h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 92740 (* h1 h1 h1 h1) (* h2 h2) h3 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 73195 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 
h5) h6 (* j2 j2 j2 j2 j2)) (* 39647 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5) h6 
(* j2 j2 j2 j2)) (* 14517 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2)
) (* 3425 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5) h6 (* j2 j2)) (* 468 (* h1 h1 
h1 h1) (* h2 h2) h3 (* h5 h5) h6 j2) (* 28 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5
) h6) (* 1360 (* h1 h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 9544 (* h1 h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 30180 (* h1 h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 56682 (* h1 h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 69940 (* h1 h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 59038 (* h1 h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
34342 (* h1 h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 13508 (* h1 
h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2)) (* 3418 (* h1 h1 h1 h1) (* h2 
h2) h3 h5 (* h6 h6) (* j2 j2)) (* 500 (* h1 h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6) 
j2) (* 32 (* h1 h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6)) (* 320 (* h1 h1 h1 h1) (* 
h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2128 (* h1 h1 h1 h1) 
(* h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6160 (* h1 h1 h1 h1) 
(* h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 10164 (* h1 h1 h1 h1) (* 
h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 10508 (* h1 h1 h1 h1) (* h2 h2)
 h3 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 7040 (* h1 h1 h1 h1) (* h2 h2) h3 (* h6 
h6 h6) (* j2 j2 j2 j2)) (* 3048 (* h1 h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6) (* j2 
j2 j2)) (* 820 (* h1 h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6) (* j2 j2)) (* 124 (* h1
 h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6) j2) (* 8 (* h1 h1 h1 h1) (* h2 h2) h3 (* h6
 h6 h6)) (* 400 (* h1 h1 h1 h1) (* h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 2800 (* h1 h1 h1 h1) (* h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 8616 (* h1 h1 h1 h1) (* h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 15344 (* h1 h1 h1 h1) (* h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2)) (* 17513 (* h1 h1 h1 h1) (* h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2 
j2 j2)) (* 13389 (* h1 h1 h1 h1) (* h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) 
(* 6947 (* h1 h1 h1 h1) (* h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 2417 (* h1
 h1 h1 h1) (* h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 540 (* h1 h1 h1 h1) (* h2 
h2) h4 (* h5 h5) h6 (* j2 j2)) (* 70 (* h1 h1 h1 h1) (* h2 h2) h4 (* h5 h5) h6 
j2) (* 4 (* h1 h1 h1 h1) (* h2 h2) h4 (* h5 h5) h6) (* 120 (* h1 h1 h1 h1) (* h2
 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 868 (* h1 h1 h1 h1) 
(* h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2778 (* h1 h1 h1 h1
) (* h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 5175 (* h1 h1 h1 h1)
 (* h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 6208 (* h1 h1 h1 h1) (* 
h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 5007 (* h1 h1 h1 h1) (* h2 h2) 
h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2748 (* h1 h1 h1 h1) (* h2 h2) h4 h5 (* 
h6 h6) (* j2 j2 j2 j2)) (* 1013 (* h1 h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6) (* j2 
j2 j2)) (* 240 (* h1 h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6) (* j2 j2)) (* 33 (* h1 
h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6) j2) (* 2 (* h1 h1 h1 h1) (* h2 h2) h4 h5 (* 
h6 h6)) (* 320 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2
 j2 j2 j2)) (* 2288 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 7184 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 13048 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2)) (* 15188 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2)) (* 11847 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
6277 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 2233 (* h1 h1
 h1 h1) (* h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 511 (* h1 h1 h1 h1) (* h2 h2)
 (* h5 h5 h5) h6 (* j2 j2)) (* 68 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5 h5) h6 j2) 
(* 4 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5 h5) h6) (* 400 (* h1 h1 h1 h1) (* h2 h2)
 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3000 (* h1 h1 h1 h1) 
(* h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 9876 (* h1 h1 
h1 h1) (* h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 18806 (* h1
 h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 22954 (* 
h1 h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 18777 (* h1
 h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 10433 (* h1 h1 
h1 h1) (* h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 3891 (* h1 h1 h1 h1) 
(* h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 933 (* h1 h1 h1 h1) (* h2 h2) (* 
h5 h5) (* h6 h6) (* j2 j2)) (* 130 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6)
 j2) (* 8 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6)) (* 160 (* h1 h1 h1 h1) 
(* h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1184 (* h1 h1 h1
 h1) (* h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3888 (* h1 h1 
h1 h1) (* h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 7456 (* h1 h1 
h1 h1) (* h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 9242 (* h1 h1 h1 
h1) (* h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 7734 (* h1 h1 h1 h1) (* 
h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 4424 (* h1 h1 h1 h1) (* h2 h2) h5 
(* h6 h6 h6) (* j2 j2 j2 j2)) (* 1708 (* h1 h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6) 
(* j2 j2 j2)) (* 426 (* h1 h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6) (* j2 j2)) (* 62 
(* h1 h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6) j2) (* 4 (* h1 h1 h1 h1) (* h2 h2) h5 
(* h6 h6 h6)) (* 4400 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2
 j2 j2 j2)) (* 29120 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 82784 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2))
 (* 132126 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 
129856 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 81100 (* h1 
h1 h1 h1) h2 (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2)) (* 32040 (* h1 h1 h1 h1) h2 (* 
h3 h3 h3) h4 h5 (* j2 j2 j2)) (* 7694 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h5 (* 
j2 j2)) (* 1016 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h5 j2) (* 56 (* h1 h1 h1 h1) 
h2 (* h3 h3 h3) h4 h5) (* 2400 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h6 (* j2 j2 j2
 j2 j2 j2 j2 j2 j2)) (* 15320 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h6 (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 42304 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 
j2 j2 j2)) (* 66104 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2))
 (* 64192 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 40040 (* 
h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 16000 (* h1 h1 h1 h1) h2 
(* h3 h3 h3) h4 h6 (* j2 j2 j2)) (* 3944 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h6 
(* j2 j2)) (* 544 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h6 j2) (* 32 (* h1 h1 h1 h1
) h2 (* h3 h3 h3) h4 h6) (* 3200 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* j2
 j2 j2 j2 j2 j2 j2 j2 j2)) (* 21760 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 63072 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 101632 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) 
(* j2 j2 j2 j2 j2 j2)) (* 99592 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* j2 
j2 j2 j2 j2)) (* 61048 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2)
) (* 23224 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2)) (* 5256 (* h1
 h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* j2 j2)) (* 640 (* h1 h1 h1 h1) h2 (* h3 
h3 h3) (* h5 h5) j2) (* 32 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5)) (* 6400 
(* h1 h1 h1 h1) h2 (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 42320 
(* h1 h1 h1 h1) h2 (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 120184 (* 
h1 h1 h1 h1) h2 (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 191572 (* h1 h1 
h1 h1) h2 (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 187984 (* h1 h1 h1 h1) h2
 (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 117176 (* h1 h1 h1 h1) h2 (* h3 h3 h3
) h5 h6 (* j2 j2 j2 j2)) (* 46184 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h5 h6 (* j2 j2
 j2)) (* 11060 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h5 h6 (* j2 j2)) (* 1456 (* h1 h1
 h1 h1) h2 (* h3 h3 h3) h5 h6 j2) (* 80 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h5 h6) 
(* 3200 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 20960 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 59632 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 96464 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
97504 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 63680 (* 
h1 h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 26800 (* h1 h1 h1 h1)
 h2 (* h3 h3 h3) (* h6 h6) (* j2 j2 j2)) (* 6992 (* h1 h1 h1 h1) h2 (* h3 h3 h3)
 (* h6 h6) (* j2 j2)) (* 1024 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6) j2) (* 
64 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6)) (* 480 (* h1 h1 h1 h1) h2 (* h3 h3
) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4792 (* h1 h1 h1 h1) h2 (* 
h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 19640 (* h1 h1 h1 h1) h2 
(* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 44300 (* h1 h1 h1 h1) h2 
(* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 61347 (* h1 h1 h1 h1) h2 (* 
h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 54615 (* h1 h1 h1 h1) h2 (* h3 h3)
 (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 31640 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4
) h5 (* j2 j2 j2 j2)) (* 11762 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* j2 
j2 j2)) (* 2683 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* j2 j2)) (* 339 (* 
h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 j2) (* 18 (* h1 h1 h1 h1) h2 (* h3 h3) 
(* h4 h4) h5) (* 720 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2
 j2 j2 j2 j2)) (* 4548 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 12404 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 
j2 j2 j2)) (* 19100 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 
j2)) (* 18228 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 
11140 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2)) (* 4348 (* h1 
h1 h1 h1) h2 (* h3 h3) (* h4 h4) h6 (* j2 j2 j2)) (* 1044 (* h1 h1 h1 h1) h2 (* 
h3 h3) (* h4 h4) h6 (* j2 j2)) (* 140 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h6 
j2) (* 8 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h6) (* 1440 (* h1 h1 h1 h1) h2 
(* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 12496 (* h1 h1 h1 
h1) h2 (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 47608 (* h1 h1 
h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 103956 (* h1 h1
 h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 142918 (* h1 h1 
h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 128301 (* h1 h1 h1 h1
) h2 (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 75665 (* h1 h1 h1 h1) h2 (* 
h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 28797 (* h1 h1 h1 h1) h2 (* h3 h3) h4 
(* h5 h5) (* j2 j2 j2)) (* 6749 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* j2 
j2)) (* 878 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) j2) (* 48 (* h1 h1 h1 h1) 
h2 (* h3 h3) h4 (* h5 h5)) (* 3200 (* h1 h1 h1 h1) h2 (* h3 h3) h4 h5 h6 (* j2 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 26000 (* h1 h1 h1 h1) h2 (* h3 h3) h4 h5 h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 93108 (* h1 h1 h1 h1) h2 (* h3 h3) h4 h5 h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 192478 (* h1 h1 h1 h1) h2 (* h3 h3) h4 h5 h6 (* j2 
j2 j2 j2 j2 j2 j2)) (* 253056 (* h1 h1 h1 h1) h2 (* h3 h3) h4 h5 h6 (* j2 j2 j2 
j2 j2 j2)) (* 219992 (* h1 h1 h1 h1) h2 (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) 
(* 127476 (* h1 h1 h1 h1) h2 (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 48422 (* h1 
h1 h1 h1) h2 (* h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 11504 (* h1 h1 h1 h1) h2 (* h3 
h3) h4 h5 h6 (* j2 j2)) (* 1540 (* h1 h1 h1 h1) h2 (* h3 h3) h4 h5 h6 j2) (* 88 
(* h1 h1 h1 h1) h2 (* h3 h3) h4 h5 h6) (* 1920 (* h1 h1 h1 h1) h2 (* h3 h3) h4 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 12448 (* h1 h1 h1 h1) h2 (* h3 h3) 
h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 34992 (* h1 h1 h1 h1) h2 (* h3 h3) 
h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 55808 (* h1 h1 h1 h1) h2 (* h3 h3) h4 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 55472 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h6 
h6) (* j2 j2 j2 j2 j2)) (* 35520 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6) (* j2
 j2 j2 j2)) (* 14608 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6) (* j2 j2 j2)) (* 
3712 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6) (* j2 j2)) (* 528 (* h1 h1 h1 h1)
 h2 (* h3 h3) h4 (* h6 h6) j2) (* 32 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6)) 
(* 1280 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 9152 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2))
 (* 27776 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 46608 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 
47232 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 29692 (* 
h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 11480 (* h1 h1 h1 h1)
 h2 (* h3 h3) (* h5 h5 h5) (* j2 j2 j2)) (* 2620 (* h1 h1 h1 h1) h2 (* h3 h3) 
(* h5 h5 h5) (* j2 j2)) (* 320 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) j2) (* 
16 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5)) (* 4480 (* h1 h1 h1 h1) h2 (* h3 
h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 33472 (* h1 h1 h1 h1) h2 
(* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 110112 (* h1 h1 h1 h1)
 h2 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 209656 (* h1 h1 h1 h1
) h2 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 255292 (* h1 h1 h1 h1) 
h2 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 207138 (* h1 h1 h1 h1) h2 
(* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 113002 (* h1 h1 h1 h1) h2 (* h3 h3
) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 40738 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5) 
h6 (* j2 j2 j2)) (* 9234 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5) h6 (* j2 j2)) 
(* 1180 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5) h6 j2) (* 64 (* h1 h1 h1 h1) h2 
(* h3 h3) (* h5 h5) h6) (* 3680 (* h1 h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 28032 (* h1 h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 95024 (* h1 h1 h1 h1) h2 (* h3 h3) h5 (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 188440 (* h1 h1 h1 h1) h2 (* h3 h3) h5 (* h6
 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 241532 (* h1 h1 h1 h1) h2 (* h3 h3) h5 (* h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 208444 (* h1 h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* 122192 (* h1 h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6) (* j2 j2
 j2 j2)) (* 47824 (* h1 h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 
11900 (* h1 h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6) (* j2 j2)) (* 1692 (* h1 h1 h1 
h1) h2 (* h3 h3) h5 (* h6 h6) j2) (* 104 (* h1 h1 h1 h1) h2 (* h3 h3) h5 (* h6 
h6)) (* 1280 (* h1 h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 8512 (* h1 h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 24640 (* h1 h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 40656 (* h1 h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 42032 (* h1 h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 28160 
(* h1 h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 12192 (* h1 h1 h1 
h1) h2 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2)) (* 3280 (* h1 h1 h1 h1) h2 (* h3 h3)
 (* h6 h6 h6) (* j2 j2)) (* 496 (* h1 h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6) j2) 
(* 32 (* h1 h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6)) (* 400 (* h1 h1 h1 h1) h2 h3 
(* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3240 (* h1 h1 h1 h1) 
h2 h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 11552 (* h1 h1 h1 
h1) h2 h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 23718 (* h1 h1 h1 
h1) h2 h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 30831 (* h1 h1 h1 h1)
 h2 h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 26313 (* h1 h1 h1 h1) h2 h3
 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 14821 (* h1 h1 h1 h1) h2 h3 (* h4 h4
) (* h5 h5) (* j2 j2 j2 j2)) (* 5405 (* h1 h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) 
(* j2 j2 j2)) (* 1216 (* h1 h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* j2 j2)) (* 
152 (* h1 h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) j2) (* 8 (* h1 h1 h1 h1) h2 h3 (* 
h4 h4) (* h5 h5)) (* 480 (* h1 h1 h1 h1) h2 h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 3352 (* h1 h1 h1 h1) h2 h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 10394 (* h1 h1 h1 h1) h2 h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 18827 (* h1 h1 h1 h1) h2 h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 22030 (* h1 h1 h1 h1) h2 h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) 
(* 17369 (* h1 h1 h1 h1) h2 h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 9324 (* h1
 h1 h1 h1) h2 h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 3357 (* h1 h1 h1 h1) h2 h3 
(* h4 h4) h5 h6 (* j2 j2 j2)) (* 774 (* h1 h1 h1 h1) h2 h3 (* h4 h4) h5 h6 (* j2
 j2)) (* 103 (* h1 h1 h1 h1) h2 h3 (* h4 h4) h5 h6 j2) (* 6 (* h1 h1 h1 h1) h2 
h3 (* h4 h4) h5 h6) (* 320 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 2768 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 10616 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 23544 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 
j2 j2)) (* 33078 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) 
(* 30421 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 18353 (* 
h1 h1 h1 h1) h2 h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 7111 (* h1 h1 h1 h1) h2 
h3 h4 (* h5 h5 h5) (* j2 j2 j2)) (* 1685 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5 h5) 
(* j2 j2)) (* 220 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5 h5) j2) (* 12 (* h1 h1 h1 h1
) h2 h3 h4 (* h5 h5 h5)) (* 2160 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 16624 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 56244 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 109946 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2)) (* 137173 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 
j2 j2)) (* 113789 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
63341 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 23281 (* h1 h1 
h1 h1) h2 h3 h4 (* h5 h5) h6 (* j2 j2 j2)) (* 5390 (* h1 h1 h1 h1) h2 h3 h4 (* 
h5 h5) h6 (* j2 j2)) (* 708 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5) h6 j2) (* 40 (* 
h1 h1 h1 h1) h2 h3 h4 (* h5 h5) h6) (* 1360 (* h1 h1 h1 h1) h2 h3 h4 h5 (* h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 9904 (* h1 h1 h1 h1) h2 h3 h4 h5 (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 31984 (* h1 h1 h1 h1) h2 h3 h4 h5 (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 60196 (* h1 h1 h1 h1) h2 h3 h4 h5 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 72960 (* h1 h1 h1 h1) h2 h3 h4 h5 (* h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 59380 (* h1 h1 h1 h1) h2 h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 32808 (* h1 h1 h1 h1) h2 h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 12140 
(* h1 h1 h1 h1) h2 h3 h4 h5 (* h6 h6) (* j2 j2 j2)) (* 2880 (* h1 h1 h1 h1) h2 
h3 h4 h5 (* h6 h6) (* j2 j2)) (* 396 (* h1 h1 h1 h1) h2 h3 h4 h5 (* h6 h6) j2) 
(* 24 (* h1 h1 h1 h1) h2 h3 h4 h5 (* h6 h6)) (* 1280 (* h1 h1 h1 h1) h2 h3 (* h5
 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 9792 (* h1 h1 h1 h1) h2 h3 (* 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 32672 (* h1 h1 h1 h1) h2 h3 (* 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 62464 (* h1 h1 h1 h1) h2 h3 (* h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 75592 (* h1 h1 h1 h1) h2 h3 (* h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2)) (* 60356 (* h1 h1 h1 h1) h2 h3 (* h5 h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* 32124 (* h1 h1 h1 h1) h2 h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) 
(* 11228 (* h1 h1 h1 h1) h2 h3 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 2460 (* h1 h1 h1
 h1) h2 h3 (* h5 h5 h5) h6 (* j2 j2)) (* 304 (* h1 h1 h1 h1) h2 h3 (* h5 h5 h5) 
h6 j2) (* 16 (* h1 h1 h1 h1) h2 h3 (* h5 h5 h5) h6) (* 2080 (* h1 h1 h1 h1) h2 
h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 16232 (* h1 h1 h1 
h1) h2 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 55600 (* h1 h1 
h1 h1) h2 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 109886 (* h1 h1
 h1 h1) h2 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 138504 (* h1 h1 
h1 h1) h2 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 116124 (* h1 h1 h1 h1
) h2 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 65496 (* h1 h1 h1 h1) h2 h3 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 24526 (* h1 h1 h1 h1) h2 h3 (* h5 h5) 
(* h6 h6) (* j2 j2 j2)) (* 5840 (* h1 h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6) (* j2 
j2)) (* 800 (* h1 h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6) j2) (* 48 (* h1 h1 h1 h1) 
h2 h3 (* h5 h5) (* h6 h6)) (* 960 (* h1 h1 h1 h1) h2 h3 h5 (* h6 h6 h6) (* j2 j2
 j2 j2 j2 j2 j2 j2 j2 j2)) (* 7264 (* h1 h1 h1 h1) h2 h3 h5 (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 24352 (* h1 h1 h1 h1) h2 h3 h5 (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 47520 (* h1 h1 h1 h1) h2 h3 h5 (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 59632 (* h1 h1 h1 h1) h2 h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 50172 (* h1 h1 h1 h1) h2 h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
28616 (* h1 h1 h1 h1) h2 h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 10920 (* h1 h1 
h1 h1) h2 h3 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 2672 (* h1 h1 h1 h1) h2 h3 h5 (* 
h6 h6 h6) (* j2 j2)) (* 380 (* h1 h1 h1 h1) h2 h3 h5 (* h6 h6 h6) j2) (* 24 (* 
h1 h1 h1 h1) h2 h3 h5 (* h6 h6 h6)) (* 120 (* h1 h1 h1 h1) h2 (* h4 h4) (* h5 h5
) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 928 (* h1 h1 h1 h1) h2 (* h4 h4) (* 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3122 (* h1 h1 h1 h1) h2 (* h4 h4) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6018 (* h1 h1 h1 h1) h2 (* h4 h4) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 7359 (* h1 h1 h1 h1) h2 (* h4 h4) (* 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 5963 (* h1 h1 h1 h1) h2 (* h4 h4) (* h5 h5) 
h6 (* j2 j2 j2 j2 j2)) (* 3242 (* h1 h1 h1 h1) h2 (* h4 h4) (* h5 h5) h6 (* j2 
j2 j2 j2)) (* 1168 (* h1 h1 h1 h1) h2 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 
267 (* h1 h1 h1 h1) h2 (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 35 (* h1 h1 h1 h1) 
h2 (* h4 h4) (* h5 h5) h6 j2) (* 2 (* h1 h1 h1 h1) h2 (* h4 h4) (* h5 h5) h6) 
(* 160 (* h1 h1 h1 h1) h2 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 1304 (* h1 h1 h1 h1) h2 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 4616 (* h1 h1 h1 h1) h2 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
9338 (* h1 h1 h1 h1) h2 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 11946 
(* h1 h1 h1 h1) h2 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 10093 (* h1 h1 
h1 h1) h2 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 5703 (* h1 h1 h1 h1) h2 h4 
(* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 2129 (* h1 h1 h1 h1) h2 h4 (* h5 h5 h5) h6 
(* j2 j2 j2)) (* 503 (* h1 h1 h1 h1) h2 h4 (* h5 h5 h5) h6 (* j2 j2)) (* 68 (* 
h1 h1 h1 h1) h2 h4 (* h5 h5 h5) h6 j2) (* 4 (* h1 h1 h1 h1) h2 h4 (* h5 h5 h5) 
h6) (* 400 (* h1 h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 3060 (* h1 h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 10260 (* h1 h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 19845 (* h1 h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 24507 (* h1 h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)
) (* 20180 (* h1 h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
11218 (* h1 h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 4157 (* h1 
h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 983 (* h1 h1 h1 h1) h2 h4 
(* h5 h5) (* h6 h6) (* j2 j2)) (* 134 (* h1 h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6) 
j2) (* 8 (* h1 h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6)) (* 320 (* h1 h1 h1 h1) h2 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2528 (* h1 h1 h1 h1
) h2 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8740 (* h1 h1 h1 
h1) h2 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 17392 (* h1 h1 h1 
h1) h2 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 22037 (* h1 h1 h1 h1)
 h2 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 18565 (* h1 h1 h1 h1) h2 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 10529 (* h1 h1 h1 h1) h2 (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2)) (* 3971 (* h1 h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6)
 (* j2 j2 j2)) (* 954 (* h1 h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 
132 (* h1 h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6) j2) (* 8 (* h1 h1 h1 h1) h2 (* h5 
h5 h5) (* h6 h6)) (* 320 (* h1 h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 2448 (* h1 h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 8248 (* h1 h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 16108 (* h1 h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 20182 (* h1 h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 16944 (* h1 h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2)) (* 9652 (* h1 h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 
3684 (* h1 h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 902 (* h1 h1 h1 
h1) h2 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 128 (* h1 h1 h1 h1) h2 (* h5 h5) (* 
h6 h6 h6) j2) (* 8 (* h1 h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6)) (* 1200 (* h1 h1 
h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 9160 (* 
h1 h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 30652 
(* h1 h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 59032 
(* h1 h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 72204 (* 
h1 h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 58376 (* h1 h1 
h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 31460 (* h1 h1 h1 h1) 
(* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 11112 (* h1 h1 h1 h1) (* h3 h3 h3)
 (* h4 h4) h5 (* j2 j2 j2)) (* 2452 (* h1 h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 
(* j2 j2)) (* 304 (* h1 h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 j2) (* 16 (* h1 h1 
h1 h1) (* h3 h3 h3) (* h4 h4) h5) (* 1600 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h5 
h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 12480 (* h1 h1 h1 h1) (* h3 h3 h3) h4 
(* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 42416 (* h1 h1 h1 h1) (* h3 h3 h3) 
h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 82352 (* h1 h1 h1 h1) (* h3 h3 h3) 
h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 100612 (* h1 h1 h1 h1) (* h3 h3 h3) h4
 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 80320 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h5
 h5) (* j2 j2 j2 j2 j2)) (* 42136 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* 
j2 j2 j2 j2)) (* 14240 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2)) 
(* 2948 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2)) (* 336 (* h1 h1 h1 
h1) (* h3 h3 h3) h4 (* h5 h5) j2) (* 16 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5
)) (* 4000 (* h1 h1 h1 h1) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 30800 (* h1 h1 h1 h1) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 104120 (* h1 h1 h1 h1) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 202936 (* h1 h1 h1 h1) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
251744 (* h1 h1 h1 h1) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 206944 
(* h1 h1 h1 h1) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 113720 (* h1 h1 h1 
h1) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 41080 (* h1 h1 h1 h1) (* h3 h3 h3)
 h4 h5 h6 (* j2 j2 j2)) (* 9296 (* h1 h1 h1 h1) (* h3 h3 h3) h4 h5 h6 (* j2 j2))
 (* 1184 (* h1 h1 h1 h1) (* h3 h3 h3) h4 h5 h6 j2) (* 64 (* h1 h1 h1 h1) (* h3 
h3 h3) h4 h5 h6) (* 3200 (* h1 h1 h1 h1) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 24960 (* h1 h1 h1 h1) (* h3 h3 h3) (* h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 84832 (* h1 h1 h1 h1) (* h3 h3 h3) (* h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 164704 (* h1 h1 h1 h1) (* h3 h3 h3) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 201224 (* h1 h1 h1 h1) (* h3 h3 h3) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 160640 (* h1 h1 h1 h1) (* h3 h3 h3) (* h5 h5) h6 (* j2
 j2 j2 j2 j2)) (* 84272 (* h1 h1 h1 h1) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2
)) (* 28480 (* h1 h1 h1 h1) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 5896 (* 
h1 h1 h1 h1) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2)) (* 672 (* h1 h1 h1 h1) (* h3 
h3 h3) (* h5 h5) h6 j2) (* 32 (* h1 h1 h1 h1) (* h3 h3 h3) (* h5 h5) h6) (* 3200
 (* h1 h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 24960 (* h1 h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2
)) (* 85632 (* h1 h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 169744 (* h1 h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2))
 (* 214672 (* h1 h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
180384 (* h1 h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 101600 
(* h1 h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 37712 (* h1 h1 h1 
h1) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 8784 (* h1 h1 h1 h1) (* h3 h3 h3)
 h5 (* h6 h6) (* j2 j2)) (* 1152 (* h1 h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6) j2) 
(* 64 (* h1 h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6)) (* 360 (* h1 h1 h1 h1) (* h3 h3
) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2724 (* h1 h1 h1 h1) (* 
h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 9022 (* h1 h1 h1 h1) 
(* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 17166 (* h1 h1 h1 h1) 
(* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 20698 (* h1 h1 h1 h1) (* 
h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 16454 (* h1 h1 h1 h1) (* h3 h3)
 (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 8694 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4 
h4) h5 (* j2 j2 j2 j2)) (* 3002 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 (* j2 
j2 j2)) (* 646 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2)) (* 78 (* h1 
h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 j2) (* 4 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4 
h4) h5) (* 960 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 7744 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 27204 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 54614 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 
h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 69109 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h5
 h5) (* j2 j2 j2 j2 j2 j2)) (* 57338 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 
h5) (* j2 j2 j2 j2 j2)) (* 31442 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) 
(* j2 j2 j2 j2)) (* 11206 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2
 j2)) (* 2477 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 306 
(* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) j2) (* 16 (* h1 h1 h1 h1) (* h3 h3
) (* h4 h4) (* h5 h5)) (* 1680 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) h5 h6 (* j2 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 12872 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) h5 h6 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 43260 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) h5 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 83732 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) h5 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 103012 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) h5 h6
 (* j2 j2 j2 j2 j2 j2)) (* 83844 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) h5 h6 (* j2
 j2 j2 j2 j2)) (* 45532 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2
)) (* 16220 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 3612 (* 
h1 h1 h1 h1) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 452 (* h1 h1 h1 h1) (* h3 
h3) (* h4 h4) h5 h6 j2) (* 24 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) h5 h6) (* 640 
(* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
5216 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 18464 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 37192 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
46920 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 38462 
(* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 20586 (* h1 h1 
h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 7050 (* h1 h1 h1 h1) (* h3 
h3) h4 (* h5 h5 h5) (* j2 j2 j2)) (* 1470 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5 
h5) (* j2 j2)) (* 168 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) j2) (* 8 (* h1 
h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5)) (* 3200 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 25960 (* h1 h1 h1 h1) (* h3 h3) h4 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 91932 (* h1 h1 h1 h1) (* h3 h3) 
h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 186554 (* h1 h1 h1 h1) (* h3 h3)
 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 239352 (* h1 h1 h1 h1) (* h3 h3) 
h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 202044 (* h1 h1 h1 h1) (* h3 h3) h4 
(* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 113140 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5
) h6 (* j2 j2 j2 j2)) (* 41322 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5) h6 (* j2 
j2 j2)) (* 9384 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 1192 (* 
h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5) h6 j2) (* 64 (* h1 h1 h1 h1) (* h3 h3) h4 
(* h5 h5) h6) (* 2560 (* h1 h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 19904 (* h1 h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 68032 (* h1 h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 134272 (* h1 h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6) (* j2
 j2 j2 j2 j2 j2 j2)) (* 168952 (* h1 h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 141128 (* h1 h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2
 j2 j2)) (* 78944 (* h1 h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 
29072 (* h1 h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 6712 (* h1 h1 
h1 h1) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 872 (* h1 h1 h1 h1) (* h3 h3) h4 
h5 (* h6 h6) j2) (* 48 (* h1 h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6)) (* 1280 (* h1 
h1 h1 h1) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 10432 
(* h1 h1 h1 h1) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
36928 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
74384 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
93840 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 76924 
(* h1 h1 h1 h1) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 41172 (* h1 h1 
h1 h1) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 14100 (* h1 h1 h1 h1) (* h3
 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 2940 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5 h5
) h6 (* j2 j2)) (* 336 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5 h5) h6 j2) (* 16 (* h1
 h1 h1 h1) (* h3 h3) (* h5 h5 h5) h6) (* 2560 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5
) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 20944 (* h1 h1 h1 h1) (* h3 h3
) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 75048 (* h1 h1 h1 h1) 
(* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 154652 (* h1 h1 h1
 h1) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 202268 (* h1 h1 
h1 h1) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 174736 (* h1 h1 
h1 h1) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 100512 (* h1 h1 h1 
h1) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 37820 (* h1 h1 h1 h1) (* 
h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 8860 (* h1 h1 h1 h1) (* h3 h3) (* h5
 h5) (* h6 h6) (* j2 j2)) (* 1160 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6) 
j2) (* 64 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6)) (* 1280 (* h1 h1 h1 h1)
 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 10112 (* h1 h1 
h1 h1) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 35200 (* h1 
h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 70944 (* h1 
h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 91440 (* h1 h1 
h1 h1) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 78512 (* h1 h1 h1 h1)
 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 45312 (* h1 h1 h1 h1) (* h3 h3
) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 17280 (* h1 h1 h1 h1) (* h3 h3) h5 (* h6 
h6 h6) (* j2 j2 j2)) (* 4144 (* h1 h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2)
) (* 560 (* h1 h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6) j2) (* 32 (* h1 h1 h1 h1) (* 
h3 h3) h5 (* h6 h6 h6)) (* 120 (* h1 h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 988 (* h1 h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3526 (* h1 h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5
) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 7160 (* h1 h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5)
 (* j2 j2 j2 j2 j2 j2 j2)) (* 9125 (* h1 h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) (* 
j2 j2 j2 j2 j2 j2)) (* 7591 (* h1 h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 
j2 j2 j2)) (* 4154 (* h1 h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) 
(* 1470 (* h1 h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 321 (* h1 h1 
h1 h1) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 39 (* h1 h1 h1 h1) h3 (* h4 h4 h4
) (* h5 h5) j2) (* 2 (* h1 h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5)) (* 160 (* h1 h1 
h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1384 (* 
h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 5188 
(* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 11054 
(* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 14756 (* 
h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 12827 (* h1 h1 
h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 7313 (* h1 h1 h1 h1) h3 
(* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 2687 (* h1 h1 h1 h1) h3 (* h4 h4) (* 
h5 h5 h5) (* j2 j2 j2)) (* 607 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* j2 
j2)) (* 76 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) j2) (* 4 (* h1 h1 h1 h1) h3
 (* h4 h4) (* h5 h5 h5)) (* 640 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 5236 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 18642 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 37915 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 48597 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 40838 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* 22680 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)
) (* 8183 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 1829 (* h1 
h1 h1 h1) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 228 (* h1 h1 h1 h1) h3 (* h4 
h4) (* h5 h5) h6 j2) (* 12 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5) h6) (* 640 (* 
h1 h1 h1 h1) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 5456 
(* h1 h1 h1 h1) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 20220 
(* h1 h1 h1 h1) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 42726 (* 
h1 h1 h1 h1) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 56743 (* h1 h1 
h1 h1) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 49237 (* h1 h1 h1 h1) h3 
h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 28121 (* h1 h1 h1 h1) h3 h4 (* h5 h5 
h5) h6 (* j2 j2 j2 j2)) (* 10389 (* h1 h1 h1 h1) h3 h4 (* h5 h5 h5) h6 (* j2 j2 
j2)) (* 2368 (* h1 h1 h1 h1) h3 h4 (* h5 h5 h5) h6 (* j2 j2)) (* 300 (* h1 h1 h1
 h1) h3 h4 (* h5 h5 h5) h6 j2) (* 16 (* h1 h1 h1 h1) h3 h4 (* h5 h5 h5) h6) (* 
1120 (* h1 h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 9128 (* h1 h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 32492 (* h1 h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 66318 (* h1 h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 85644 (* h1 h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
72824 (* h1 h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 41108 (* 
h1 h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 15142 (* h1 h1 h1 h1)
 h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 3468 (* h1 h1 h1 h1) h3 h4 (* h5 h5)
 (* h6 h6) (* j2 j2)) (* 444 (* h1 h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6) j2) (* 24
 (* h1 h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6)) (* 640 (* h1 h1 h1 h1) h3 (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 5376 (* h1 h1 h1 h1) h3 (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 19688 (* h1 h1 h1 h1) h3 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 41236 (* h1 h1 h1 h1) h3 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 54462 (* h1 h1 h1 h1) h3 (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 47166 (* h1 h1 h1 h1) h3 (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 26990 (* h1 h1 h1 h1) h3 (* h5 h5 h5) (* h6
 h6) (* j2 j2 j2 j2)) (* 10030 (* h1 h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6) (* j2 
j2 j2)) (* 2308 (* h1 h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 296 (* 
h1 h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6) j2) (* 16 (* h1 h1 h1 h1) h3 (* h5 h5 h5)
 (* h6 h6)) (* 640 (* h1 h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 5216 (* h1 h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 18624 (* h1 h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 38256 (* h1 h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 49900 (* h1 h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 43024 (* h1 h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)
) (* 24728 (* h1 h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 9312 
(* h1 h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 2188 (* h1 h1 h1 h1) 
h3 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 288 (* h1 h1 h1 h1) h3 (* h5 h5) (* h6 
h6 h6) j2) (* 16 (* h1 h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6)) (* 640 (* h1 h1 h1) 
(* h2 h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3392 (* h1 h1 h1) 
(* h2 h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 7520 (* h1 h1 h1) (* 
h2 h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2 j2 j2)) (* 9088 (* h1 h1 h1) (* h2 h2 
h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2 j2)) (* 6536 (* h1 h1 h1) (* h2 h2 h2 h2) (* 
h3 h3) h5 (* j2 j2 j2 j2)) (* 2860 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 (* 
j2 j2 j2)) (* 742 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 (* j2 j2)) (* 104 
(* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 j2) (* 6 (* h1 h1 h1) (* h2 h2 h2 h2) 
(* h3 h3) h5) (* 640 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h6 (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 3232 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 6912 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h6 (* j2 j2 j2 j2 j2 j2))
 (* 8160 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h6 (* j2 j2 j2 j2 j2)) (* 5808 
(* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h6 (* j2 j2 j2 j2)) (* 2550 (* h1 h1 h1) 
(* h2 h2 h2 h2) (* h3 h3) h6 (* j2 j2 j2)) (* 674 (* h1 h1 h1) (* h2 h2 h2 h2) 
(* h3 h3) h6 (* j2 j2)) (* 98 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h6 j2) (* 6
 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h6) (* 256 (* h1 h1 h1) (* h2 h2 h2 h2) 
h3 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1536 (* h1 h1 h1) (* h2 h2 h2 h2
) h3 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3968 (* h1 h1 h1) (* h2 h2 h2 h2)
 h3 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 5792 (* h1 h1 h1) (* h2 h2 h2 h2) h3 
(* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 5264 (* h1 h1 h1) (* h2 h2 h2 h2) h3 (* h5 
h5) (* j2 j2 j2 j2 j2)) (* 3088 (* h1 h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) (* j2 
j2 j2 j2)) (* 1168 (* h1 h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) (* j2 j2 j2)) (* 
274 (* h1 h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) (* j2 j2)) (* 36 (* h1 h1 h1) (* 
h2 h2 h2 h2) h3 (* h5 h5) j2) (* 2 (* h1 h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5)) 
(* 448 (* h1 h1 h1) (* h2 h2 h2 h2) h3 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
2624 (* h1 h1 h1) (* h2 h2 h2 h2) h3 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6736 
(* h1 h1 h1) (* h2 h2 h2 h2) h3 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 9936 (* h1 h1
 h1) (* h2 h2 h2 h2) h3 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 9268 (* h1 h1 h1) (* h2 
h2 h2 h2) h3 h5 h6 (* j2 j2 j2 j2 j2)) (* 5660 (* h1 h1 h1) (* h2 h2 h2 h2) h3 
h5 h6 (* j2 j2 j2 j2)) (* 2259 (* h1 h1 h1) (* h2 h2 h2 h2) h3 h5 h6 (* j2 j2 j2
)) (* 567 (* h1 h1 h1) (* h2 h2 h2 h2) h3 h5 h6 (* j2 j2)) (* 81 (* h1 h1 h1) 
(* h2 h2 h2 h2) h3 h5 h6 j2) (* 5 (* h1 h1 h1) (* h2 h2 h2 h2) h3 h5 h6) (* 128 
(* h1 h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 800
 (* h1 h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2176 
(* h1 h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3376 (* 
h1 h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3288 (* h1 h1 
h1) (* h2 h2 h2 h2) h3 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2082 (* h1 h1 h1) (* h2 
h2 h2 h2) h3 (* h6 h6) (* j2 j2 j2 j2)) (* 856 (* h1 h1 h1) (* h2 h2 h2 h2) h3 
(* h6 h6) (* j2 j2 j2)) (* 220 (* h1 h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6) (* j2 
j2)) (* 32 (* h1 h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6) j2) (* 2 (* h1 h1 h1) (* h2
 h2 h2 h2) h3 (* h6 h6)) (* 128 (* h1 h1 h1) (* h2 h2 h2 h2) (* h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 832 (* h1 h1 h1) (* h2 h2 h2 h2) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2400 (* h1 h1 h1) (* h2 h2 h2 h2) (* h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4048 (* h1 h1 h1) (* h2 h2 h2 h2) (* h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 4424 (* h1 h1 h1) (* h2 h2 h2 h2) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 3276 (* h1 h1 h1) (* h2 h2 h2 h2) (* h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* 1666 (* h1 h1 h1) (* h2 h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2 j2))
 (* 575 (* h1 h1 h1) (* h2 h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2)) (* 129 (* h1 h1 
h1) (* h2 h2 h2 h2) (* h5 h5) h6 (* j2 j2)) (* 17 (* h1 h1 h1) (* h2 h2 h2 h2) 
(* h5 h5) h6 j2) (* (* h1 h1 h1) (* h2 h2 h2 h2) (* h5 h5) h6) (* 64 (* h1 h1 h1
) (* h2 h2 h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 448 (* h1 
h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1392 (* 
h1 h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2528 (* 
h1 h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2972 (* h1 
h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2364 (* h1 h1 h1) 
(* h2 h2 h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1289 (* h1 h1 h1) (* h2 h2 
h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 476 (* h1 h1 h1) (* h2 h2 h2 h2) h5 (* 
h6 h6) (* j2 j2 j2)) (* 114 (* h1 h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6) (* j2 j2))
 (* 16 (* h1 h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6) j2) (* (* h1 h1 h1) (* h2 h2 h2
 h2) h5 (* h6 h6)) (* 2240 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 15232 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2
 j2 j2 j2 j2)) (* 41008 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2
 j2 j2)) (* 57192 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2 j2)) 
(* 45120 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2)) (* 20638 (* 
h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2)) (* 5398 (* h1 h1 h1) (* h2 
h2 h2) (* h3 h3 h3) h5 (* j2 j2)) (* 746 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) 
h5 j2) (* 42 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5) (* 2240 (* h1 h1 h1) (* 
h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 14672 (* h1 h1 h1) (* 
h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 38040 (* h1 h1 h1) (* h2 
h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2 j2 j2 j2)) (* 51532 (* h1 h1 h1) (* h2 h2 h2)
 (* h3 h3 h3) h6 (* j2 j2 j2 j2 j2)) (* 40054 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3
 h3) h6 (* j2 j2 j2 j2)) (* 18372 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h6 (* 
j2 j2 j2)) (* 4904 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2)) (* 704 
(* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h6 j2) (* 42 (* h1 h1 h1) (* h2 h2 h2) 
(* h3 h3 h3) h6) (* 704 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 8528 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 34032 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2 
j2 j2 j2 j2)) (* 67792 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2 
j2 j2)) (* 77720 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2 j2)) 
(* 54183 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2)) (* 23168 (* 
h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2)) (* 5880 (* h1 h1 h1) (* h2 
h2 h2) (* h3 h3) h4 h5 (* j2 j2)) (* 804 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 
h5 j2) (* 45 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5) (* 384 (* h1 h1 h1) (* 
h2 h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 5216 (* h1 h1 h1) 
(* h2 h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 21152 (* h1 h1 h1) 
(* h2 h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 42280 (* h1 h1 h1) (* 
h2 h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2)) (* 48816 (* h1 h1 h1) (* h2 h2 
h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 34592 (* h1 h1 h1) (* h2 h2 h2) (* h3
 h3) h4 h6 (* j2 j2 j2 j2)) (* 15220 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h6 
(* j2 j2 j2)) (* 4036 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h6 (* j2 j2)) (* 
588 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h6 j2) (* 36 (* h1 h1 h1) (* h2 h2 h2
) (* h3 h3) h4 h6) (* 1408 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 11168 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5)
 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 35984 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h5
 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 62384 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* 
h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 64452 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h5
 h5) (* j2 j2 j2 j2 j2)) (* 41338 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) 
(* j2 j2 j2 j2)) (* 16552 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) (* j2 j2
 j2)) (* 4012 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) (* j2 j2)) (* 536 
(* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) j2) (* 30 (* h1 h1 h1) (* h2 h2 h2
) (* h3 h3) (* h5 h5)) (* 2592 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 h6 (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 20640 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 66616 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 h6 (* 
j2 j2 j2 j2 j2 j2 j2)) (* 116440 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 h6 (* j2
 j2 j2 j2 j2 j2)) (* 122556 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 h6 (* j2 j2 
j2 j2 j2)) (* 80964 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2)) 
(* 33693 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2)) (* 8541 (* h1 
h1 h1) (* h2 h2 h2) (* h3 h3) h5 h6 (* j2 j2)) (* 1199 (* h1 h1 h1) (* h2 h2 h2)
 (* h3 h3) h5 h6 j2) (* 71 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 h6) (* 960 (* 
h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
8272 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 27976 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2))
 (* 50628 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 54946 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
37410 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 16064 
(* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2)) (* 4212 (* h1 h1 h1)
 (* h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2)) (* 614 (* h1 h1 h1) (* h2 h2 h2) 
(* h3 h3) (* h6 h6) j2) (* 38 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6)) (* 
128 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (* 2464 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2
)) (* 12624 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 31616 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 46344 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 
42814 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 25599 (* 
h1 h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2)) (* 9846 (* h1 h1 h1) (* 
h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2)) (* 2336 (* h1 h1 h1) (* h2 h2 h2) h3 h4 
(* h5 h5) (* j2 j2)) (* 308 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) j2) (* 17 
(* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5)) (* 256 (* h1 h1 h1) (* h2 h2 h2) h3 
h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3728 (* h1 h1 h1) (* h2 h2 h2) h3
 h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 17280 (* h1 h1 h1) (* h2 h2 h2) h3 
h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 41056 (* h1 h1 h1) (* h2 h2 h2) h3 h4 
h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 58700 (* h1 h1 h1) (* h2 h2 h2) h3 h4 h5 h6 
(* j2 j2 j2 j2 j2 j2)) (* 54079 (* h1 h1 h1) (* h2 h2 h2) h3 h4 h5 h6 (* j2 j2 
j2 j2 j2)) (* 32901 (* h1 h1 h1) (* h2 h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2)) (* 
13130 (* h1 h1 h1) (* h2 h2 h2) h3 h4 h5 h6 (* j2 j2 j2)) (* 3298 (* h1 h1 h1) 
(* h2 h2 h2) h3 h4 h5 h6 (* j2 j2)) (* 471 (* h1 h1 h1) (* h2 h2 h2) h3 h4 h5 h6
 j2) (* 29 (* h1 h1 h1) (* h2 h2 h2) h3 h4 h5 h6) (* 320 (* h1 h1 h1) (* h2 h2 
h2) h3 h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2128 (* h1 h1 h1) (* h2 
h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6160 (* h1 h1 h1) (* h2 
h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 10164 (* h1 h1 h1) (* h2 h2 
h2) h3 h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 10508 (* h1 h1 h1) (* h2 h2 h2) h3
 h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 7040 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h6 
h6) (* j2 j2 j2 j2)) (* 3048 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6) (* j2 j2 
j2)) (* 820 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6) (* j2 j2)) (* 124 (* h1 h1
 h1) (* h2 h2 h2) h3 h4 (* h6 h6) j2) (* 8 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h6
 h6)) (* 576 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 3776 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 10640 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 
j2)) (* 16872 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) 
(* 16552 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 10394 
(* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 4168 (* h1 h1 h1) 
(* h2 h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2)) (* 1026 (* h1 h1 h1) (* h2 h2 h2) h3 
(* h5 h5 h5) (* j2 j2)) (* 140 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) j2) (* 
8 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5)) (* 960 (* h1 h1 h1) (* h2 h2 h2) h3
 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8496 (* h1 h1 h1) (* h2 h2 
h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 31184 (* h1 h1 h1) (* h2 
h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 63768 (* h1 h1 h1) (* h2 
h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 81400 (* h1 h1 h1) (* h2 h2 
h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 68303 (* h1 h1 h1) (* h2 h2 h2) h3
 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 38356 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5
) h6 (* j2 j2 j2 j2)) (* 14279 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) h6 (* j2 
j2 j2)) (* 3377 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) h6 (* j2 j2)) (* 458 (* 
h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) h6 j2) (* 27 (* h1 h1 h1) (* h2 h2 h2) h3 
(* h5 h5) h6) (* 608 (* h1 h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 5664 (* h1 h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 21816 (* h1 h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 47000 (* h1 h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 63564 (* h1 h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 56782 (* h1 h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2)
) (* 34043 (* h1 h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 13540 
(* h1 h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2)) (* 3418 (* h1 h1 h1) (* 
h2 h2 h2) h3 h5 (* h6 h6) (* j2 j2)) (* 494 (* h1 h1 h1) (* h2 h2 h2) h3 h5 (* 
h6 h6) j2) (* 31 (* h1 h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6)) (* 320 (* h1 h1 h1) 
(* h2 h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2128 (* h1 h1 h1
) (* h2 h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6160 (* h1 h1 h1)
 (* h2 h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 10164 (* h1 h1 h1) 
(* h2 h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 10508 (* h1 h1 h1) (* h2 
h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 7040 (* h1 h1 h1) (* h2 h2 h2) h3 
(* h6 h6 h6) (* j2 j2 j2 j2)) (* 3048 (* h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6) 
(* j2 j2 j2)) (* 820 (* h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6) (* j2 j2)) (* 124
 (* h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6) j2) (* 8 (* h1 h1 h1) (* h2 h2 h2) h3
 (* h6 h6 h6)) (* 544 (* h1 h1 h1) (* h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 3792 (* h1 h1 h1) (* h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 11696 (* h1 h1 h1) (* h2 h2 h2) h4 (* h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 21016 (* h1 h1 h1) (* h2 h2 h2) h4 (* h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2)) (* 24362 (* h1 h1 h1) (* h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2 
j2 j2 j2 j2)) (* 19041 (* h1 h1 h1) (* h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2 
j2)) (* 10166 (* h1 h1 h1) (* h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 3663
 (* h1 h1 h1) (* h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 853 (* h1 h1 h1) (* 
h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2)) (* 116 (* h1 h1 h1) (* h2 h2 h2) h4 (* h5 
h5) h6 j2) (* 7 (* h1 h1 h1) (* h2 h2 h2) h4 (* h5 h5) h6) (* 160 (* h1 h1 h1) 
(* h2 h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1184 (* h1 h1
 h1) (* h2 h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3888 (* h1 
h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 7456 (* h1 
h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 9242 (* h1 h1 
h1) (* h2 h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 7734 (* h1 h1 h1) (* 
h2 h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 4424 (* h1 h1 h1) (* h2 h2 h2) 
h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 1708 (* h1 h1 h1) (* h2 h2 h2) h4 h5 (* h6 
h6) (* j2 j2 j2)) (* 426 (* h1 h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6) (* j2 j2)) 
(* 62 (* h1 h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6) j2) (* 4 (* h1 h1 h1) (* h2 h2 
h2) h4 h5 (* h6 h6)) (* 288 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 2032 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 6336 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 11496 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 13442 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2)) (* 10587 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2)) (* 5691 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) 
(* 2063 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 483 (* h1 h1 
h1) (* h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2)) (* 66 (* h1 h1 h1) (* h2 h2 h2) (* 
h5 h5 h5) h6 j2) (* 4 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5 h5) h6) (* 432 (* h1 h1
 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3120
 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 9976 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 18592 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 22363 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2
)) (* 18141 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 10053 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 3759 
(* h1 h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 908 (* h1 h1 h1) 
(* h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 j2)) (* 128 (* h1 h1 h1) (* h2 h2 h2) (* 
h5 h5) (* h6 h6) j2) (* 8 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6)) (* 160 
(* h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
1184 (* h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 3888 (* h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 7456 (* h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
9242 (* h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 7734 
(* h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 4424 (* h1 h1 
h1) (* h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1708 (* h1 h1 h1) (* h2 h2 
h2) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 426 (* h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6 
h6) (* j2 j2)) (* 62 (* h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6) j2) (* 4 (* h1 h1
 h1) (* h2 h2 h2) h5 (* h6 h6 h6)) (* 1600 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3
) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 9920 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3)
 h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 25952 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5
 (* j2 j2 j2 j2 j2 j2)) (* 37176 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 (* j2
 j2 j2 j2 j2)) (* 31632 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2 j2 j2
)) (* 16208 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2 j2)) (* 4832 (* 
h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2)) (* 760 (* h1 h1 h1) (* h2 h2) 
(* h3 h3 h3 h3) h5 j2) (* 48 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5) (* 1600 
(* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 9520 
(* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 24072 (* 
h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2 j2 j2 j2 j2)) (* 33608 (* h1 h1 
h1) (* h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2 j2 j2 j2)) (* 28160 (* h1 h1 h1) (* h2
 h2) (* h3 h3 h3 h3) h6 (* j2 j2 j2 j2)) (* 14400 (* h1 h1 h1) (* h2 h2) (* h3 
h3 h3 h3) h6 (* j2 j2 j2)) (* 4360 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h6 (* 
j2 j2)) (* 712 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h6 j2) (* 48 (* h1 h1 h1) 
(* h2 h2) (* h3 h3 h3 h3) h6) (* 2464 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 27064 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 
h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 106680 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4
 h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 215118 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 
h5 (* j2 j2 j2 j2 j2 j2)) (* 251572 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 
(* j2 j2 j2 j2 j2)) (* 178867 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2
 j2 j2)) (* 77654 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2)) (* 
19902 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2)) (* 2734 (* h1 h1 h1) 
(* h2 h2) (* h3 h3 h3) h4 h5 j2) (* 153 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 
h5) (* 1344 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2 j2
 j2)) (* 14992 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2
 j2)) (* 58432 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2
)) (* 116604 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2)) 
(* 136208 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 98084
 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 43872 (* h1 h1 h1
) (* h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2)) (* 11812 (* h1 h1 h1) (* h2 h2) (* 
h3 h3 h3) h4 h6 (* j2 j2)) (* 1744 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h6 j2)
 (* 108 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h6) (* 2432 (* h1 h1 h1) (* h2 h2
) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 21472 (* h1 h1 h1) 
(* h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 76224 (* h1 h1 
h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 143840 (* h1 
h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 159036 (* h1 
h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 106640 (* h1 h1 
h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 43450 (* h1 h1 h1) (* 
h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2)) (* 10496 (* h1 h1 h1) (* h2 h2) (* 
h3 h3 h3) (* h5 h5) (* j2 j2)) (* 1382 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h5
 h5) j2) (* 76 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5)) (* 4704 (* h1 h1 
h1) (* h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 41608 (* h1 
h1 h1) (* h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 146704 (* h1
 h1 h1) (* h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 275626 (* h1 
h1 h1) (* h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 306372 (* h1 h1 h1
) (* h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 209644 (* h1 h1 h1) (* h2 
h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 88638 (* h1 h1 h1) (* h2 h2) (* h3 h3
 h3) h5 h6 (* j2 j2 j2)) (* 22484 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 h6 (* 
j2 j2)) (* 3126 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 h6 j2) (* 182 (* h1 h1 h1
) (* h2 h2) (* h3 h3 h3) h5 h6) (* 2112 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 19696 (* h1 h1 h1) (* h2 h2) (* h3 h3 
h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 70840 (* h1 h1 h1) (* h2 h2) (* h3
 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 135072 (* h1 h1 h1) (* h2 h2) (* 
h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 153320 (* h1 h1 h1) (* h2 h2) (* 
h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 108392 (* h1 h1 h1) (* h2 h2) (* h3 
h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 47976 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) 
(* h6 h6) (* j2 j2 j2)) (* 12880 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6) 
(* j2 j2)) (* 1912 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6) j2) (* 120 (* 
h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6)) (* 192 (* h1 h1 h1) (* h2 h2) (* h3 
h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4528 (* h1 h1 h1) (* h2 
h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 26876 (* h1 h1 h1)
 (* h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 76608 (* h1 h1
 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 125789 (* h1 
h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 127817 (* h1 
h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 82262 (* h1 h1 h1
) (* h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 33236 (* h1 h1 h1) (* h2 
h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 8079 (* h1 h1 h1) (* h2 h2) (* h3 h3
) (* h4 h4) h5 (* j2 j2)) (* 1067 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 
j2) (* 58 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5) (* 960 (* h1 h1 h1) (* 
h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 7424 (* h1 h1 
h1) (* h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 23932 (* h1
 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 42462 (* 
h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 45784 (* h1
 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 31106 (* h1 h1 
h1) (* h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2)) (* 13308 (* h1 h1 h1) (* 
h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2 j2)) (* 3458 (* h1 h1 h1) (* h2 h2) (* h3
 h3) (* h4 h4) h6 (* j2 j2)) (* 496 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) 
h6 j2) (* 30 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h6) (* 704 (* h1 h1 h1) 
(* h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 12160 (* 
h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
64480 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2))
 (* 171560 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2
)) (* 268632 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)
) (* 264164 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) 
(* 166634 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 
66865 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 16393 (* h1
 h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2)) (* 2219 (* h1 h1 h1) (* h2 
h2) (* h3 h3) h4 (* h5 h5) j2) (* 125 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 
h5)) (* 1536 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 22952 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 114196 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2
 j2 j2 j2 j2)) (* 292102 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 
j2 j2 j2 j2)) (* 446147 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2
 j2 j2)) (* 433266 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2))
 (* 273171 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 110842 
(* h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 27761 (* h1 h1 h1) 
(* h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2)) (* 3878 (* h1 h1 h1) (* h2 h2) (* h3 h3)
 h4 h5 h6 j2) (* 229 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6) (* 2560 (* h1 h1
 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 19184 
(* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
60788 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 107174 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 115948 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
79822 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 34972 
(* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2)) (* 9410 (* h1 h1 h1)
 (* h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2)) (* 1412 (* h1 h1 h1) (* h2 h2) (* 
h3 h3) h4 (* h6 h6) j2) (* 90 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6)) (* 
1792 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2
)) (* 13248 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 41824 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2
 j2 j2)) (* 73328 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 
j2 j2)) (* 77840 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2
)) (* 51312 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 
20840 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2)) (* 5032 (* h1 
h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2)) (* 660 (* h1 h1 h1) (* h2 h2)
 (* h3 h3) (* h5 h5 h5) j2) (* 36 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5))
 (* 2624 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 27264 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 113312 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 256420 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 355276 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2)) (* 317395 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) 
h6 (* j2 j2 j2 j2 j2)) (* 185996 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) h6 
(* j2 j2 j2 j2)) (* 70818 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2
 j2)) (* 16808 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2)) (* 2247 
(* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) h6 j2) (* 128 (* h1 h1 h1) (* h2 h2) 
(* h3 h3) (* h5 h5) h6) (* 2016 (* h1 h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 22504 (* h1 h1 h1) (* h2 h2) (* h3 h3) h5 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 97936 (* h1 h1 h1) (* h2 h2) (* h3 
h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 230986 (* h1 h1 h1) (* h2 h2) 
(* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 334440 (* h1 h1 h1) (* h2 h2
) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 314086 (* h1 h1 h1) (* h2 h2)
 (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 194960 (* h1 h1 h1) (* h2 h2) (* 
h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 79276 (* h1 h1 h1) (* h2 h2) (* h3 h3) 
h5 (* h6 h6) (* j2 j2 j2)) (* 20250 (* h1 h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6
) (* j2 j2)) (* 2932 (* h1 h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6) j2) (* 182 
(* h1 h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6)) (* 1600 (* h1 h1 h1) (* h2 h2) 
(* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 11760 (* h1 h1 h1) (* 
h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 36856 (* h1 h1 h1)
 (* h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 64712 (* h1 h1 h1
) (* h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 70164 (* h1 h1 h1) 
(* h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 48716 (* h1 h1 h1) (* h2
 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 21664 (* h1 h1 h1) (* h2 h2) (* 
h3 h3) (* h6 h6 h6) (* j2 j2 j2)) (* 5952 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h6
 h6 h6) (* j2 j2)) (* 916 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6) j2) (* 
60 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6)) (* 544 (* h1 h1 h1) (* h2 h2) 
h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 5320 (* h1 h1 h1) 
(* h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 21860 (* h1 
h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 50026 
(* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 70791
 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 64740 
(* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 38701 (* h1
 h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 14898 (* h1 h1 h1) 
(* h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 3523 (* h1 h1 h1) (* h2 h2) h3
 (* h4 h4) (* h5 h5) (* j2 j2)) (* 460 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h5
 h5) j2) (* 25 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5)) (* 640 (* h1 h1 h1
) (* h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 5404 (* h1 
h1 h1) (* h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 19716 (* 
h1 h1 h1) (* h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 41085 (* 
h1 h1 h1) (* h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 54259 (* h1 
h1 h1) (* h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 47491 (* h1 h1 h1)
 (* h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 27901 (* h1 h1 h1) (* h2 h2
) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 10859 (* h1 h1 h1) (* h2 h2) h3 (* h4 
h4) h5 h6 (* j2 j2 j2)) (* 2677 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) h5 h6 (* j2 
j2)) (* 377 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) h5 h6 j2) (* 23 (* h1 h1 h1) (* 
h2 h2) h3 (* h4 h4) h5 h6) (* 48 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 340 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1050 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1850 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2042 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* 
h6 h6) (* j2 j2 j2 j2 j2)) (* 1458 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h6 h6)
 (* j2 j2 j2 j2)) (* 670 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 j2 
j2)) (* 190 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 j2)) (* 30 (* h1
 h1 h1) (* h2 h2) h3 (* h4 h4) (* h6 h6) j2) (* 2 (* h1 h1 h1) (* h2 h2) h3 (* 
h4 h4) (* h6 h6)) (* 288 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 3584 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 17072 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 43384 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 66602 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) (* j2 
j2 j2 j2 j2 j2)) (* 65158 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 
j2 j2)) (* 41288 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 
16740 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2)) (* 4150 (* h1 h1 
h1) (* h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2)) (* 566 (* h1 h1 h1) (* h2 h2) h3 h4 
(* h5 h5 h5) j2) (* 32 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5)) (* 3376 (* h1 
h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 27592 
(* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
98892 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
203914 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
266992 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
231286 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 133941 
(* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 51120 (* h1 h1 h1)
 (* h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2)) (* 12292 (* h1 h1 h1) (* h2 h2) h3 
h4 (* h5 h5) h6 (* j2 j2)) (* 1680 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6 j2)
 (* 99 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6) (* 1760 (* h1 h1 h1) (* h2 h2)
 h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 14556 (* h1 h1 h1) (* 
h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 52444 (* h1 h1 h1) 
(* h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 108609 (* h1 h1 h1)
 (* h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 143329 (* h1 h1 h1) 
(* h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 126015 (* h1 h1 h1) (* h2
 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 74775 (* h1 h1 h1) (* h2 h2) h3 
h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 29575 (* h1 h1 h1) (* h2 h2) h3 h4 h5 (* h6 
h6) (* j2 j2 j2)) (* 7463 (* h1 h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2)) 
(* 1085 (* h1 h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6) j2) (* 69 (* h1 h1 h1) (* h2 
h2) h3 h4 h5 (* h6 h6)) (* 112 (* h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 804 (* h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 2522 (* h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 4526 (* h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 5106 (* h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2 j2 j2 
j2)) (* 3742 (* h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1774 
(* h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2 j2)) (* 522 (* h1 h1 h1) (* 
h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2)) (* 86 (* h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6
 h6) j2) (* 6 (* h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6 h6)) (* 128 (* h1 h1 h1) (* 
h2 h2) h3 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 928 (* h1 h1 h1) 
(* h2 h2) h3 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2896 (* h1 h1 h1) 
(* h2 h2) h3 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 5088 (* h1 h1 h1) (* 
h2 h2) h3 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 5524 (* h1 h1 h1) (* h2 h2) 
h3 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 3826 (* h1 h1 h1) (* h2 h2) h3 (* h5 
h5 h5 h5) (* j2 j2 j2 j2)) (* 1682 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) (* 
j2 j2 j2)) (* 450 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) (* j2 j2)) (* 66 (* 
h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) j2) (* 4 (* h1 h1 h1) (* h2 h2) h3 (* h5 
h5 h5 h5)) (* 1472 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 11936 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 42312 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 85988 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2)) (* 110522 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2
 j2 j2 j2)) (* 93595 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2
)) (* 52779 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 19549 
(* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 4549 (* h1 h1 h1) (* 
h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2)) (* 600 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 
h5) h6 j2) (* 34 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) h6) (* 2608 (* h1 h1 h1)
 (* h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 21024 
(* h1 h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 74324 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 151348 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 196186 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 168914 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 97776 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 
37590 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 9198 (* h1 
h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2)) (* 1296 (* h1 h1 h1) (* h2 h2
) h3 (* h5 h5) (* h6 h6) j2) (* 80 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6)
) (* 1120 (* h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 9136 (* h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 32620 (* h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 67210 (* h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 88558 (* h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)
) (* 78014 (* h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
46558 (* h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 18598 (* h1 
h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 4762 (* h1 h1 h1) (* h2 h2)
 h3 h5 (* h6 h6 h6) (* j2 j2)) (* 706 (* h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6) 
j2) (* 46 (* h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6)) (* 64 (* h1 h1 h1) (* h2 h2
) h3 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 464 (* h1 h1 h1) (* h2 
h2) h3 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1472 (* h1 h1 h1) (* h2 
h2) h3 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2676 (* h1 h1 h1) (* h2 h2) 
h3 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3064 (* h1 h1 h1) (* h2 h2) h3 (* 
h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2284 (* h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6 
h6) (* j2 j2 j2 j2)) (* 1104 (* h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6 h6) (* j2 j2 
j2)) (* 332 (* h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6 h6) (* j2 j2)) (* 56 (* h1 h1 
h1) (* h2 h2) h3 (* h6 h6 h6 h6) j2) (* 4 (* h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6 
h6)) (* 328 (* h1 h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 2484 (* h1 h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 8282 (* h1 h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 15995 (* h1 h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 19799 (* h1 h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) h6
 (* j2 j2 j2 j2 j2 j2)) (* 16401 (* h1 h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) h6 
(* j2 j2 j2 j2 j2)) (* 9203 (* h1 h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 
j2 j2 j2)) (* 3453 (* h1 h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) 
(* 829 (* h1 h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 115 (* h1 h1 
h1) (* h2 h2) (* h4 h4) (* h5 h5) h6 j2) (* 7 (* h1 h1 h1) (* h2 h2) (* h4 h4) 
(* h5 h5) h6) (* 24 (* h1 h1 h1) (* h2 h2) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2
 j2 j2 j2 j2 j2 j2)) (* 188 (* h1 h1 h1) (* h2 h2) (* h4 h4) h5 (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 654 (* h1 h1 h1) (* h2 h2) (* h4 h4) h5 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1329 (* h1 h1 h1) (* h2 h2) (* h4 h4) h5 (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1745 (* h1 h1 h1) (* h2 h2) (* h4 h4) h5 (* h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 1545 (* h1 h1 h1) (* h2 h2) (* h4 h4) h5 (* h6 h6)
 (* j2 j2 j2 j2 j2)) (* 933 (* h1 h1 h1) (* h2 h2) (* h4 h4) h5 (* h6 h6) (* j2 
j2 j2 j2)) (* 379 (* h1 h1 h1) (* h2 h2) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2)) 
(* 99 (* h1 h1 h1) (* h2 h2) (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 15 (* h1 h1 h1
) (* h2 h2) (* h4 h4) h5 (* h6 h6) j2) (* (* h1 h1 h1) (* h2 h2) (* h4 h4) h5 
(* h6 h6)) (* 464 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2
 j2 j2 j2 j2)) (* 3568 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 12088 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 23736 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2)) (* 29889 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2)) (* 25203 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) 
(* 14407 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 5513 (* 
h1 h1 h1) (* h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 1352 (* h1 h1 h1) (* h2 
h2) h4 (* h5 h5 h5) h6 (* j2 j2)) (* 192 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5 h5) 
h6 j2) (* 12 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5 h5) h6) (* 792 (* h1 h1 h1) (* 
h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 6044 (* h1 
h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 20350
 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
39785 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 49989 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 42165 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
24177 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 9307 (* 
h1 h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 2303 (* h1 h1 h1) 
(* h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 331 (* h1 h1 h1) (* h2 h2) h4 (* 
h5 h5) (* h6 h6) j2) (* 21 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6)) (* 56 
(* h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
444 (* h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 1566 (* h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 3233 (* h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
4323 (* h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3909 
(* h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2419 (* h1 h1 
h1) (* h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1011 (* h1 h1 h1) (* h2 h2)
 h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 273 (* h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6 
h6) (* j2 j2)) (* 43 (* h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6 h6) j2) (* 3 (* h1 h1
 h1) (* h2 h2) h4 h5 (* h6 h6 h6)) (* 64 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 496 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1696 (* h1 h1 h1) (* h2 h2) (* h5 h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3368 (* h1 h1 h1) (* h2 h2) (* h5 h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 4300 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 3687 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5 h5) h6 
(* j2 j2 j2 j2 j2)) (* 2150 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5 h5) h6 (* j2 j2 
j2 j2)) (* 842 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 212 
(* h1 h1 h1) (* h2 h2) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 31 (* h1 h1 h1) (* h2 h2
) (* h5 h5 h5 h5) h6 j2) (* 2 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5 h5) h6) (* 464 
(* h1 h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (* 3624 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 12460 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 24818 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 31696 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2
 j2 j2 j2)) (* 27111 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2)) (* 15727 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) 
(* 6111 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 1523 (* 
h1 h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 220 (* h1 h1 h1) (* h2 
h2) (* h5 h5 h5) (* h6 h6) j2) (* 14 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 
h6)) (* 456 (* h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 3500 (* h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 11870 (* h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 23413 (* h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 29734 (* h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2)) (* 25401 (* h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2)) (* 14784 (* h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6) (* j2
 j2 j2 j2)) (* 5791 (* h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) 
(* 1462 (* h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 215 (* h1 h1
 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6) j2) (* 14 (* h1 h1 h1) (* h2 h2) (* h5 h5)
 (* h6 h6 h6)) (* 32 (* h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 256 (* h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 912 (* h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 1904 (* h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 2578 (* h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 2364 (* h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 1486 (* h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 632 (* h1 
h1 h1) (* h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 174 (* h1 h1 h1) (* h2 h2) 
h5 (* h6 h6 h6 h6) (* j2 j2)) (* 28 (* h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6 h6) j2
) (* 2 (* h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6 h6)) (* 1760 (* h1 h1 h1) h2 (* h3 
h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 12704 (* h1 h1 h1) h2 (* h3 
h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 39680 (* h1 h1 h1) h2 (* h3 h3 
h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 70092 (* h1 h1 h1) h2 (* h3 h3 h3 h3) 
h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 76756 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h5 (* 
j2 j2 j2 j2 j2)) (* 53680 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2))
 (* 23784 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2)) (* 6380 (* h1 h1 
h1) h2 (* h3 h3 h3 h3) h4 h5 (* j2 j2)) (* 932 (* h1 h1 h1) h2 (* h3 h3 h3 h3) 
h4 h5 j2) (* 56 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h5) (* 960 (* h1 h1 h1) h2 
(* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 6704 (* h1 h1 h1) h2 
(* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 20368 (* h1 h1 h1) h2 (* 
h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 35216 (* h1 h1 h1) h2 (* h3 h3 
h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2)) (* 38032 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 
h6 (* j2 j2 j2 j2 j2)) (* 26480 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h6 (* j2 j2 
j2 j2)) (* 11824 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2)) (* 3248 (* 
h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h6 (* j2 j2)) (* 496 (* h1 h1 h1) h2 (* h3 h3 h3
 h3) h4 h6 j2) (* 32 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h6) (* 1280 (* h1 h1 h1)
 h2 (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 9472 (* h1 h1 
h1) h2 (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 30144 (* h1 h1 
h1) h2 (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 53824 (* h1 h1 h1)
 h2 (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 58960 (* h1 h1 h1) h2 
(* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 40672 (* h1 h1 h1) h2 (* h3 h3 
h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 17440 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h5
 h5) (* j2 j2 j2)) (* 4416 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) (* j2 j2)) 
(* 592 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) j2) (* 32 (* h1 h1 h1) h2 (* h3
 h3 h3 h3) (* h5 h5)) (* 2560 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 18464 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 57616 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 
j2 j2 j2)) (* 101656 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2)
) (* 111160 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 77600 
(* h1 h1 h1) h2 (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 34304 (* h1 h1 h1) h2 
(* h3 h3 h3 h3) h5 h6 (* j2 j2 j2)) (* 9176 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h5 
h6 (* j2 j2)) (* 1336 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h5 h6 j2) (* 80 (* h1 h1 
h1) h2 (* h3 h3 h3 h3) h5 h6) (* 1280 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 9152 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 28576 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6
) (* j2 j2 j2 j2 j2 j2 j2)) (* 51008 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 57184 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6) (* j2 
j2 j2 j2 j2)) (* 41600 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2)
) (* 19552 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2)) (* 5696 (* h1
 h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6) (* j2 j2)) (* 928 (* h1 h1 h1) h2 (* h3 h3 
h3 h3) (* h6 h6) j2) (* 64 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6)) (* 672 (* 
h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
11096 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 57428 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 149996 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 231538 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 
225460 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 141430 
(* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 56564 (* h1 h1 h1)
 h2 (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 13790 (* h1 h1 h1) h2 (* h3 h3 h3
) (* h4 h4) h5 (* j2 j2)) (* 1844 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 j2) 
(* 102 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5) (* 960 (* h1 h1 h1) h2 (* h3 
h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 6704 (* h1 h1 h1) h2 (* 
h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 20368 (* h1 h1 h1) h2 (* 
h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 35216 (* h1 h1 h1) h2 (* h3 
h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 38032 (* h1 h1 h1) h2 (* h3 h3 h3)
 (* h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 26480 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4
) h6 (* j2 j2 j2 j2)) (* 11824 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h6 (* j2 
j2 j2)) (* 3248 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h6 (* j2 j2)) (* 496 (* 
h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h6 j2) (* 32 (* h1 h1 h1) h2 (* h3 h3 h3) 
(* h4 h4) h6) (* 1216 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 17072 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 85312 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 221016 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) (* j2
 j2 j2 j2 j2 j2 j2)) (* 340010 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) (* j2 
j2 j2 j2 j2 j2)) (* 328854 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2
 j2 j2)) (* 203513 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) 
(* 79721 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 18947 (* h1 
h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) (* j2 j2)) (* 2469 (* h1 h1 h1) h2 (* h3 h3 
h3) h4 (* h5 h5) j2) (* 134 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5)) (* 2880 
(* h1 h1 h1) h2 (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
37832 (* h1 h1 h1) h2 (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
180628 (* h1 h1 h1) h2 (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
452716 (* h1 h1 h1) h2 (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 681480
 (* h1 h1 h1) h2 (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 652568 (* h1 h1
 h1) h2 (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 404780 (* h1 h1 h1) h2 (* 
h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 160860 (* h1 h1 h1) h2 (* h3 h3 h3) h4 h5
 h6 (* j2 j2 j2)) (* 39184 (* h1 h1 h1) h2 (* h3 h3 h3) h4 h5 h6 (* j2 j2)) (* 
5272 (* h1 h1 h1) h2 (* h3 h3 h3) h4 h5 h6 j2) (* 296 (* h1 h1 h1) h2 (* h3 h3 
h3) h4 h5 h6) (* 2240 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 15856 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 48944 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 86224 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 95216 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 68080 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 31376 (* 
h1 h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2)) (* 8944 (* h1 h1 h1) h2 (* 
h3 h3 h3) h4 (* h6 h6) (* j2 j2)) (* 1424 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h6 
h6) j2) (* 96 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6)) (* 1280 (* h1 h1 h1) h2
 (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 9600 (* h1 h1 h1) 
h2 (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 30720 (* h1 h1 h1) 
h2 (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 54752 (* h1 h1 h1) h2 
(* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 59520 (* h1 h1 h1) h2 (* h3 
h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 40632 (* h1 h1 h1) h2 (* h3 h3 h3) 
(* h5 h5 h5) (* j2 j2 j2 j2)) (* 17276 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5)
 (* j2 j2 j2)) (* 4368 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) (* j2 j2)) (* 
588 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) j2) (* 32 (* h1 h1 h1) h2 (* h3 h3
 h3) (* h5 h5 h5)) (* 3072 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2
 j2 j2 j2 j2 j2 j2 j2)) (* 32320 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) h6 (* j2
 j2 j2 j2 j2 j2 j2 j2 j2)) (* 138656 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 324800 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) h6
 (* j2 j2 j2 j2 j2 j2 j2)) (* 462944 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 420080 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) h6 (* j2
 j2 j2 j2 j2)) (* 245650 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 
j2)) (* 91458 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 20826 
(* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2)) (* 2630 (* h1 h1 h1) h2 (* 
h3 h3 h3) (* h5 h5) h6 j2) (* 140 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) h6) (* 
2752 (* h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 30752 (* h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 136280 (* h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2
 j2)) (* 327632 (* h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 481052 (* h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 454240 (* h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
280456 (* h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 112096 (* 
h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 27836 (* h1 h1 h1) h2 
(* h3 h3 h3) h5 (* h6 h6) (* j2 j2)) (* 3888 (* h1 h1 h1) h2 (* h3 h3 h3) h5 (* 
h6 h6) j2) (* 232 (* h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6)) (* 1280 (* h1 h1 h1
) h2 (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 9152 (* h1 h1 
h1) h2 (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 28576 (* h1 h1 
h1) h2 (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 51008 (* h1 h1 h1)
 h2 (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 57184 (* h1 h1 h1) h2 
(* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 41600 (* h1 h1 h1) h2 (* h3 h3 
h3) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 19552 (* h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6
 h6) (* j2 j2 j2)) (* 5696 (* h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6) (* j2 j2)) 
(* 928 (* h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6) j2) (* 64 (* h1 h1 h1) h2 (* h3
 h3 h3) (* h6 h6 h6)) (* 480 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 4996 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 21154 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 49102 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 
(* j2 j2 j2 j2 j2 j2 j2)) (* 69861 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 (* 
j2 j2 j2 j2 j2 j2)) (* 63864 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 
j2 j2 j2)) (* 37975 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) 
(* 14470 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 3371 (* h1 
h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 (* j2 j2)) (* 432 (* h1 h1 h1) h2 (* h3 h3) 
(* h4 h4 h4) h5 j2) (* 23 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5) (* 144 (* 
h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 996 
(* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2992 
(* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 5104 (* 
h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 5424 (* h1 h1 
h1) h2 (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 3704 (* h1 h1 h1) h2 (* 
h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2)) (* 1616 (* h1 h1 h1) h2 (* h3 h3) (* h4 
h4 h4) h6 (* j2 j2 j2)) (* 432 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h6 (* j2 
j2)) (* 64 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h6 j2) (* 4 (* h1 h1 h1) h2 
(* h3 h3) (* h4 h4 h4) h6) (* 1856 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5)
 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 17808 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4)
 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 73152 (* h1 h1 h1) h2 (* h3 h3) 
(* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 169138 (* h1 h1 h1) h2 (* h3
 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 243143 (* h1 h1 h1) h2 (* 
h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 226331 (* h1 h1 h1) h2 (* 
h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 137668 (* h1 h1 h1) h2 (* h3 
h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 53857 (* h1 h1 h1) h2 (* h3 h3) (* 
h4 h4) (* h5 h5) (* j2 j2 j2)) (* 12938 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* 
h5 h5) (* j2 j2)) (* 1718 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) j2) (* 
95 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5)) (* 2720 (* h1 h1 h1) h2 (* h3 
h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 25988 (* h1 h1 h1) h2 
(* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 104878 (* h1 h1 h1)
 h2 (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 237030 (* h1 h1 h1
) h2 (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 333137 (* h1 h1 h1) 
h2 (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 304332 (* h1 h1 h1) h2 
(* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 182807 (* h1 h1 h1) h2 (* h3 h3
) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 71174 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) 
h5 h6 (* j2 j2 j2)) (* 17159 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 h6 (* j2 j2)
) (* 2308 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 h6 j2) (* 131 (* h1 h1 h1) h2 
(* h3 h3) (* h4 h4) h5 h6) (* 528 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3716 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 11392 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 19904 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4
) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 21760 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 15368 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h6
 h6) (* j2 j2 j2 j2)) (* 6976 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h6 h6) (* 
j2 j2 j2)) (* 1952 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2)) (* 
304 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h6 h6) j2) (* 20 (* h1 h1 h1) h2 (* 
h3 h3) (* h4 h4) (* h6 h6)) (* 896 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 9632 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5
) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 43232 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5
 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 107272 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 163016 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5
 h5) (* j2 j2 j2 j2 j2 j2)) (* 158114 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) 
(* j2 j2 j2 j2 j2)) (* 98720 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 
j2 j2)) (* 39024 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2)) (* 9330
 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) (* j2 j2)) (* 1218 (* h1 h1 h1) h2 
(* h3 h3) h4 (* h5 h5 h5) j2) (* 66 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5)) 
(* 6816 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 60464 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 233360 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 513634 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 710561 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2
)) (* 642435 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
382681 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 147739 (* 
h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 35284 (* h1 h1 h1) h2 
(* h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 4692 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 
h5) h6 j2) (* 262 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) h6) (* 4480 (* h1 h1 h1
) h2 (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 40912 (* h1
 h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 160576 
(* h1 h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 357268
 (* h1 h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 499120 
(* h1 h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 457216 (* h1
 h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 277848 (* h1 h1 h1) 
h2 (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 110500 (* h1 h1 h1) h2 (* h3 h3
) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 27504 (* h1 h1 h1) h2 (* h3 h3) h4 h5 (* h6 
h6) (* j2 j2)) (* 3864 (* h1 h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6) j2) (* 232 (* 
h1 h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6)) (* 640 (* h1 h1 h1) h2 (* h3 h3) h4 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4576 (* h1 h1 h1) h2 (* h3 h3) h4 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 14288 (* h1 h1 h1) h2 (* h3 h3) h4 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 25504 (* h1 h1 h1) h2 (* h3 h3) h4 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 28592 (* h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6 
h6) (* j2 j2 j2 j2 j2)) (* 20800 (* h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6 h6) (* j2
 j2 j2 j2)) (* 9776 (* h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2)) (* 
2848 (* h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6 h6) (* j2 j2)) (* 464 (* h1 h1 h1) h2
 (* h3 h3) h4 (* h6 h6 h6) j2) (* 32 (* h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6 h6)) 
(* 256 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (* 1984 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 6592 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
12240 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 13872 
(* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 9836 (* h1 h1 
h1) h2 (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 4300 (* h1 h1 h1) h2 (* h3 
h3) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 1100 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5 
h5) (* j2 j2)) (* 148 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) j2) (* 8 (* h1 
h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5)) (* 2432 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 21248 (* h1 h1 h1) h2 (* h3 h3) (* 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 80864 (* h1 h1 h1) h2 (* h3 h3) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 175432 (* h1 h1 h1) h2 (* h3 h3)
 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 238564 (* h1 h1 h1) h2 (* h3 h3) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 210850 (* h1 h1 h1) h2 (* h3 h3) (* h5
 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 121744 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) 
h6 (* j2 j2 j2 j2)) (* 45088 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 
j2)) (* 10232 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2)) (* 1286 (* h1
 h1 h1) h2 (* h3 h3) (* h5 h5 h5) h6 j2) (* 68 (* h1 h1 h1) h2 (* h3 h3) (* h5 
h5 h5) h6) (* 4848 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 42208 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2 j2)) (* 160264 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 348070 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 476820 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5
) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 428710 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 255282 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2)) (* 99176 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6) 
(* j2 j2 j2)) (* 24042 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) 
(* 3284 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6) j2) (* 192 (* h1 h1 h1) h2
 (* h3 h3) (* h5 h5) (* h6 h6)) (* 2240 (* h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 19904 (* h1 h1 h1) h2 (* h3 h3) h5 (* h6
 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 76736 (* h1 h1 h1) h2 (* h3 h3) h5 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 168976 (* h1 h1 h1) h2 (* h3 h3) h5
 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 235200 (* h1 h1 h1) h2 (* h3 h3) h5 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 216048 (* h1 h1 h1) h2 (* h3 h3) h5 (* h6
 h6 h6) (* j2 j2 j2 j2 j2)) (* 132540 (* h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6) 
(* j2 j2 j2 j2)) (* 53600 (* h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)
) (* 13672 (* h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 1984 (* h1 h1
 h1) h2 (* h3 h3) h5 (* h6 h6 h6) j2) (* 124 (* h1 h1 h1) h2 (* h3 h3) h5 (* h6 
h6 h6)) (* 256 (* h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2
 j2 j2)) (* 1856 (* h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 5888 (* h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 10704 (* h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 12256 (* h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 9136 
(* h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 4416 (* h1 h1 h1) 
h2 (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 1328 (* h1 h1 h1) h2 (* h3 h3) (* 
h6 h6 h6 h6) (* j2 j2)) (* 224 (* h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6 h6) j2) (* 
16 (* h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6 h6)) (* 328 (* h1 h1 h1) h2 h3 (* h4 h4
 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2876 (* h1 h1 h1) h2 h3 (* 
h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 11038 (* h1 h1 h1) h2 h3 
(* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 24249 (* h1 h1 h1) h2 h3 
(* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 33532 (* h1 h1 h1) h2 h3 (* 
h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 30280 (* h1 h1 h1) h2 h3 (* h4 h4 
h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 17953 (* h1 h1 h1) h2 h3 (* h4 h4 h4) (* h5
 h5) (* j2 j2 j2 j2)) (* 6853 (* h1 h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) (* j2 j2
 j2)) (* 1602 (* h1 h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 206 (* h1 
h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) j2) (* 11 (* h1 h1 h1) h2 h3 (* h4 h4 h4) 
(* h5 h5)) (* 96 (* h1 h1 h1) h2 h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 728 (* h1 h1 h1) h2 h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 2458 (* h1 h1 h1) h2 h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 4861 (* h1 h1 h1) h2 h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
6227 (* h1 h1 h1) h2 h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 5389 (* h1 
h1 h1) h2 h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 3183 (* h1 h1 h1) h2 h3 
(* h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 1263 (* h1 h1 h1) h2 h3 (* h4 h4 h4) h5 
h6 (* j2 j2 j2)) (* 321 (* h1 h1 h1) h2 h3 (* h4 h4 h4) h5 h6 (* j2 j2)) (* 47 
(* h1 h1 h1) h2 h3 (* h4 h4 h4) h5 h6 j2) (* 3 (* h1 h1 h1) h2 h3 (* h4 h4 h4) 
h5 h6) (* 464 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 4200 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 16740 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 38376 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 
j2 j2 j2)) (* 55567 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 
j2)) (* 52646 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 
32770 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 13126 (* h1 
h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 3215 (* h1 h1 h1) h2 h3 (* 
h4 h4) (* h5 h5 h5) (* j2 j2)) (* 432 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) 
j2) (* 24 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5)) (* 1904 (* h1 h1 h1) h2 h3 
(* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 16044 (* h1 h1 h1) 
h2 h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 59426 (* h1 h1 
h1) h2 h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 126750 (* h1 h1
 h1) h2 h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 171446 (* h1 h1 
h1) h2 h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 152785 (* h1 h1 h1) 
h2 h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 90325 (* h1 h1 h1) h2 h3 (* 
h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 34796 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5
 h5) h6 (* j2 j2 j2)) (* 8324 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) h6 (* j2 j2
)) (* 1113 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) h6 j2) (* 63 (* h1 h1 h1) h2 
h3 (* h4 h4) (* h5 h5) h6) (* 368 (* h1 h1 h1) h2 h3 (* h4 h4) h5 (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2872 (* h1 h1 h1) h2 h3 (* h4 h4) h5 (* h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 9978 (* h1 h1 h1) h2 h3 (* h4 h4) h5 (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 20289 (* h1 h1 h1) h2 h3 (* h4 h4) h5 (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 26687 (* h1 h1 h1) h2 h3 (* h4 h4) h5 (* h6 h6)
 (* j2 j2 j2 j2 j2 j2)) (* 23673 (* h1 h1 h1) h2 h3 (* h4 h4) h5 (* h6 h6) (* j2
 j2 j2 j2 j2)) (* 14307 (* h1 h1 h1) h2 h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2
)) (* 5803 (* h1 h1 h1) h2 h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 1509 (* h1
 h1 h1) h2 h3 (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 227 (* h1 h1 h1) h2 h3 (* h4 
h4) h5 (* h6 h6) j2) (* 15 (* h1 h1 h1) h2 h3 (* h4 h4) h5 (* h6 h6)) (* 64 (* 
h1 h1 h1) h2 h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 592 (* 
h1 h1 h1) h2 h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2440 (* h1
 h1 h1) h2 h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 5856 (* h1 h1 
h1) h2 h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 8982 (* h1 h1 h1) h2 
h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 9107 (* h1 h1 h1) h2 h3 h4 (* h5
 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 6112 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5 h5) (* 
j2 j2 j2 j2)) (* 2648 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2)) (* 700
 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5 h5) (* j2 j2)) (* 101 (* h1 h1 h1) h2 h3 h4 
(* h5 h5 h5 h5) j2) (* 6 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5 h5)) (* 1968 (* h1 h1
 h1) h2 h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 16832 (* h1 
h1 h1) h2 h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 63236 (* h1 
h1 h1) h2 h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 136742 (* h1 h1 
h1) h2 h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 187391 (* h1 h1 h1) h2
 h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 168958 (* h1 h1 h1) h2 h3 h4 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 100827 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5)
 h6 (* j2 j2 j2 j2)) (* 39079 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2)
) (* 9368 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5) h6 (* j2 j2)) (* 1249 (* h1 h1 h1) 
h2 h3 h4 (* h5 h5 h5) h6 j2) (* 70 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5) h6) (* 
3080 (* h1 h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 25736 (* h1 h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 94574 (* h1 h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 200464 (* h1 h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2
)) (* 270234 (* h1 h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 240970 (* h1 h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
143302 (* h1 h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 55904 (* h1
 h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 13658 (* h1 h1 h1) h2 h3 
h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 1886 (* h1 h1 h1) h2 h3 h4 (* h5 h5) (* h6 
h6) j2) (* 112 (* h1 h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6)) (* 464 (* h1 h1 h1) h2
 h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3712 (* h1 h1 h1) 
h2 h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 13216 (* h1 h1 h1) 
h2 h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 27524 (* h1 h1 h1) h2 
h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 37052 (* h1 h1 h1) h2 h3 h4 
h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 33608 (* h1 h1 h1) h2 h3 h4 h5 (* h6 
h6 h6) (* j2 j2 j2 j2 j2)) (* 20752 (* h1 h1 h1) h2 h3 h4 h5 (* h6 h6 h6) (* j2 
j2 j2 j2)) (* 8596 (* h1 h1 h1) h2 h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 2284 
(* h1 h1 h1) h2 h3 h4 h5 (* h6 h6 h6) (* j2 j2)) (* 352 (* h1 h1 h1) h2 h3 h4 h5
 (* h6 h6 h6) j2) (* 24 (* h1 h1 h1) h2 h3 h4 h5 (* h6 h6 h6)) (* 256 (* h1 h1 
h1) h2 h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2112 (* h1 h1
 h1) h2 h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 7648 (* h1 h1 
h1) h2 h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 15968 (* h1 h1 h1) 
h2 h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 21224 (* h1 h1 h1) h2 h3 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 18700 (* h1 h1 h1) h2 h3 (* h5 h5 
h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 11016 (* h1 h1 h1) h2 h3 (* h5 h5 h5 h5) h6 (* 
j2 j2 j2 j2)) (* 4264 (* h1 h1 h1) h2 h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 
1032 (* h1 h1 h1) h2 h3 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 140 (* h1 h1 h1) h2 h3 
(* h5 h5 h5 h5) h6 j2) (* 8 (* h1 h1 h1) h2 h3 (* h5 h5 h5 h5) h6) (* 1504 (* h1
 h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 12792
 (* h1 h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
47656 (* h1 h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
102028 (* h1 h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
138411 (* h1 h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
123731 (* h1 h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 73473 
(* h1 h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 28517 (* h1 h1 h1)
 h2 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 6916 (* h1 h1 h1) h2 h3 (* h5 h5 
h5) (* h6 h6) (* j2 j2)) (* 948 (* h1 h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6) j2) 
(* 56 (* h1 h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6)) (* 1488 (* h1 h1 h1) h2 h3 (* 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 12432 (* h1 h1 h1) h2 
h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 45688 (* h1 h1 h1) 
h2 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 96932 (* h1 h1 h1) 
h2 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 130992 (* h1 h1 h1) h2
 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 117364 (* h1 h1 h1) h2 h3 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 70344 (* h1 h1 h1) h2 h3 (* h5 h5)
 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 27768 (* h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6
) (* j2 j2 j2)) (* 6900 (* h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 
976 (* h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6) j2) (* 60 (* h1 h1 h1) h2 h3 (* h5
 h5) (* h6 h6 h6)) (* 192 (* h1 h1 h1) h2 h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 1568 (* h1 h1 h1) h2 h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 5696 (* h1 h1 h1) h2 h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 12096 (* h1 h1 h1) h2 h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 16592 (* h1 h1 h1) h2 h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 15324 (* h1 h1 h1) h2 h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 9628 (* h1
 h1 h1) h2 h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 4056 (* h1 h1 h1) h2 h3 h5 
(* h6 h6 h6 h6) (* j2 j2 j2)) (* 1096 (* h1 h1 h1) h2 h3 h5 (* h6 h6 h6 h6) (* 
j2 j2)) (* 172 (* h1 h1 h1) h2 h3 h5 (* h6 h6 h6 h6) j2) (* 12 (* h1 h1 h1) h2 
h3 h5 (* h6 h6 h6 h6)) (* 24 (* h1 h1 h1) h2 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 200 (* h1 h1 h1) h2 (* h4 h4 h4) (* h5 h5) h6 (* j2
 j2 j2 j2 j2 j2 j2 j2 j2)) (* 730 (* h1 h1 h1) h2 (* h4 h4 h4) (* h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 1536 (* h1 h1 h1) h2 (* h4 h4 h4) (* h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2)) (* 2061 (* h1 h1 h1) h2 (* h4 h4 h4) (* h5 h5) h6 (* j2 
j2 j2 j2 j2 j2)) (* 1840 (* h1 h1 h1) h2 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 
j2 j2)) (* 1105 (* h1 h1 h1) h2 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 
440 (* h1 h1 h1) h2 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 111 (* h1 h1 h1) 
h2 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 16 (* h1 h1 h1) h2 (* h4 h4 h4) (* h5
 h5) h6 j2) (* (* h1 h1 h1) h2 (* h4 h4 h4) (* h5 h5) h6) (* 80 (* h1 h1 h1) h2 
(* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 672 (* h1 h1 h1)
 h2 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2476 (* h1 h1 
h1) h2 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 5268 (* h1 h1 
h1) h2 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 7162 (* h1 h1 h1) 
h2 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 6494 (* h1 h1 h1) h2 (* 
h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 3972 (* h1 h1 h1) h2 (* h4 h4) (* 
h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 1616 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5 h5) h6 
(* j2 j2 j2)) (* 418 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 62 
(* h1 h1 h1) h2 (* h4 h4) (* h5 h5 h5) h6 j2) (* 4 (* h1 h1 h1) h2 (* h4 h4) (* 
h5 h5 h5) h6) (* 104 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 860 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3130 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6597 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 8907 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 8039 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2)) (* 4905 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2)) (* 1995 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 
j2)) (* 517 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 77 (* h1
 h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 h6) j2) (* 5 (* h1 h1 h1) h2 (* h4 h4) (* 
h5 h5) (* h6 h6)) (* 32 (* h1 h1 h1) h2 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 280 (* h1 h1 h1) h2 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 1072 (* h1 h1 h1) h2 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 2362 (* h1 h1 h1) h2 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2))
 (* 3312 (* h1 h1 h1) h2 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 3083 
(* h1 h1 h1) h2 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 1926 (* h1 h1 h1) 
h2 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 796 (* h1 h1 h1) h2 h4 (* h5 h5 h5 
h5) h6 (* j2 j2 j2)) (* 208 (* h1 h1 h1) h2 h4 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 
31 (* h1 h1 h1) h2 h4 (* h5 h5 h5 h5) h6 j2) (* 2 (* h1 h1 h1) h2 h4 (* h5 h5 h5
 h5) h6) (* 232 (* h1 h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 1912 (* h1 h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 6950 (* h1 h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 14660 (* h1 h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 19851 (* h1 h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 18009 (* h1 h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 11072 (* h1 h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 4550 (* 
h1 h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 1195 (* h1 h1 h1) h2 h4 
(* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 181 (* h1 h1 h1) h2 h4 (* h5 h5 h5) (* h6 
h6) j2) (* 12 (* h1 h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6)) (* 144 (* h1 h1 h1) h2 
h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1188 (* h1 h1 h1
) h2 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4328 (* h1 h1 
h1) h2 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 9161 (* h1 h1 
h1) h2 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 12464 (* h1 h1 h1)
 h2 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 11377 (* h1 h1 h1) h2 h4
 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 7048 (* h1 h1 h1) h2 h4 (* h5 h5)
 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 2923 (* h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6 h6)
 (* j2 j2 j2)) (* 776 (* h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 
119 (* h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6 h6) j2) (* 8 (* h1 h1 h1) h2 h4 (* h5 
h5) (* h6 h6 h6)) (* 64 (* h1 h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2
 j2 j2 j2 j2 j2 j2)) (* 544 (* h1 h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 2036 (* h1 h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 4412 (* h1 h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 6121 (* h1 h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 5672 (* h1 h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 3550 (* h1 h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 1480 
(* h1 h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 393 (* h1 h1 h1) h2 
(* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 60 (* h1 h1 h1) h2 (* h5 h5 h5 h5) (* h6
 h6) j2) (* 4 (* h1 h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6)) (* 144 (* h1 h1 h1) h2 
(* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1180 (* h1 h1 h1
) h2 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4276 (* h1 h1 
h1) h2 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 9015 (* h1 h1 
h1) h2 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 12233 (* h1 h1 h1)
 h2 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 11152 (* h1 h1 h1) h2 
(* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 6910 (* h1 h1 h1) h2 (* h5 h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 2871 (* h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6 
h6) (* j2 j2 j2)) (* 765 (* h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) 
(* 118 (* h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6) j2) (* 8 (* h1 h1 h1) h2 (* h5 
h5 h5) (* h6 h6 h6)) (* 64 (* h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2
 j2 j2 j2 j2 j2 j2 j2)) (* 528 (* h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 1928 (* h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 4100 (* h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 5618 (* h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 5178 (* h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 
j2 j2)) (* 3248 (* h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 
1368 (* h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 370 (* h1 h1 h1)
 h2 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 58 (* h1 h1 h1) h2 (* h5 h5) (* h6 
h6 h6 h6) j2) (* 4 (* h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6 h6)) (* 480 (* h1 h1 h1
) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3952 (* h1 
h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 14344 (* 
h1 h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 30136 (* 
h1 h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 40440 (* h1 
h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 36056 (* h1 h1 h1)
 (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 21512 (* h1 h1 h1) (* h3 h3
 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 8424 (* h1 h1 h1) (* h3 h3 h3 h3) (* h4
 h4) h5 (* j2 j2 j2)) (* 2056 (* h1 h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2
)) (* 280 (* h1 h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 j2) (* 16 (* h1 h1 h1) (* h3
 h3 h3 h3) (* h4 h4) h5) (* 640 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 5376 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 19808 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h5 
h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 41984 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h5 
h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 56392 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5)
 (* j2 j2 j2 j2 j2 j2)) (* 49816 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2
 j2 j2 j2 j2)) (* 29056 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2
)) (* 10928 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 2504 (* 
h1 h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2)) (* 312 (* h1 h1 h1) (* h3 h3 
h3 h3) h4 (* h5 h5) j2) (* 16 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5)) (* 1600
 (* h1 h1 h1) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
13280 (* h1 h1 h1) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
48656 (* h1 h1 h1) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
103360 (* h1 h1 h1) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 140528
 (* h1 h1 h1) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 127264 (* h1 h1
 h1) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 77360 (* h1 h1 h1) (* h3 h3
 h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 30976 (* h1 h1 h1) (* h3 h3 h3 h3) h4 h5 h6
 (* j2 j2 j2)) (* 7760 (* h1 h1 h1) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2)) (* 1088 
(* h1 h1 h1) (* h3 h3 h3 h3) h4 h5 h6 j2) (* 64 (* h1 h1 h1) (* h3 h3 h3 h3) h4 
h5 h6) (* 1280 (* h1 h1 h1) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2
 j2 j2 j2)) (* 10752 (* h1 h1 h1) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2
 j2 j2 j2 j2)) (* 39616 (* h1 h1 h1) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2
 j2 j2 j2 j2)) (* 83968 (* h1 h1 h1) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2
 j2 j2 j2)) (* 112784 (* h1 h1 h1) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 
j2 j2)) (* 99632 (* h1 h1 h1) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) 
(* 58112 (* h1 h1 h1) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 21856 (* 
h1 h1 h1) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 5008 (* h1 h1 h1) (* h3 
h3 h3 h3) (* h5 h5) h6 (* j2 j2)) (* 624 (* h1 h1 h1) (* h3 h3 h3 h3) (* h5 h5) 
h6 j2) (* 32 (* h1 h1 h1) (* h3 h3 h3 h3) (* h5 h5) h6) (* 1280 (* h1 h1 h1) (* 
h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 10752 (* h1 h1 
h1) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 39936 (* h1 
h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 86176 (* h1 
h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 119296 (* h1 h1
 h1) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 110304 (* h1 h1 h1) 
(* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 68672 (* h1 h1 h1) (* h3 h3 
h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 28256 (* h1 h1 h1) (* h3 h3 h3 h3) h5 
(* h6 h6) (* j2 j2 j2)) (* 7296 (* h1 h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 
j2)) (* 1056 (* h1 h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6) j2) (* 64 (* h1 h1 h1) 
(* h3 h3 h3 h3) h5 (* h6 h6)) (* 480 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3952 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4 h4
) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 14344 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4
 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 30136 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4
 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 40440 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4 h4
) h5 (* j2 j2 j2 j2 j2 j2)) (* 36056 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 
(* j2 j2 j2 j2 j2)) (* 21512 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 
j2 j2)) (* 8424 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 2056 
(* h1 h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2)) (* 280 (* h1 h1 h1) (* h3 
h3 h3) (* h4 h4 h4) h5 j2) (* 16 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5) (* 
1360 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2
 j2)) (* 11432 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 42012 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 88644 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 
j2 j2 j2 j2 j2 j2)) (* 118516 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* 
j2 j2 j2 j2 j2 j2)) (* 104470 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* 
j2 j2 j2 j2 j2)) (* 61172 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2
 j2 j2)) (* 23352 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2)) 
(* 5524 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 726 (* h1 h1
 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) j2) (* 40 (* h1 h1 h1) (* h3 h3 h3) (* h4 
h4) (* h5 h5)) (* 2080 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 17232 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 63000 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 133496 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2
 j2 j2 j2 j2 j2 j2)) (* 180968 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 
j2 j2 j2 j2 j2)) (* 163320 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2
 j2 j2)) (* 98872 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 
39400 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 9816 (* h1 h1 
h1) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 1368 (* h1 h1 h1) (* h3 h3 h3) 
(* h4 h4) h5 h6 j2) (* 80 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 h6) (* 640 (* 
h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
5440 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 20160 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 42736 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
57136 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 50076 
(* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 28954 (* h1 h1 
h1) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 10822 (* h1 h1 h1) (* h3 h3
 h3) h4 (* h5 h5 h5) (* j2 j2 j2)) (* 2478 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5
 h5) (* j2 j2)) (* 310 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) j2) (* 16 (* h1
 h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5)) (* 4080 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5
 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 34392 (* h1 h1 h1) (* h3 h3 h3) h4
 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 126844 (* h1 h1 h1) (* h3 h3 h3
) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 268896 (* h1 h1 h1) (* h3 h3 
h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 361750 (* h1 h1 h1) (* h3 h3 h3
) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 321536 (* h1 h1 h1) (* h3 h3 h3) h4 
(* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 190392 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5
) h6 (* j2 j2 j2 j2)) (* 73784 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 
j2 j2)) (* 17806 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 2400 
(* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) h6 j2) (* 136 (* h1 h1 h1) (* h3 h3 h3) 
h4 (* h5 h5) h6) (* 2880 (* h1 h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 24032 (* h1 h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 88592 (* h1 h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 189536 (* h1 h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 259824 (* h1 h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 237568 (* h1 h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2
 j2 j2 j2 j2)) (* 146032 (* h1 h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 
j2)) (* 59232 (* h1 h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 15056 
(* h1 h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 2144 (* h1 h1 h1) (* h3 
h3 h3) h4 h5 (* h6 h6) j2) (* 128 (* h1 h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6)) (* 
1280 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 10880 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 40320 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 85472 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)
) (* 114272 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
100152 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 57908 
(* h1 h1 h1) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 21644 (* h1 h1 h1)
 (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 4956 (* h1 h1 h1) (* h3 h3 h3) 
(* h5 h5 h5) h6 (* j2 j2)) (* 620 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5 h5) h6 j2) 
(* 32 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5 h5) h6) (* 2720 (* h1 h1 h1) (* h3 h3 
h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 23056 (* h1 h1 h1)
 (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 85640 (* h1
 h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 183216 
(* h1 h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
249436 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
225192 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
136096 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 54160 
(* h1 h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 13516 (* h1 h1 h1
) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 1896 (* h1 h1 h1) (* h3 h3 h3) 
(* h5 h5) (* h6 h6) j2) (* 112 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6)) 
(* 1280 (* h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 10752 (* h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 39936 (* h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 86176 (* h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 119296 (* h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 110304 (* h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 68672
 (* h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 28256 (* h1 h1 h1
) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 7296 (* h1 h1 h1) (* h3 h3 h3) 
h5 (* h6 h6 h6) (* j2 j2)) (* 1056 (* h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6) j2)
 (* 64 (* h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6)) (* 72 (* h1 h1 h1) (* h3 h3) 
(* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 588 (* h1 h1 h1) (* h3 
h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2114 (* h1 h1 h1) (* 
h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4392 (* h1 h1 h1) (* 
h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 5816 (* h1 h1 h1) (* h3 
h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 5104 (* h1 h1 h1) (* h3 h3) (* 
h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 2988 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4 
h4) h5 (* j2 j2 j2 j2)) (* 1144 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 
j2 j2)) (* 272 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2)) (* 36 (* h1 
h1 h1) (* h3 h3) (* h4 h4 h4 h4) h5 j2) (* 2 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4 
h4) h5) (* 456 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 3844 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 14210 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 30252 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 
h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 40937 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) (* h5
 h5) (* j2 j2 j2 j2 j2 j2)) (* 36641 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 
h5) (* j2 j2 j2 j2 j2)) (* 21860 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) 
(* j2 j2 j2 j2)) (* 8534 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 
j2)) (* 2073 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 281 (* 
h1 h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) j2) (* 16 (* h1 h1 h1) (* h3 h3) (* 
h4 h4 h4) (* h5 h5)) (* 408 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 3364 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 12230 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 h6 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 25744 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 34624 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 h6 (* 
j2 j2 j2 j2 j2 j2)) (* 30952 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 
j2 j2 j2)) (* 18524 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) 
(* 7280 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 1784 (* h1 h1
 h1) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2)) (* 244 (* h1 h1 h1) (* h3 h3) (* h4
 h4 h4) h5 h6 j2) (* 14 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 h6) (* 576 (* h1 
h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
4992 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2
)) (* 18888 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 40936 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2
 j2 j2)) (* 56040 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 
j2 j2)) (* 50385 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2
)) (* 29962 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 
11564 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 2754 (* h1 
h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 363 (* h1 h1 h1) (* h3 h3)
 (* h4 h4) (* h5 h5 h5) j2) (* 20 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5))
 (* 1952 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 16544 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 61580 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 132242 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 180905 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2)) (* 164123 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) 
h6 (* j2 j2 j2 j2 j2)) (* 99558 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) h6 
(* j2 j2 j2 j2)) (* 39656 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2
 j2)) (* 9861 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 1371 
(* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) h6 j2) (* 80 (* h1 h1 h1) (* h3 h3) 
(* h4 h4) (* h5 h5) h6) (* 848 (* h1 h1 h1) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 7064 (* h1 h1 h1) (* h3 h3) (* h4 h4) h5 (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 25988 (* h1 h1 h1) (* h3 h3) (* h4 h4)
 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 55464 (* h1 h1 h1) (* h3 h3) (* h4
 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 75808 (* h1 h1 h1) (* h3 h3) (* 
h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 69064 (* h1 h1 h1) (* h3 h3) (* h4
 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 42264 (* h1 h1 h1) (* h3 h3) (* h4 h4) 
h5 (* h6 h6) (* j2 j2 j2 j2)) (* 17048 (* h1 h1 h1) (* h3 h3) (* h4 h4) h5 (* h6
 h6) (* j2 j2 j2)) (* 4304 (* h1 h1 h1) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 
j2)) (* 608 (* h1 h1 h1) (* h3 h3) (* h4 h4) h5 (* h6 h6) j2) (* 36 (* h1 h1 h1)
 (* h3 h3) (* h4 h4) h5 (* h6 h6)) (* 128 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5 
h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1120 (* h1 h1 h1) (* h3 h3) h4 (* h5 
h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4288 (* h1 h1 h1) (* h3 h3) h4 (* 
h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 9416 (* h1 h1 h1) (* h3 h3) h4 (* 
h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 13056 (* h1 h1 h1) (* h3 h3) h4 (* h5 
h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 11854 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5 
h5) (* j2 j2 j2 j2 j2)) (* 7068 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 
j2 j2 j2)) (* 2700 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2)) (* 
624 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2)) (* 78 (* h1 h1 h1) (* 
h3 h3) h4 (* h5 h5 h5 h5) j2) (* 4 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5)) 
(* 1728 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 15032 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 57116 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 124418 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2
 j2)) (* 171426 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2))
 (* 155440 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
93490 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 36636 (* h1 
h1 h1) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 8900 (* h1 h1 h1) (* h3 h3)
 h4 (* h5 h5 h5) h6 (* j2 j2)) (* 1202 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) h6
 j2) (* 68 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) h6) (* 2656 (* h1 h1 h1) (* h3
 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 22656 (* h1 h1
 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 85016 
(* h1 h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
184416 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 255414 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 235224 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
145276 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 59096 
(* h1 h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 15046 (* h1 h1 h1
) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 2144 (* h1 h1 h1) (* h3 h3) h4 
(* h5 h5) (* h6 h6) j2) (* 128 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6)) 
(* 768 (* h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 6464 (* h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 24064 (* h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 52064 (* h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 72296 (* h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 67088 (* h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 41944 
(* h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 17344 (* h1 h1 h1)
 (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 4504 (* h1 h1 h1) (* h3 h3) h4 h5
 (* h6 h6 h6) (* j2 j2)) (* 656 (* h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6) j2) 
(* 40 (* h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6)) (* 256 (* h1 h1 h1) (* h3 h3) 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2240 (* h1 h1 h1) (* h3
 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8576 (* h1 h1 h1) (* 
h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 18832 (* h1 h1 h1) (* 
h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 26112 (* h1 h1 h1) (* h3 
h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 23708 (* h1 h1 h1) (* h3 h3) 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 14136 (* h1 h1 h1) (* h3 h3) (* h5 h5 
h5 h5) h6 (* j2 j2 j2 j2)) (* 5400 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5 h5) h6 (* 
j2 j2 j2)) (* 1248 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 156 
(* h1 h1 h1) (* h3 h3) (* h5 h5 h5 h5) h6 j2) (* 8 (* h1 h1 h1) (* h3 h3) (* h5 
h5 h5 h5) h6) (* 1152 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 10096 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 38680 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 85092 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 118692 (* h1 h1 h1) (* h3 h3) (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 109340 (* h1 h1 h1) (* h3 h3) (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 67132 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2)) (* 27016 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6
) (* j2 j2 j2)) (* 6784 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2))
 (* 952 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6) j2) (* 56 (* h1 h1 h1) (* 
h3 h3) (* h5 h5 h5) (* h6 h6)) (* 1152 (* h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 9888 (* h1 h1 h1) (* h3 h3) (* h5 h5)
 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 37392 (* h1 h1 h1) (* h3 h3) 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 81880 (* h1 h1 h1) (* h3 
h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 114704 (* h1 h1 h1) (* 
h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 107084 (* h1 h1 h1) (* 
h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 67200 (* h1 h1 h1) (* h3 h3
) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 27840 (* h1 h1 h1) (* h3 h3) (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2)) (* 7232 (* h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6
 h6) (* j2 j2)) (* 1052 (* h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6) j2) (* 64 
(* h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6)) (* 256 (* h1 h1 h1) (* h3 h3) h5 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2176 (* h1 h1 h1) (* h3 h3
) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8192 (* h1 h1 h1) (* h3 
h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 17952 (* h1 h1 h1) (* h3 
h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 25296 (* h1 h1 h1) (* h3 h3)
 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 23872 (* h1 h1 h1) (* h3 h3) h5 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 15216 (* h1 h1 h1) (* h3 h3) h5 (* h6 h6 
h6 h6) (* j2 j2 j2 j2)) (* 6432 (* h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 
j2 j2)) (* 1712 (* h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2)) (* 256 (* 
h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6 h6) j2) (* 16 (* h1 h1 h1) (* h3 h3) h5 (* h6
 h6 h6 h6)) (* 24 (* h1 h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2
 j2 j2 j2 j2)) (* 212 (* h1 h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 818 (* h1 h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2
 j2 j2 j2 j2)) (* 1810 (* h1 h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 
j2 j2 j2)) (* 2533 (* h1 h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 
j2)) (* 2330 (* h1 h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 
1417 (* h1 h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 558 (* h1 h1 
h1) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 135 (* h1 h1 h1) h3 (* h4 h4 
h4 h4) (* h5 h5) (* j2 j2)) (* 18 (* h1 h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5) j2) 
(* (* h1 h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5)) (* 80 (* h1 h1 h1) h3 (* h4 h4 h4)
 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 712 (* h1 h1 h1) h3 (* h4 h4
 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2772 (* h1 h1 h1) h3 (* h4 
h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6200 (* h1 h1 h1) h3 (* h4 
h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 8790 (* h1 h1 h1) h3 (* h4 h4 
h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 8214 (* h1 h1 h1) h3 (* h4 h4 h4) (* 
h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 5092 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) 
(* j2 j2 j2 j2)) (* 2052 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2))
 (* 510 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2)) (* 70 (* h1 h1 h1) 
h3 (* h4 h4 h4) (* h5 h5 h5) j2) (* 4 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5))
 (* 152 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 1336 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 5144 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 11391 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2)) (* 16003 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 14829 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 9121 
(* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 3649 (* h1 h1 h1) 
h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 901 (* h1 h1 h1) h3 (* h4 h4 h4) 
(* h5 h5) h6 (* j2 j2)) (* 123 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) h6 j2) (* 
7 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) h6) (* 32 (* h1 h1 h1) h3 (* h4 h4) (* 
h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 296 (* h1 h1 h1) h3 (* h4 h4)
 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1196 (* h1 h1 h1) h3 (* h4 
h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2770 (* h1 h1 h1) h3 (* h4 
h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 4054 (* h1 h1 h1) h3 (* h4 h4) 
(* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 3895 (* h1 h1 h1) h3 (* h4 h4) (* h5 
h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 2470 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) 
(* j2 j2 j2 j2)) (* 1012 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2))
 (* 254 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 35 (* h1 h1 h1) 
h3 (* h4 h4) (* h5 h5 h5 h5) j2) (* 2 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5))
 (* 392 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 3452 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 13334 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 29666 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2)) (* 41945 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 39197 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 24372 
(* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 9884 (* h1 h1 h1) 
h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 2481 (* h1 h1 h1) h3 (* h4 h4) (* 
h5 h5 h5) h6 (* j2 j2)) (* 345 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) h6 j2) (* 
20 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) h6) (* 352 (* h1 h1 h1) h3 (* h4 h4) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3084 (* h1 h1 h1) h3 
(* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 11866 (* h1 h1 
h1) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 26327 (* h1
 h1 h1) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 37164 (* 
h1 h1 h1) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 34715 (* h1
 h1 h1) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 21604 (* h1 h1 
h1) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 8781 (* h1 h1 h1) h3 
(* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 2212 (* h1 h1 h1) h3 (* h4 h4) 
(* h5 h5) (* h6 h6) (* j2 j2)) (* 309 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5) (* h6 
h6) j2) (* 18 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5) (* h6 h6)) (* 128 (* h1 h1 h1)
 h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1168 (* h1 h1 h1
) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4668 (* h1 h1 h1) 
h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 10722 (* h1 h1 h1) h3 
h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 15605 (* h1 h1 h1) h3 h4 (* 
h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 14954 (* h1 h1 h1) h3 h4 (* h5 h5 h5 
h5) h6 (* j2 j2 j2 j2 j2)) (* 9490 (* h1 h1 h1) h3 h4 (* h5 h5 h5 h5) h6 (* j2 
j2 j2 j2)) (* 3906 (* h1 h1 h1) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 989 
(* h1 h1 h1) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 138 (* h1 h1 h1) h3 h4 (* h5
 h5 h5 h5) h6 j2) (* 8 (* h1 h1 h1) h3 h4 (* h5 h5 h5 h5) h6) (* 608 (* h1 h1 h1
) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 5308 (* h1 
h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 20374 (* 
h1 h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 45149 (* 
h1 h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 63739 (* h1 
h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 59630 (* h1 h1 h1)
 h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 37228 (* h1 h1 h1) h3 h4 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 15209 (* h1 h1 h1) h3 h4 (* h5 h5 h5)
 (* h6 h6) (* j2 j2 j2)) (* 3859 (* h1 h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2
 j2)) (* 544 (* h1 h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6) j2) (* 32 (* h1 h1 h1) h3
 h4 (* h5 h5 h5) (* h6 h6)) (* 352 (* h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3080 (* h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 11860 (* h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 26394 (* h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6
 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 37466 (* h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6
) (* j2 j2 j2 j2 j2 j2)) (* 35292 (* h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2)) (* 22220 (* h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2)) (* 9170 (* h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 2354 (* 
h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 336 (* h1 h1 h1) h3 h4 (* 
h5 h5) (* h6 h6 h6) j2) (* 20 (* h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6)) (* 128 
(* h1 h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
1152 (* h1 h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 4552 (* h1 h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 10364 (* h1 h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
14994 (* h1 h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 14328 
(* h1 h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 9100 (* h1 h1 
h1) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 3764 (* h1 h1 h1) h3 (* h5 
h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 962 (* h1 h1 h1) h3 (* h5 h5 h5 h5) (* h6 
h6) (* j2 j2)) (* 136 (* h1 h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6) j2) (* 8 (* h1 
h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6)) (* 288 (* h1 h1 h1) h3 (* h5 h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2504 (* h1 h1 h1) h3 (* h5 h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 9588 (* h1 h1 h1) h3 (* h5 h5 h5
) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 21234 (* h1 h1 h1) h3 (* h5 h5 h5
) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 30018 (* h1 h1 h1) h3 (* h5 h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 28184 (* h1 h1 h1) h3 (* h5 h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2)) (* 17704 (* h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2)) (* 7298 (* h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2))
 (* 1874 (* h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 268 (* h1 h1 h1
) h3 (* h5 h5 h5) (* h6 h6 h6) j2) (* 16 (* h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6 
h6)) (* 128 (* h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
 j2 j2)) (* 1120 (* h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 4320 (* h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 9648 (* h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 13772 (* h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)
) (* 13076 (* h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 8320
 (* h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 3480 (* h1 h1 h1)
 h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 908 (* h1 h1 h1) h3 (* h5 h5) (* 
h6 h6 h6 h6) (* j2 j2)) (* 132 (* h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6 h6) j2) (* 
8 (* h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6 h6)) (* 1280 (* h1 h1) (* h2 h2 h2 h2) 
(* h3 h3 h3) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 5824 (* h1 h1) (* h2 h2 h2 h2) (* 
h3 h3 h3) h5 (* j2 j2 j2 j2 j2 j2)) (* 10592 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 
h3) h5 (* j2 j2 j2 j2 j2)) (* 9888 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* 
j2 j2 j2 j2)) (* 5080 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2)) 
(* 1436 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2)) (* 208 (* h1 h1) 
(* h2 h2 h2 h2) (* h3 h3 h3) h5 j2) (* 12 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3)
 h5) (* 1280 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2 j2 j2 j2 j2))
 (* 5504 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2 j2 j2 j2)) (* 
9616 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2 j2 j2)) (* 8784 (* h1
 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2 j2)) (* 4508 (* h1 h1) (* h2 h2
 h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2)) (* 1300 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3
 h3) h6 (* j2 j2)) (* 196 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h6 j2) (* 12 
(* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h6) (* 1312 (* h1 h1) (* h2 h2 h2 h2) (* 
h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 7088 (* h1 h1) (* h2 h2 h2 h2) (* 
h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 16016 (* h1 h1) (* h2 h2 h2 h2) (* h3 
h3) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 19712 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4
 h5 (* j2 j2 j2 j2 j2)) (* 14406 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* j2
 j2 j2 j2)) (* 6377 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2)) (* 
1661 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* j2 j2)) (* 231 (* h1 h1) (* h2
 h2 h2 h2) (* h3 h3) h4 h5 j2) (* 13 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h5) 
(* 832 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 4336 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
9592 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2)) (* 11732 
(* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 8654 (* h1 h1) 
(* h2 h2 h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 3932 (* h1 h1) (* h2 h2 h2 
h2) (* h3 h3) h4 h6 (* j2 j2 j2)) (* 1072 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4
 h6 (* j2 j2)) (* 160 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h6 j2) (* 10 (* h1 
h1) (* h2 h2 h2 h2) (* h3 h3) h4 h6) (* 960 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) 
(* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 5120 (* h1 h1) (* h2 h2 h2 h2) (* h3 
h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 11344 (* h1 h1) (* h2 h2 h2 h2) (* h3
 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 13592 (* h1 h1) (* h2 h2 h2 h2) (* h3 
h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 9616 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) 
(* h5 h5) (* j2 j2 j2 j2)) (* 4114 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h5 h5)
 (* j2 j2 j2)) (* 1040 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* j2 j2)) 
(* 142 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) j2) (* 8 (* h1 h1) (* h2 h2
 h2 h2) (* h3 h3) (* h5 h5)) (* 1888 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 h6 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 9824 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 21576 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 h6 (* 
j2 j2 j2 j2 j2 j2)) (* 26052 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 h6 (* j2 j2 
j2 j2 j2)) (* 18868 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2)) 
(* 8373 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2)) (* 2217 (* h1 h1
) (* h2 h2 h2 h2) (* h3 h3) h5 h6 (* j2 j2)) (* 319 (* h1 h1) (* h2 h2 h2 h2) 
(* h3 h3) h5 h6 j2) (* 19 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 h6) (* 832 (* 
h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4336 
(* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 9592 
(* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 11732 
(* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 8654 (* h1 
h1) (* h2 h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 3932 (* h1 h1) (* h2
 h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2)) (* 1072 (* h1 h1) (* h2 h2 h2 h2) 
(* h3 h3) (* h6 h6) (* j2 j2)) (* 160 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h6 
h6) j2) (* 10 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h6 h6)) (* 448 (* h1 h1) 
(* h2 h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2816 (* h1 h1
) (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 7632 (* h1 h1)
 (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 11696 (* h1 h1) 
(* h2 h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 11156 (* h1 h1) (* h2 
h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 6856 (* h1 h1) (* h2 h2 h2 h2) 
h3 h4 (* h5 h5) (* j2 j2 j2 j2)) (* 2707 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h5 
h5) (* j2 j2 j2)) (* 659 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2)) 
(* 89 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h5 h5) j2) (* 5 (* h1 h1) (* h2 h2 h2 
h2) h3 h4 (* h5 h5)) (* 576 (* h1 h1) (* h2 h2 h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 3488 (* h1 h1) (* h2 h2 h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 9232 (* h1 h1) (* h2 h2 h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2 j2 j2
 j2)) (* 14008 (* h1 h1) (* h2 h2 h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 
13416 (* h1 h1) (* h2 h2 h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 8400 (* h1 h1
) (* h2 h2 h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2)) (* 3432 (* h1 h1) (* h2 h2 h2 h2)
 h3 h4 h5 h6 (* j2 j2 j2)) (* 880 (* h1 h1) (* h2 h2 h2 h2) h3 h4 h5 h6 (* j2 j2
)) (* 128 (* h1 h1) (* h2 h2 h2 h2) h3 h4 h5 h6 j2) (* 8 (* h1 h1) (* h2 h2 h2 
h2) h3 h4 h5 h6) (* 64 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 432 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2 j2
 j2 j2 j2 j2)) (* 1272 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 2140 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 2262 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
1554 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2 j2)) (* 692 (* h1 h1)
 (* h2 h2 h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2)) (* 192 (* h1 h1) (* h2 h2 h2 h2) 
h3 h4 (* h6 h6) (* j2 j2)) (* 30 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h6 h6) j2) 
(* 2 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h6 h6)) (* 128 (* h1 h1) (* h2 h2 h2 h2)
 h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 832 (* h1 h1) (* h2 h2 h2 h2
) h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2336 (* h1 h1) (* h2 h2 h2 h2)
 h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 3712 (* h1 h1) (* h2 h2 h2 h2) h3 
(* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 3672 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 
h5 h5) (* j2 j2 j2 j2 j2)) (* 2340 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* 
j2 j2 j2 j2)) (* 958 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2)) (* 
242 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* j2 j2)) (* 34 (* h1 h1) (* h2 
h2 h2 h2) h3 (* h5 h5 h5) j2) (* 2 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5 h5)) 
(* 736 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (* 4368 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 11232 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
16432 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 15082 
(* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 9011 (* h1 h1) 
(* h2 h2 h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 3504 (* h1 h1) (* h2 h2 h2 
h2) h3 (* h5 h5) h6 (* j2 j2 j2)) (* 854 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) 
h6 (* j2 j2)) (* 118 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) h6 j2) (* 7 (* h1 h1
) (* h2 h2 h2 h2) h3 (* h5 h5) h6) (* 512 (* h1 h1) (* h2 h2 h2 h2) h3 h5 (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3120 (* h1 h1) (* h2 h2 h2 h2) h3 h5 (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 8328 (* h1 h1) (* h2 h2 h2 h2) h3 h5 (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 12772 (* h1 h1) (* h2 h2 h2 h2) h3 h5 (* h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 12390 (* h1 h1) (* h2 h2 h2 h2) h3 h5 (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* 7872 (* h1 h1) (* h2 h2 h2 h2) h3 h5 (* h6 h6) (* j2 j2 
j2 j2)) (* 3268 (* h1 h1) (* h2 h2 h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2)) (* 852 
(* h1 h1) (* h2 h2 h2 h2) h3 h5 (* h6 h6) (* j2 j2)) (* 126 (* h1 h1) (* h2 h2 
h2 h2) h3 h5 (* h6 h6) j2) (* 8 (* h1 h1) (* h2 h2 h2 h2) h3 h5 (* h6 h6)) (* 64
 (* h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
432 (* h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
1272 (* h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2140
 (* h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2262 (* h1 
h1) (* h2 h2 h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1554 (* h1 h1) (* h2 
h2 h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 692 (* h1 h1) (* h2 h2 h2 h2) h3 
(* h6 h6 h6) (* j2 j2 j2)) (* 192 (* h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6 h6) (* 
j2 j2)) (* 30 (* h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6 h6) j2) (* 2 (* h1 h1) (* h2
 h2 h2 h2) h3 (* h6 h6 h6)) (* 128 (* h1 h1) (* h2 h2 h2 h2) h4 (* h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 896 (* h1 h1) (* h2 h2 h2 h2) h4 (* h5 h5) h6
 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2784 (* h1 h1) (* h2 h2 h2 h2) h4 (* h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 5056 (* h1 h1) (* h2 h2 h2 h2) h4 (* h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 5944 (* h1 h1) (* h2 h2 h2 h2) h4 (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 4728 (* h1 h1) (* h2 h2 h2 h2) h4 (* h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* 2578 (* h1 h1) (* h2 h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2))
 (* 952 (* h1 h1) (* h2 h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 228 (* h1 h1)
 (* h2 h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2)) (* 32 (* h1 h1) (* h2 h2 h2 h2) h4 
(* h5 h5) h6 j2) (* 2 (* h1 h1) (* h2 h2 h2 h2) h4 (* h5 h5) h6) (* 32 (* h1 h1)
 (* h2 h2 h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 240 (* h1
 h1) (* h2 h2 h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 800 (* 
h1 h1) (* h2 h2 h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1560 (* 
h1 h1) (* h2 h2 h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1970 (* h1 
h1) (* h2 h2 h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1683 (* h1 h1) (* 
h2 h2 h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 985 (* h1 h1) (* h2 h2 h2 h2
) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 390 (* h1 h1) (* h2 h2 h2 h2) h4 h5 (* h6 
h6) (* j2 j2 j2)) (* 100 (* h1 h1) (* h2 h2 h2 h2) h4 h5 (* h6 h6) (* j2 j2)) 
(* 15 (* h1 h1) (* h2 h2 h2 h2) h4 h5 (* h6 h6) j2) (* (* h1 h1) (* h2 h2 h2 h2)
 h4 h5 (* h6 h6)) (* 64 (* h1 h1) (* h2 h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2
 j2 j2 j2 j2 j2 j2)) (* 448 (* h1 h1) (* h2 h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 1392 (* h1 h1) (* h2 h2 h2 h2) (* h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 2528 (* h1 h1) (* h2 h2 h2 h2) (* h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2)) (* 2972 (* h1 h1) (* h2 h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2)) (* 2364 (* h1 h1) (* h2 h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2)) (* 1289 (* h1 h1) (* h2 h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 476 
(* h1 h1) (* h2 h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 114 (* h1 h1) (* h2 
h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2)) (* 16 (* h1 h1) (* h2 h2 h2 h2) (* h5 h5 h5
) h6 j2) (* (* h1 h1) (* h2 h2 h2 h2) (* h5 h5 h5) h6) (* 96 (* h1 h1) (* h2 h2 
h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 688 (* h1 h1) 
(* h2 h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2192 (* 
h1 h1) (* h2 h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4088 
(* h1 h1) (* h2 h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4942 
(* h1 h1) (* h2 h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4047 (* 
h1 h1) (* h2 h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2274 (* h1 h1)
 (* h2 h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 866 (* h1 h1) (* h2 h2 
h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 214 (* h1 h1) (* h2 h2 h2 h2) (* h5 
h5) (* h6 h6) (* j2 j2)) (* 31 (* h1 h1) (* h2 h2 h2 h2) (* h5 h5) (* h6 h6) j2)
 (* 2 (* h1 h1) (* h2 h2 h2 h2) (* h5 h5) (* h6 h6)) (* 32 (* h1 h1) (* h2 h2 h2
 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 240 (* h1 h1) (* h2 
h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 800 (* h1 h1) (* h2
 h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1560 (* h1 h1) (* h2 
h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1970 (* h1 h1) (* h2 h2 
h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1683 (* h1 h1) (* h2 h2 h2 h2) 
h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 985 (* h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6
 h6) (* j2 j2 j2 j2)) (* 390 (* h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2 
j2)) (* 100 (* h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2)) (* 15 (* h1 h1)
 (* h2 h2 h2 h2) h5 (* h6 h6 h6) j2) (* (* h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6 h6
)) (* 1280 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 6464 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2 j2 j2 j2 j2)) (* 
13184 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2 j2 j2 j2)) (* 13888 (* 
h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2 j2 j2)) (* 8024 (* h1 h1) (* h2 
h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2 j2)) (* 2504 (* h1 h1) (* h2 h2 h2) (* h3 h3 
h3 h3) h5 (* j2 j2)) (* 392 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h5 j2) (* 24 
(* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h5) (* 1280 (* h1 h1) (* h2 h2 h2) (* h3 
h3 h3 h3) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 6144 (* h1 h1) (* h2 h2 h2) (* h3 h3 
h3 h3) h6 (* j2 j2 j2 j2 j2 j2)) (* 12048 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3)
 h6 (* j2 j2 j2 j2 j2)) (* 12376 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h6 (* j2
 j2 j2 j2)) (* 7104 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2 j2)) (* 
2256 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2)) (* 368 (* h1 h1) (* h2
 h2 h2) (* h3 h3 h3 h3) h6 j2) (* 24 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h6) 
(* 5520 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 35392 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 
91784 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 125016
 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 97245 (* h1 h1
) (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2)) (* 44138 (* h1 h1) (* h2 h2 
h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2)) (* 11484 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3
) h4 h5 (* j2 j2)) (* 1574 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h5 j2) (* 87 
(* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h5) (* 3200 (* h1 h1) (* h2 h2 h2) (* h3 
h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 19616 (* h1 h1) (* h2 h2 h2) (* h3 
h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 49056 (* h1 h1) (* h2 h2 h2) (* h3 h3 
h3) h4 h6 (* j2 j2 j2 j2 j2 j2)) (* 65440 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4
 h6 (* j2 j2 j2 j2 j2)) (* 50932 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2
 j2 j2 j2)) (* 23736 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2)) (* 
6512 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2)) (* 968 (* h1 h1) (* h2
 h2 h2) (* h3 h3 h3) h4 h6 j2) (* 60 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h6) 
(* 3008 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 19104 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 
j2)) (* 49152 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2
)) (* 65992 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) 
(* 49876 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 21608
 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2)) (* 5330 (* h1 h1) 
(* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2)) (* 700 (* h1 h1) (* h2 h2 h2) (* 
h3 h3 h3) (* h5 h5) j2) (* 38 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h5 h5)) (* 
6224 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
38576 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
97448 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 129956
 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 99373 (* h1 h1
) (* h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 44550 (* h1 h1) (* h2 h2 
h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2)) (* 11544 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3
) h5 h6 (* j2 j2)) (* 1598 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 h6 j2) (* 91 
(* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 h6) (* 3200 (* h1 h1) (* h2 h2 h2) (* h3 
h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 19616 (* h1 h1) (* h2 h2 h2) 
(* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 49056 (* h1 h1) (* h2 h2 h2)
 (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 65440 (* h1 h1) (* h2 h2 h2) 
(* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 50932 (* h1 h1) (* h2 h2 h2) (* h3
 h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 23736 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) 
(* h6 h6) (* j2 j2 j2)) (* 6512 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h6 h6) 
(* j2 j2)) (* 968 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h6 h6) j2) (* 60 (* h1 
h1) (* h2 h2 h2) (* h3 h3 h3) (* h6 h6)) (* 896 (* h1 h1) (* h2 h2 h2) (* h3 h3)
 (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 9424 (* h1 h1) (* h2 h2 h2) (* 
h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 36320 (* h1 h1) (* h2 h2 h2)
 (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 72216 (* h1 h1) (* h2 h2 h2
) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 83752 (* h1 h1) (* h2 h2 h2) 
(* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 59329 (* h1 h1) (* h2 h2 h2) (* h3
 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 25736 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* 
h4 h4) h5 (* j2 j2 j2)) (* 6582 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 
(* j2 j2)) (* 896 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 j2) (* 49 (* h1 
h1) (* h2 h2 h2) (* h3 h3) (* h4 h4) h5) (* 192 (* h1 h1) (* h2 h2 h2) (* h3 h3)
 (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2704 (* h1 h1) (* h2 h2 h2) (* 
h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 11496 (* h1 h1) (* h2 h2 h2)
 (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 24140 (* h1 h1) (* h2 h2 h2
) (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 29270 (* h1 h1) (* h2 h2 h2) 
(* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 21738 (* h1 h1) (* h2 h2 h2) (* h3
 h3) (* h4 h4) h6 (* j2 j2 j2 j2)) (* 9988 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* 
h4 h4) h6 (* j2 j2 j2)) (* 2752 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h4 h4) h6 
(* j2 j2)) (* 414 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h4 h4) h6 j2) (* 26 (* h1 
h1) (* h2 h2 h2) (* h3 h3) (* h4 h4) h6) (* 2688 (* h1 h1) (* h2 h2 h2) (* h3 h3
) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 21368 (* h1 h1) (* h2 h2 h2) 
(* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 70348 (* h1 h1) (* h2 h2 
h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 126210 (* h1 h1) (* h2 
h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 136017 (* h1 h1) (* h2 
h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 91260 (* h1 h1) (* h2 h2 h2
) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 38105 (* h1 h1) (* h2 h2 h2) (* h3 
h3) h4 (* h5 h5) (* j2 j2 j2)) (* 9549 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h5
 h5) (* j2 j2)) (* 1302 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) j2) (* 73 
(* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h5 h5)) (* 4432 (* h1 h1) (* h2 h2 h2) 
(* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 35648 (* h1 h1) (* h2 h2 
h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 117840 (* h1 h1) (* h2 h2
 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 212120 (* h1 h1) (* h2 h2 
h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 230063 (* h1 h1) (* h2 h2 h2) 
(* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 156110 (* h1 h1) (* h2 h2 h2) (* h3 h3
) h4 h5 h6 (* j2 j2 j2 j2)) (* 66274 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 h6 
(* j2 j2 j2)) (* 16968 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2)) (* 
2375 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 h6 j2) (* 138 (* h1 h1) (* h2 h2 h2)
 (* h3 h3) h4 h5 h6) (* 576 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 6544 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 25872 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 52388 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h6
 h6) (* j2 j2 j2 j2 j2 j2)) (* 62204 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h6 
h6) (* j2 j2 j2 j2 j2)) (* 45648 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h6 h6) 
(* j2 j2 j2 j2)) (* 20872 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2
 j2)) (* 5764 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2)) (* 876 
(* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h6 h6) j2) (* 56 (* h1 h1) (* h2 h2 h2) 
(* h3 h3) h4 (* h6 h6)) (* 512 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4416 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5 
h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 15648 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5
 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 29968 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* 
h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 34072 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5
 h5 h5) (* j2 j2 j2 j2 j2)) (* 23700 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5 
h5) (* j2 j2 j2 j2)) (* 10026 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* 
j2 j2 j2)) (* 2486 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2)) (* 
330 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) j2) (* 18 (* h1 h1) (* h2 h2 
h2) (* h3 h3) (* h5 h5 h5)) (* 3840 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 27832 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 84676 (* h1 h1) (* h2 h2 h2) (* h3 h3)
 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 141630 (* h1 h1) (* h2 h2 h2) (* h3 
h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 143231 (* h1 h1) (* h2 h2 h2) (* h3 
h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 90727 (* h1 h1) (* h2 h2 h2) (* h3 h3) 
(* h5 h5) h6 (* j2 j2 j2 j2)) (* 36023 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5
) h6 (* j2 j2 j2)) (* 8667 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 
j2)) (* 1150 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) h6 j2) (* 64 (* h1 h1) 
(* h2 h2 h2) (* h3 h3) (* h5 h5) h6) (* 3344 (* h1 h1) (* h2 h2 h2) (* h3 h3) h5
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 25184 (* h1 h1) (* h2 h2 h2) (* h3
 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 79144 (* h1 h1) (* h2 h2 h2) 
(* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 136948 (* h1 h1) (* h2 h2 h2
) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 144177 (* h1 h1) (* h2 h2 h2)
 (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 95935 (* h1 h1) (* h2 h2 h2) (* 
h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 40422 (* h1 h1) (* h2 h2 h2) (* h3 h3) 
h5 (* h6 h6) (* j2 j2 j2)) (* 10426 (* h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* h6 h6
) (* j2 j2)) (* 1497 (* h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* h6 h6) j2) (* 91 (* 
h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* h6 h6)) (* 384 (* h1 h1) (* h2 h2 h2) (* h3 
h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3840 (* h1 h1) (* h2 h2 h2) 
(* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 14376 (* h1 h1) (* h2 h2 
h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 28248 (* h1 h1) (* h2 h2
 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 32934 (* h1 h1) (* h2 h2 
h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 23910 (* h1 h1) (* h2 h2 h2) 
(* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 10884 (* h1 h1) (* h2 h2 h2) (* h3 h3
) (* h6 h6 h6) (* j2 j2 j2)) (* 3012 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6 
h6) (* j2 j2)) (* 462 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6 h6) j2) (* 30 
(* h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6 h6)) (* 128 (* h1 h1) (* h2 h2 h2) h3 
(* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2224 (* h1 h1) (* h2 
h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 11584 (* h1 h1)
 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 30168 (* h1
 h1) (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 46336 (* 
h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 44955 (* h1
 h1) (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 28202 (* h1 h1) 
(* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 11339 (* h1 h1) (* h2 h2
 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 2793 (* h1 h1) (* h2 h2 h2) h3 (* 
h4 h4) (* h5 h5) (* j2 j2)) (* 378 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h5 h5)
 j2) (* 21 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h5 h5)) (* 128 (* h1 h1) (* h2
 h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1920 (* h1 h1) 
(* h2 h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 9280 (* h1 h1
) (* h2 h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 23008 (* h1 h1
) (* h2 h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 34264 (* h1 h1) 
(* h2 h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 32784 (* h1 h1) (* h2 
h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 20644 (* h1 h1) (* h2 h2 h2) h3
 (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 8496 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) h5
 h6 (* j2 j2 j2)) (* 2192 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2)) 
(* 320 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) h5 h6 j2) (* 20 (* h1 h1) (* h2 h2 h2
) h3 (* h4 h4) h5 h6) (* 32 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 232 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 736 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h6 h6
) (* j2 j2 j2 j2 j2 j2 j2)) (* 1338 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h6 h6
) (* j2 j2 j2 j2 j2 j2)) (* 1532 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* 1142 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 
j2 j2 j2)) (* 552 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 j2 j2)) 
(* 166 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 j2)) (* 28 (* h1 h1) 
(* h2 h2 h2) h3 (* h4 h4) (* h6 h6) j2) (* 2 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4)
 (* h6 h6)) (* 64 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2
 j2 j2 j2 j2)) (* 1392 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 7824 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 21416 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 
j2 j2 j2 j2)) (* 34256 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 
j2 j2)) (* 34463 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) 
(* 22364 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 9287 (* 
h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2)) (* 2361 (* h1 h1) (* h2 h2 
h2) h3 h4 (* h5 h5 h5) (* j2 j2)) (* 330 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5 
h5) j2) (* 19 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5 h5)) (* 928 (* h1 h1) (* h2 
h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 9736 (* h1 h1) 
(* h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 41124 (* h1 
h1) (* h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 95102 (* h1 
h1) (* h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 135329 (* h1 h1
) (* h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 124740 (* h1 h1) (* 
h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 75715 (* h1 h1) (* h2 h2 h2)
 h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 29933 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5
 h5) h6 (* j2 j2 j2)) (* 7376 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2
)) (* 1021 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) h6 j2) (* 60 (* h1 h1) (* h2 
h2 h2) h3 h4 (* h5 h5) h6) (* 384 (* h1 h1) (* h2 h2 h2) h3 h4 h5 (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4704 (* h1 h1) (* h2 h2 h2) h3 h4 h5 (* h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 21128 (* h1 h1) (* h2 h2 h2) h3 h4 h5 (* h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 50452 (* h1 h1) (* h2 h2 h2) h3 h4 h5 (* h6
 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 73490 (* h1 h1) (* h2 h2 h2) h3 h4 h5 (* h6 h6
) (* j2 j2 j2 j2 j2 j2)) (* 69369 (* h1 h1) (* h2 h2 h2) h3 h4 h5 (* h6 h6) (* 
j2 j2 j2 j2 j2)) (* 43347 (* h1 h1) (* h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 
j2)) (* 17790 (* h1 h1) (* h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2)) (* 4600 
(* h1 h1) (* h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2)) (* 677 (* h1 h1) (* h2 h2 
h2) h3 h4 h5 (* h6 h6) j2) (* 43 (* h1 h1) (* h2 h2 h2) h3 h4 h5 (* h6 h6)) (* 
64 (* h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
464 (* h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
1472 (* h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2676
 (* h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3064 (* h1 
h1) (* h2 h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2284 (* h1 h1) (* h2 
h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1104 (* h1 h1) (* h2 h2 h2) h3 h4 
(* h6 h6 h6) (* j2 j2 j2)) (* 332 (* h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6 h6) (* 
j2 j2)) (* 56 (* h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6 h6) j2) (* 4 (* h1 h1) (* h2
 h2 h2) h3 h4 (* h6 h6 h6)) (* 64 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 448 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1360 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 2344 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* 
j2 j2 j2 j2 j2 j2)) (* 2520 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* j2 j2 
j2 j2 j2)) (* 1746 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* j2 j2 j2 j2)) 
(* 776 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* j2 j2 j2)) (* 212 (* h1 h1) 
(* h2 h2 h2) h3 (* h5 h5 h5 h5) (* j2 j2)) (* 32 (* h1 h1) (* h2 h2 h2) h3 (* h5
 h5 h5 h5) j2) (* 2 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5 h5)) (* 384 (* h1 h1) 
(* h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3760 (* h1
 h1) (* h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 15216 
(* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 34072 
(* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 47124 (* 
h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 42231 (* h1 h1)
 (* h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 24884 (* h1 h1) (* h2 h2
 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 9527 (* h1 h1) (* h2 h2 h2) h3 (* h5
 h5 h5) h6 (* j2 j2 j2)) (* 2267 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2
 j2)) (* 302 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) h6 j2) (* 17 (* h1 h1) (* h2
 h2 h2) h3 (* h5 h5 h5) h6) (* 672 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 6696 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 27284 (* h1 h1) (* h2 h2 h2) h3 (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 61402 (* h1 h1) (* h2 h2 h2) h3
 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 85573 (* h1 h1) (* h2 h2 h2) 
h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 77701 (* h1 h1) (* h2 h2 h2) h3
 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 46754 (* h1 h1) (* h2 h2 h2) h3 (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 18466 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5) 
(* h6 h6) (* j2 j2 j2)) (* 4593 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* h6 h6) 
(* j2 j2)) (* 651 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* h6 h6) j2) (* 40 (* h1 
h1) (* h2 h2 h2) h3 (* h5 h5) (* h6 h6)) (* 256 (* h1 h1) (* h2 h2 h2) h3 h5 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2784 (* h1 h1) (* h2 h2 h2) h3 
h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 11848 (* h1 h1) (* h2 h2 h2) 
h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 27444 (* h1 h1) (* h2 h2 h2) 
h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 39226 (* h1 h1) (* h2 h2 h2) h3 
h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 36585 (* h1 h1) (* h2 h2 h2) h3 h5 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 22703 (* h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6 h6)
 (* j2 j2 j2 j2)) (* 9294 (* h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2)
) (* 2408 (* h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2)) (* 357 (* h1 h1) 
(* h2 h2 h2) h3 h5 (* h6 h6 h6) j2) (* 23 (* h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6 
h6)) (* 32 (* h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 232 (* h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 736 (* h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 1338 (* h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1532
 (* h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1142 (* h1 h1)
 (* h2 h2 h2) h3 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 552 (* h1 h1) (* h2 h2 h2) 
h3 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 166 (* h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6 h6
) (* j2 j2)) (* 28 (* h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6 h6) j2) (* 2 (* h1 h1) 
(* h2 h2 h2) h3 (* h6 h6 h6 h6)) (* 224 (* h1 h1) (* h2 h2 h2) (* h4 h4) (* h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1680 (* h1 h1) (* h2 h2 h2) (* h4 
h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 5584 (* h1 h1) (* h2 h2 h2) 
(* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 10824 (* h1 h1) (* h2 h2 
h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 13542 (* h1 h1) (* h2 h2
 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 11421 (* h1 h1) (* h2 h2 
h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 6574 (* h1 h1) (* h2 h2 h2) 
(* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 2550 (* h1 h1) (* h2 h2 h2) (* h4 h4)
 (* h5 h5) h6 (* j2 j2 j2)) (* 638 (* h1 h1) (* h2 h2 h2) (* h4 h4) (* h5 h5) h6
 (* j2 j2)) (* 93 (* h1 h1) (* h2 h2 h2) (* h4 h4) (* h5 h5) h6 j2) (* 6 (* h1 
h1) (* h2 h2 h2) (* h4 h4) (* h5 h5) h6) (* 16 (* h1 h1) (* h2 h2 h2) (* h4 h4) 
h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 128 (* h1 h1) (* h2 h2 h2) 
(* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 456 (* h1 h1) (* h2 h2
 h2) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 952 (* h1 h1) (* h2 
h2 h2) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1289 (* h1 h1) (* h2 
h2 h2) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1182 (* h1 h1) (* h2 h2 
h2) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 743 (* h1 h1) (* h2 h2 h2) (* 
h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 316 (* h1 h1) (* h2 h2 h2) (* h4 h4) h5 
(* h6 h6) (* j2 j2 j2)) (* 87 (* h1 h1) (* h2 h2 h2) (* h4 h4) h5 (* h6 h6) (* 
j2 j2)) (* 14 (* h1 h1) (* h2 h2 h2) (* h4 h4) h5 (* h6 h6) j2) (* (* h1 h1) (* 
h2 h2 h2) (* h4 h4) h5 (* h6 h6)) (* 240 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1824 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5
 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 6136 (* h1 h1) (* h2 h2 h2) h4 (* h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 12024 (* h1 h1) (* h2 h2 h2) h4 (* h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 15191 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 12924 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5 h5) h6
 (* j2 j2 j2 j2 j2)) (* 7497 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 
j2 j2)) (* 2928 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 737 
(* h1 h1) (* h2 h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2)) (* 108 (* h1 h1) (* h2 h2 
h2) h4 (* h5 h5 h5) h6 j2) (* 7 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5 h5) h6) (* 
448 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 3376 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 11280 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2
 j2 j2 j2 j2)) (* 21992 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 27692 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2
 j2 j2 j2 j2)) (* 23523 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2)) (* 13649 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2
)) (* 5342 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 1350 
(* h1 h1) (* h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 199 (* h1 h1) (* h2 
h2 h2) h4 (* h5 h5) (* h6 h6) j2) (* 13 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5) (* 
h6 h6)) (* 32 (* h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 256 (* h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2 j2)) (* 912 (* h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 1904 (* h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 2578 (* h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2))
 (* 2364 (* h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1486 
(* h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 632 (* h1 h1) (* 
h2 h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 174 (* h1 h1) (* h2 h2 h2) h4 h5 
(* h6 h6 h6) (* j2 j2)) (* 28 (* h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6 h6) j2) (* 2
 (* h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6 h6)) (* 32 (* h1 h1) (* h2 h2 h2) (* h5 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 240 (* h1 h1) (* h2 h2 h2) 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 800 (* h1 h1) (* h2 h2 h2)
 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1560 (* h1 h1) (* h2 h2 h2) 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1970 (* h1 h1) (* h2 h2 h2) (* 
h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 1683 (* h1 h1) (* h2 h2 h2) (* h5 h5 
h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 985 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5 h5) h6 
(* j2 j2 j2 j2)) (* 390 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) 
(* 100 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 15 (* h1 h1) (* 
h2 h2 h2) (* h5 h5 h5 h5) h6 j2) (* (* h1 h1) (* h2 h2 h2) (* h5 h5 h5 h5) h6) 
(* 224 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 1712 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 5792 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 11416 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2
 j2 j2 j2 j2 j2)) (* 14510 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 12423 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2
 j2 j2 j2)) (* 7255 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2
)) (* 2854 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 724 
(* h1 h1) (* h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 107 (* h1 h1) (* h2 
h2 h2) (* h5 h5 h5) (* h6 h6) j2) (* 7 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5) (* h6
 h6)) (* 224 (* h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 1696 (* h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 5696 (* h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 11168 (* h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 14150 (* h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2)) (* 12102 (* h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2)) (* 7075 (* h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2)) (* 2792 (* h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) 
(* 712 (* h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 106 (* h1 h1)
 (* h2 h2 h2) (* h5 h5) (* h6 h6 h6) j2) (* 7 (* h1 h1) (* h2 h2 h2) (* h5 h5) 
(* h6 h6 h6)) (* 16 (* h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 128 (* h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 456 (* h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 952 (* h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2
 j2 j2 j2)) (* 1289 (* h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 1182 (* h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
743 (* h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 316 (* h1 h1) 
(* h2 h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 87 (* h1 h1) (* h2 h2 h2) h5 
(* h6 h6 h6 h6) (* j2 j2)) (* 14 (* h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6 h6) j2) 
(* (* h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6 h6)) (* 4208 (* h1 h1) (* h2 h2) (* h3 
h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 26032 (* h1 h1) (* h2 h2) (* h3 
h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 67812 (* h1 h1) (* h2 h2) (* h3 h3 
h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 96460 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3)
 h4 h5 (* j2 j2 j2 j2 j2)) (* 81188 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h5 
(* j2 j2 j2 j2)) (* 40920 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2)
) (* 11900 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2)) (* 1804 (* h1 h1
) (* h2 h2) (* h3 h3 h3 h3) h4 h5 j2) (* 108 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3)
 h4 h5) (* 2368 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 14128 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 
j2)) (* 35832 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2)) 
(* 50192 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 42200 
(* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 21648 (* h1 h1) 
(* h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2)) (* 6568 (* h1 h1) (* h2 h2) (* h3 
h3 h3 h3) h4 h6 (* j2 j2)) (* 1072 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h6 j2)
 (* 72 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h6) (* 2048 (* h1 h1) (* h2 h2) 
(* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 12928 (* h1 h1) (* h2 
h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 33856 (* h1 h1) (* h2
 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 47440 (* h1 h1) (* h2 
h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 38232 (* h1 h1) (* h2 h2) 
(* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 17732 (* h1 h1) (* h2 h2) (* h3 h3
 h3 h3) (* h5 h5) (* j2 j2 j2)) (* 4508 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* 
h5 h5) (* j2 j2)) (* 572 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) j2) (* 28
 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h5 h5)) (* 4336 (* h1 h1) (* h2 h2) (* 
h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 26576 (* h1 h1) (* h2 h2) (* 
h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 68260 (* h1 h1) (* h2 h2) (* h3 
h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 95164 (* h1 h1) (* h2 h2) (* h3 h3 h3 
h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 77900 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 h6
 (* j2 j2 j2 j2)) (* 37816 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2
)) (* 10476 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2)) (* 1500 (* h1 
h1) (* h2 h2) (* h3 h3 h3 h3) h5 h6 j2) (* 84 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3
) h5 h6) (* 2368 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 14128 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 35832 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2
 j2 j2 j2)) (* 50192 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 
j2 j2)) (* 42200 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2)) 
(* 21648 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2)) (* 6568 (* 
h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2)) (* 1072 (* h1 h1) (* h2 h2
) (* h3 h3 h3 h3) (* h6 h6) j2) (* 72 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h6 
h6)) (* 2992 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 27560 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2
 j2 j2 j2 j2)) (* 100844 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 
j2 j2 j2 j2 j2)) (* 196898 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 
j2 j2 j2 j2 j2)) (* 228112 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 
j2 j2 j2 j2)) (* 162976 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 
j2 j2)) (* 71704 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 
18662 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2)) (* 2588 (* h1 h1)
 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 j2) (* 144 (* h1 h1) (* h2 h2) (* h3 h3 h3)
 (* h4 h4) h5) (* 384 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 4160 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 17000 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 36636 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h6
 (* j2 j2 j2 j2 j2 j2)) (* 46960 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h6 
(* j2 j2 j2 j2 j2)) (* 37444 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2
 j2 j2 j2)) (* 18600 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2))
 (* 5540 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2)) (* 896 (* h1 
h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h6 j2) (* 60 (* h1 h1) (* h2 h2) (* h3 h3 
h3) (* h4 h4) h6) (* 4864 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2
 j2 j2 j2 j2 j2 j2 j2)) (* 40728 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 140968 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h5
 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 264210 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* 
h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 294436 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* 
h5 h5) (* j2 j2 j2 j2 j2)) (* 201689 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h5 
h5) (* j2 j2 j2 j2)) (* 85000 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* 
j2 j2 j2)) (* 21418 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2)) (* 
2944 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) j2) (* 167 (* h1 h1) (* h2 h2
) (* h3 h3 h3) h4 (* h5 h5)) (* 9536 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 h6 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 79480 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 272488 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5
 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 507342 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 
h6 (* j2 j2 j2 j2 j2 j2)) (* 566304 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 h6 
(* j2 j2 j2 j2 j2)) (* 392866 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2
 j2 j2)) (* 169300 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 
43718 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2)) (* 6132 (* h1 h1) (* 
h2 h2) (* h3 h3 h3) h4 h5 h6 j2) (* 354 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 
h6) (* 960 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2
 j2 j2)) (* 9552 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 37400 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 78560 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2
 j2 j2 j2)) (* 99048 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 
j2 j2)) (* 78160 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) 
(* 38632 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2)) (* 11520 
(* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2)) (* 1880 (* h1 h1) (* h2
 h2) (* h3 h3 h3) h4 (* h6 h6) j2) (* 128 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 
(* h6 h6)) (* 640 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 5792 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 21600 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2
 j2 j2 j2 j2 j2 j2)) (* 43488 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* 
j2 j2 j2 j2 j2 j2)) (* 51772 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2
 j2 j2 j2 j2)) (* 37448 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 
j2 j2)) (* 16284 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2)) (* 
4062 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2)) (* 520 (* h1 h1) 
(* h2 h2) (* h3 h3 h3) (* h5 h5 h5) j2) (* 26 (* h1 h1) (* h2 h2) (* h3 h3 h3) 
(* h5 h5 h5)) (* 6304 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 49512 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 162400 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 289978 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2)) (* 308178 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) 
h6 (* j2 j2 j2 j2 j2)) (* 200685 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) h6 
(* j2 j2 j2 j2)) (* 79837 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2
 j2)) (* 18813 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2)) (* 2393 
(* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) h6 j2) (* 124 (* h1 h1) (* h2 h2) (* 
h3 h3 h3) (* h5 h5) h6) (* 6352 (* h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 50784 (* h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 168796 (* h1 h1) (* h2 h2) (* h3 h3 h3) 
h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 306536 (* h1 h1) (* h2 h2) (* h3 h3 h3
) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 335056 (* h1 h1) (* h2 h2) (* h3 h3 h3)
 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 228478 (* h1 h1) (* h2 h2) (* h3 h3 h3) h5 
(* h6 h6) (* j2 j2 j2 j2)) (* 97340 (* h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* h6 h6
) (* j2 j2 j2)) (* 25108 (* h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2)
) (* 3576 (* h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* h6 h6) j2) (* 214 (* h1 h1) (* 
h2 h2) (* h3 h3 h3) h5 (* h6 h6)) (* 576 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 5392 (* h1 h1) (* h2 h2) (* h3 h3 h3) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 20400 (* h1 h1) (* h2 h2) (* h3 h3 
h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 41924 (* h1 h1) (* h2 h2) (* h3 h3
 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 52088 (* h1 h1) (* h2 h2) (* h3 h3 
h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 40716 (* h1 h1) (* h2 h2) (* h3 h3 h3) 
(* h6 h6 h6) (* j2 j2 j2 j2)) (* 20032 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6
 h6) (* j2 j2 j2)) (* 5980 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6 h6) (* j2 
j2)) (* 984 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6 h6) j2) (* 68 (* h1 h1) 
(* h2 h2) (* h3 h3 h3) (* h6 h6 h6)) (* 96 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 
h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2288 (* h1 h1) (* h2 h2) (* h3 
h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 14076 (* h1 h1) (* h2 h2)
 (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 41636 (* h1 h1) (* h2
 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 70853 (* h1 h1) (* 
h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 74469 (* h1 h1) (* h2
 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 49434 (* h1 h1) (* h2 h2) 
(* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 20502 (* h1 h1) (* h2 h2) (* h3 h3
) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 5073 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4 
h4) h5 (* j2 j2)) (* 673 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 j2) (* 36
 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4 h4) h5) (* 96 (* h1 h1) (* h2 h2) (* h3 
h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 872 (* h1 h1) (* h2 h2) 
(* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3220 (* h1 h1) (* h2 
h2) (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 6464 (* h1 h1) (* h2 
h2) (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 7828 (* h1 h1) (* h2 h2)
 (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 5936 (* h1 h1) (* h2 h2) (* h3
 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2)) (* 2812 (* h1 h1) (* h2 h2) (* h3 h3) (* 
h4 h4 h4) h6 (* j2 j2 j2)) (* 800 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4 h4) h6 
(* j2 j2)) (* 124 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4 h4) h6 j2) (* 8 (* h1 
h1) (* h2 h2) (* h3 h3) (* h4 h4 h4) h6) (* 576 (* h1 h1) (* h2 h2) (* h3 h3) 
(* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 9360 (* h1 h1) (* h2 
h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 50952 (* h1
 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
141548 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2
)) (* 232158 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2
 j2)) (* 238806 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2
 j2)) (* 157062 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2
)) (* 65434 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 
16566 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 2296 (* h1
 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) j2) (* 130 (* h1 h1) (* h2 h2) (* 
h3 h3) (* h4 h4) (* h5 h5)) (* 672 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 h6
 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 11760 (* h1 h1) (* h2 h2) (* h3 h3) (* h4
 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 65472 (* h1 h1) (* h2 h2) (* h3 h3
) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 183476 (* h1 h1) (* h2 h2) (* 
h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 302086 (* h1 h1) (* h2 h2) 
(* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 311614 (* h1 h1) (* h2 h2) 
(* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 205668 (* h1 h1) (* h2 h2) (* 
h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 86040 (* h1 h1) (* h2 h2) (* h3 h3) 
(* h4 h4) h5 h6 (* j2 j2 j2)) (* 21862 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) 
h5 h6 (* j2 j2)) (* 3046 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 h6 j2) (* 
176 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 h6) (* 352 (* h1 h1) (* h2 h2) 
(* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3112 (* h1 h1) 
(* h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 11348 
(* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
22696 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 27572 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 21112 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 
10172 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 2968 
(* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2)) (* 476 (* h1 h1) 
(* h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) j2) (* 32 (* h1 h1) (* h2 h2) (* h3 h3) 
(* h4 h4) (* h6 h6)) (* 256 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4896 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5 
h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 28432 (* h1 h1) (* h2 h2) (* h3 h3) h4 
(* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 82288 (* h1 h1) (* h2 h2) (* h3 h3)
 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 139076 (* h1 h1) (* h2 h2) (* h3 
h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 146172 (* h1 h1) (* h2 h2) (* h3 
h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 97341 (* h1 h1) (* h2 h2) (* h3 h3) 
h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 40664 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5
 h5 h5) (* j2 j2 j2)) (* 10250 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* 
j2 j2)) (* 1416 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) j2) (* 81 (* h1 h1
) (* h2 h2) (* h3 h3) h4 (* h5 h5 h5)) (* 2400 (* h1 h1) (* h2 h2) (* h3 h3) h4 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 29416 (* h1 h1) (* h2 h2) (* 
h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 140864 (* h1 h1) (* h2
 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 362570 (* h1 h1) 
(* h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 564828 (* h1 h1
) (* h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 559968 (* h1 h1)
 (* h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 358521 (* h1 h1) (* 
h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 146565 (* h1 h1) (* h2 h2) 
(* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 36691 (* h1 h1) (* h2 h2) (* h3 h3) 
h4 (* h5 h5) h6 (* j2 j2)) (* 5077 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) h6
 j2) (* 292 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) h6) (* 1248 (* h1 h1) (* 
h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 17968 (* 
h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
92500 (* h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2))
 (* 248064 (* h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2
)) (* 397473 (* h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)
) (* 403621 (* h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 264946 (* h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 
111458 (* h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 28845 (* 
h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 4153 (* h1 h1) (* h2 h2
) (* h3 h3) h4 h5 (* h6 h6) j2) (* 252 (* h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* h6
 h6)) (* 416 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 3608 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 13036 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2
 j2 j2 j2 j2)) (* 26000 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 31660 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2
 j2 j2)) (* 24416 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2))
 (* 11908 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2)) (* 3536 
(* h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2)) (* 580 (* h1 h1) (* h2 
h2) (* h3 h3) h4 (* h6 h6 h6) j2) (* 40 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 
h6 h6)) (* 192 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 1568 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 5488 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 
j2 j2 j2 j2 j2)) (* 10696 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2
 j2 j2 j2 j2)) (* 12620 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 
j2 j2 j2)) (* 9178 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2)
) (* 4016 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 992 (* 
h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2)) (* 124 (* h1 h1) (* h2 h2)
 (* h3 h3) (* h5 h5 h5 h5) j2) (* 6 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5 h5
)) (* 832 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 9456 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 43368 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2
 j2 j2 j2 j2 j2 j2)) (* 108324 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2)) (* 164490 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 158628 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2)) (* 97936 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2
 j2 j2 j2)) (* 38013 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2))
 (* 8853 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2)) (* 1115 (* h1 
h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) h6 j2) (* 57 (* h1 h1) (* h2 h2) (* h3 h3) 
(* h5 h5 h5) h6) (* 1632 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 18776 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 86272 (* h1 h1) (* h2 h2) (* h3 h3)
 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 215270 (* h1 h1) (* h2 h2) 
(* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 327186 (* h1 h1) (* 
h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 318009 (* h1 h1) 
(* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 200498 (* h1 h1) 
(* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 81097 (* h1 h1) (* 
h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 20207 (* h1 h1) (* h2 h2) 
(* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 2808 (* h1 h1) (* h2 h2) (* h3 h3) 
(* h5 h5) (* h6 h6) j2) (* 165 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6)
) (* 672 (* h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 8496 (* h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 41104 (* h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2
 j2 j2 j2 j2 j2 j2)) (* 106224 (* h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 166240 (* h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 166476 (* h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2)) (* 108712 (* h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* 
j2 j2 j2 j2)) (* 45920 (* h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2
)) (* 12056 (* h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 1780 (* 
h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6 h6) j2) (* 112 (* h1 h1) (* h2 h2) (* h3 
h3) h5 (* h6 h6 h6)) (* 160 (* h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 1368 (* h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4908 (* h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 9768 (* h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 11916 (* h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6 h6
) (* j2 j2 j2 j2 j2)) (* 9240 (* h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6 h6) (* 
j2 j2 j2 j2)) (* 4548 (* h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2)
) (* 1368 (* h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6 h6) (* j2 j2)) (* 228 (* h1 
h1) (* h2 h2) (* h3 h3) (* h6 h6 h6 h6) j2) (* 16 (* h1 h1) (* h2 h2) (* h3 h3) 
(* h6 h6 h6 h6)) (* 224 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 2364 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 10400 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) (* 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 25379 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4)
 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 38195 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4
) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 37050 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) 
(* h5 h5) (* j2 j2 j2 j2 j2)) (* 23403 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) (* h5
 h5) (* j2 j2 j2 j2)) (* 9463 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* 
j2 j2 j2)) (* 2329 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 
312 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) j2) (* 17 (* h1 h1) (* h2 h2) 
h3 (* h4 h4 h4) (* h5 h5)) (* 64 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) h5 h6 (* j2
 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 628 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) h5 h6 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2600 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) h5 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6063 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) h5 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 8878 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) h5 h6 
(* j2 j2 j2 j2 j2 j2)) (* 8555 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) h5 h6 (* j2 
j2 j2 j2 j2)) (* 5498 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2))
 (* 2325 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 618 (* h1 h1
) (* h2 h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2)) (* 93 (* h1 h1) (* h2 h2) h3 (* h4 
h4 h4) h5 h6 j2) (* 6 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) h5 h6) (* 240 (* h1 h1
) (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2896
 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 13868 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 36020 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2
 j2)) (* 57052 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 
j2)) (* 57913 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) 
(* 38186 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 16111
 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 4141 (* h1 h1) 
(* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 580 (* h1 h1) (* h2 h2) h3 (* 
h4 h4) (* h5 h5 h5) j2) (* 33 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5 h5)) (* 
1408 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2
 j2)) (* 13072 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 52488 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 119900 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2)) (* 172168 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2)) (* 161879 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* 
j2 j2 j2 j2 j2)) (* 100563 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 
j2 j2 j2)) (* 40598 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) 
(* 10154 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 1415 (* h1 
h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) h6 j2) (* 83 (* h1 h1) (* h2 h2) h3 (* h4 
h4) (* h5 h5) h6) (* 240 (* h1 h1) (* h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 2304 (* h1 h1) (* h2 h2) h3 (* h4 h4) h5 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 9432 (* h1 h1) (* h2 h2) h3 (* h4 h4) h5 (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 21894 (* h1 h1) (* h2 h2) h3 (* h4 h4) h5
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 32070 (* h1 h1) (* h2 h2) h3 (* h4 h4) 
h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 31044 (* h1 h1) (* h2 h2) h3 (* h4 h4) h5
 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 20124 (* h1 h1) (* h2 h2) h3 (* h4 h4) h5 (* 
h6 h6) (* j2 j2 j2 j2)) (* 8622 (* h1 h1) (* h2 h2) h3 (* h4 h4) h5 (* h6 h6) 
(* j2 j2 j2)) (* 2334 (* h1 h1) (* h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2)) 
(* 360 (* h1 h1) (* h2 h2) h3 (* h4 h4) h5 (* h6 h6) j2) (* 24 (* h1 h1) (* h2 
h2) h3 (* h4 h4) h5 (* h6 h6)) (* 32 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 480 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5 
h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2592 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 7344 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 12522 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5 
h5) (* j2 j2 j2 j2 j2 j2)) (* 13618 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5 h5) 
(* j2 j2 j2 j2 j2)) (* 9613 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2 
j2 j2)) (* 4346 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2)) (* 1198 
(* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2)) (* 180 (* h1 h1) (* h2 h2) 
h3 h4 (* h5 h5 h5 h5) j2) (* 11 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5 h5)) (* 
1248 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 11672 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 47344 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 109402 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2
)) (* 158984 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 151241 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 94976
 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 38704 (* h1 h1) 
(* h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 9752 (* h1 h1) (* h2 h2) h3 h4 
(* h5 h5 h5) h6 (* j2 j2)) (* 1365 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) h6 j2)
 (* 80 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) h6) (* 2144 (* h1 h1) (* h2 h2) h3
 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 19048 (* h1 h1) 
(* h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 73808 (* 
h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
163946 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 230572 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 213872 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
132083 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 53474 
(* h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 13554 (* h1 h1) 
(* h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 1940 (* h1 h1) (* h2 h2) h3 h4
 (* h5 h5) (* h6 h6) j2) (* 119 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* h6 h6)) 
(* 288 (* h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 2724 (* h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 11064 (* h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 25599 (* h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 37506 (* h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 36423 (* h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 23754 
(* h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 10269 (* h1 h1) 
(* h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 2814 (* h1 h1) (* h2 h2) h3 h4 
h5 (* h6 h6 h6) (* j2 j2)) (* 441 (* h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6 h6) j2) 
(* 30 (* h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6 h6)) (* 160 (* h1 h1) (* h2 h2) h3 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1440 (* h1 h1) (* h2 h2
) h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 5664 (* h1 h1) (* h2 
h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 12760 (* h1 h1) (* h2 
h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 18138 (* h1 h1) (* h2 h2)
 h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 16900 (* h1 h1) (* h2 h2) h3 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 10383 (* h1 h1) (* h2 h2) h3 (* h5 h5 
h5 h5) h6 (* j2 j2 j2 j2)) (* 4120 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) h6 (* 
j2 j2 j2)) (* 1000 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 132 
(* h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) h6 j2) (* 7 (* h1 h1) (* h2 h2) h3 (* h5 
h5 h5 h5) h6) (* 960 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 8440 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 32456 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 71646 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 100152 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5
) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 92246 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 56459 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* h6
 h6) (* j2 j2 j2 j2)) (* 22593 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2)) (* 5645 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 
795 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* h6 h6) j2) (* 48 (* h1 h1) (* h2 h2) 
h3 (* h5 h5 h5) (* h6 h6)) (* 960 (* h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8340 (* h1 h1) (* h2 h2) h3 (* h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 31720 (* h1 h1) (* h2 h2) h3 (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 69425 (* h1 h1) (* h2 h2) h3 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 96599 (* h1 h1) (* h2 h2) h3
 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 89043 (* h1 h1) (* h2 h2) h3 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 54923 (* h1 h1) (* h2 h2) h3 (* h5
 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 22339 (* h1 h1) (* h2 h2) h3 (* h5 h5) (* 
h6 h6 h6) (* j2 j2 j2)) (* 5729 (* h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6 h6) 
(* j2 j2)) (* 837 (* h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6 h6) j2) (* 53 (* h1 
h1) (* h2 h2) h3 (* h5 h5) (* h6 h6 h6)) (* 112 (* h1 h1) (* h2 h2) h3 h5 (* h6 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1048 (* h1 h1) (* h2 h2) h3 h5 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4232 (* h1 h1) (* h2 h2) h3 
h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 9768 (* h1 h1) (* h2 h2) h3 
h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 14314 (* h1 h1) (* h2 h2) h3 h5 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 13934 (* h1 h1) (* h2 h2) h3 h5 (* h6 
h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 9128 (* h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6 h6) 
(* j2 j2 j2 j2)) (* 3972 (* h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2))
 (* 1098 (* h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2)) (* 174 (* h1 h1) 
(* h2 h2) h3 h5 (* h6 h6 h6 h6) j2) (* 12 (* h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6 
h6)) (* 40 (* h1 h1) (* h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2
 j2 j2 j2)) (* 324 (* h1 h1) (* h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 1162 (* h1 h1) (* h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 2427 (* h1 h1) (* h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2)) (* 3265 (* h1 h1) (* h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 
j2 j2 j2 j2 j2)) (* 2952 (* h1 h1) (* h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 
j2 j2 j2)) (* 1814 (* h1 h1) (* h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)
) (* 747 (* h1 h1) (* h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 197 (* 
h1 h1) (* h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 30 (* h1 h1) (* h2 h2) 
(* h4 h4 h4) (* h5 h5) h6 j2) (* 2 (* h1 h1) (* h2 h2) (* h4 h4 h4) (* h5 h5) h6
) (* 128 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 1032 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 3692 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 7710 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2)) (* 10397 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2
 j2 j2 j2 j2 j2)) (* 9450 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2
 j2 j2 j2)) (* 5857 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2
)) (* 2442 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 655 
(* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 102 (* h1 h1) (* h2 
h2) (* h4 h4) (* h5 h5 h5) h6 j2) (* 7 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5 h5
) h6) (* 136 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 1108 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4002 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 8431 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 11461 (* h1 h1) (* h2 h2) (* h4 h4) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 10494 (* h1 h1) (* h2 h2) (* h4 h4
) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 6548 (* h1 h1) (* h2 h2) (* h4 h4) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 2747 (* h1 h1) (* h2 h2) (* h4 h4) (* h5
 h5) (* h6 h6) (* j2 j2 j2)) (* 741 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) (* 
h6 h6) (* j2 j2)) (* 116 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) j2) 
(* 8 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6)) (* 64 (* h1 h1) (* h2 h2
) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 528 (* h1 h1) (* 
h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1928 (* h1 h1) 
(* h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4100 (* h1 h1) 
(* h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 5618 (* h1 h1) (* 
h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 5178 (* h1 h1) (* h2 h2) 
h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 3248 (* h1 h1) (* h2 h2) h4 (* h5 
h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 1368 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5 h5) h6 
(* j2 j2 j2)) (* 370 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 58 
(* h1 h1) (* h2 h2) h4 (* h5 h5 h5 h5) h6 j2) (* 4 (* h1 h1) (* h2 h2) h4 (* h5 
h5 h5 h5) h6) (* 256 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 2072 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 7444 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 15618 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 21171 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 19356 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 12077 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5) (* h6
 h6) (* j2 j2 j2 j2)) (* 5074 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2)) (* 1373 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 
216 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5) (* h6 h6) j2) (* 15 (* h1 h1) (* h2 h2) 
h4 (* h5 h5 h5) (* h6 h6)) (* 152 (* h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1244 (* h1 h1) (* h2 h2) h4 (* h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4518 (* h1 h1) (* h2 h2) h4 (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 9581 (* h1 h1) (* h2 h2) h4 (* 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 13127 (* h1 h1) (* h2 h2) h4 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 12132 (* h1 h1) (* h2 h2) h4 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 7654 (* h1 h1) (* h2 h2) h4 (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 3253 (* h1 h1) (* h2 h2) h4 (* h5 h5) (* h6
 h6 h6) (* j2 j2 j2)) (* 891 (* h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2
 j2)) (* 142 (* h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6 h6) j2) (* 10 (* h1 h1) 
(* h2 h2) h4 (* h5 h5) (* h6 h6 h6)) (* 64 (* h1 h1) (* h2 h2) (* h5 h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 528 (* h1 h1) (* h2 h2) (* h5 h5
 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1928 (* h1 h1) (* h2 h2) 
(* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4100 (* h1 h1) (* h2 
h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 5618 (* h1 h1) (* h2 
h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 5178 (* h1 h1) (* h2 h2)
 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 3248 (* h1 h1) (* h2 h2) (* h5
 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 1368 (* h1 h1) (* h2 h2) (* h5 h5 h5 h5
) (* h6 h6) (* j2 j2 j2)) (* 370 (* h1 h1) (* h2 h2) (* h5 h5 h5 h5) (* h6 h6) 
(* j2 j2)) (* 58 (* h1 h1) (* h2 h2) (* h5 h5 h5 h5) (* h6 h6) j2) (* 4 (* h1 h1
) (* h2 h2) (* h5 h5 h5 h5) (* h6 h6)) (* 128 (* h1 h1) (* h2 h2) (* h5 h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1040 (* h1 h1) (* h2 h2) (* 
h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3752 (* h1 h1) (* h2 
h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 7908 (* h1 h1) (* 
h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 10774 (* h1 h1) 
(* h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 9906 (* h1 h1) (* 
h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 6220 (* h1 h1) (* h2 h2)
 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 2632 (* h1 h1) (* h2 h2) (* h5 h5
 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 718 (* h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6
 h6) (* j2 j2)) (* 114 (* h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6 h6) j2) (* 8 
(* h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6 h6)) (* 56 (* h1 h1) (* h2 h2) (* h5 
h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 460 (* h1 h1) (* h2 h2
) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1678 (* h1 h1) 
(* h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3577 (* h1 
h1) (* h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4931 (* h1 
h1) (* h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4590 (* h1 h1)
 (* h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2920 (* h1 h1) (* h2
 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 1253 (* h1 h1) (* h2 h2) (* 
h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 347 (* h1 h1) (* h2 h2) (* h5 h5) (* h6 
h6 h6 h6) (* j2 j2)) (* 56 (* h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6 h6) j2) (* 
4 (* h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6 h6)) (* 2096 (* h1 h1) h2 (* h3 h3 
h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 15256 (* h1 h1) h2 (* h3 
h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 48056 (* h1 h1) h2 (* h3 
h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 85620 (* h1 h1) h2 (* h3 h3 
h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 94568 (* h1 h1) h2 (* h3 h3 h3 h3)
 (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 66676 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4
) h5 (* j2 j2 j2 j2)) (* 29736 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 
j2 j2)) (* 7996 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2)) (* 1160 (* 
h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h5 j2) (* 68 (* h1 h1) h2 (* h3 h3 h3 h3) 
(* h4 h4) h5) (* 192 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2
 j2 j2 j2 j2)) (* 1456 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 4832 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 
j2 j2 j2)) (* 9184 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 
j2)) (* 10976 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 
8512 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2)) (* 4256 (* h1 h1
) h2 (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2)) (* 1312 (* h1 h1) h2 (* h3 h3 h3
 h3) (* h4 h4) h6 (* j2 j2)) (* 224 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h6 j2
) (* 16 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h6) (* 2624 (* h1 h1) h2 (* h3 h3
 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 19648 (* h1 h1) h2 (* h3
 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 63072 (* h1 h1) h2 (* h3
 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 113200 (* h1 h1) h2 (* h3 
h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 124132 (* h1 h1) h2 (* h3 h3 h3
 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 85294 (* h1 h1) h2 (* h3 h3 h3 h3) h4 
(* h5 h5) (* j2 j2 j2 j2)) (* 36208 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h5 h5) 
(* j2 j2 j2)) (* 9012 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2)) (* 
1180 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h5 h5) j2) (* 62 (* h1 h1) h2 (* h3 h3 
h3 h3) h4 (* h5 h5)) (* 5680 (* h1 h1) h2 (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 41336 (* h1 h1) h2 (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 130024 (* h1 h1) h2 (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 
j2 j2 j2)) (* 231012 (* h1 h1) h2 (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)
) (* 254032 (* h1 h1) h2 (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 177980 
(* h1 h1) h2 (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 78696 (* h1 h1) h2 (* 
h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 20924 (* h1 h1) h2 (* h3 h3 h3 h3) h4 h5 
h6 (* j2 j2)) (* 2992 (* h1 h1) h2 (* h3 h3 h3 h3) h4 h5 h6 j2) (* 172 (* h1 h1)
 h2 (* h3 h3 h3 h3) h4 h5 h6) (* 448 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3440 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 11584 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6
) (* j2 j2 j2 j2 j2 j2 j2)) (* 22400 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 27328 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 
j2 j2 j2 j2)) (* 21728 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)
) (* 11200 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2)) (* 3584 (* h1
 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2)) (* 640 (* h1 h1) h2 (* h3 h3 h3 
h3) h4 (* h6 h6) j2) (* 48 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6)) (* 256 (* 
h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2048 
(* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6976 
(* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 13184 (* 
h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 15088 (* h1 h1)
 h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 10704 (* h1 h1) h2 (* h3
 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 4632 (* h1 h1) h2 (* h3 h3 h3 h3) 
(* h5 h5 h5) (* j2 j2 j2)) (* 1160 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* 
j2 j2)) (* 152 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5 h5) j2) (* 8 (* h1 h1) h2 
(* h3 h3 h3 h3) (* h5 h5 h5)) (* 3200 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 23584 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 74352 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 130632 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) h6
 (* j2 j2 j2 j2 j2 j2)) (* 139560 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) h6 (* 
j2 j2 j2 j2 j2)) (* 92772 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 
j2)) (* 37712 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 8864 
(* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2)) (* 1080 (* h1 h1) h2 (* h3 
h3 h3 h3) (* h5 h5) h6 j2) (* 52 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) h6) (* 
3520 (* h1 h1) h2 (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 25616 (* h1 h1) h2 (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 80512 (* h1 h1) h2 (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
142816 (* h1 h1) h2 (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
156664 (* h1 h1) h2 (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 109400 
(* h1 h1) h2 (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 48176 (* h1 h1) h2
 (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 12752 (* h1 h1) h2 (* h3 h3 h3 h3
) h5 (* h6 h6) (* j2 j2)) (* 1816 (* h1 h1) h2 (* h3 h3 h3 h3) h5 (* h6 h6) j2) 
(* 104 (* h1 h1) h2 (* h3 h3 h3 h3) h5 (* h6 h6)) (* 256 (* h1 h1) h2 (* h3 h3 
h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1984 (* h1 h1) h2 (* h3 
h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6752 (* h1 h1) h2 (* h3 
h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 13216 (* h1 h1) h2 (* h3 h3 
h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 16352 (* h1 h1) h2 (* h3 h3 h3 h3)
 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 13216 (* h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6
 h6) (* j2 j2 j2 j2)) (* 6944 (* h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2
 j2)) (* 2272 (* h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2)) (* 416 (* h1 
h1) h2 (* h3 h3 h3 h3) (* h6 h6 h6) j2) (* 32 (* h1 h1) h2 (* h3 h3 h3 h3) (* h6
 h6 h6)) (* 192 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 3136 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 17048 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 47632 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 
j2 j2 j2 j2)) (* 79430 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 
j2 j2)) (* 84076 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) 
(* 57506 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 25048 (* 
h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 6602 (* h1 h1) h2 (* h3 
h3 h3) (* h4 h4 h4) h5 (* j2 j2)) (* 940 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) 
h5 j2) (* 54 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h5) (* 96 (* h1 h1) h2 (* h3
 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 728 (* h1 h1) h2 (* 
h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2416 (* h1 h1) h2 (* 
h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 4592 (* h1 h1) h2 (* h3 
h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 5488 (* h1 h1) h2 (* h3 h3 h3) 
(* h4 h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 4256 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 
h4) h6 (* j2 j2 j2 j2)) (* 2128 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 
j2 j2)) (* 656 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2)) (* 112 (* h1
 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h6 j2) (* 8 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4
 h4) h6) (* 768 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 10168 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2
 j2 j2 j2 j2 j2 j2 j2)) (* 51380 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 138284 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h5
 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 224528 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* 
h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 231926 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* 
h5 h5) (* j2 j2 j2 j2 j2)) (* 154739 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h5 
h5) (* j2 j2 j2 j2)) (* 65740 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* 
j2 j2 j2)) (* 16938 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 
2370 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) j2) (* 135 (* h1 h1) h2 (* h3
 h3 h3) (* h4 h4) (* h5 h5)) (* 960 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 h6 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 13536 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) 
h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 69720 (* h1 h1) h2 (* h3 h3 h3) (* h4 
h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 189548 (* h1 h1) h2 (* h3 h3 h3) (* h4
 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 311084 (* h1 h1) h2 (* h3 h3 h3) (* h4 
h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 326052 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) 
h5 h6 (* j2 j2 j2 j2 j2)) (* 221716 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 h6 
(* j2 j2 j2 j2)) (* 96340 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)
) (* 25428 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 3644 (* h1 h1
) h2 (* h3 h3 h3) (* h4 h4) h5 h6 j2) (* 212 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4)
 h5 h6) (* 320 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 2448 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 8208 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 15792 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2
 j2 j2 j2 j2)) (* 19152 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 
j2 j2 j2)) (* 15120 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2
)) (* 7728 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 2448 
(* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2)) (* 432 (* h1 h1) h2 (* 
h3 h3 h3) (* h4 h4) (* h6 h6) j2) (* 32 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* 
h6 h6)) (* 320 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2
 j2 j2 j2)) (* 4784 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 25776 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 72264 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 
j2 j2 j2)) (* 120390 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2
 j2)) (* 125910 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) 
(* 83884 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 35033 (* 
h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2)) (* 8709 (* h1 h1) h2 (* h3 
h3 h3) h4 (* h5 h5 h5) (* j2 j2)) (* 1149 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5 
h5) j2) (* 61 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5 h5)) (* 2528 (* h1 h1) h2 
(* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 29216 (* h1 
h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 136976 
(* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 350936
 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 549468 
(* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 551346 (* h1
 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 359057 (* h1 h1) h2 
(* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 149486 (* h1 h1) h2 (* h3 h3 h3
) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 37900 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) 
h6 (* j2 j2)) (* 5240 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6 j2) (* 295 (* h1
 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6) (* 1472 (* h1 h1) h2 (* h3 h3 h3) h4 h5 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 18656 (* h1 h1) h2 (* h3 h3 h3) 
h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 91680 (* h1 h1) h2 (* h3 h3 
h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 242932 (* h1 h1) h2 (* h3 h3
 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 392650 (* h1 h1) h2 (* h3 h3 
h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 407904 (* h1 h1) h2 (* h3 h3 h3) 
h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 276326 (* h1 h1) h2 (* h3 h3 h3) h4 h5 
(* h6 h6) (* j2 j2 j2 j2)) (* 120260 (* h1 h1) h2 (* h3 h3 h3) h4 h5 (* h6 h6) 
(* j2 j2 j2)) (* 32022 (* h1 h1) h2 (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 
4680 (* h1 h1) h2 (* h3 h3 h3) h4 h5 (* h6 h6) j2) (* 282 (* h1 h1) h2 (* h3 h3 
h3) h4 h5 (* h6 h6)) (* 352 (* h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 2712 (* h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 9168 (* h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 17808 (* h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 21840 (* h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 
j2)) (* 17472 (* h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 9072
 (* h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2)) (* 2928 (* h1 h1) h2 
(* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2)) (* 528 (* h1 h1) h2 (* h3 h3 h3) h4 (* 
h6 h6 h6) j2) (* 40 (* h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6 h6)) (* 128 (* h1 h1) 
h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1024 (* h1 h1
) h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3488 (* h1 h1)
 h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 6592 (* h1 h1) h2 
(* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 7544 (* h1 h1) h2 (* h3 
h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 5352 (* h1 h1) h2 (* h3 h3 h3) (* 
h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 2316 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5 h5) 
(* j2 j2 j2)) (* 580 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2)) (* 76 
(* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5 h5) j2) (* 4 (* h1 h1) h2 (* h3 h3 h3) (* 
h5 h5 h5 h5)) (* 768 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 8576 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 39376 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 99128 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2)) (* 152060 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2
 j2 j2 j2)) (* 148260 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2)) (* 92554 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 
36224 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 8408 (* h1 h1) 
h2 (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2)) (* 1028 (* h1 h1) h2 (* h3 h3 h3) (* 
h5 h5 h5) h6 j2) (* 50 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) h6) (* 1632 (* h1 
h1) h2 (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
18104 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 82572 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 207136 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 318638 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 314764 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2)) (* 202124 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2))
 (* 83142 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 20896 
(* h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 2878 (* h1 h1) h2 
(* h3 h3 h3) (* h5 h5) (* h6 h6) j2) (* 162 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5) 
(* h6 h6)) (* 704 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2 j2 j2)) (* 8256 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 39008 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 101016 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2
 j2 j2 j2 j2)) (* 160996 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 165928 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2
)) (* 112116 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 48968
 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 13196 (* h1 h1) h2 
(* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 1976 (* h1 h1) h2 (* h3 h3 h3) h5 (* 
h6 h6 h6) j2) (* 124 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6 h6)) (* 128 (* h1 h1)
 h2 (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 992 (* h1 h1
) h2 (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3376 (* h1 h1)
 h2 (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 6608 (* h1 h1) h2 
(* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 8176 (* h1 h1) h2 (* h3 
h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 6608 (* h1 h1) h2 (* h3 h3 h3) (* 
h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 3472 (* h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6 h6) 
(* j2 j2 j2)) (* 1136 (* h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2)) (* 
208 (* h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6 h6) j2) (* 16 (* h1 h1) h2 (* h3 h3 h3
) (* h6 h6 h6 h6)) (* 48 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 604 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2
 j2 j2 j2 j2 j2 j2 j2)) (* 2926 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 7606 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 
j2 j2 j2 j2 j2 j2)) (* 12000 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 
j2 j2 j2 j2)) (* 12094 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 
j2)) (* 7884 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 3266 
(* h1 h1) h2 (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2)) (* 816 (* h1 h1) h2 (* 
h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2)) (* 110 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4 
h4) h5 j2) (* 6 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4 h4) h5) (* 512 (* h1 h1) h2 
(* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 5276 (* 
h1 h1) h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
23090 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2))
 (* 56812 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)
) (* 87159 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) 
(* 87027 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 
57096 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 24182 
(* h1 h1) h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 6283 (* h1 h1) h2
 (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 895 (* h1 h1) h2 (* h3 h3) (* h4
 h4 h4) (* h5 h5) j2) (* 52 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) (* h5 h5)) (* 
320 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (* 3672 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2
)) (* 17048 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 43410 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 67940 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 
68550 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 45112 (* 
h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 19038 (* h1 h1) h2 
(* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 4900 (* h1 h1) h2 (* h3 h3) (* h4 
h4 h4) h5 h6 (* j2 j2)) (* 690 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 h6 j2) (* 
40 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 h6) (* 544 (* h1 h1) h2 (* h3 h3) (* 
h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 5912 (* h1 h1) h2 (* 
h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 27152 (* h1 h1)
 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 69672 (* h1
 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 110643 (* 
h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 113371 (* 
h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 75597 (* h1 h1
) h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 32210 (* h1 h1) h2 (* 
h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 8333 (* h1 h1) h2 (* h3 h3) (* h4
 h4) (* h5 h5 h5) (* j2 j2)) (* 1171 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5 
h5) j2) (* 67 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5 h5)) (* 2336 (* h1 h1) 
h2 (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 22668 
(* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 94970 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 226242 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 338909 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 
j2 j2)) (* 332668 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 
j2)) (* 215817 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) 
(* 90862 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 23579 
(* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 3368 (* h1 h1) h2 
(* h3 h3) (* h4 h4) (* h5 h5) h6 j2) (* 197 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* 
h5 h5) h6) (* 720 (* h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 7836 (* h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 35414 (* h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 88986 (* h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* h6
 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 138652 (* h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 140254 (* h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* 
h6 h6) (* j2 j2 j2 j2 j2)) (* 93156 (* h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* h6 h6
) (* j2 j2 j2 j2)) (* 39974 (* h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 
j2 j2)) (* 10556 (* h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 
1542 (* h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* h6 h6) j2) (* 94 (* h1 h1) h2 (* h3 
h3) (* h4 h4) h5 (* h6 h6)) (* 96 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1200 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5 h5
) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 6072 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5 
h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 16756 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5 
h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 28134 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5 h5)
 (* j2 j2 j2 j2 j2 j2)) (* 30007 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* j2
 j2 j2 j2 j2)) (* 20449 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2
)) (* 8688 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2)) (* 2170 (* h1
 h1) h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2)) (* 285 (* h1 h1) h2 (* h3 h3) h4
 (* h5 h5 h5 h5) j2) (* 15 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5 h5)) (* 1904 
(* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
18448 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 77608 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 185934 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 279630 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
274352 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 176759 
(* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 73345 (* h1 h1) h2
 (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 18613 (* h1 h1) h2 (* h3 h3) h4 
(* h5 h5 h5) h6 (* j2 j2)) (* 2581 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) h6 j2)
 (* 146 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) h6) (* 3136 (* h1 h1) h2 (* h3 h3
) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 29504 (* h1 h1) 
h2 (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 120716 
(* h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
282490 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 417798 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 406813 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
263027 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 110904 
(* h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 28976 (* h1 h1) 
h2 (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 4193 (* h1 h1) h2 (* h3 h3) h4
 (* h5 h5) (* h6 h6) j2) (* 251 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* h6 h6)) 
(* 672 (* h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 7072 (* h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 31388 (* h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 78166 (* h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 121484 (* h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 123234 (* h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 82512
 (* h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 35898 (* h1 h1) 
h2 (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 9676 (* h1 h1) h2 (* h3 h3) h4 
h5 (* h6 h6 h6) (* j2 j2)) (* 1454 (* h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6) j2)
 (* 92 (* h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6)) (* 256 (* h1 h1) h2 (* h3 h3) 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2496 (* h1 h1) h2 (* h3
 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 10560 (* h1 h1) h2 
(* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 25392 (* h1 h1) h2 
(* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 38144 (* h1 h1) h2 (* 
h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 37028 (* h1 h1) h2 (* h3 h3)
 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 23204 (* h1 h1) h2 (* h3 h3) (* h5 h5
 h5 h5) h6 (* j2 j2 j2 j2)) (* 9104 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) h6 
(* j2 j2 j2)) (* 2096 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 
252 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) h6 j2) (* 12 (* h1 h1) h2 (* h3 h3) 
(* h5 h5 h5 h5) h6) (* 1312 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 12176 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 49276 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 114058 (* h1 h1) h2 (* h3 h3) (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 166432 (* h1 h1) h2 (* h3 h3) (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 159116 (* h1 h1) h2 (* h3 h3) (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 100345 (* h1 h1) h2 (* h3 h3) (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 40957 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2)) (* 10279 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* h6 h6) 
(* j2 j2)) (* 1417 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* h6 h6) j2) (* 80 (* h1
 h1) h2 (* h3 h3) (* h5 h5 h5) (* h6 h6)) (* 1312 (* h1 h1) h2 (* h3 h3) (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 12112 (* h1 h1) h2 (* h3 
h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 48836 (* h1 h1) h2
 (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 113060 (* h1 
h1) h2 (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 166048 (* 
h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 161172 (* 
h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 104306 (* h1 
h1) h2 (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 44224 (* h1 h1) h2 
(* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 11680 (* h1 h1) h2 (* h3 h3) 
(* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 1720 (* h1 h1) h2 (* h3 h3) (* h5 h5) (* h6
 h6 h6) j2) (* 106 (* h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6 h6)) (* 224 (* h1 
h1) h2 (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2304 
(* h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
10096 (* h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
24984 (* h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
38772 (* h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 39436 
(* h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 26584 (* h1 h1)
 h2 (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 11696 (* h1 h1) h2 (* h3 h3
) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 3204 (* h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6
 h6) (* j2 j2)) (* 492 (* h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6 h6) j2) (* 32 (* h1
 h1) h2 (* h3 h3) h5 (* h6 h6 h6 h6)) (* 40 (* h1 h1) h2 h3 (* h4 h4 h4 h4) (* 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 380 (* h1 h1) h2 h3 (* h4 h4 h4 h4)
 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1586 (* h1 h1) h2 h3 (* h4 h4 h4 
h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3803 (* h1 h1) h2 h3 (* h4 h4 h4 
h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 5760 (* h1 h1) h2 h3 (* h4 h4 h4 h4) 
(* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 5712 (* h1 h1) h2 h3 (* h4 h4 h4 h4) (* h5 
h5) (* j2 j2 j2 j2 j2)) (* 3721 (* h1 h1) h2 h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 
j2 j2 j2)) (* 1555 (* h1 h1) h2 h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 
394 (* h1 h1) h2 h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2)) (* 54 (* h1 h1) h2 h3 
(* h4 h4 h4 h4) (* h5 h5) j2) (* 3 (* h1 h1) h2 h3 (* h4 h4 h4 h4) (* h5 h5)) 
(* 128 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 1232 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 5228 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 12788 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 
j2)) (* 19827 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) 
(* 20208 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 13595 
(* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 5900 (* h1 h1) h2 
h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 1561 (* h1 h1) h2 h3 (* h4 h4 h4) 
(* h5 h5 h5) (* j2 j2)) (* 224 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5 h5) j2) (* 
13 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5 h5)) (* 264 (* h1 h1) h2 h3 (* h4 h4 h4
) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2432 (* h1 h1) h2 h3 (* h4 
h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 9878 (* h1 h1) h2 h3 (* 
h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 23164 (* h1 h1) h2 h3 (* 
h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 34515 (* h1 h1) h2 h3 (* h4 
h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 33905 (* h1 h1) h2 h3 (* h4 h4 h4)
 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 22056 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5
) h6 (* j2 j2 j2 j2)) (* 9294 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2
 j2)) (* 2403 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 341 (* h1 
h1) h2 h3 (* h4 h4 h4) (* h5 h5) h6 j2) (* 20 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5
 h5) h6) (* 64 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2
 j2 j2 j2)) (* 624 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 2692 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 6718 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 
j2 j2 j2)) (* 10656 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 
j2)) (* 11129 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 
7674 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 3410 (* h1 h1
) h2 h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 922 (* h1 h1) h2 h3 (* h4 h4)
 (* h5 h5 h5 h5) (* j2 j2)) (* 135 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5 h5) j2)
 (* 8 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5 h5)) (* 648 (* h1 h1) h2 h3 (* h4 h4
) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 5964 (* h1 h1) h2 h3 (* 
h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 24228 (* h1 h1) h2 h3 
(* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 56908 (* h1 h1) h2 h3 
(* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 85084 (* h1 h1) h2 h3 (* 
h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 84033 (* h1 h1) h2 h3 (* h4 h4)
 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 55075 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5
 h5) h6 (* j2 j2 j2 j2)) (* 23422 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) h6 (* 
j2 j2 j2)) (* 6114 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 873 
(* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) h6 j2) (* 51 (* h1 h1) h2 h3 (* h4 h4) 
(* h5 h5 h5) h6) (* 584 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 5316 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 21358 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 49645 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 73544 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5
) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 72110 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 47057 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* h6
 h6) (* j2 j2 j2 j2)) (* 20017 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* h6 h6) (* 
j2 j2 j2)) (* 5266 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 
768 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* h6 h6) j2) (* 47 (* h1 h1) h2 h3 (* 
h4 h4) (* h5 h5) (* h6 h6)) (* 256 (* h1 h1) h2 h3 h4 (* h5 h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2368 (* h1 h1) h2 h3 h4 (* h5 h5 h5 h5) h6 (* j2
 j2 j2 j2 j2 j2 j2 j2 j2)) (* 9664 (* h1 h1) h2 h3 h4 (* h5 h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 22804 (* h1 h1) h2 h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2)) (* 34250 (* h1 h1) h2 h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2)) (* 33960 (* h1 h1) h2 h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
22308 (* h1 h1) h2 h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 9480 (* h1 h1) 
h2 h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 2462 (* h1 h1) h2 h3 h4 (* h5 h5 h5
 h5) h6 (* j2 j2)) (* 348 (* h1 h1) h2 h3 h4 (* h5 h5 h5 h5) h6 j2) (* 20 (* h1 
h1) h2 h3 h4 (* h5 h5 h5 h5) h6) (* 912 (* h1 h1) h2 h3 h4 (* h5 h5 h5) (* h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8252 (* h1 h1) h2 h3 h4 (* h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 32944 (* h1 h1) h2 h3 h4 (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 76093 (* h1 h1) h2 h3 h4 (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 112045 (* h1 h1) h2 h3 h4 (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 109242 (* h1 h1) h2 h3 h4 (* h5 h5 h5) (* h6
 h6) (* j2 j2 j2 j2 j2)) (* 70910 (* h1 h1) h2 h3 h4 (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2)) (* 30001 (* h1 h1) h2 h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) 
(* 7841 (* h1 h1) h2 h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 1132 (* h1 h1) 
h2 h3 h4 (* h5 h5 h5) (* h6 h6) j2) (* 68 (* h1 h1) h2 h3 h4 (* h5 h5 h5) (* h6 
h6)) (* 536 (* h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
 j2 j2)) (* 4856 (* h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 19426 (* h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 45010 (* h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 66583 (* h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)
) (* 65353 (* h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
42830 (* h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 18372 (* h1 
h1) h2 h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 4899 (* h1 h1) h2 h3 h4 (* 
h5 h5) (* h6 h6 h6) (* j2 j2)) (* 729 (* h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6 h6) 
j2) (* 46 (* h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6 h6)) (* 192 (* h1 h1) h2 h3 (* 
h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1744 (* h1 h1) h2 
h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 6968 (* h1 h1) 
h2 h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 16062 (* h1 h1) 
h2 h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 23533 (* h1 h1) h2 
h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 22746 (* h1 h1) h2 h3 (* 
h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 14564 (* h1 h1) h2 h3 (* h5 h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2)) (* 6036 (* h1 h1) h2 h3 (* h5 h5 h5 h5) (* h6 h6)
 (* j2 j2 j2)) (* 1531 (* h1 h1) h2 h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 
212 (* h1 h1) h2 h3 (* h5 h5 h5 h5) (* h6 h6) j2) (* 12 (* h1 h1) h2 h3 (* h5 h5
 h5 h5) (* h6 h6)) (* 392 (* h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 3520 (* h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 13944 (* h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 31973 (* h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 46788 (* h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 45417 (* h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2)) (* 29430 (* h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 
12479 (* h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 3288 (* h1 h1) 
h2 h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 483 (* h1 h1) h2 h3 (* h5 h5 h5) 
(* h6 h6 h6) j2) (* 30 (* h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6 h6)) (* 176 (* h1 
h1) h2 h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1592 
(* h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
6360 (* h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
14726 (* h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
21794 (* h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 21436 
(* h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 14108 (* h1 h1)
 h2 h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 6094 (* h1 h1) h2 h3 (* h5 
h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 1642 (* h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6 
h6) (* j2 j2)) (* 248 (* h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6 h6) j2) (* 16 (* h1 
h1) h2 h3 (* h5 h5) (* h6 h6 h6 h6)) (* 8 (* h1 h1) h2 (* h4 h4 h4) (* h5 h5 h5)
 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 72 (* h1 h1) h2 (* h4 h4 h4) (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 286 (* h1 h1) h2 (* h4 h4 h4) (* h5 h5
 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 660 (* h1 h1) h2 (* h4 h4 h4) (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 979 (* h1 h1) h2 (* h4 h4 h4) (* h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2)) (* 974 (* h1 h1) h2 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2
 j2 j2 j2 j2)) (* 657 (* h1 h1) h2 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2))
 (* 296 (* h1 h1) h2 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 85 (* h1 h1) 
h2 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 14 (* h1 h1) h2 (* h4 h4 h4) (* h5
 h5 h5) h6 j2) (* (* h1 h1) h2 (* h4 h4 h4) (* h5 h5 h5) h6) (* 8 (* h1 h1) h2 
(* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 72 (* h1 h1) 
h2 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 286 (* h1 h1)
 h2 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 660 (* h1 h1) 
h2 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 979 (* h1 h1) h2 
(* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 974 (* h1 h1) h2 (* h4 h4
) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 657 (* h1 h1) h2 (* h4 h4) (* h5 h5 
h5 h5) h6 (* j2 j2 j2 j2)) (* 296 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5 h5) h6 (* 
j2 j2 j2)) (* 85 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 14 (* 
h1 h1) h2 (* h4 h4) (* h5 h5 h5 h5) h6 j2) (* (* h1 h1) h2 (* h4 h4) (* h5 h5 h5
 h5) h6) (* 32 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 284 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 1116 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 2555 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 3770 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 3741 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2)) (* 2524 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2)) (* 1141 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 
330 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 55 (* h1 h1) h2 
(* h4 h4) (* h5 h5 h5) (* h6 h6) j2) (* 4 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5) 
(* h6 h6)) (* 24 (* h1 h1) h2 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 212 (* h1 h1) h2 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2 j2)) (* 830 (* h1 h1) h2 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 1895 (* h1 h1) h2 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 2791 (* h1 h1) h2 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 2767 (* h1 h1) h2 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
1867 (* h1 h1) h2 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 845 (* h1 h1)
 h2 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 245 (* h1 h1) h2 h4 (* h5 h5 
h5 h5) (* h6 h6) (* j2 j2)) (* 41 (* h1 h1) h2 h4 (* h5 h5 h5 h5) (* h6 h6) j2) 
(* 3 (* h1 h1) h2 h4 (* h5 h5 h5 h5) (* h6 h6)) (* 40 (* h1 h1) h2 h4 (* h5 h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 352 (* h1 h1) h2 h4 (* h5
 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1374 (* h1 h1) h2 h4 (* 
h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3130 (* h1 h1) h2 h4 (* 
h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4603 (* h1 h1) h2 h4 (* h5 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4560 (* h1 h1) h2 h4 (* h5 h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 3077 (* h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2)) (* 1394 (* h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 
j2)) (* 405 (* h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 68 (* h1 h1)
 h2 h4 (* h5 h5 h5) (* h6 h6 h6) j2) (* 5 (* h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6 
h6)) (* 16 (* h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 140 (* h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2
 j2 j2)) (* 544 (* h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 1235 (* h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 1812 (* h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 1793 (* h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1210 
(* h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 549 (* h1 h1) h2 
(* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 160 (* h1 h1) h2 (* h5 h5 h5 h5) 
(* h6 h6 h6) (* j2 j2)) (* 27 (* h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6 h6) j2) (* 2
 (* h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6 h6)) (* 16 (* h1 h1) h2 (* h5 h5 h5) (* 
h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 140 (* h1 h1) h2 (* h5 h5 h5)
 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 544 (* h1 h1) h2 (* h5 h5 h5
) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1235 (* h1 h1) h2 (* h5 h5 h5)
 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1812 (* h1 h1) h2 (* h5 h5 h5) (* 
h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1793 (* h1 h1) h2 (* h5 h5 h5) (* h6 h6 
h6 h6) (* j2 j2 j2 j2 j2)) (* 1210 (* h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6 h6) (* 
j2 j2 j2 j2)) (* 549 (* h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 
160 (* h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 27 (* h1 h1) h2 (* 
h5 h5 h5) (* h6 h6 h6 h6) j2) (* 2 (* h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6 h6)) 
(* 96 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2
)) (* 848 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 3320 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 7568 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2))
 (* 11088 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 
10864 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 7168 (* 
h1 h1) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 3120 (* h1 h1) (* h3 
h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 848 (* h1 h1) (* h3 h3 h3 h3) (* h4 
h4 h4) h5 (* j2 j2)) (* 128 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4 h4) h5 j2) (* 8 
(* h1 h1) (* h3 h3 h3 h3) (* h4 h4 h4) h5) (* 320 (* h1 h1) (* h3 h3 h3 h3) (* 
h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2848 (* h1 h1) (* h3 h3 
h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 11104 (* h1 h1) 
(* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 24904 (* h1 
h1) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 35444 (* h1
 h1) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 33276 (* h1 
h1) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 20728 (* h1 h1) 
(* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 8384 (* h1 h1) (* h3 h3 
h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 2084 (* h1 h1) (* h3 h3 h3 h3) (* h4
 h4) (* h5 h5) (* j2 j2)) (* 284 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) 
j2) (* 16 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5)) (* 416 (* h1 h1) (* h3 
h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3696 (* h1 h1) 
(* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 14568 (* h1 
h1) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 33472 (* h1 
h1) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 49504 (* h1 h1)
 (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 49056 (* h1 h1) (* h3
 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 32816 (* h1 h1) (* h3 h3 h3 h3
) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 14528 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) 
h5 h6 (* j2 j2 j2)) (* 4032 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2))
 (* 624 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 h6 j2) (* 40 (* h1 h1) (* h3 h3 
h3 h3) (* h4 h4) h5 h6) (* 128 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1152 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4512 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5 h5
) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 10080 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5 h5
) (* j2 j2 j2 j2 j2 j2 j2)) (* 14136 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2)) (* 12896 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 
j2 j2 j2 j2)) (* 7668 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2))
 (* 2896 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2)) (* 656 (* h1 h1
) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2)) (* 80 (* h1 h1) (* h3 h3 h3 h3) h4 
(* h5 h5 h5) j2) (* 4 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5 h5)) (* 928 (* h1 h1
) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8272 (* 
h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 32296 
(* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 72528 
(* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 103364 
(* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 97196 (* h1 
h1) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 60672 (* h1 h1) (* h3
 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 24616 (* h1 h1) (* h3 h3 h3 h3) 
h4 (* h5 h5) h6 (* j2 j2 j2)) (* 6148 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) h6 
(* j2 j2)) (* 844 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) h6 j2) (* 48 (* h1 h1) 
(* h3 h3 h3 h3) h4 (* h5 h5) h6) (* 576 (* h1 h1) (* h3 h3 h3 h3) h4 h5 (* h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 5152 (* h1 h1) (* h3 h3 h3 h3) h4 h5 (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 20464 (* h1 h1) (* h3 h3 h3 h3) h4 h5 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 47440 (* h1 h1) (* h3 h3 h3 h3) h4 h5 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 70896 (* h1 h1) (* h3 h3 h3 h3) h4 h5 (* 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 71120 (* h1 h1) (* h3 h3 h3 h3) h4 h5 (* h6 h6)
 (* j2 j2 j2 j2 j2)) (* 48272 (* h1 h1) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2
 j2 j2)) (* 21744 (* h1 h1) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 
6160 (* h1 h1) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 976 (* h1 h1) (* h3
 h3 h3 h3) h4 h5 (* h6 h6) j2) (* 64 (* h1 h1) (* h3 h3 h3 h3) h4 h5 (* h6 h6)) 
(* 256 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 2304 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 9024 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 20160 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2)) (* 28272 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 25792 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 15336 
(* h1 h1) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 5792 (* h1 h1) (* 
h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 1312 (* h1 h1) (* h3 h3 h3 h3) (* 
h5 h5 h5) h6 (* j2 j2)) (* 160 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5 h5) h6 j2) (* 
8 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5 h5) h6) (* 576 (* h1 h1) (* h3 h3 h3 h3) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 5152 (* h1 h1) (* h3 
h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 20176 (* h1 h1)
 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 45440 (* h1
 h1) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 64952 (* 
h1 h1) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 61288 (* h1
 h1) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 38432 (* h1 h1) 
(* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 15696 (* h1 h1) (* h3 h3
 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 3960 (* h1 h1) (* h3 h3 h3 h3) (* 
h5 h5) (* h6 h6) (* j2 j2)) (* 552 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6)
 j2) (* 32 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6)) (* 256 (* h1 h1) (* h3
 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2304 (* h1 h1) 
(* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 9216 (* h1 h1
) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 21536 (* h1 h1
) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 32480 (* h1 h1) 
(* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 32928 (* h1 h1) (* h3 
h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 22624 (* h1 h1) (* h3 h3 h3 h3)
 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 10336 (* h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6
 h6) (* j2 j2 j2)) (* 2976 (* h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2)) 
(* 480 (* h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6 h6) j2) (* 32 (* h1 h1) (* h3 h3 h3
 h3) h5 (* h6 h6 h6)) (* 48 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 424 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2
 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1660 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 3784 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* 
j2 j2 j2 j2 j2 j2 j2)) (* 5544 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 
j2 j2 j2 j2 j2)) (* 5432 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 
j2 j2)) (* 3584 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 
1560 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2)) (* 424 (* h1 h1) 
(* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2)) (* 64 (* h1 h1) (* h3 h3 h3) (* h4 h4
 h4 h4) h5 j2) (* 4 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4 h4) h5) (* 288 (* h1 h1) 
(* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2576 
(* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 10136 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 23048 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2
 j2)) (* 33432 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 
j2)) (* 32188 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) 
(* 20716 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 8736 
(* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 2288 (* h1 h1) 
(* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 332 (* h1 h1) (* h3 h3 h3) (* 
h4 h4 h4) (* h5 h5) j2) (* 20 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5)) (* 
256 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (* 2272 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2
)) (* 8944 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 20520 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 30296 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 
29960 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 19992 (* 
h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 8824 (* h1 h1) (* h3 
h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 2440 (* h1 h1) (* h3 h3 h3) (* h4 h4 
h4) h5 h6 (* j2 j2)) (* 376 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 h6 j2) (* 24 
(* h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 h6) (* 304 (* h1 h1) (* h3 h3 h3) (* h4 
h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2744 (* h1 h1) (* h3 h3 
h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 10820 (* h1 h1) 
(* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 24468 (* h1 
h1) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 35008 (* h1
 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 32958 (* h1 
h1) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 20553 (* h1 h1) 
(* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 8319 (* h1 h1) (* h3 h3 
h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 2071 (* h1 h1) (* h3 h3 h3) (* h4 h4
) (* h5 h5 h5) (* j2 j2)) (* 283 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) 
j2) (* 16 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5)) (* 1152 (* h1 h1) (* h3
 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 10320 (* h1
 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
40696 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2))
 (* 92820 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)
) (* 135208 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2))
 (* 130940 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
84960 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 36236 
(* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 9640 (* h1 h1) 
(* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 1428 (* h1 h1) (* h3 h3 h3) 
(* h4 h4) (* h5 h5) h6 j2) (* 88 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6) 
(* 496 (* h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 4424 (* h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 17516 (* h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 40456 (* h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 60200 (* h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2
 j2 j2 j2 j2 j2)) (* 60088 (* h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 
j2 j2 j2 j2)) (* 40544 (* h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2
 j2)) (* 18136 (* h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 
5096 (* h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 800 (* h1 h1) 
(* h3 h3 h3) (* h4 h4) h5 (* h6 h6) j2) (* 52 (* h1 h1) (* h3 h3 h3) (* h4 h4) 
h5 (* h6 h6)) (* 64 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 576 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 2256 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 5040 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 
j2 j2 j2 j2)) (* 7068 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 
j2 j2)) (* 6448 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) 
(* 3834 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 1448 (* h1
 h1) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2)) (* 328 (* h1 h1) (* h3 h3 h3)
 h4 (* h5 h5 h5 h5) (* j2 j2)) (* 40 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5 h5) 
j2) (* 2 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5 h5)) (* 896 (* h1 h1) (* h3 h3 h3
) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8096 (* h1 h1) (* h3 
h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 31944 (* h1 h1) (* 
h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 72260 (* h1 h1) (* 
h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 103398 (* h1 h1) (* h3
 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 97348 (* h1 h1) (* h3 h3 h3
) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 60723 (* h1 h1) (* h3 h3 h3) h4 (* 
h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 24601 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) h6
 (* j2 j2 j2)) (* 6139 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2)) (* 
843 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) h6 j2) (* 48 (* h1 h1) (* h3 h3 h3) 
h4 (* h5 h5 h5) h6) (* 1440 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 12928 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 51136 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 117124 (* h1 h1) (* h3 h3 h3) h4 (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 171600 (* h1 h1) (* h3 h3 h3) h4 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 167504 (* h1 h1) (* h3 h3 h3) h4 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 109868 (* h1 h1) (* h3 h3 h3) h4 (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 47556 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5) 
(* h6 h6) (* j2 j2 j2)) (* 12904 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) 
(* j2 j2)) (* 1960 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) j2) (* 124 (* 
h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6)) (* 416 (* h1 h1) (* h3 h3 h3) h4 h5 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3728 (* h1 h1) (* h3 h3 h3) 
h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 14840 (* h1 h1) (* h3 h3 
h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 34488 (* h1 h1) (* h3 h3 
h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 51688 (* h1 h1) (* h3 h3 h3)
 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 52024 (* h1 h1) (* h3 h3 h3) h4 h5
 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 35448 (* h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6
 h6) (* j2 j2 j2 j2)) (* 16040 (* h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 
j2 j2)) (* 4568 (* h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2)) (* 728 (* 
h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6 h6) j2) (* 48 (* h1 h1) (* h3 h3 h3) h4 h5 
(* h6 h6 h6)) (* 128 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 1152 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 4512 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 10080 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2)) (* 14136 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2)) (* 12896 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)
) (* 7668 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 2896 (* 
h1 h1) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 656 (* h1 h1) (* h3 h3 
h3) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 80 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5 h5) 
h6 j2) (* 4 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5 h5) h6) (* 576 (* h1 h1) (* h3 h3
 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 5216 (* h1 h1)
 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 20608 
(* h1 h1) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
46648 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 66764 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 62864 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
39234 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 15926 
(* h1 h1) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 3994 (* h1 h1) 
(* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 554 (* h1 h1) (* h3 h3 h3) (* 
h5 h5 h5) (* h6 h6) j2) (* 32 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6)) (* 
576 (* h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 5184 (* h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 20576 (* h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2
 j2 j2 j2 j2)) (* 47352 (* h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 69824 (* h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2
 j2 j2 j2 j2)) (* 68752 (* h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2)) (* 45624 (* h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2
)) (* 20056 (* h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 5552 
(* h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 864 (* h1 h1) (* h3 
h3 h3) (* h5 h5) (* h6 h6 h6) j2) (* 56 (* h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 
h6 h6)) (* 128 (* h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2
 j2 j2 j2)) (* 1152 (* h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 4608 (* h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 10768 (* h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 16240 (* h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 16464 (* h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
11312 (* h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 5168 (* h1 
h1) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 1488 (* h1 h1) (* h3 h3 h3)
 h5 (* h6 h6 h6 h6) (* j2 j2)) (* 240 (* h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6 h6) 
j2) (* 16 (* h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6 h6)) (* 48 (* h1 h1) (* h3 h3) 
(* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 432 (* h1 h1) 
(* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1712 (* 
h1 h1) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3926 
(* h1 h1) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 5754 
(* h1 h1) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 5612 (* 
h1 h1) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 3672 (* h1 h1)
 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 1582 (* h1 h1) (* h3 h3
) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 426 (* h1 h1) (* h3 h3) (* h4 h4 h4
 h4) (* h5 h5) (* j2 j2)) (* 64 (* h1 h1) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) j2
) (* 4 (* h1 h1) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5)) (* 136 (* h1 h1) (* h3 h3)
 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1228 (* h1 h1) 
(* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4874 (* 
h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 11172
 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
16326 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 
15826 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 10248
 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 4344 (* h1 h1
) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 1142 (* h1 h1) (* h3 h3) 
(* h4 h4 h4) (* h5 h5 h5) (* j2 j2)) (* 166 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* 
h5 h5 h5) j2) (* 10 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5)) (* 256 (* h1 
h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
2312 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2
)) (* 9204 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2
 j2)) (* 21230 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 31346 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2
 j2)) (* 30860 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2))
 (* 20432 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 8934
 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 2450 (* h1 h1) 
(* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 376 (* h1 h1) (* h3 h3) (* h4 
h4 h4) (* h5 h5) h6 j2) (* 24 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6) (* 
64 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 592 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 2396 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 5566 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 
j2 j2 j2 j2)) (* 8179 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 
j2 j2 j2)) (* 7895 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 
j2)) (* 5030 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 
2068 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 519 (* h1 h1
) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 71 (* h1 h1) (* h3 h3) (* h4
 h4) (* h5 h5 h5 h5) j2) (* 4 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5)) (* 
544 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 4920 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 19576 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2
 j2 j2 j2 j2)) (* 45028 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2)) (* 66115 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2
 j2 j2 j2 j2)) (* 64503 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2)) (* 42130 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2
)) (* 18066 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 4823 
(* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 715 (* h1 h1) (* h3 
h3) (* h4 h4) (* h5 h5 h5) h6 j2) (* 44 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 
h5) h6) (* 496 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 4496 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 17984 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 41734 (* h1 h1) (* h3 h3) (* h4 h4) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 62090 (* h1 h1) (* h3 h3) (* h4
 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 61708 (* h1 h1) (* h3 h3) (* 
h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 41336 (* h1 h1) (* h3 h3) (* 
h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 18334 (* h1 h1) (* h3 h3) (* h4 
h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 5114 (* h1 h1) (* h3 h3) (* h4 h4) (* 
h5 h5) (* h6 h6) (* j2 j2)) (* 800 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* h6
 h6) j2) (* 52 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6)) (* 192 (* h1 
h1) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1776 
(* h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
7184 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
16672 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
24466 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 23580 
(* h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 15000 (* h1 h1)
 (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 6160 (* h1 h1) (* h3 h3) h4
 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 1546 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5)
 h6 (* j2 j2)) (* 212 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) h6 j2) (* 12 (* h1 
h1) (* h3 h3) h4 (* h5 h5 h5 h5) h6) (* 680 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 6164 (* h1 h1) (* h3 h3) h4 (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 24610 (* h1 h1) (* h3 h3)
 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 56880 (* h1 h1) (* h3
 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 84063 (* h1 h1) (* 
h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 82727 (* h1 h1) (* h3
 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 54654 (* h1 h1) (* h3 h3) 
h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 23790 (* h1 h1) (* h3 h3) h4 (* h5
 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 6475 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* 
h6 h6) (* j2 j2)) (* 983 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) j2) (* 62
 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6)) (* 416 (* h1 h1) (* h3 h3) h4 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3784 (* h1 h1) (* 
h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 15204 (* h1 
h1) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 35482 
(* h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 53158
 (* h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 53284 
(* h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 36064 (* h1
 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 16194 (* h1 h1) (* 
h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 4582 (* h1 h1) (* h3 h3) h4 
(* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 728 (* h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 
h6 h6) j2) (* 48 (* h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6)) (* 128 (* h1 h1)
 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1184 
(* h1 h1) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 4784 (* h1 h1) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 11080 (* h1 h1) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 16216 (* h1 h1) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2
)) (* 15580 (* h1 h1) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 9880 (* h1 h1) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 4048 
(* h1 h1) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 1016 (* h1 h1) 
(* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 140 (* h1 h1) (* h3 h3) (* h5 
h5 h5 h5) (* h6 h6) j2) (* 8 (* h1 h1) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6)) (* 
272 (* h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 2472 (* h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 9908 (* h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 23024 (* h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2
 j2 j2 j2 j2)) (* 34274 (* h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 34050 (* h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2
 j2 j2)) (* 22772 (* h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2))
 (* 10068 (* h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 2794 
(* h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 434 (* h1 h1) (* h3 
h3) (* h5 h5 h5) (* h6 h6 h6) j2) (* 28 (* h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 
h6 h6)) (* 128 (* h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 1168 (* h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 4712 (* h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 11052 (* h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2)) (* 16660 (* h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6
) (* j2 j2 j2 j2 j2 j2)) (* 16824 (* h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2)) (* 11488 (* h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2
 j2 j2 j2)) (* 5212 (* h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) 
(* 1492 (* h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 240 (* h1 h1
) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) j2) (* 16 (* h1 h1) (* h3 h3) (* h5 h5) 
(* h6 h6 h6 h6)) (* 8 (* h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 76 (* h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 318 (* h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 770 (* h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 
j2 j2 j2 j2)) (* 1191 (* h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 
j2 j2)) (* 1224 (* h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) 
(* 841 (* h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 378 (* h1 
h1) h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 105 (* h1 h1) h3 (* h4 h4 
h4 h4) (* h5 h5 h5) (* j2 j2)) (* 16 (* h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5 h5) 
j2) (* (* h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5 h5)) (* 8 (* h1 h1) h3 (* h4 h4 h4)
 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 76 (* h1 h1) h3 (* h4 h4 
h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 318 (* h1 h1) h3 (* h4 h4
 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 770 (* h1 h1) h3 (* h4 h4 
h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1191 (* h1 h1) h3 (* h4 h4 h4) 
(* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1224 (* h1 h1) h3 (* h4 h4 h4) (* h5 
h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 841 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5 h5) 
(* j2 j2 j2 j2)) (* 378 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) 
(* 105 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 16 (* h1 h1) h3 
(* h4 h4 h4) (* h5 h5 h5 h5) j2) (* (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5 h5)) 
(* 48 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2
)) (* 452 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 1878 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 4523 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2))
 (* 6970 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
7149 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 4912 (* h1
 h1) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 2213 (* h1 h1) h3 (* h4
 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 618 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 
h5) h6 (* j2 j2)) (* 95 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) h6 j2) (* 6 (* h1
 h1) h3 (* h4 h4 h4) (* h5 h5 h5) h6) (* 40 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 376 (* h1 h1) h3 (* h4 h4) (* h5 h5
 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1560 (* h1 h1) h3 (* h4 h4) (* h5 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3753 (* h1 h1) h3 (* h4 h4) (* h5 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 5779 (* h1 h1) h3 (* h4 h4) (* h5 h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 5925 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2)) (* 4071 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 
j2 j2 j2)) (* 1835 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 
513 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 79 (* h1 h1) h3 (* 
h4 h4) (* h5 h5 h5 h5) h6 j2) (* 5 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) h6) 
(* 104 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 972 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 4014 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 9622 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 14779 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2
 j2 j2 j2 j2)) (* 15132 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2)) (* 10397 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2
)) (* 4694 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 1317 
(* h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 204 (* h1 h1) h3 (* 
h4 h4) (* h5 h5 h5) (* h6 h6) j2) (* 13 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* 
h6 h6)) (* 64 (* h1 h1) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 596 (* h1 h1) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2 j2)) (* 2454 (* h1 h1) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 5869 (* h1 h1) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 9000 (* h1 h1) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2))
 (* 9207 (* h1 h1) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 6326 
(* h1 h1) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 2859 (* h1 h1) h3 
h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 804 (* h1 h1) h3 h4 (* h5 h5 h5 h5
) (* h6 h6) (* j2 j2)) (* 125 (* h1 h1) h3 h4 (* h5 h5 h5 h5) (* h6 h6) j2) (* 8
 (* h1 h1) h3 h4 (* h5 h5 h5 h5) (* h6 h6)) (* 96 (* h1 h1) h3 h4 (* h5 h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 892 (* h1 h1) h3 h4 (* h5 h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3666 (* h1 h1) h3 h4 (* h5 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 8755 (* h1 h1) h3 h4 (* h5 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 13412 (* h1 h1) h3 h4 (* h5 h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 13713 (* h1 h1) h3 h4 (* h5 h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 9422 (* h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2)) (* 4261 (* h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 
j2)) (* 1200 (* h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 187 (* h1 
h1) h3 h4 (* h5 h5 h5) (* h6 h6 h6) j2) (* 12 (* h1 h1) h3 h4 (* h5 h5 h5) (* h6
 h6 h6)) (* 32 (* h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2
 j2 j2 j2)) (* 296 (* h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 1212 (* h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 2886 (* h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 4412 (* h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 4506 (* h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
3096 (* h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1402 (* h1 h1
) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 396 (* h1 h1) h3 (* h5 h5 h5 
h5) (* h6 h6 h6) (* j2 j2)) (* 62 (* h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6 h6) j2) 
(* 4 (* h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6 h6)) (* 32 (* h1 h1) h3 (* h5 h5 h5) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 296 (* h1 h1) h3 (* h5 h5 
h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1212 (* h1 h1) h3 (* h5 
h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2886 (* h1 h1) h3 (* h5 
h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4412 (* h1 h1) h3 (* h5 h5 
h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4506 (* h1 h1) h3 (* h5 h5 h5) (* 
h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 3096 (* h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6 
h6) (* j2 j2 j2 j2)) (* 1402 (* h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 
j2)) (* 396 (* h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 62 (* h1 h1)
 h3 (* h5 h5 h5) (* h6 h6 h6 h6) j2) (* 4 (* h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6 
h6)) (* 1984 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 
8976 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 16120 h1 
(* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 14724 h1 (* h2 h2 h2 
h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2)) (* 7310 h1 (* h2 h2 h2 h2) (* h3 h3 h3) 
h4 h5 (* j2 j2 j2)) (* 1966 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2)) (* 
266 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 j2) (* 14 h1 (* h2 h2 h2 h2) (* h3 h3 
h3) h4 h5) (* 1024 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2
)) (* 4352 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2)) (* 7488 
h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 6704 h1 (* h2 h2 h2
 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 3352 h1 (* h2 h2 h2 h2) (* h3 h3 h3)
 h4 h6 (* j2 j2 j2)) (* 936 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2)) (* 
136 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h6 j2) (* 8 h1 (* h2 h2 h2 h2) (* h3 h3 
h3) h4 h6) (* 768 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2
 j2)) (* 3648 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) 
(* 6752 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 6176 h1
 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 2952 h1 (* h2 h2 h2 
h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2)) (* 732 h1 (* h2 h2 h2 h2) (* h3 h3 h3) 
(* h5 h5) (* j2 j2)) (* 88 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) j2) (* 4 h1
 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5)) (* 1728 h1 (* h2 h2 h2 h2) (* h3 h3 h3)
 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 7824 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h5 h6 
(* j2 j2 j2 j2 j2 j2)) (* 13992 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 
j2 j2 j2)) (* 12644 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 
6154 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2)) (* 1602 h1 (* h2 h2 h2 
h2) (* h3 h3 h3) h5 h6 (* j2 j2)) (* 206 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h5 h6 
j2) (* 10 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h5 h6) (* 1024 h1 (* h2 h2 h2 h2) (* 
h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4352 h1 (* h2 h2 h2 h2) (* h3 
h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 7488 h1 (* h2 h2 h2 h2) (* h3 h3 h3) 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 6704 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h6 h6) 
(* j2 j2 j2 j2)) (* 3352 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2))
 (* 936 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2)) (* 136 h1 (* h2 h2 
h2 h2) (* h3 h3 h3) (* h6 h6) j2) (* 8 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h6 h6)
) (* 880 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 4880 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 
11312 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 14252 
h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 10613 h1 (* h2 
h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 4748 h1 (* h2 h2 h2 h2) (* 
h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 1234 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4)
 h5 (* j2 j2)) (* 168 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 j2) (* 9 h1 (* 
h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5) (* 256 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 
h4) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1408 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 
h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 3280 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) 
h6 (* j2 j2 j2 j2 j2 j2)) (* 4208 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h6 (* 
j2 j2 j2 j2 j2)) (* 3236 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 
j2)) (* 1520 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2 j2)) (* 424 h1 
(* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2)) (* 64 h1 (* h2 h2 h2 h2) (* h3
 h3) (* h4 h4) h6 j2) (* 4 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h6) (* 1232 h1
 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6784 h1 
(* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 15552 h1 (* 
h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 19308 h1 (* h2 h2 
h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 14143 h1 (* h2 h2 h2 h2) 
(* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 6233 h1 (* h2 h2 h2 h2) (* h3 h3) h4 
(* h5 h5) (* j2 j2 j2)) (* 1605 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 
j2)) (* 219 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) j2) (* 12 h1 (* h2 h2 h2 
h2) (* h3 h3) h4 (* h5 h5)) (* 2272 h1 (* h2 h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 12192 h1 (* h2 h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 
j2 j2 j2 j2 j2)) (* 27488 h1 (* h2 h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 
j2 j2)) (* 33864 h1 (* h2 h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 
24810 h1 (* h2 h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 11004 h1 (* h2 
h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 2864 h1 (* h2 h2 h2 h2) (* h3 h3) 
h4 h5 h6 (* j2 j2)) (* 396 h1 (* h2 h2 h2 h2) (* h3 h3) h4 h5 h6 j2) (* 22 h1 
(* h2 h2 h2 h2) (* h3 h3) h4 h5 h6) (* 512 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2816 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 6560 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 8416 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 
j2 j2 j2 j2)) (* 6472 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2))
 (* 3040 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2)) (* 848 h1 (* h2
 h2 h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2)) (* 128 h1 (* h2 h2 h2 h2) (* h3 h3)
 h4 (* h6 h6) j2) (* 8 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h6 h6)) (* 192 h1 (* 
h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1152 h1 (* 
h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 2864 h1 (* h2 
h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 3816 h1 (* h2 h2 h2 
h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 2944 h1 (* h2 h2 h2 h2) (* h3 
h3) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 1326 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 
h5) (* j2 j2 j2)) (* 334 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2)) 
(* 42 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) j2) (* 2 h1 (* h2 h2 h2 h2) (* 
h3 h3) (* h5 h5 h5)) (* 1296 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 6960 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2)) (* 15480 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 
j2 j2 j2)) (* 18536 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)
) (* 13005 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 5443 h1
 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 1315 h1 (* h2 h2 h2 h2)
 (* h3 h3) (* h5 h5) h6 (* j2 j2)) (* 165 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5)
 h6 j2) (* 8 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) h6) (* 1392 h1 (* h2 h2 h2 
h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 7312 h1 (* h2 h2 h2 
h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 16176 h1 (* h2 h2 h2 h2)
 (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 19612 h1 (* h2 h2 h2 h2) (* h3
 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 14197 h1 (* h2 h2 h2 h2) (* h3 h3) h5 
(* h6 h6) (* j2 j2 j2 j2)) (* 6256 h1 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* 
j2 j2 j2)) (* 1630 h1 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2)) (* 228 
h1 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6) j2) (* 13 h1 (* h2 h2 h2 h2) (* h3 h3)
 h5 (* h6 h6)) (* 256 h1 (* h2 h2 h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 1408 h1 (* h2 h2 h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 3280 h1 (* h2 h2 h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 4208 h1 (* h2 h2 h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
3236 h1 (* h2 h2 h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1520 h1 (* h2
 h2 h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2)) (* 424 h1 (* h2 h2 h2 h2) (* h3 
h3) (* h6 h6 h6) (* j2 j2)) (* 64 h1 (* h2 h2 h2 h2) (* h3 h3) (* h6 h6 h6) j2) 
(* 4 h1 (* h2 h2 h2 h2) (* h3 h3) (* h6 h6 h6)) (* 256 h1 (* h2 h2 h2 h2) h3 (* 
h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1696 h1 (* h2 h2 h2 h2) h3 
(* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4848 h1 (* h2 h2 h2 h2) h3 
(* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 7832 h1 (* h2 h2 h2 h2) h3 (* 
h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 7860 h1 (* h2 h2 h2 h2) h3 (* h4 h4) 
(* h5 h5) (* j2 j2 j2 j2 j2)) (* 5064 h1 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) 
(* j2 j2 j2 j2)) (* 2084 h1 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2))
 (* 524 h1 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2)) (* 72 h1 (* h2 h2 
h2 h2) h3 (* h4 h4) (* h5 h5) j2) (* 4 h1 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5)
) (* 176 h1 (* h2 h2 h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 1120 h1 (* h2 h2 h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
3104 h1 (* h2 h2 h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 4908 h1 
(* h2 h2 h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 4869 h1 (* h2 h2 h2
 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 3135 h1 (* h2 h2 h2 h2) h3 (* h4 
h4) h5 h6 (* j2 j2 j2 j2)) (* 1306 h1 (* h2 h2 h2 h2) h3 (* h4 h4) h5 h6 (* j2 
j2 j2)) (* 338 h1 (* h2 h2 h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2)) (* 49 h1 (* h2 
h2 h2 h2) h3 (* h4 h4) h5 h6 j2) (* 3 h1 (* h2 h2 h2 h2) h3 (* h4 h4) h5 h6) (* 
160 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
1072 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3104 
h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 5088 h1 (* h2
 h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 5190 h1 (* h2 h2 h2 h2) 
h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 3405 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5
 h5) (* j2 j2 j2 j2)) (* 1430 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2)
) (* 368 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2)) (* 52 h1 (* h2 h2 h2 
h2) h3 h4 (* h5 h5 h5) j2) (* 3 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5)) (* 656 h1
 (* h2 h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4240 h1 
(* h2 h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 11872 h1 (* 
h2 h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 18860 h1 (* h2 h2 
h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 18687 h1 (* h2 h2 h2 h2) h3 
h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 11940 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5) 
h6 (* j2 j2 j2 j2)) (* 4900 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2)) 
(* 1238 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2)) (* 173 h1 (* h2 h2 h2 
h2) h3 h4 (* h5 h5) h6 j2) (* 10 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5) h6) (* 352 
h1 (* h2 h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2240 h1
 (* h2 h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6208 h1 (* 
h2 h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 9816 h1 (* h2 h2 h2
 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 9738 h1 (* h2 h2 h2 h2) h3 h4 
h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 6270 h1 (* h2 h2 h2 h2) h3 h4 h5 (* h6 h6) 
(* j2 j2 j2 j2)) (* 2612 h1 (* h2 h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2)) (* 
676 h1 (* h2 h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2)) (* 98 h1 (* h2 h2 h2 h2) h3
 h4 h5 (* h6 h6) j2) (* 6 h1 (* h2 h2 h2 h2) h3 h4 h5 (* h6 h6)) (* 192 h1 (* h2
 h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1248 h1 (* h2 
h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3488 h1 (* h2 h2 h2
 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 5488 h1 (* h2 h2 h2 h2) h3 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 5340 h1 (* h2 h2 h2 h2) h3 (* h5 h5 h5
) h6 (* j2 j2 j2 j2 j2)) (* 3318 h1 (* h2 h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 
j2 j2)) (* 1308 h1 (* h2 h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 312 h1 
(* h2 h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2)) (* 40 h1 (* h2 h2 h2 h2) h3 (* h5 
h5 h5) h6 j2) (* 2 h1 (* h2 h2 h2 h2) h3 (* h5 h5 h5) h6) (* 400 h1 (* h2 h2 h2 
h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2544 h1 (* h2 h2 
h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 7024 h1 (* h2 h2 
h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 11028 h1 (* h2 h2 h2 
h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 10827 h1 (* h2 h2 h2 h2) h3
 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 6876 h1 (* h2 h2 h2 h2) h3 (* h5 h5)
 (* h6 h6) (* j2 j2 j2 j2)) (* 2816 h1 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6) 
(* j2 j2 j2)) (* 714 h1 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2)) (* 101
 h1 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6) j2) (* 6 h1 (* h2 h2 h2 h2) h3 (* h5 
h5) (* h6 h6)) (* 176 h1 (* h2 h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2 j2)) (* 1120 h1 (* h2 h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 3104 h1 (* h2 h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 4908 h1 (* h2 h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4869 h1 
(* h2 h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 3135 h1 (* h2 h2 h2 h2
) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1306 h1 (* h2 h2 h2 h2) h3 h5 (* h6 h6 
h6) (* j2 j2 j2)) (* 338 h1 (* h2 h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2)) (* 49 
h1 (* h2 h2 h2 h2) h3 h5 (* h6 h6 h6) j2) (* 3 h1 (* h2 h2 h2 h2) h3 h5 (* h6 h6
 h6)) (* 32 h1 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2
 j2 j2)) (* 240 h1 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 800 h1 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 1560 h1 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2)) (* 1970 h1 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 1683 h1 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 985 h1 
(* h2 h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 390 h1 (* h2 h2 h2 h2
) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 100 h1 (* h2 h2 h2 h2) (* h4 h4) (* h5
 h5) h6 (* j2 j2)) (* 15 h1 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5) h6 j2) (* h1 (* 
h2 h2 h2 h2) (* h4 h4) (* h5 h5) h6) (* 32 h1 (* h2 h2 h2 h2) h4 (* h5 h5 h5) h6
 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 240 h1 (* h2 h2 h2 h2) h4 (* h5 h5 h5) h6
 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 800 h1 (* h2 h2 h2 h2) h4 (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1560 h1 (* h2 h2 h2 h2) h4 (* h5 h5 h5) h6 (* j2
 j2 j2 j2 j2 j2 j2)) (* 1970 h1 (* h2 h2 h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2)) (* 1683 h1 (* h2 h2 h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
985 h1 (* h2 h2 h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 390 h1 (* h2 h2 h2
 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 100 h1 (* h2 h2 h2 h2) h4 (* h5 h5 h5) 
h6 (* j2 j2)) (* 15 h1 (* h2 h2 h2 h2) h4 (* h5 h5 h5) h6 j2) (* h1 (* h2 h2 h2 
h2) h4 (* h5 h5 h5) h6) (* 64 h1 (* h2 h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2
 j2 j2 j2 j2 j2 j2 j2 j2)) (* 480 h1 (* h2 h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1600 h1 (* h2 h2 h2 h2) h4 (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3120 h1 (* h2 h2 h2 h2) h4 (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 3940 h1 (* h2 h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 3366 h1 (* h2 h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2)) (* 1970 h1 (* h2 h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) 
(* 780 h1 (* h2 h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 200 h1 (* h2 
h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 30 h1 (* h2 h2 h2 h2) h4 (* h5 h5
) (* h6 h6) j2) (* 2 h1 (* h2 h2 h2 h2) h4 (* h5 h5) (* h6 h6)) (* 32 h1 (* h2 
h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 240 h1 
(* h2 h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 800 h1
 (* h2 h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1560 h1 
(* h2 h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1970 h1 (* 
h2 h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1683 h1 (* h2 h2 
h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 985 h1 (* h2 h2 h2 h2) (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 390 h1 (* h2 h2 h2 h2) (* h5 h5 h5) (* 
h6 h6) (* j2 j2 j2)) (* 100 h1 (* h2 h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2))
 (* 15 h1 (* h2 h2 h2 h2) (* h5 h5 h5) (* h6 h6) j2) (* h1 (* h2 h2 h2 h2) (* h5
 h5 h5) (* h6 h6)) (* 32 h1 (* h2 h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 240 h1 (* h2 h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2
 j2 j2 j2 j2 j2 j2 j2)) (* 800 h1 (* h2 h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 1560 h1 (* h2 h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 1970 h1 (* h2 h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 1683 h1 (* h2 h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2)) (* 985 h1 (* h2 h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 390 h1
 (* h2 h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 100 h1 (* h2 h2 h2 h2) 
(* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 15 h1 (* h2 h2 h2 h2) (* h5 h5) (* h6 h6 h6
) j2) (* h1 (* h2 h2 h2 h2) (* h5 h5) (* h6 h6 h6)) (* 1984 h1 (* h2 h2 h2) (* 
h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 9968 h1 (* h2 h2 h2) (* h3 h3 h3
 h3) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 20112 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5
 (* j2 j2 j2 j2 j2)) (* 20788 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 
j2)) (* 11640 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2)) (* 3456 h1 (* 
h2 h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2)) (* 504 h1 (* h2 h2 h2) (* h3 h3 h3 h3
) h4 h5 j2) (* 28 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5) (* 1024 h1 (* h2 h2 h2)
 (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 4864 h1 (* h2 h2 h2) (* h3 
h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2)) (* 9408 h1 (* h2 h2 h2) (* h3 h3 h3 h3) 
h4 h6 (* j2 j2 j2 j2 j2)) (* 9488 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2
 j2 j2)) (* 5312 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2)) (* 1632 h1 
(* h2 h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2)) (* 256 h1 (* h2 h2 h2) (* h3 h3 h3
 h3) h4 h6 j2) (* 16 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h6) (* 768 h1 (* h2 h2 
h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 4032 h1 (* h2 h2 h2) 
(* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 8384 h1 (* h2 h2 h2) (* h3 
h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 8736 h1 (* h2 h2 h2) (* h3 h3 h3 h3) 
(* h5 h5) (* j2 j2 j2 j2)) (* 4760 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* 
j2 j2 j2)) (* 1304 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2)) (* 168 
h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) j2) (* 8 h1 (* h2 h2 h2) (* h3 h3 h3 
h3) (* h5 h5)) (* 1728 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 8688 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 
17472 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 17900 h1 (* 
h2 h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 9848 h1 (* h2 h2 h2) (* h3 
h3 h3 h3) h5 h6 (* j2 j2 j2)) (* 2832 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h5 h6 (* 
j2 j2)) (* 392 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h5 h6 j2) (* 20 h1 (* h2 h2 h2) 
(* h3 h3 h3 h3) h5 h6) (* 1024 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 4864 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 9408 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 9488 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 5312 
h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2)) (* 1632 h1 (* h2 h2 h2) 
(* h3 h3 h3 h3) (* h6 h6) (* j2 j2)) (* 256 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* 
h6 h6) j2) (* 16 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h6 h6)) (* 3424 h1 (* h2 h2 
h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 21328 h1 (* h2 h2 
h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 54400 h1 (* h2 h2 h2)
 (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 73620 h1 (* h2 h2 h2) (* h3
 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 57382 h1 (* h2 h2 h2) (* h3 h3 h3) 
(* h4 h4) h5 (* j2 j2 j2 j2)) (* 26244 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5
 (* j2 j2 j2)) (* 6872 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2)) (* 
936 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 j2) (* 50 h1 (* h2 h2 h2) (* h3 h3
 h3) (* h4 h4) h5) (* 512 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 3072 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 
j2 j2 j2 j2)) (* 7840 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 
j2 j2)) (* 11056 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2)) 
(* 9360 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2)) (* 4832 h1 
(* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2)) (* 1472 h1 (* h2 h2 h2) (* 
h3 h3 h3) (* h4 h4) h6 (* j2 j2)) (* 240 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) 
h6 j2) (* 16 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h6) (* 3664 h1 (* h2 h2 h2) 
(* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 23064 h1 (* h2 h2 h2) 
(* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 59060 h1 (* h2 h2 h2) (* 
h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 79366 h1 (* h2 h2 h2) (* h3 h3 
h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 60506 h1 (* h2 h2 h2) (* h3 h3 h3) h4 
(* h5 h5) (* j2 j2 j2 j2)) (* 26697 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) 
(* j2 j2 j2)) (* 6753 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2)) (* 
905 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) j2) (* 49 h1 (* h2 h2 h2) (* h3 h3
 h3) h4 (* h5 h5)) (* 7872 h1 (* h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 48160 h1 (* h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 120832 h1 (* h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) 
(* 161072 h1 (* h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 123840 h1
 (* h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 55996 h1 (* h2 h2 h2) 
(* h3 h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 14564 h1 (* h2 h2 h2) (* h3 h3 h3) h4 h5 
h6 (* j2 j2)) (* 1988 h1 (* h2 h2 h2) (* h3 h3 h3) h4 h5 h6 j2) (* 108 h1 (* h2 
h2 h2) (* h3 h3 h3) h4 h5 h6) (* 1024 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6144 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 15680 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 22112 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 
j2 j2 j2)) (* 18720 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) 
(* 9664 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2)) (* 2944 h1 (* h2
 h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2)) (* 480 h1 (* h2 h2 h2) (* h3 h3 h3)
 h4 (* h6 h6) j2) (* 32 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6)) (* 384 h1 (* 
h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2592 h1 (* 
h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 7120 h1 (* h2 
h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 10320 h1 (* h2 h2 h2)
 (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 8580 h1 (* h2 h2 h2) (* h3 h3 
h3) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 4178 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 
h5) (* j2 j2 j2)) (* 1156 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2)) 
(* 158 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) j2) (* 8 h1 (* h2 h2 h2) (* h3 
h3 h3) (* h5 h5 h5)) (* 3792 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 23448 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2)) (* 58988 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 
j2 j2 j2)) (* 77702 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)
) (* 57732 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 24553 
h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 5885 h1 (* h2 h2 h2) 
(* h3 h3 h3) (* h5 h5) h6 (* j2 j2)) (* 729 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 
h5) h6 j2) (* 35 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6) (* 4448 h1 (* h2 h2 
h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 26832 h1 (* h2 h2 
h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 66432 h1 (* h2 h2 h2)
 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 87452 h1 (* h2 h2 h2) (* h3
 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 66458 h1 (* h2 h2 h2) (* h3 h3 h3) 
h5 (* h6 h6) (* j2 j2 j2 j2)) (* 29752 h1 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6)
 (* j2 j2 j2)) (* 7692 h1 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2)) (* 
1052 h1 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) j2) (* 58 h1 (* h2 h2 h2) (* h3 
h3 h3) h5 (* h6 h6)) (* 512 h1 (* h2 h2 h2) (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 3072 h1 (* h2 h2 h2) (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 7840 h1 (* h2 h2 h2) (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 11056 h1 (* h2 h2 h2) (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)
) (* 9360 h1 (* h2 h2 h2) (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 4832 h1 
(* h2 h2 h2) (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2)) (* 1472 h1 (* h2 h2 h2) (* 
h3 h3 h3) (* h6 h6 h6) (* j2 j2)) (* 240 h1 (* h2 h2 h2) (* h3 h3 h3) (* h6 h6 
h6) j2) (* 16 h1 (* h2 h2 h2) (* h3 h3 h3) (* h6 h6 h6)) (* 272 h1 (* h2 h2 h2) 
(* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3056 h1 (* h2 h2 h2
) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 12384 h1 (* h2 h2 h2
) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 25744 h1 (* h2 h2 h2) 
(* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 31091 h1 (* h2 h2 h2) (* h3 
h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 22823 h1 (* h2 h2 h2) (* h3 h3) (* h4
 h4 h4) h5 (* j2 j2 j2 j2)) (* 10182 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 
(* j2 j2 j2)) (* 2646 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2)) (* 
359 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 j2) (* 19 h1 (* h2 h2 h2) (* h3 h3
) (* h4 h4 h4) h5) (* 128 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 768 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2
 j2 j2 j2)) (* 1960 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 
j2)) (* 2764 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 
2340 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2)) (* 1208 h1 (* h2
 h2 h2) (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2)) (* 368 h1 (* h2 h2 h2) (* h3 h3)
 (* h4 h4 h4) h6 (* j2 j2)) (* 60 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h6 j2) 
(* 4 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h6) (* 1312 h1 (* h2 h2 h2) (* h3 h3
) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 10792 h1 (* h2 h2 h2) 
(* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 37012 h1 (* h2 h2 
h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 69462 h1 (* h2 h2
 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 78421 h1 (* h2 h2 
h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 55016 h1 (* h2 h2 h2) 
(* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 23883 h1 (* h2 h2 h2) (* h3 h3
) (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 6163 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) 
(* h5 h5) (* j2 j2)) (* 852 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) j2) 
(* 47 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5)) (* 1344 h1 (* h2 h2 h2) (* 
h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 12632 h1 (* h2 h2 h2) 
(* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 46884 h1 (* h2 h2 h2) 
(* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 92582 h1 (* h2 h2 h2) (* 
h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 108275 h1 (* h2 h2 h2) (* h3 h3
) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 77957 h1 (* h2 h2 h2) (* h3 h3) (* h4 
h4) h5 h6 (* j2 j2 j2 j2)) (* 34490 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 
(* j2 j2 j2)) (* 9000 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 
1247 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 j2) (* 69 h1 (* h2 h2 h2) (* h3 
h3) (* h4 h4) h5 h6) (* 384 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 2304 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 5880 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 8292 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 
j2 j2 j2 j2)) (* 7020 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 
j2)) (* 3624 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 1104
 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2)) (* 180 h1 (* h2 h2 h2)
 (* h3 h3) (* h4 h4) (* h6 h6) j2) (* 12 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* 
h6 h6)) (* 672 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2
 j2 j2)) (* 5584 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 19328 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 
j2)) (* 36524 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) 
(* 41338 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 28882 
h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 12392 h1 (* h2 h2 
h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2)) (* 3146 h1 (* h2 h2 h2) (* h3 h3) h4
 (* h5 h5 h5) (* j2 j2)) (* 430 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) j2) 
(* 24 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5)) (* 3056 h1 (* h2 h2 h2) (* h3 
h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 24368 h1 (* h2 h2 h2) (* 
h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 81472 h1 (* h2 h2 h2) (* 
h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 149688 h1 (* h2 h2 h2) (* h3
 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 165965 h1 (* h2 h2 h2) (* h3 h3) 
h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 114621 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5
 h5) h6 (* j2 j2 j2 j2)) (* 49084 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* 
j2 j2 j2)) (* 12524 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 1719
 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 j2) (* 95 h1 (* h2 h2 h2) (* h3 h3) 
h4 (* h5 h5) h6) (* 1872 h1 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 16096 h1 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 56616 h1 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 107932 h1 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2
 j2 j2 j2)) (* 123277 h1 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 87445 h1 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 
38434 h1 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 10062 h1 (* h2 
h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 1417 h1 (* h2 h2 h2) (* h3 h3) h4
 h5 (* h6 h6) j2) (* 81 h1 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6)) (* 384 h1 (* 
h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2304 h1 (* 
h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 5880 h1 (* h2 
h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 8292 h1 (* h2 h2 h2) 
(* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 7020 h1 (* h2 h2 h2) (* h3 h3) 
h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 3624 h1 (* h2 h2 h2) (* h3 h3) h4 (* h6 h6 
h6) (* j2 j2 j2)) (* 1104 h1 (* h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2)) 
(* 180 h1 (* h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6) j2) (* 12 h1 (* h2 h2 h2) (* h3
 h3) h4 (* h6 h6 h6)) (* 96 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 624 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2
 j2 j2 j2 j2)) (* 1696 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 
j2 j2)) (* 2492 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) 
(* 2134 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 1068 h1 
(* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 296 h1 (* h2 h2 h2) (* 
h3 h3) (* h5 h5 h5 h5) (* j2 j2)) (* 40 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5
) j2) (* 2 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5)) (* 768 h1 (* h2 h2 h2) (* 
h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 6144 h1 (* h2 h2 h2) 
(* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 20576 h1 (* h2 h2 h2) 
(* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 37720 h1 (* h2 h2 h2) (* 
h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 41436 h1 (* h2 h2 h2) (* h3 h3)
 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 28030 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5
 h5) h6 (* j2 j2 j2 j2)) (* 11559 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* 
j2 j2 j2)) (* 2777 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2)) (* 349 
h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 j2) (* 17 h1 (* h2 h2 h2) (* h3 h3) 
(* h5 h5 h5) h6) (* 1744 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 13576 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 44460 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 80226 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6
 h6) (* j2 j2 j2 j2 j2 j2)) (* 87544 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2)) (* 59605 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2)) (* 25201 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2
 j2)) (* 6361 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 867 h1
 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) j2) (* 48 h1 (* h2 h2 h2) (* h3 h3) 
(* h5 h5) (* h6 h6)) (* 800 h1 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 6520 h1 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 22116 h1 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 41094 h1 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 46093 h1 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 
j2)) (* 32311 h1 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 
14126 h1 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 3708 h1 (* h2 
h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 529 h1 (* h2 h2 h2) (* h3 h3) h5 
(* h6 h6 h6) j2) (* 31 h1 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6)) (* 128 h1 (* 
h2 h2 h2) (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 768 h1 (* h2
 h2 h2) (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1960 h1 (* h2 h2 
h2) (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2764 h1 (* h2 h2 h2) (* 
h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2340 h1 (* h2 h2 h2) (* h3 h3) (* 
h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 1208 h1 (* h2 h2 h2) (* h3 h3) (* h6 h6 h6 h6) 
(* j2 j2 j2)) (* 368 h1 (* h2 h2 h2) (* h3 h3) (* h6 h6 h6 h6) (* j2 j2)) (* 60 
h1 (* h2 h2 h2) (* h3 h3) (* h6 h6 h6 h6) j2) (* 4 h1 (* h2 h2 h2) (* h3 h3) (* 
h6 h6 h6 h6)) (* 32 h1 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 624 h1 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 3496 h1 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 9724 h1 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 
j2 j2 j2 j2)) (* 15912 h1 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 
j2 j2)) (* 16410 h1 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) 
(* 10903 h1 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 4614 h1 
(* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 1184 h1 (* h2 h2 h2) h3 
(* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 164 h1 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 
h5) j2) (* 9 h1 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5)) (* 88 h1 (* h2 h2 h2) h3
 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 604 h1 (* h2 h2 h2) h3 
(* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1810 h1 (* h2 h2 h2) h3 (* h4
 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 3101 h1 (* h2 h2 h2) h3 (* h4 h4 h4) 
h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 3338 h1 (* h2 h2 h2) h3 (* h4 h4 h4) h5 h6 (* j2
 j2 j2 j2 j2)) (* 2333 h1 (* h2 h2 h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) 
(* 1054 h1 (* h2 h2 h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 295 h1 (* h2 h2 
h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2)) (* 46 h1 (* h2 h2 h2) h3 (* h4 h4 h4) h5 h6
 j2) (* 3 h1 (* h2 h2 h2) h3 (* h4 h4 h4) h5 h6) (* 32 h1 (* h2 h2 h2) h3 (* h4 
h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 680 h1 (* h2 h2 h2) h3 
(* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3940 h1 (* h2 h2 h2) 
h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 11226 h1 (* h2 h2 h2) 
h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 18753 h1 (* h2 h2 h2) h3 
(* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 19713 h1 (* h2 h2 h2) h3 (* h4 
h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 13342 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5
 h5 h5) (* j2 j2 j2 j2)) (* 5752 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2
 j2 j2)) (* 1505 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 213 h1 
(* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) j2) (* 12 h1 (* h2 h2 h2) h3 (* h4 h4) 
(* h5 h5 h5)) (* 224 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 2912 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 14168 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 36660 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2)) (* 57464 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 
j2 j2 j2)) (* 57689 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)
) (* 37719 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 15852 
h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 4080 h1 (* h2 h2 h2) 
h3 (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 575 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 
h5) h6 j2) (* 33 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6) (* 264 h1 (* h2 h2 
h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1812 h1 (* h2 
h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 5430 h1 (* h2 
h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 9303 h1 (* h2 h2 
h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 10014 h1 (* h2 h2 h2) h3
 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 6999 h1 (* h2 h2 h2) h3 (* h4 h4)
 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 3162 h1 (* h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6)
 (* j2 j2 j2)) (* 885 h1 (* h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 
138 h1 (* h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6) j2) (* 9 h1 (* h2 h2 h2) h3 (* h4 
h4) h5 (* h6 h6)) (* 80 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 576 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 1800 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 3196 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 3541 h1 
(* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 2527 h1 (* h2 h2 h2) 
h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 1154 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5
 h5) (* j2 j2 j2)) (* 322 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2)) (* 49
 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) j2) (* 3 h1 (* h2 h2 h2) h3 h4 (* h5 h5 
h5 h5)) (* 192 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 2344 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2
 j2)) (* 11132 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 28522 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
44565 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 44747 h1 
(* h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 29312 h1 (* h2 h2 h2) 
h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 12352 h1 (* h2 h2 h2) h3 h4 (* h5 h5 
h5) h6 (* j2 j2 j2)) (* 3189 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2)) 
(* 451 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5) h6 j2) (* 26 h1 (* h2 h2 h2) h3 h4 (* 
h5 h5 h5) h6) (* 352 h1 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 3952 h1 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 17848 h1 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 44148 h1 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 67192 h1 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 66148 h1 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)
) (* 42729 h1 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 17862 
h1 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 4608 h1 (* h2 h2 h2) 
h3 h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 658 h1 (* h2 h2 h2) h3 h4 (* h5 h5) (* 
h6 h6) j2) (* 39 h1 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6)) (* 264 h1 (* h2 h2 
h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1812 h1 (* h2 h2 h2
) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 5430 h1 (* h2 h2 h2) h3 
h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 9303 h1 (* h2 h2 h2) h3 h4 h5 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 10014 h1 (* h2 h2 h2) h3 h4 h5 (* h6 h6 
h6) (* j2 j2 j2 j2 j2)) (* 6999 h1 (* h2 h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 
j2 j2)) (* 3162 h1 (* h2 h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 885 h1 
(* h2 h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2)) (* 138 h1 (* h2 h2 h2) h3 h4 h5 
(* h6 h6 h6) j2) (* 9 h1 (* h2 h2 h2) h3 h4 h5 (* h6 h6 h6)) (* 96 h1 (* h2 h2 
h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 672 h1 (* h2 h2 h2)
 h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2032 h1 (* h2 h2 h2) h3 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 3472 h1 (* h2 h2 h2) h3 (* h5 h5
 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 3678 h1 (* h2 h2 h2) h3 (* h5 h5 h5 h5) h6 
(* j2 j2 j2 j2 j2)) (* 2490 h1 (* h2 h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2
)) (* 1068 h1 (* h2 h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 276 h1 (* h2 
h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 38 h1 (* h2 h2 h2) h3 (* h5 h5 h5 h5)
 h6 j2) (* 2 h1 (* h2 h2 h2) h3 (* h5 h5 h5 h5) h6) (* 160 h1 (* h2 h2 h2) h3 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1664 h1 (* h2 h2 h2
) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 7192 h1 (* h2 h2 
h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 17296 h1 (* h2 h2 
h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 25812 h1 (* h2 h2 h2)
 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 25034 h1 (* h2 h2 h2) h3 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 15970 h1 (* h2 h2 h2) h3 (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2)) (* 6600 h1 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6)
 (* j2 j2 j2)) (* 1684 h1 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 
238 h1 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) j2) (* 14 h1 (* h2 h2 h2) h3 (* h5
 h5 h5) (* h6 h6)) (* 160 h1 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 1664 h1 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 7176 h1 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 17212 h1 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 25640 h1 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 24869 h1 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2)) (* 15913 h1 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 
6624 h1 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 1712 h1 (* h2 h2
 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 247 h1 (* h2 h2 h2) h3 (* h5 h5) 
(* h6 h6 h6) j2) (* 15 h1 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6)) (* 88 h1 (* h2
 h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 604 h1 (* h2 h2
 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1810 h1 (* h2 h2 h2) 
h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3101 h1 (* h2 h2 h2) h3 h5 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3338 h1 (* h2 h2 h2) h3 h5 (* h6 h6 h6
 h6) (* j2 j2 j2 j2 j2)) (* 2333 h1 (* h2 h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 
j2 j2)) (* 1054 h1 (* h2 h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 295 h1 
(* h2 h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2)) (* 46 h1 (* h2 h2 h2) h3 h5 (* h6 
h6 h6 h6) j2) (* 3 h1 (* h2 h2 h2) h3 h5 (* h6 h6 h6 h6)) (* 16 h1 (* h2 h2 h2) 
(* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 128 h1 (* h2 h2 
h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 456 h1 (* h2 h2
 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 952 h1 (* h2 h2 
h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1289 h1 (* h2 h2 h2) 
(* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 1182 h1 (* h2 h2 h2) (* h4 
h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 743 h1 (* h2 h2 h2) (* h4 h4 h4) (* 
h5 h5) h6 (* j2 j2 j2 j2)) (* 316 h1 (* h2 h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* 
j2 j2 j2)) (* 87 h1 (* h2 h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 14 h1 
(* h2 h2 h2) (* h4 h4 h4) (* h5 h5) h6 j2) (* h1 (* h2 h2 h2) (* h4 h4 h4) (* h5
 h5) h6) (* 32 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2
 j2 j2 j2)) (* 256 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 912 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 1904 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 2578 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2))
 (* 2364 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 1486 
h1 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 632 h1 (* h2 h2 h2
) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 174 h1 (* h2 h2 h2) (* h4 h4) (* h5
 h5 h5) h6 (* j2 j2)) (* 28 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5) h6 j2) (* 2 
h1 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5) h6) (* 48 h1 (* h2 h2 h2) (* h4 h4) (* h5
 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 384 h1 (* h2 h2 h2) (* h4 
h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1368 h1 (* h2 h2 h2) 
(* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2856 h1 (* h2 h2 
h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3867 h1 (* h2 h2 
h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3546 h1 (* h2 h2 h2)
 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2229 h1 (* h2 h2 h2) (* h4
 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 948 h1 (* h2 h2 h2) (* h4 h4) (* h5
 h5) (* h6 h6) (* j2 j2 j2)) (* 261 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6
) (* j2 j2)) (* 42 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) j2) (* 3 h1 (* 
h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6)) (* 16 h1 (* h2 h2 h2) h4 (* h5 h5 h5 h5
) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 128 h1 (* h2 h2 h2) h4 (* h5 h5 h5 h5
) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 456 h1 (* h2 h2 h2) h4 (* h5 h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 952 h1 (* h2 h2 h2) h4 (* h5 h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2)) (* 1289 h1 (* h2 h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2
 j2 j2 j2)) (* 1182 h1 (* h2 h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) 
(* 743 h1 (* h2 h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 316 h1 (* h2 h2
 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 87 h1 (* h2 h2 h2) h4 (* h5 h5 h5 h5
) h6 (* j2 j2)) (* 14 h1 (* h2 h2 h2) h4 (* h5 h5 h5 h5) h6 j2) (* h1 (* h2 h2 
h2) h4 (* h5 h5 h5 h5) h6) (* 64 h1 (* h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 512 h1 (* h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1824 h1 (* h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3808 h1 (* h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2)) (* 5156 h1 (* h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 4728 h1 (* h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2)) (* 2972 h1 (* h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) 
(* 1264 h1 (* h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 348 h1 (* h2 
h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 56 h1 (* h2 h2 h2) h4 (* h5 h5 h5
) (* h6 h6) j2) (* 4 h1 (* h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6)) (* 48 h1 (* h2 
h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 384 h1 
(* h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1368 
h1 (* h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2856 
h1 (* h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3867 h1 
(* h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3546 h1 (* h2 
h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2229 h1 (* h2 h2 h2) h4 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 948 h1 (* h2 h2 h2) h4 (* h5 h5) (* 
h6 h6 h6) (* j2 j2 j2)) (* 261 h1 (* h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 
j2)) (* 42 h1 (* h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6) j2) (* 3 h1 (* h2 h2 h2) h4
 (* h5 h5) (* h6 h6 h6)) (* 16 h1 (* h2 h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 128 h1 (* h2 h2 h2) (* h5 h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 456 h1 (* h2 h2 h2) (* h5 h5 h5 h5) (* h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 952 h1 (* h2 h2 h2) (* h5 h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 1289 h1 (* h2 h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 1182 h1 (* h2 h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2)) (* 743 h1 (* h2 h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 
316 h1 (* h2 h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 87 h1 (* h2 h2 h2
) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 14 h1 (* h2 h2 h2) (* h5 h5 h5 h5) (* 
h6 h6) j2) (* h1 (* h2 h2 h2) (* h5 h5 h5 h5) (* h6 h6)) (* 32 h1 (* h2 h2 h2) 
(* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 256 h1 (* h2 h2 
h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 912 h1 (* h2 h2
 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1904 h1 (* h2 h2 
h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2578 h1 (* h2 h2 h2) 
(* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2364 h1 (* h2 h2 h2) (* h5 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1486 h1 (* h2 h2 h2) (* h5 h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2)) (* 632 h1 (* h2 h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* 
j2 j2 j2)) (* 174 h1 (* h2 h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 28 h1 
(* h2 h2 h2) (* h5 h5 h5) (* h6 h6 h6) j2) (* 2 h1 (* h2 h2 h2) (* h5 h5 h5) (* 
h6 h6 h6)) (* 16 h1 (* h2 h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 128 h1 (* h2 h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2 j2)) (* 456 h1 (* h2 h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 952 h1 (* h2 h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2
 j2 j2)) (* 1289 h1 (* h2 h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)
) (* 1182 h1 (* h2 h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 743 
h1 (* h2 h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 316 h1 (* h2 h2 h2
) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 87 h1 (* h2 h2 h2) (* h5 h5) (* h6 
h6 h6 h6) (* j2 j2)) (* 14 h1 (* h2 h2 h2) (* h5 h5) (* h6 h6 h6 h6) j2) (* h1 
(* h2 h2 h2) (* h5 h5) (* h6 h6 h6 h6)) (* 2544 h1 (* h2 h2) (* h3 h3 h3 h3) (* 
h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 15840 h1 (* h2 h2) (* h3 h3 h3 h3) (* 
h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 41492 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 
h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 59272 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5
 (* j2 j2 j2 j2 j2)) (* 49988 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2
 j2 j2)) (* 25136 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 
7228 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2)) (* 1064 h1 (* h2 h2) 
(* h3 h3 h3 h3) (* h4 h4) h5 j2) (* 60 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5
) (* 256 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 1664 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
4624 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 7136 h1
 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 6640 h1 (* h2 h2)
 (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2)) (* 3776 h1 (* h2 h2) (* h3 h3 h3 
h3) (* h4 h4) h6 (* j2 j2 j2)) (* 1264 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h6
 (* j2 j2)) (* 224 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h6 j2) (* 16 h1 (* h2 
h2) (* h3 h3 h3 h3) (* h4 h4) h6) (* 2432 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 
h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 15552 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 
h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 41136 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5)
 (* j2 j2 j2 j2 j2 j2)) (* 58020 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2
 j2 j2 j2 j2)) (* 46870 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2
)) (* 21676 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 5464 h1 
(* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2)) (* 688 h1 (* h2 h2) (* h3 h3 
h3 h3) h4 (* h5 h5) j2) (* 34 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5)) (* 5600
 h1 (* h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 34624 h1 
(* h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 89768 h1 (* h2 
h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 126432 h1 (* h2 h2) (* h3
 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 104640 h1 (* h2 h2) (* h3 h3 h3 h3) 
h4 h5 h6 (* j2 j2 j2 j2)) (* 51360 h1 (* h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 
j2 j2)) (* 14344 h1 (* h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2)) (* 2048 h1 (* 
h2 h2) (* h3 h3 h3 h3) h4 h5 h6 j2) (* 112 h1 (* h2 h2) (* h3 h3 h3 h3) h4 h5 h6
) (* 512 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 3328 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
9248 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 14272 
h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 13280 h1 (* h2 
h2) (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 7552 h1 (* h2 h2) (* h3 h3 
h3 h3) h4 (* h6 h6) (* j2 j2 j2)) (* 2528 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 
h6) (* j2 j2)) (* 448 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6) j2) (* 32 h1 (* 
h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6)) (* 192 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1344 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 3872 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 
h5) (* j2 j2 j2 j2 j2 j2)) (* 5912 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) (* 
j2 j2 j2 j2 j2)) (* 5128 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 
j2)) (* 2516 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2)) (* 660 h1 
(* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2)) (* 84 h1 (* h2 h2) (* h3 h3 h3
 h3) (* h5 h5 h5) j2) (* 4 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5)) (* 2496 h1
 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 15792 h1
 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 41288 h1 
(* h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 57436 h1 (* h2 
h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 45566 h1 (* h2 h2) (* h3
 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 20524 h1 (* h2 h2) (* h3 h3 h3 h3) 
(* h5 h5) h6 (* j2 j2 j2)) (* 4960 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* 
j2 j2)) (* 584 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 j2) (* 26 h1 (* h2 h2) 
(* h3 h3 h3 h3) (* h5 h5) h6) (* 3056 h1 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 18784 h1 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 48276 h1 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 67160 h1 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 
j2 j2 j2)) (* 54652 h1 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) 
(* 26224 h1 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 7116 h1 (* 
h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2)) (* 984 h1 (* h2 h2) (* h3 h3 h3 
h3) h5 (* h6 h6) j2) (* 52 h1 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6)) (* 256 h1 
(* h2 h2) (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1664 h1 
(* h2 h2) (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4624 h1 (* 
h2 h2) (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 7136 h1 (* h2 h2) 
(* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 6640 h1 (* h2 h2) (* h3 h3 
h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 3776 h1 (* h2 h2) (* h3 h3 h3 h3) (* h6 
h6 h6) (* j2 j2 j2)) (* 1264 h1 (* h2 h2) (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2)
) (* 224 h1 (* h2 h2) (* h3 h3 h3 h3) (* h6 h6 h6) j2) (* 16 h1 (* h2 h2) (* h3 
h3 h3 h3) (* h6 h6 h6)) (* 544 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 5176 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 20104 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* 
j2 j2 j2 j2 j2 j2 j2)) (* 42370 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 
j2 j2 j2 j2 j2)) (* 53560 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 
j2 j2)) (* 41970 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 
20200 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 5670 h1 (* h2 
h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2)) (* 824 h1 (* h2 h2) (* h3 h3 h3) (* 
h4 h4 h4) h5 j2) (* 46 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5) (* 128 h1 (* 
h2 h2) (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 832 h1 (* h2
 h2) (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2312 h1 (* h2 h2)
 (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 3568 h1 (* h2 h2) (* h3 
h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 3320 h1 (* h2 h2) (* h3 h3 h3) (* 
h4 h4 h4) h6 (* j2 j2 j2 j2)) (* 1888 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h6 
(* j2 j2 j2)) (* 632 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2)) (* 112
 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h6 j2) (* 8 h1 (* h2 h2) (* h3 h3 h3) 
(* h4 h4 h4) h6) (* 1856 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 15648 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 55496 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 
h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 108320 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* 
h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 127716 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* 
h5 h5) (* j2 j2 j2 j2 j2)) (* 93919 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5
) (* j2 j2 j2 j2)) (* 42886 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 
j2 j2)) (* 11664 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 
1694 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) j2) (* 97 h1 (* h2 h2) (* h3 
h3 h3) (* h4 h4) (* h5 h5)) (* 2160 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 19256 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 71580 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 146158 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6
 (* j2 j2 j2 j2 j2 j2)) (* 180436 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* 
j2 j2 j2 j2 j2)) (* 138918 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2
 j2)) (* 66068 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 18458 
h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 2700 h1 (* h2 h2) (* h3 
h3 h3) (* h4 h4) h5 h6 j2) (* 154 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6) (* 
384 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 2496 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 6936 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
10704 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 9960 
h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 5664 h1 (* h2 
h2) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 1896 h1 (* h2 h2) (* h3 h3
 h3) (* h4 h4) (* h6 h6) (* j2 j2)) (* 336 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) 
(* h6 h6) j2) (* 24 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6)) (* 864 h1 (* 
h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 7528 h1 
(* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 27320 h1 
(* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 53938 h1 (* 
h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 63364 h1 (* h2 h2)
 (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 45493 h1 (* h2 h2) (* h3 h3
 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 19752 h1 (* h2 h2) (* h3 h3 h3) h4 (* 
h5 h5 h5) (* j2 j2 j2)) (* 4948 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 
j2)) (* 640 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) j2) (* 33 h1 (* h2 h2) (* 
h3 h3 h3) h4 (* h5 h5 h5)) (* 4144 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 34296 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 119532 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6
 (* j2 j2 j2 j2 j2 j2 j2)) (* 229366 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 265748 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2
 j2 j2 j2 j2)) (* 191776 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 
j2)) (* 85738 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 22760 
h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 3214 h1 (* h2 h2) (* h3 
h3 h3) h4 (* h5 h5) h6 j2) (* 178 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6) (* 
2688 h1 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 22984 h1 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 82848 h1 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
165206 h1 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
200192 h1 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 151926 
h1 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 71536 h1 (* h2 h2)
 (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 19906 h1 (* h2 h2) (* h3 h3 h3) 
h4 h5 (* h6 h6) (* j2 j2)) (* 2928 h1 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) j2)
 (* 170 h1 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6)) (* 384 h1 (* h2 h2) (* h3 h3 
h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2496 h1 (* h2 h2) (* h3 h3 
h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 6936 h1 (* h2 h2) (* h3 h3 h3) 
h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 10704 h1 (* h2 h2) (* h3 h3 h3) h4 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 9960 h1 (* h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6) 
(* j2 j2 j2 j2)) (* 5664 h1 (* h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2))
 (* 1896 h1 (* h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2)) (* 336 h1 (* h2 h2
) (* h3 h3 h3) h4 (* h6 h6 h6) j2) (* 24 h1 (* h2 h2) (* h3 h3 h3) h4 (* h6 h6 
h6)) (* 96 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 672 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
1936 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2956 h1
 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 2564 h1 (* h2 h2)
 (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 1258 h1 (* h2 h2) (* h3 h3 h3)
 (* h5 h5 h5 h5) (* j2 j2 j2)) (* 330 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) 
(* j2 j2)) (* 42 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) j2) (* 2 h1 (* h2 h2)
 (* h3 h3 h3) (* h5 h5 h5 h5)) (* 960 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8136 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 28816 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 55626 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 63906 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* 44776 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)
) (* 18861 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 4525 h1 
(* h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2)) (* 545 h1 (* h2 h2) (* h3 h3 
h3) (* h5 h5 h5) h6 j2) (* 25 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6) (* 2288
 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 18648 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 64036 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2
 j2)) (* 121046 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 138032 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2))
 (* 97857 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 
42852 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 11096 h1 
(* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 1520 h1 (* h2 h2) (* h3
 h3 h3) (* h5 h5) (* h6 h6) j2) (* 81 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 
h6)) (* 1072 h1 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 8904 h1 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 31372 h1 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 61418 h1 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 73316 h1 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 54978 
h1 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 25668 h1 (* h2 h2)
 (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 7118 h1 (* h2 h2) (* h3 h3 h3) h5
 (* h6 h6 h6) (* j2 j2)) (* 1052 h1 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) j2) 
(* 62 h1 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6)) (* 128 h1 (* h2 h2) (* h3 h3 h3
) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 832 h1 (* h2 h2) (* h3 h3 h3) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2312 h1 (* h2 h2) (* h3 h3 h3) (* 
h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3568 h1 (* h2 h2) (* h3 h3 h3) (* h6 h6 
h6 h6) (* j2 j2 j2 j2 j2)) (* 3320 h1 (* h2 h2) (* h3 h3 h3) (* h6 h6 h6 h6) (* 
j2 j2 j2 j2)) (* 1888 h1 (* h2 h2) (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2)) 
(* 632 h1 (* h2 h2) (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2)) (* 112 h1 (* h2 h2) 
(* h3 h3 h3) (* h6 h6 h6 h6) j2) (* 8 h1 (* h2 h2) (* h3 h3 h3) (* h6 h6 h6 h6))
 (* 136 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 1136 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2))
 (* 4006 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 
7808 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 9220 h1
 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 6782 h1 (* h2 h2)
 (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 3070 h1 (* h2 h2) (* h3 h3) 
(* h4 h4 h4 h4) h5 (* j2 j2 j2)) (* 812 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) 
h5 (* j2 j2)) (* 112 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 j2) (* 6 h1 (* h2
 h2) (* h3 h3) (* h4 h4 h4 h4) h5) (* 96 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1728 h1 (* h2 h2) (* h3 h3) (* h4 
h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 10128 h1 (* h2 h2) (* h3 h3)
 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 30072 h1 (* h2 h2) (* h3
 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 52700 h1 (* h2 h2) (* 
h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 58145 h1 (* h2 h2) (* h3
 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 41260 h1 (* h2 h2) (* h3 h3) 
(* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 18634 h1 (* h2 h2) (* h3 h3) (* h4 h4
 h4) (* h5 h5) (* j2 j2 j2)) (* 5108 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 
h5) (* j2 j2)) (* 757 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) j2) (* 44 h1
 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5)) (* 720 h1 (* h2 h2) (* h3 h3) (* h4
 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 5856 h1 (* h2 h2) (* h3 h3) (* 
h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 20264 h1 (* h2 h2) (* h3 h3) (* 
h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 39010 h1 (* h2 h2) (* h3 h3) (* h4 
h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 45780 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4)
 h5 h6 (* j2 j2 j2 j2 j2)) (* 33694 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 
(* j2 j2 j2 j2)) (* 15392 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2)
) (* 4158 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2)) (* 596 h1 (* h2 
h2) (* h3 h3) (* h4 h4 h4) h5 h6 j2) (* 34 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) 
h5 h6) (* 96 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 1840 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 10996 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 33024 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 58337 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5)
 (* j2 j2 j2 j2 j2 j2)) (* 64651 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) 
(* j2 j2 j2 j2 j2)) (* 45870 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2
 j2 j2 j2)) (* 20606 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2))
 (* 5597 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 823 h1 (* 
h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) j2) (* 48 h1 (* h2 h2) (* h3 h3) (* h4 
h4) (* h5 h5 h5)) (* 480 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 6848 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 36572 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 103272 h1 (* h2 h2) (* h3 h3) (* h4 h4) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 175483 h1 (* h2 h2) (* h3 h3) (* h4 h4
) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 189778 h1 (* h2 h2) (* h3 h3) (* h4 h4)
 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 132927 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* 
h5 h5) h6 (* j2 j2 j2 j2)) (* 59552 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) 
h6 (* j2 j2 j2)) (* 16253 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2
)) (* 2406 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 j2) (* 141 h1 (* h2 h2)
 (* h3 h3) (* h4 h4) (* h5 h5) h6) (* 1344 h1 (* h2 h2) (* h3 h3) (* h4 h4) h5 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 10752 h1 (* h2 h2) (* h3 h3) (* h4 
h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 36756 h1 (* h2 h2) (* h3 h3) 
(* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 70182 h1 (* h2 h2) (* h3 h3)
 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 82020 h1 (* h2 h2) (* h3 h3) 
(* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 60390 h1 (* h2 h2) (* h3 h3) (* h4
 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 27756 h1 (* h2 h2) (* h3 h3) (* h4 h4) h5 
(* h6 h6) (* j2 j2 j2)) (* 7602 h1 (* h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6) 
(* j2 j2)) (* 1116 h1 (* h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6) j2) (* 66 h1 
(* h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6)) (* 256 h1 (* h2 h2) (* h3 h3) h4 (* 
h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2048 h1 (* h2 h2) (* h3 h3) h4 
(* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 7024 h1 (* h2 h2) (* h3 h3) h4 
(* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 13436 h1 (* h2 h2) (* h3 h3) h4 (* 
h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 15606 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 
h5 h5) (* j2 j2 j2 j2 j2)) (* 11226 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) 
(* j2 j2 j2 j2)) (* 4894 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2))
 (* 1218 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2)) (* 156 h1 (* h2 h2
) (* h3 h3) h4 (* h5 h5 h5 h5) j2) (* 8 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5
)) (* 384 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 5232 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 27268 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 75812 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 127243 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2
)) (* 135840 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
93591 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 41011 h1 (* 
h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 10878 h1 (* h2 h2) (* h3 h3
) h4 (* h5 h5 h5) h6 (* j2 j2)) (* 1557 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) 
h6 j2) (* 88 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6) (* 672 h1 (* h2 h2) (* 
h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8512 h1 (* 
h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 42760
 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
116328 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 192866 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 205121 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
142074 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 63202 
h1 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 17182 h1 (* h2 h2
) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 2541 h1 (* h2 h2) (* h3 h3) h4 
(* h5 h5) (* h6 h6) j2) (* 150 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6)) 
(* 1072 h1 (* h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 8480 h1 (* h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2))
 (* 28744 h1 (* h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 54566 h1 (* h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
63580 h1 (* h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 46826 h1 
(* h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 21616 h1 (* h2 h2) 
(* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 5978 h1 (* h2 h2) (* h3 h3) h4 h5 
(* h6 h6 h6) (* j2 j2)) (* 892 h1 (* h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) j2) (* 
54 h1 (* h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6)) (* 288 h1 (* h2 h2) (* h3 h3) (* 
h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2256 h1 (* h2 h2) (* h3 h3) 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 7572 h1 (* h2 h2) (* h3 h3) 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 14164 h1 (* h2 h2) (* h3 h3) (* 
h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 16065 h1 (* h2 h2) (* h3 h3) (* h5 h5 
h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 11250 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6
 (* j2 j2 j2 j2)) (* 4742 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2)
) (* 1124 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 133 h1 (* h2 
h2) (* h3 h3) (* h5 h5 h5 h5) h6 j2) (* 6 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5)
 h6) (* 288 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 3392 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 16272 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 42788 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 68906 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6)
 (* j2 j2 j2 j2 j2 j2)) (* 71189 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* 47721 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2
 j2 j2 j2)) (* 20405 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2))
 (* 5281 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 734 h1 (* 
h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) j2) (* 40 h1 (* h2 h2) (* h3 h3) (* h5 
h5 h5) (* h6 h6)) (* 288 h1 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 3392 h1 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 16316 h1 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 43128 h1 (* h2 h2) (* h3 h3) (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 70083 h1 (* h2 h2) (* h3 h3) (* h5 h5)
 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 73488 h1 (* h2 h2) (* h3 h3) (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 50407 h1 (* h2 h2) (* h3 h3) (* h5 h5) (* h6
 h6 h6) (* j2 j2 j2 j2)) (* 22284 h1 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2)) (* 6037 h1 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2)) 
(* 892 h1 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) j2) (* 53 h1 (* h2 h2) (* 
h3 h3) (* h5 h5) (* h6 h6 h6)) (* 312 h1 (* h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2448 h1 (* h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 8246 h1 (* h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2)) (* 15586 h1 (* h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 18120 h1 (* h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 
j2 j2 j2 j2)) (* 13348 h1 (* h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)
) (* 6182 h1 (* h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 1722 h1 (* 
h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2)) (* 260 h1 (* h2 h2) (* h3 h3) h5 
(* h6 h6 h6 h6) j2) (* 16 h1 (* h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6)) (* 16 h1 
(* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 196
 h1 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
968 h1 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
2617 h1 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 4342
 h1 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 4636 h1 (* 
h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 3219 h1 (* h2 h2) h3 
(* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 1425 h1 (* h2 h2) h3 (* h4 h4 h4 
h4) (* h5 h5) (* j2 j2 j2)) (* 380 h1 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* 
j2 j2)) (* 54 h1 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) j2) (* 3 h1 (* h2 h2) h3
 (* h4 h4 h4 h4) (* h5 h5)) (* 32 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 480 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5)
 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2604 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 
h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 7440 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 
h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 12831 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5)
 (* j2 j2 j2 j2 j2 j2)) (* 14142 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2
 j2 j2 j2 j2)) (* 10121 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2
)) (* 4628 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 1281 h1 
(* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2)) (* 190 h1 (* h2 h2) h3 (* h4 
h4 h4) (* h5 h5 h5) j2) (* 11 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5)) (* 112 
h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
1208 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 5520 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 14184 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
22754 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 23787 
h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 16345 h1 (* h2 
h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 7238 h1 (* h2 h2) h3 (* h4 
h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 1956 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5)
 h6 (* j2 j2)) (* 287 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 j2) (* 17 h1 (* 
h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6) (* 16 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5
 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 248 h1 (* h2 h2) h3 (* h4 h4) (* h5 
h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1384 h1 (* h2 h2) h3 (* h4 h4) (* 
h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4058 h1 (* h2 h2) h3 (* h4 h4) (* 
h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 7169 h1 (* h2 h2) h3 (* h4 h4) (* h5 
h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 8082 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 
h5) (* j2 j2 j2 j2 j2)) (* 5909 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 
j2 j2 j2)) (* 2758 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 
779 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 118 h1 (* h2 h2) h3 
(* h4 h4) (* h5 h5 h5 h5) j2) (* 7 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5)) 
(* 192 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 2216 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 10560 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 27924 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2)) (* 45767 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 48696 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 33999 
h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 15292 h1 (* h2 h2)
 h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 4197 h1 (* h2 h2) h3 (* h4 h4) 
(* h5 h5 h5) h6 (* j2 j2)) (* 624 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 j2) 
(* 37 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6) (* 240 h1 (* h2 h2) h3 (* h4 h4
) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2448 h1 (* h2 h2) h3
 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 10752 h1 (* h2
 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 26850 h1 
(* h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 42210 h1
 (* h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 43545 h1 
(* h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 29721 h1 (* h2
 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 13164 h1 (* h2 h2) h3 
(* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 3588 h1 (* h2 h2) h3 (* h4 h4) 
(* h5 h5) (* h6 h6) (* j2 j2)) (* 537 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 
h6) j2) (* 33 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6)) (* 80 h1 (* h2 h2) 
h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 872 h1 (* h2 h2) 
h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4040 h1 (* h2 h2) h3
 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 10538 h1 (* h2 h2) h3 h4 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 17163 h1 (* h2 h2) h3 h4 (* h5 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 18206 h1 (* h2 h2) h3 h4 (* h5 h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2)) (* 12679 h1 (* h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 
j2 j2)) (* 5678 h1 (* h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 1545 h1 
(* h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 226 h1 (* h2 h2) h3 h4 (* h5 h5
 h5 h5) h6 j2) (* 13 h1 (* h2 h2) h3 h4 (* h5 h5 h5 h5) h6) (* 288 h1 (* h2 h2) 
h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2992 h1 (* h2
 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 13308 h1 
(* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 33528 h1 
(* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 53041 h1 (* 
h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 54966 h1 (* h2 h2)
 h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 37635 h1 (* h2 h2) h3 h4 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 16700 h1 (* h2 h2) h3 h4 (* h5 h5 h5)
 (* h6 h6) (* j2 j2 j2)) (* 4551 h1 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2
 j2)) (* 678 h1 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) j2) (* 41 h1 (* h2 h2) h3
 h4 (* h5 h5 h5) (* h6 h6)) (* 208 h1 (* h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2056 h1 (* h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8816 h1 (* h2 h2) h3 h4 (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 21616 h1 (* h2 h2) h3 h4 (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 33526 h1 (* h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2)) (* 34273 h1 (* h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2
 j2 j2 j2 j2)) (* 23283 h1 (* h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2
)) (* 10314 h1 (* h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 2828 h1 
(* h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 429 h1 (* h2 h2) h3 h4 (* 
h5 h5) (* h6 h6 h6) j2) (* 27 h1 (* h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6)) (* 64 
h1 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
624 h1 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 2656 h1 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 6480 h1 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
9994 h1 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 10124 
h1 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 6770 h1 (* h2 
h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 2920 h1 (* h2 h2) h3 (* h5 
h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 766 h1 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 
h6) (* j2 j2)) (* 108 h1 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) j2) (* 6 h1 (* 
h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6)) (* 128 h1 (* h2 h2) h3 (* h5 h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1256 h1 (* h2 h2) h3 (* h5 h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 5352 h1 (* h2 h2) h3 (* h5 h5 h5
) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 13044 h1 (* h2 h2) h3 (* h5 h5 h5
) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 20105 h1 (* h2 h2) h3 (* h5 h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 20412 h1 (* h2 h2) h3 (* h5 h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2)) (* 13757 h1 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2)) (* 6036 h1 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2))
 (* 1635 h1 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 244 h1 (* h2 h2
) h3 (* h5 h5 h5) (* h6 h6 h6) j2) (* 15 h1 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 
h6)) (* 64 h1 (* h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 620 h1 (* h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2
 j2 j2)) (* 2616 h1 (* h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 6333 h1 (* h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 9728 h1 (* h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 9879 h1 (* h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 6688 h1
 (* h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 2963 h1 (* h2 h2) h3
 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 816 h1 (* h2 h2) h3 (* h5 h5) (* h6 
h6 h6 h6) (* j2 j2)) (* 125 h1 (* h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) j2) (* 8 
h1 (* h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6)) (* 8 h1 (* h2 h2) (* h4 h4 h4) (* h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 68 h1 (* h2 h2) (* h4 h4 h4) (* 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 258 h1 (* h2 h2) (* h4 h4 h4) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 575 h1 (* h2 h2) (* h4 h4 h4) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 833 h1 (* h2 h2) (* h4 h4 h4) (* h5
 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 819 h1 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2)) (* 553 h1 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2
 j2 j2)) (* 253 h1 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 75 h1
 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 13 h1 (* h2 h2) (* h4 h4 
h4) (* h5 h5 h5) h6 j2) (* h1 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5) h6) (* 8 h1 
(* h2 h2) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 68 
h1 (* h2 h2) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 258
 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 575 
h1 (* h2 h2) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 833 h1 
(* h2 h2) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 819 h1 (* h2 h2
) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 553 h1 (* h2 h2) (* h4 h4)
 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 253 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5 
h5) h6 (* j2 j2 j2)) (* 75 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2)) 
(* 13 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5 h5) h6 j2) (* h1 (* h2 h2) (* h4 h4) 
(* h5 h5 h5 h5) h6) (* 24 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2
 j2 j2 j2 j2 j2 j2 j2 j2)) (* 204 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 774 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1725 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2499 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2457 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2)) (* 1659 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6)
 (* j2 j2 j2 j2)) (* 759 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 
j2)) (* 225 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 39 h1 
(* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6) j2) (* 3 h1 (* h2 h2) (* h4 h4) (* h5
 h5 h5) (* h6 h6)) (* 16 h1 (* h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 136 h1 (* h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2
 j2 j2 j2 j2 j2 j2 j2)) (* 516 h1 (* h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 1150 h1 (* h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 1666 h1 (* h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 1638 h1 (* h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 1106 h1 (* h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 506 
h1 (* h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 150 h1 (* h2 h2) h4 
(* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 26 h1 (* h2 h2) h4 (* h5 h5 h5 h5) (* h6
 h6) j2) (* 2 h1 (* h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6)) (* 24 h1 (* h2 h2) h4 
(* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 204 h1 (* h2 h2)
 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 774 h1 (* h2 h2
) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1725 h1 (* h2 h2)
 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2499 h1 (* h2 h2) h4 
(* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2457 h1 (* h2 h2) h4 (* h5 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1659 h1 (* h2 h2) h4 (* h5 h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2)) (* 759 h1 (* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6) (* 
j2 j2 j2)) (* 225 h1 (* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 39 h1 
(* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6) j2) (* 3 h1 (* h2 h2) h4 (* h5 h5 h5) (* 
h6 h6 h6)) (* 8 h1 (* h2 h2) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 68 h1 (* h2 h2) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 258 h1 (* h2 h2) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 575 h1 (* h2 h2) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 833 h1 (* h2 h2) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 819 h1 (* h2 h2) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 553 h1 
(* h2 h2) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 253 h1 (* h2 h2) (* 
h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 75 h1 (* h2 h2) (* h5 h5 h5 h5) (* h6
 h6 h6) (* j2 j2)) (* 13 h1 (* h2 h2) (* h5 h5 h5 h5) (* h6 h6 h6) j2) (* h1 (* 
h2 h2) (* h5 h5 h5 h5) (* h6 h6 h6)) (* 8 h1 (* h2 h2) (* h5 h5 h5) (* h6 h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 68 h1 (* h2 h2) (* h5 h5 h5) (* h6 h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 258 h1 (* h2 h2) (* h5 h5 h5) (* h6 h6
 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 575 h1 (* h2 h2) (* h5 h5 h5) (* h6 h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 833 h1 (* h2 h2) (* h5 h5 h5) (* h6 h6 h6 h6
) (* j2 j2 j2 j2 j2 j2)) (* 819 h1 (* h2 h2) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 
j2 j2 j2 j2)) (* 553 h1 (* h2 h2) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) 
(* 253 h1 (* h2 h2) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 75 h1 (* h2 h2
) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 13 h1 (* h2 h2) (* h5 h5 h5) (* h6 
h6 h6 h6) j2) (* h1 (* h2 h2) (* h5 h5 h5) (* h6 h6 h6 h6)) (* 272 h1 h2 (* h3 
h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2120 h1 h2 (* h3 h3
 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 7184 h1 h2 (* h3 h3 h3 
h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 13832 h1 h2 (* h3 h3 h3 h3) (* 
h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 16576 h1 h2 (* h3 h3 h3 h3) (* h4 h4 h4) 
h5 (* j2 j2 j2 j2 j2)) (* 12712 h1 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 
j2 j2)) (* 6160 h1 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 1784 h1 
h2 (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2)) (* 272 h1 h2 (* h3 h3 h3 h3) (* h4
 h4 h4) h5 j2) (* 16 h1 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h5) (* 800 h1 h2 (* h3 
h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 6320 h1 h2 (* 
h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 21384 h1 h2 (* 
h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 40476 h1 h2 (* h3 
h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 46916 h1 h2 (* h3 h3 h3 
h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 34216 h1 h2 (* h3 h3 h3 h3) (* h4
 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 15504 h1 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 
h5) (* j2 j2 j2)) (* 4140 h1 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) 
(* 580 h1 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) j2) (* 32 h1 h2 (* h3 h3 h3 h3)
 (* h4 h4) (* h5 h5)) (* 992 h1 h2 (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 7744 h1 h2 (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2
 j2 j2 j2 j2)) (* 26272 h1 h2 (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 50616 h1 h2 (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) 
(* 60656 h1 h2 (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 46472 h1 
h2 (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 22464 h1 h2 (* h3 h3 h3 
h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 6472 h1 h2 (* h3 h3 h3 h3) (* h4 h4) h5 h6 
(* j2 j2)) (* 976 h1 h2 (* h3 h3 h3 h3) (* h4 h4) h5 h6 j2) (* 56 h1 h2 (* h3 h3
 h3 h3) (* h4 h4) h5 h6) (* 352 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 2848 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 9792 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 
j2 j2 j2)) (* 18628 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2))
 (* 21376 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 15122 h1 
h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 6472 h1 h2 (* h3 h3 h3 h3
) h4 (* h5 h5 h5) (* j2 j2 j2)) (* 1584 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) 
(* j2 j2)) (* 200 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) j2) (* 10 h1 h2 (* h3 h3
 h3 h3) h4 (* h5 h5 h5)) (* 1744 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 13704 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 46024 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2)) (* 86256 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 
j2)) (* 98704 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 70820
 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 31448 h1 h2 (* h3 h3 
h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 8200 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5) 
h6 (* j2 j2)) (* 1120 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5) h6 j2) (* 60 h1 h2 (* 
h3 h3 h3 h3) h4 (* h5 h5) h6) (* 1168 h1 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 9128 h1 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 30992 h1 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 59736 h1 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 71584 h1 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
54808 h1 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 26448 h1 h2 (* 
h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 7592 h1 h2 (* h3 h3 h3 h3) h4 h5 
(* h6 h6) (* j2 j2)) (* 1136 h1 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6) j2) (* 64 h1 
h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6)) (* 384 h1 h2 (* h3 h3 h3 h3) (* h5 h5 h5) h6
 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3072 h1 h2 (* h3 h3 h3 h3) (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 10432 h1 h2 (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2)) (* 19568 h1 h2 (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2)) (* 22080 h1 h2 (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2))
 (* 15288 h1 h2 (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 6352 h1 h2 
(* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 1488 h1 h2 (* h3 h3 h3 h3) (* 
h5 h5 h5) h6 (* j2 j2)) (* 176 h1 h2 (* h3 h3 h3 h3) (* h5 h5 h5) h6 j2) (* 8 h1
 h2 (* h3 h3 h3 h3) (* h5 h5 h5) h6) (* 944 h1 h2 (* h3 h3 h3 h3) (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 7384 h1 h2 (* h3 h3 h3 h3) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 24640 h1 h2 (* h3 h3 h3 h3) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 45780 h1 h2 (* h3 h3 h3 h3) (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 51788 h1 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6)
 (* j2 j2 j2 j2 j2)) (* 36604 h1 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2
 j2 j2)) (* 15944 h1 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 
4060 h1 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 540 h1 h2 (* h3 h3 
h3 h3) (* h5 h5) (* h6 h6) j2) (* 28 h1 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6)) 
(* 448 h1 h2 (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
3504 h1 h2 (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 11904
 h1 h2 (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 22952 h1 h2 
(* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 27504 h1 h2 (* h3 h3 
h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 21048 h1 h2 (* h3 h3 h3 h3) h5 (* 
h6 h6 h6) (* j2 j2 j2 j2)) (* 10144 h1 h2 (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 
j2 j2)) (* 2904 h1 h2 (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 432 h1 h2 
(* h3 h3 h3 h3) h5 (* h6 h6 h6) j2) (* 24 h1 h2 (* h3 h3 h3 h3) h5 (* h6 h6 h6))
 (* 136 h1 h2 (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 1060 h1 h2 (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
3592 h1 h2 (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 6916 h1 
h2 (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 8288 h1 h2 (* h3 h3
 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 6356 h1 h2 (* h3 h3 h3) (* h4 h4 
h4 h4) h5 (* j2 j2 j2 j2)) (* 3080 h1 h2 (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 
j2 j2)) (* 892 h1 h2 (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2)) (* 136 h1 h2 (* 
h3 h3 h3) (* h4 h4 h4 h4) h5 j2) (* 8 h1 h2 (* h3 h3 h3) (* h4 h4 h4 h4) h5) (* 
96 h1 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 1408 h1 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 7736 h1 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2))
 (* 22604 h1 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 39974 h1 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 
45168 h1 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 33074 h1 
h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 15420 h1 h2 (* h3 h3 
h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 4330 h1 h2 (* h3 h3 h3) (* h4 h4 h4)
 (* h5 h5) (* j2 j2)) (* 648 h1 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) j2) (* 38
 h1 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5)) (* 632 h1 h2 (* h3 h3 h3) (* h4 h4 
h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4932 h1 h2 (* h3 h3 h3) (* h4 h4 h4
) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 16728 h1 h2 (* h3 h3 h3) (* h4 h4 h4) h5
 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 32224 h1 h2 (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* 
j2 j2 j2 j2 j2 j2)) (* 38616 h1 h2 (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 
j2 j2)) (* 29592 h1 h2 (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 14312
 h1 h2 (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 4128 h1 h2 (* h3 h3 h3) 
(* h4 h4 h4) h5 h6 (* j2 j2)) (* 624 h1 h2 (* h3 h3 h3) (* h4 h4 h4) h5 h6 j2) 
(* 36 h1 h2 (* h3 h3 h3) (* h4 h4 h4) h5 h6) (* 96 h1 h2 (* h3 h3 h3) (* h4 h4) 
(* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1464 h1 h2 (* h3 h3 h3) (* h4
 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8204 h1 h2 (* h3 h3 h3) (* 
h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 24136 h1 h2 (* h3 h3 h3) (* 
h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 42482 h1 h2 (* h3 h3 h3) (* h4 
h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 47238 h1 h2 (* h3 h3 h3) (* h4 h4) 
(* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 33660 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 
h5) (* j2 j2 j2 j2)) (* 15106 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2
 j2)) (* 4042 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 572 h1 h2 
(* h3 h3 h3) (* h4 h4) (* h5 h5 h5) j2) (* 32 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5
 h5 h5)) (* 416 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 5392 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 27848 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 78364 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2)) (* 135100 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2
 j2 j2)) (* 149888 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2))
 (* 108280 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 49980 
h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 13932 h1 h2 (* h3 h3 
h3) (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 2072 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5
 h5) h6 j2) (* 120 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) h6) (* 1080 h1 h2 (* 
h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8436 h1 h2 
(* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 28632 h1 h2 
(* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 55176 h1 h2 (* 
h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 66120 h1 h2 (* h3 h3 
h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 50640 h1 h2 (* h3 h3 h3) (* h4
 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 24456 h1 h2 (* h3 h3 h3) (* h4 h4) h5 (* 
h6 h6) (* j2 j2 j2)) (* 7032 h1 h2 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2)
) (* 1056 h1 h2 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) j2) (* 60 h1 h2 (* h3 h3 h3)
 (* h4 h4) h5 (* h6 h6)) (* 176 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 1424 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 4896 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 
j2 j2 j2)) (* 9314 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) 
(* 10688 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 7561 h1 h2
 (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 3236 h1 h2 (* h3 h3 h3) h4 
(* h5 h5 h5 h5) (* j2 j2 j2)) (* 792 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2
 j2)) (* 100 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) j2) (* 5 h1 h2 (* h3 h3 h3) 
h4 (* h5 h5 h5 h5)) (* 320 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 4040 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 20532 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 56740 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 95372 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 102130 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 70389 h1 
h2 (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 30627 h1 h2 (* h3 h3 h3) 
h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 7963 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5) h6 
(* j2 j2)) (* 1099 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5) h6 j2) (* 60 h1 h2 (* h3 
h3 h3) h4 (* h5 h5 h5) h6) (* 544 h1 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 6560 h1 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 32488 h1 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 88916 h1 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6
 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 150278 h1 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 164272 h1 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* 117338 h1 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2
 j2 j2)) (* 53700 h1 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 
14874 h1 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 2200 h1 h2 (* h3 
h3 h3) h4 (* h5 h5) (* h6 h6) j2) (* 126 h1 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 
h6)) (* 808 h1 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 6316 h1 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
21448 h1 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 41344 
h1 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 49544 h1 h2 (* 
h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 37928 h1 h2 (* h3 h3 h3) h4 
h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 18296 h1 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6) 
(* j2 j2 j2)) (* 5248 h1 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2)) (* 784 h1
 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6) j2) (* 44 h1 h2 (* h3 h3 h3) h4 h5 (* h6 h6 
h6)) (* 192 h1 h2 (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 1536 h1 h2 (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
5216 h1 h2 (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 9784 h1 
h2 (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 11040 h1 h2 (* h3 
h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 7644 h1 h2 (* h3 h3 h3) (* h5 
h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 3176 h1 h2 (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* 
j2 j2 j2)) (* 744 h1 h2 (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 88 h1 h2 
(* h3 h3 h3) (* h5 h5 h5 h5) h6 j2) (* 4 h1 h2 (* h3 h3 h3) (* h5 h5 h5 h5) h6) 
(* 224 h1 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 2576 h1 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 12328 h1 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 32604 h1 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 52890 h1 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 54892 h1 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 36729 
h1 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 15521 h1 h2 (* h3 
h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 3921 h1 h2 (* h3 h3 h3) (* h5 h5 
h5) (* h6 h6) (* j2 j2)) (* 527 h1 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) j2) 
(* 28 h1 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6)) (* 224 h1 h2 (* h3 h3 h3) (* h5
 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2576 h1 h2 (* h3 h3 h3) 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 12376 h1 h2 (* h3 h3 
h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 33156 h1 h2 (* h3 h3 
h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 55152 h1 h2 (* h3 h3 h3)
 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 59552 h1 h2 (* h3 h3 h3) (* h5
 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 42132 h1 h2 (* h3 h3 h3) (* h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2)) (* 19140 h1 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2)) (* 5272 h1 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 
776 h1 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) j2) (* 44 h1 h2 (* h3 h3 h3) (* h5
 h5) (* h6 h6 h6)) (* 224 h1 h2 (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 1752 h1 h2 (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 5952 h1 h2 (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 11476 h1 h2 (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
13752 h1 h2 (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 10524 h1 h2 
(* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 5072 h1 h2 (* h3 h3 h3) h5 
(* h6 h6 h6 h6) (* j2 j2 j2)) (* 1452 h1 h2 (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* 
j2 j2)) (* 216 h1 h2 (* h3 h3 h3) h5 (* h6 h6 h6 h6) j2) (* 12 h1 h2 (* h3 h3 h3
) h5 (* h6 h6 h6 h6)) (* 32 h1 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 368 h1 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2
 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1776 h1 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 4794 h1 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 8057 h1 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 
j2 j2 j2 j2 j2)) (* 8819 h1 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 
j2 j2)) (* 6354 h1 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 
2960 h1 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 845 h1 h2 (* h3 
h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2)) (* 131 h1 h2 (* h3 h3) (* h4 h4 h4 h4) 
(* h5 h5) j2) (* 8 h1 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5)) (* 64 h1 h2 (* h3 
h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 804 h1 h2 
(* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4118 h1 
h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 11600 h1 
h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 20105 h1 h2 
(* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 22470 h1 h2 (* h3 
h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 16367 h1 h2 (* h3 h3) (* h4
 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 7620 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5
 h5 h5) (* j2 j2 j2)) (* 2143 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2
)) (* 322 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) j2) (* 19 h1 h2 (* h3 h3) 
(* h4 h4 h4) (* h5 h5 h5)) (* 176 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1920 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8940 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5
) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 23520 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5
) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 38783 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2)) (* 41843 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* 
j2 j2 j2 j2 j2)) (* 29814 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 
j2)) (* 13766 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 3899 h1
 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 599 h1 h2 (* h3 h3) (* h4 
h4 h4) (* h5 h5) h6 j2) (* 36 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) h6) (* 32 
h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
400 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 2064 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 5874 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
10257 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 11467 
h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 8262 h1 h2 (* 
h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 3748 h1 h2 (* h3 h3) (* h4 
h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 1009 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 
h5) (* j2 j2)) (* 143 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) j2) (* 8 h1 h2 
(* h3 h3) (* h4 h4) (* h5 h5 h5 h5)) (* 288 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3236 h1 h2 (* h3 h3) (* h4 h4) (* 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 15442 h1 h2 (* h3 h3) (* h4 h4) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 41440 h1 h2 (* h3 h3) (* h4 h4) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 69365 h1 h2 (* h3 h3) (* h4 h4) (* 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 75557 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2)) (* 53992 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 
(* j2 j2 j2 j2)) (* 24786 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)
) (* 6901 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 1029 h1 h2 (* 
h3 h3) (* h4 h4) (* h5 h5 h5) h6 j2) (* 60 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5
) h6) (* 336 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 3552 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 16164 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 41796 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 68007 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6)
 (* j2 j2 j2 j2 j2 j2)) (* 72615 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* 51318 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2
 j2 j2 j2)) (* 23538 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2))
 (* 6627 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 1011 h1 h2 
(* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) j2) (* 60 h1 h2 (* h3 h3) (* h4 h4) (* 
h5 h5) (* h6 h6)) (* 112 h1 h2 (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 1200 h1 h2 (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 5556 h1 h2 (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 14586 h1 h2 (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2)) (* 23917 h1 h2 (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
25407 h1 h2 (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 17533 h1 h2 
(* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 7660 h1 h2 (* h3 h3) h4 (* 
h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 1995 h1 h2 (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* 
j2 j2)) (* 275 h1 h2 (* h3 h3) h4 (* h5 h5 h5 h5) h6 j2) (* 15 h1 h2 (* h3 h3) 
h4 (* h5 h5 h5 h5) h6) (* 384 h1 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2
 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4060 h1 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 18530 h1 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 48080 h1 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 78415 h1 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 83704 h1 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2)) (* 58883 h1 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) 
(* 26712 h1 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 7373 h1 h2 
(* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 1092 h1 h2 (* h3 h3) h4 (* h5 
h5 h5) (* h6 h6) j2) (* 63 h1 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6)) (* 272 h1 
h2 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
2816 h1 h2 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 12612 h1 h2 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 32208 h1 h2 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
51893 h1 h2 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 54977 
h1 h2 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 38610 h1 h2 (* 
h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 17618 h1 h2 (* h3 h3) h4 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 4937 h1 h2 (* h3 h3) h4 (* h5 h5) (* h6 
h6 h6) (* j2 j2)) (* 749 h1 h2 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) j2) (* 44 h1 
h2 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6)) (* 80 h1 h2 (* h3 h3) (* h5 h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 800 h1 h2 (* h3 h3) (* h5 h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3492 h1 h2 (* h3 h3) (* h5 h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 8712 h1 h2 (* h3 h3) (* h5 h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 13660 h1 h2 (* h3 h3) (* h5 h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 13940 h1 h2 (* h3 h3) (* h5 h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 9271 h1 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2)) (* 3912 h1 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2))
 (* 986 h1 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 132 h1 h2 (* h3 
h3) (* h5 h5 h5 h5) (* h6 h6) j2) (* 7 h1 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6)
) (* 160 h1 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2
 j2)) (* 1628 h1 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 7206 h1 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 18240 h1 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 29155 h1 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 30617 h1 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 21258 
h1 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 9546 h1 h2 (* h3 
h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 2615 h1 h2 (* h3 h3) (* h5 h5 h5)
 (* h6 h6 h6) (* j2 j2)) (* 385 h1 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) j2) 
(* 22 h1 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6)) (* 80 h1 h2 (* h3 h3) (* h5 h5)
 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 816 h1 h2 (* h3 h3) (* h5
 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3612 h1 h2 (* h3 h3) (* 
h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 9138 h1 h2 (* h3 h3) (* 
h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 14612 h1 h2 (* h3 h3) (* h5 
h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 15386 h1 h2 (* h3 h3) (* h5 h5) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 10752 h1 h2 (* h3 h3) (* h5 h5) (* h6 h6 
h6 h6) (* j2 j2 j2 j2)) (* 4886 h1 h2 (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 
j2 j2)) (* 1364 h1 h2 (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 206 h1 
h2 (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) j2) (* 12 h1 h2 (* h3 h3) (* h5 h5) (* h6
 h6 h6 h6)) (* 8 h1 h2 h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 84 h1 h2 h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 390 h1 h2 h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 1047 h1 h2 h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
1788 h1 h2 h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2015 h1 h2 
h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 1504 h1 h2 h3 (* h4 h4 h4
 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 725 h1 h2 h3 (* h4 h4 h4 h4) (* h5 h5 h5) 
(* j2 j2 j2)) (* 212 h1 h2 h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2)) (* 33 h1 
h2 h3 (* h4 h4 h4 h4) (* h5 h5 h5) j2) (* 2 h1 h2 h3 (* h4 h4 h4 h4) (* h5 h5 h5
)) (* 8 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (* 84 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
390 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1047 
h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1788 h1 h2 h3
 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2015 h1 h2 h3 (* h4 h4 
h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 1504 h1 h2 h3 (* h4 h4 h4) (* h5 h5 
h5 h5) (* j2 j2 j2 j2)) (* 725 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2
)) (* 212 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 33 h1 h2 h3 (* h4 
h4 h4) (* h5 h5 h5 h5) j2) (* 2 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5 h5)) (* 48 h1 
h2 h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 484 h1 
h2 h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2162 h1 h2
 h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 5602 h1 h2 h3 
(* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 9267 h1 h2 h3 (* h4 h4
 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 10152 h1 h2 h3 (* h4 h4 h4) (* h5
 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 7389 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* 
j2 j2 j2 j2)) (* 3482 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 997
 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 152 h1 h2 h3 (* h4 h4 h4) 
(* h5 h5 h5) h6 j2) (* 9 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5) h6) (* 40 h1 h2 h3 
(* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 400 h1 h2 h3 
(* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1772 h1 h2 h3 
(* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4555 h1 h2 h3 (* h4
 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 7479 h1 h2 h3 (* h4 h4) (* 
h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 8137 h1 h2 h3 (* h4 h4) (* h5 h5 h5 h5
) h6 (* j2 j2 j2 j2 j2)) (* 5885 h1 h2 h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 
j2 j2)) (* 2757 h1 h2 h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 785 h1 h2
 h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 119 h1 h2 h3 (* h4 h4) (* h5 h5 
h5 h5) h6 j2) (* 7 h1 h2 h3 (* h4 h4) (* h5 h5 h5 h5) h6) (* 96 h1 h2 h3 (* h4 
h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 948 h1 h2 h3 
(* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4146 h1 h2 
h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 10524 h1 h2 
h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 17073 h1 h2 h3 
(* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 18366 h1 h2 h3 (* h4 
h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 13143 h1 h2 h3 (* h4 h4) (* h5
 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 6096 h1 h2 h3 (* h4 h4) (* h5 h5 h5) (* h6
 h6) (* j2 j2 j2)) (* 1719 h1 h2 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2)) 
(* 258 h1 h2 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) j2) (* 15 h1 h2 h3 (* h4 h4) 
(* h5 h5 h5) (* h6 h6)) (* 56 h1 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 548 h1 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 2374 h1 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2
 j2 j2 j2 j2)) (* 5969 h1 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 9594 h1 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
10229 h1 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 7258 h1 h2 h3
 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 3339 h1 h2 h3 h4 (* h5 h5 h5 
h5) (* h6 h6) (* j2 j2 j2)) (* 934 h1 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 
j2)) (* 139 h1 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6) j2) (* 8 h1 h2 h3 h4 (* h5 h5 
h5 h5) (* h6 h6)) (* 80 h1 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 780 h1 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 3366 h1 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 8430 h1 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2))
 (* 13497 h1 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 14336 
h1 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 10135 h1 h2 h3 h4 
(* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 4646 h1 h2 h3 h4 (* h5 h5 h5) (* 
h6 h6 h6) (* j2 j2 j2)) (* 1295 h1 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2))
 (* 192 h1 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6) j2) (* 11 h1 h2 h3 h4 (* h5 h5 h5)
 (* h6 h6 h6)) (* 24 h1 h2 h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 232 h1 h2 h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 992 h1 h2 h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 2461 h1 h2 h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
3903 h1 h2 h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4107 h1 h2 
h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2877 h1 h2 h3 (* h5 h5 h5
 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1307 h1 h2 h3 (* h5 h5 h5 h5) (* h6 h6 h6)
 (* j2 j2 j2)) (* 361 h1 h2 h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 53 h1 
h2 h3 (* h5 h5 h5 h5) (* h6 h6 h6) j2) (* 3 h1 h2 h3 (* h5 h5 h5 h5) (* h6 h6 h6
)) (* 24 h1 h2 h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 232 h1 h2 h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 992 h1 h2 h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
2461 h1 h2 h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3903 h1 
h2 h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4107 h1 h2 h3 (* h5
 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2877 h1 h2 h3 (* h5 h5 h5) (* h6 
h6 h6 h6) (* j2 j2 j2 j2)) (* 1307 h1 h2 h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 
j2 j2)) (* 361 h1 h2 h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 53 h1 h2 h3 
(* h5 h5 h5) (* h6 h6 h6 h6) j2) (* 3 h1 h2 h3 (* h5 h5 h5) (* h6 h6 h6 h6)) (* 
32 h1 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 304 h1 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (* 1272 h1 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 3080 h1 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
4764 h1 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 4896 h1
 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 3364 h1 (* h3 h3 
h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 1512 h1 (* h3 h3 h3 h3) (* h4 
h4 h4) (* h5 h5) (* j2 j2 j2)) (* 420 h1 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) 
(* j2 j2)) (* 64 h1 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) j2) (* 4 h1 (* h3 h3 
h3 h3) (* h4 h4 h4) (* h5 h5)) (* 32 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 304 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 
h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1256 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2960 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 4384 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 
h5) (* j2 j2 j2 j2 j2 j2)) (* 4236 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* 
j2 j2 j2 j2 j2)) (* 2682 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 
j2)) (* 1088 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 268 h1 
(* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 36 h1 (* h3 h3 h3 h3) (* h4
 h4) (* h5 h5 h5) j2) (* 2 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5)) (* 128 h1 
(* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
1216 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 5088 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 12320 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
19056 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 19584 
h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 13456 h1 (* h3 
h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 6048 h1 (* h3 h3 h3 h3) (* 
h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 1680 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5)
 h6 (* j2 j2)) (* 256 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 j2) (* 16 h1 (* 
h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6) (* 96 h1 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6
 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 912 h1 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6
 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3768 h1 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 8880 h1 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2
 j2 j2 j2 j2 j2 j2)) (* 13152 h1 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2)) (* 12708 h1 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) 
(* 8046 h1 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 3264 h1 (* h3 
h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 804 h1 (* h3 h3 h3 h3) h4 (* h5 h5
 h5) h6 (* j2 j2)) (* 108 h1 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 j2) (* 6 h1 (* 
h3 h3 h3 h3) h4 (* h5 h5 h5) h6) (* 160 h1 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1520 h1 (* h3 h3 h3 h3) h4 (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 6360 h1 (* h3 h3 h3 h3) h4 (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 15400 h1 (* h3 h3 h3 h3) h4 (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 23820 h1 (* h3 h3 h3 h3) h4 (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 24480 h1 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6)
 (* j2 j2 j2 j2 j2)) (* 16820 h1 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2
 j2 j2)) (* 7560 h1 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 2100
 h1 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 320 h1 (* h3 h3 h3 h3) 
h4 (* h5 h5) (* h6 h6) j2) (* 20 h1 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6)) (* 
64 h1 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 608 h1 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (* 2512 h1 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 5920 h1 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
8768 h1 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 8472 h1
 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 5364 h1 (* h3 h3 
h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 2176 h1 (* h3 h3 h3 h3) (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2)) (* 536 h1 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) 
(* j2 j2)) (* 72 h1 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) j2) (* 4 h1 (* h3 h3 
h3 h3) (* h5 h5 h5) (* h6 h6)) (* 64 h1 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 608 h1 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2544 h1 (* h3 h3 h3 h3) (* h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6160 h1 (* h3 h3 h3 h3) (* h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 9528 h1 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 9792 h1 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2)) (* 6728 h1 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2)) (* 3024 h1 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 840 h1 
(* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 128 h1 (* h3 h3 h3 h3) (* 
h5 h5) (* h6 h6 h6) j2) (* 8 h1 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6)) (* 16 h1
 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
152 h1 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 636 h1 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 1540 h1 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
2382 h1 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2448 h1
 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 1682 h1 (* h3 h3 
h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 756 h1 (* h3 h3 h3) (* h4 h4 
h4 h4) (* h5 h5) (* j2 j2 j2)) (* 210 h1 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) 
(* j2 j2)) (* 32 h1 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) j2) (* 2 h1 (* h3 h3 
h3) (* h4 h4 h4 h4) (* h5 h5)) (* 32 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 304 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 
h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1272 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3080 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 4764 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 
h5) (* j2 j2 j2 j2 j2 j2)) (* 4896 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* 
j2 j2 j2 j2 j2)) (* 3364 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 
j2)) (* 1512 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 420 h1 
(* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2)) (* 64 h1 (* h3 h3 h3) (* h4 h4
 h4) (* h5 h5 h5) j2) (* 4 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5)) (* 80 h1 
(* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 760
 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
3180 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
7700 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
11910 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 12240 
h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 8410 h1 (* h3 
h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 3780 h1 (* h3 h3 h3) (* h4 
h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 1050 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5)
 h6 (* j2 j2)) (* 160 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 j2) (* 10 h1 (* 
h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6) (* 16 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5
 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 152 h1 (* h3 h3 h3) (* h4 h4) (* h5 
h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 628 h1 (* h3 h3 h3) (* h4 h4) (* h5
 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1480 h1 (* h3 h3 h3) (* h4 h4) (* h5 
h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 2192 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 
h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2118 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) 
(* j2 j2 j2 j2 j2)) (* 1341 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 
j2 j2)) (* 544 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 134 h1
 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 18 h1 (* h3 h3 h3) (* h4 
h4) (* h5 h5 h5 h5) j2) (* h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5)) (* 128 h1 
(* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
1216 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 5088 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 12320 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
19056 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 19584 
h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 13456 h1 (* h3 
h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 6048 h1 (* h3 h3 h3) (* h4 
h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 1680 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5)
 h6 (* j2 j2)) (* 256 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 j2) (* 16 h1 (* 
h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6) (* 144 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1368 h1 (* h3 h3 h3) (* h4 h4) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 5724 h1 (* h3 h3 h3) (* 
h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 13860 h1 (* h3 h3 h3)
 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 21438 h1 (* h3 h3 h3
) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 22032 h1 (* h3 h3 h3) 
(* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 15138 h1 (* h3 h3 h3) (* h4
 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 6804 h1 (* h3 h3 h3) (* h4 h4) (* 
h5 h5) (* h6 h6) (* j2 j2 j2)) (* 1890 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6
 h6) (* j2 j2)) (* 288 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) j2) (* 18 
h1 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6)) (* 48 h1 (* h3 h3 h3) h4 (* h5 h5
 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 456 h1 (* h3 h3 h3) h4 (* h5 h5
 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1884 h1 (* h3 h3 h3) h4 (* h5 h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4440 h1 (* h3 h3 h3) h4 (* h5 h5 h5 h5
) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 6576 h1 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2)) (* 6354 h1 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2
 j2)) (* 4023 h1 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 1632 h1 
(* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 402 h1 (* h3 h3 h3) h4 (* h5
 h5 h5 h5) h6 (* j2 j2)) (* 54 h1 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 j2) (* 3 h1
 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6) (* 160 h1 (* h3 h3 h3) h4 (* h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1520 h1 (* h3 h3 h3) h4 (* h5 h5 h5
) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 6360 h1 (* h3 h3 h3) h4 (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 15400 h1 (* h3 h3 h3) h4 (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 23820 h1 (* h3 h3 h3) h4 (* h5 h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 24480 h1 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6
 h6) (* j2 j2 j2 j2 j2)) (* 16820 h1 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2)) (* 7560 h1 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) 
(* 2100 h1 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 320 h1 (* h3 h3 
h3) h4 (* h5 h5 h5) (* h6 h6) j2) (* 20 h1 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6
)) (* 112 h1 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 1064 h1 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 4452 h1 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 10780 h1 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 16674 h1 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)
) (* 17136 h1 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
11774 h1 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 5292 h1 (* 
h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 1470 h1 (* h3 h3 h3) h4 (* 
h5 h5) (* h6 h6 h6) (* j2 j2)) (* 224 h1 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) 
j2) (* 14 h1 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6)) (* 32 h1 (* h3 h3 h3) (* h5
 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 304 h1 (* h3 h3 h3) 
(* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1256 h1 (* h3 h3 h3
) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2960 h1 (* h3 h3 h3)
 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4384 h1 (* h3 h3 h3) (* 
h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4236 h1 (* h3 h3 h3) (* h5 h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2682 h1 (* h3 h3 h3) (* h5 h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2)) (* 1088 h1 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 
j2 j2)) (* 268 h1 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 36 h1 (* 
h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) j2) (* 2 h1 (* h3 h3 h3) (* h5 h5 h5 h5) (* 
h6 h6)) (* 64 h1 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 608 h1 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2 j2)) (* 2544 h1 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 6160 h1 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 9528 h1 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2))
 (* 9792 h1 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 6728 
h1 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 3024 h1 (* h3 h3 
h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 840 h1 (* h3 h3 h3) (* h5 h5 h5) 
(* h6 h6 h6) (* j2 j2)) (* 128 h1 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) j2) (* 
8 h1 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6)) (* 32 h1 (* h3 h3 h3) (* h5 h5) (* 
h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 304 h1 (* h3 h3 h3) (* h5 h5)
 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1272 h1 (* h3 h3 h3) (* h5 
h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3080 h1 (* h3 h3 h3) (* h5 
h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4764 h1 (* h3 h3 h3) (* h5 h5) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4896 h1 (* h3 h3 h3) (* h5 h5) (* h6 
h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 3364 h1 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) 
(* j2 j2 j2 j2)) (* 1512 h1 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2))
 (* 420 h1 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 64 h1 (* h3 h3 
h3) (* h5 h5) (* h6 h6 h6 h6) j2) (* 4 h1 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6)
) (* 8 h1 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 76 h1 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 318 h1 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 770 h1 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 1191 h1 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1224
 h1 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 841 h1 (* h3 
h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 378 h1 (* h3 h3) (* h4 h4 
h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 105 h1 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 
h5) (* j2 j2)) (* 16 h1 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) j2) (* h1 (* h3 
h3) (* h4 h4 h4 h4) (* h5 h5 h5)) (* 8 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5)
 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 76 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 
h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 318 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5
 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 770 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 
h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1191 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2)) (* 1224 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 
j2 j2 j2 j2)) (* 841 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) 
(* 378 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 105 h1 (* h3 
h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 16 h1 (* h3 h3) (* h4 h4 h4) (* 
h5 h5 h5 h5) j2) (* h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5)) (* 40 h1 (* h3 h3
) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 380 h1 (* 
h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1590 h1 
(* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3850 h1 
(* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 5955 h1 (* 
h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 6120 h1 (* h3 h3) 
(* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 4205 h1 (* h3 h3) (* h4 h4 
h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 1890 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 
h5) h6 (* j2 j2 j2)) (* 525 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2))
 (* 80 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 j2) (* 5 h1 (* h3 h3) (* h4 h4 
h4) (* h5 h5 h5) h6) (* 32 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2
 j2 j2 j2 j2 j2 j2 j2)) (* 304 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 1272 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 3080 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2)) (* 4764 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2)) (* 4896 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 
j2 j2)) (* 3364 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 
1512 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 420 h1 (* h3 h3)
 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 64 h1 (* h3 h3) (* h4 h4) (* h5 h5 
h5 h5) h6 j2) (* 4 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6) (* 72 h1 (* h3 h3)
 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 684 h1 
(* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
2862 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 6930 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 10719 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 11016 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
7569 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 3402 h1 
(* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 945 h1 (* h3 h3) (* 
h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 144 h1 (* h3 h3) (* h4 h4) (* h5 h5 
h5) (* h6 h6) j2) (* 9 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6)) (* 40 h1 
(* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 380
 h1 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
1590 h1 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
3850 h1 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 5955
 h1 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6120 h1 (* 
h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 4205 h1 (* h3 h3) h4 
(* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 1890 h1 (* h3 h3) h4 (* h5 h5 h5 
h5) (* h6 h6) (* j2 j2 j2)) (* 525 h1 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* 
j2 j2)) (* 80 h1 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) j2) (* 5 h1 (* h3 h3) h4
 (* h5 h5 h5 h5) (* h6 h6)) (* 56 h1 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 532 h1 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2226 h1 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 5390 h1 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 8337 h1 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 8568 h1 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2)) (* 5887 h1 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2))
 (* 2646 h1 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 735 h1 (* h3
 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 112 h1 (* h3 h3) h4 (* h5 h5 h5)
 (* h6 h6 h6) j2) (* 7 h1 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6)) (* 16 h1 (* h3
 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 152 h1 
(* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 636 h1
 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1540 h1 
(* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2382 h1 (* 
h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2448 h1 (* h3 h3) 
(* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1682 h1 (* h3 h3) (* h5 h5 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 756 h1 (* h3 h3) (* h5 h5 h5 h5) (* h6 
h6 h6) (* j2 j2 j2)) (* 210 h1 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2))
 (* 32 h1 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) j2) (* 2 h1 (* h3 h3) (* h5 h5 
h5 h5) (* h6 h6 h6)) (* 16 h1 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2
 j2 j2 j2 j2 j2 j2 j2)) (* 152 h1 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 636 h1 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 1540 h1 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 2382 h1 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 2448 h1 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 
j2)) (* 1682 h1 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 756 
h1 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 210 h1 (* h3 h3) (* 
h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 32 h1 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6
 h6) j2) (* 2 h1 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6)) (* 768 (* h2 h2 h2 h2) 
(* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 3456 (* h2 h2 h2 h2) (* 
h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 6128 (* h2 h2 h2 h2) (* h3 h3 
h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 5472 (* h2 h2 h2 h2) (* h3 h3 h3) (* h4 
h4) h5 (* j2 j2 j2 j2)) (* 2620 (* h2 h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 
j2 j2)) (* 668 (* h2 h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2)) (* 84 (* h2 
h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 j2) (* 4 (* h2 h2 h2 h2) (* h3 h3 h3) (* h4 
h4) h5) (* 576 (* h2 h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2
)) (* 2736 (* h2 h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 
5016 (* h2 h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 4476 (* h2
 h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 2038 (* h2 h2 h2 h2) 
(* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 466 (* h2 h2 h2 h2) (* h3 h3 h3) h4 
(* h5 h5) (* j2 j2)) (* 50 (* h2 h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) j2) (* 2 
(* h2 h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5)) (* 1536 (* h2 h2 h2 h2) (* h3 h3 h3) 
h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 6912 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 h6
 (* j2 j2 j2 j2 j2 j2)) (* 12256 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 
j2 j2 j2)) (* 10944 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 
5240 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 1336 (* h2 h2 h2 h2)
 (* h3 h3 h3) h4 h5 h6 (* j2 j2)) (* 168 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 h6 
j2) (* 8 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 h6) (* 576 (* h2 h2 h2 h2) (* h3 h3 
h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2736 (* h2 h2 h2 h2) (* h3 h3 h3) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 5016 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 
h5) h6 (* j2 j2 j2 j2 j2)) (* 4476 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* 
j2 j2 j2 j2)) (* 2038 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2)) 
(* 466 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2)) (* 50 (* h2 h2 h2 h2
) (* h3 h3 h3) (* h5 h5) h6 j2) (* 2 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6) 
(* 768 (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
3456 (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6128 
(* h2 h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 5472 (* h2 h2 
h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 2620 (* h2 h2 h2 h2) (* h3 
h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 668 (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* h6 
h6) (* j2 j2)) (* 84 (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) j2) (* 4 (* h2 h2
 h2 h2) (* h3 h3 h3) h5 (* h6 h6)) (* 192 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4 h4)
 h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1104 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4 h4) 
h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 2648 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 
(* j2 j2 j2 j2 j2 j2)) (* 3436 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 
j2 j2 j2 j2)) (* 2614 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2))
 (* 1180 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 304 (* h2 h2
 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2)) (* 40 (* h2 h2 h2 h2) (* h3 h3) (* 
h4 h4 h4) h5 j2) (* 2 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5) (* 384 (* h2 h2
 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2208 (* h2
 h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 5296 (* h2
 h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 6872 (* h2 h2
 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 5228 (* h2 h2 h2 h2
) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 2360 (* h2 h2 h2 h2) (* h3 
h3) (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 608 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4)
 (* h5 h5) (* j2 j2)) (* 80 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) j2) 
(* 4 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5)) (* 576 (* h2 h2 h2 h2) (* h3
 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3312 (* h2 h2 h2 h2) (* h3 
h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 7944 (* h2 h2 h2 h2) (* h3 h3) 
(* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 10308 (* h2 h2 h2 h2) (* h3 h3) (* h4 
h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 7842 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 
(* j2 j2 j2 j2)) (* 3540 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2))
 (* 912 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 120 (* h2 h2 h2 
h2) (* h3 h3) (* h4 h4) h5 h6 j2) (* 6 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6
) (* 144 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 864 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
2136 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2808 
(* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 2113 (* h2 h2 
h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 912 (* h2 h2 h2 h2) (* h3 
h3) h4 (* h5 h5 h5) (* j2 j2 j2)) (* 214 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5 
h5) (* j2 j2)) (* 24 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) j2) (* (* h2 h2 
h2 h2) (* h3 h3) h4 (* h5 h5 h5)) (* 768 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4416 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 10592 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 13744 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* 10456 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)
) (* 4720 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 1216 (* h2 
h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 160 (* h2 h2 h2 h2) (* h3 h3) 
h4 (* h5 h5) h6 j2) (* 8 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6) (* 576 (* h2
 h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3312 (* h2 
h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 7944 (* h2 h2 
h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 10308 (* h2 h2 h2 h2)
 (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 7842 (* h2 h2 h2 h2) (* h3 h3)
 h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 3540 (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* h6 
h6) (* j2 j2 j2)) (* 912 (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2)) 
(* 120 (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) j2) (* 6 (* h2 h2 h2 h2) (* h3 
h3) h4 h5 (* h6 h6)) (* 144 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 864 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2
 j2 j2 j2 j2)) (* 2136 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2)) (* 2808 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) 
(* 2113 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 912 (* h2 
h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 214 (* h2 h2 h2 h2) (* h3 
h3) (* h5 h5 h5) h6 (* j2 j2)) (* 24 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 
j2) (* (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6) (* 384 (* h2 h2 h2 h2) (* h3 
h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2208 (* h2 h2 h2 h2) (* 
h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 5296 (* h2 h2 h2 h2) (* 
h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6872 (* h2 h2 h2 h2) (* h3 
h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 5228 (* h2 h2 h2 h2) (* h3 h3) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 2360 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5)
 (* h6 h6) (* j2 j2 j2)) (* 608 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) 
(* j2 j2)) (* 80 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) j2) (* 4 (* h2 h2
 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6)) (* 192 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6
 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1104 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2648 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 3436 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* 
j2 j2 j2 j2 j2)) (* 2614 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 
j2)) (* 1180 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 304 (* 
h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 40 (* h2 h2 h2 h2) (* h3 h3
) h5 (* h6 h6 h6) j2) (* 2 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6)) (* 48 (* 
h2 h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 336 
(* h2 h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1016 
(* h2 h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1736 (* 
h2 h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1839 (* h2 h2 
h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 1245 (* h2 h2 h2 h2) h3 
(* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 534 (* h2 h2 h2 h2) h3 (* h4 h4 h4) 
(* h5 h5) (* j2 j2 j2)) (* 138 (* h2 h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 
j2)) (* 19 (* h2 h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) j2) (* (* h2 h2 h2 h2) h3 
(* h4 h4 h4) (* h5 h5)) (* 48 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2
 j2 j2 j2 j2 j2 j2 j2)) (* 336 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 1016 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 
j2 j2 j2 j2 j2 j2)) (* 1736 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 
j2 j2 j2 j2)) (* 1839 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 
j2)) (* 1245 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 534 
(* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 138 (* h2 h2 h2 h2) 
h3 (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 19 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5
 h5) j2) (* (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5)) (* 144 (* h2 h2 h2 h2) h3
 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1008 (* h2 h2 h2 h2) 
h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3048 (* h2 h2 h2 h2) 
h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 5208 (* h2 h2 h2 h2) h3 
(* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 5517 (* h2 h2 h2 h2) h3 (* h4 
h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 3735 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 
h5) h6 (* j2 j2 j2 j2)) (* 1602 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 
j2 j2)) (* 414 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 57 (* h2 
h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 j2) (* 3 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 
h5) h6) (* 96 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 672 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 2032 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 3472 
(* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 3678 (* h2 h2 h2
 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 2490 (* h2 h2 h2 h2) h3 h4 (* 
h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 1068 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* 
j2 j2 j2)) (* 276 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2)) (* 38 (* h2 
h2 h2 h2) h3 h4 (* h5 h5 h5) h6 j2) (* 2 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) h6) 
(* 144 (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (* 1008 (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 3048 (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
5208 (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 5517 
(* h2 h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 3735 (* h2 h2 
h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 1602 (* h2 h2 h2 h2) h3 h4 
(* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 414 (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* h6 
h6) (* j2 j2)) (* 57 (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) j2) (* 3 (* h2 h2
 h2 h2) h3 h4 (* h5 h5) (* h6 h6)) (* 48 (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 336 (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1016 (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1736 (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 1839 (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2)) (* 1245 (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2))
 (* 534 (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 138 (* h2 h2 
h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 19 (* h2 h2 h2 h2) h3 (* h5 h5 h5
) (* h6 h6) j2) (* (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6)) (* 48 (* h2 h2 h2 
h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 336 (* h2 h2 h2
 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1016 (* h2 h2 h2 
h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1736 (* h2 h2 h2 h2) 
h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1839 (* h2 h2 h2 h2) h3 (* 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1245 (* h2 h2 h2 h2) h3 (* h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2)) (* 534 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* 
j2 j2 j2)) (* 138 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 19 (* 
h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) j2) (* (* h2 h2 h2 h2) h3 (* h5 h5) (* h6
 h6 h6)) (* 768 (* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 
j2)) (* 3840 (* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) 
(* 7664 (* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 7768 
(* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 4208 (* h2 h2 h2) 
(* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 1184 (* h2 h2 h2) (* h3 h3 h3 h3) 
(* h4 h4) h5 (* j2 j2)) (* 160 (* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 j2) (* 
8 (* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5) (* 576 (* h2 h2 h2) (* h3 h3 h3 h3)
 h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 3024 (* h2 h2 h2) (* h3 h3 h3 h3) h4 
(* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 6240 (* h2 h2 h2) (* h3 h3 h3 h3) h4 (* h5 
h5) (* j2 j2 j2 j2 j2)) (* 6372 (* h2 h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 
j2 j2 j2)) (* 3328 (* h2 h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 
840 (* h2 h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2)) (* 96 (* h2 h2 h2) (* 
h3 h3 h3 h3) h4 (* h5 h5) j2) (* 4 (* h2 h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5)) 
(* 1536 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 7680 
(* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 15328 (* h2 h2 
h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 15536 (* h2 h2 h2) (* h3 h3 
h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 8416 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 h6 
(* j2 j2 j2)) (* 2368 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2)) (* 320 
(* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 h6 j2) (* 16 (* h2 h2 h2) (* h3 h3 h3 h3) h4 
h5 h6) (* 576 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)
) (* 3024 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
6240 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 6372 (* h2
 h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 3328 (* h2 h2 h2) (* h3
 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 840 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 
h5) h6 (* j2 j2)) (* 96 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 j2) (* 4 (* h2
 h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6) (* 768 (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3840 (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 7664 (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* 
j2 j2 j2 j2 j2)) (* 7768 (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 
j2)) (* 4208 (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 1184 (* 
h2 h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2)) (* 160 (* h2 h2 h2) (* h3 h3 
h3 h3) h5 (* h6 h6) j2) (* 8 (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6)) (* 384 
(* h2 h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2400 
(* h2 h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 6304 (* 
h2 h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 9016 (* h2 h2 
h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 7592 (* h2 h2 h2) (* h3 
h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 3792 (* h2 h2 h2) (* h3 h3 h3) (* h4 
h4 h4) h5 (* j2 j2 j2)) (* 1072 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 
j2)) (* 152 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 j2) (* 8 (* h2 h2 h2) (* 
h3 h3 h3) (* h4 h4 h4) h5) (* 768 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4896 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 
h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 12824 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) (* h5
 h5) (* j2 j2 j2 j2 j2 j2)) (* 17928 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 
h5) (* j2 j2 j2 j2 j2)) (* 14554 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) 
(* j2 j2 j2 j2)) (* 6988 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 
j2)) (* 1920 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 268 (* 
h2 h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) j2) (* 14 (* h2 h2 h2) (* h3 h3 h3) 
(* h4 h4) (* h5 h5)) (* 1152 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 7200 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 
j2 j2 j2 j2 j2)) (* 18912 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 
j2 j2 j2)) (* 27048 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)
) (* 22776 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 11376 
(* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 3216 (* h2 h2 h2) (* 
h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 456 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) 
h5 h6 j2) (* 24 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6) (* 288 (* h2 h2 h2) 
(* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1944 (* h2 h2 h2) 
(* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 5316 (* h2 h2 h2) (* 
h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 7614 (* h2 h2 h2) (* h3 h3 
h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 6185 (* h2 h2 h2) (* h3 h3 h3) h4 (* 
h5 h5 h5) (* j2 j2 j2 j2)) (* 2895 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* 
j2 j2 j2)) (* 751 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2)) (* 91 (* 
h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) j2) (* 4 (* h2 h2 h2) (* h3 h3 h3) h4 (* 
h5 h5 h5)) (* 1536 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 9792 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 25648 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)
) (* 35856 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
29108 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 13976 (* h2 
h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 3840 (* h2 h2 h2) (* h3 h3 
h3) h4 (* h5 h5) h6 (* j2 j2)) (* 536 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 
j2) (* 28 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6) (* 1152 (* h2 h2 h2) (* h3 
h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 7200 (* h2 h2 h2) (* h3 
h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 18912 (* h2 h2 h2) (* h3 h3 
h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 27048 (* h2 h2 h2) (* h3 h3 h3) h4
 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 22776 (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* h6
 h6) (* j2 j2 j2 j2)) (* 11376 (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 
j2 j2)) (* 3216 (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 456 (* 
h2 h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) j2) (* 24 (* h2 h2 h2) (* h3 h3 h3) h4 h5
 (* h6 h6)) (* 288 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 1944 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 5316 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2))
 (* 7614 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 6185 
(* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 2895 (* h2 h2 h2) 
(* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 751 (* h2 h2 h2) (* h3 h3 h3) (* 
h5 h5 h5) h6 (* j2 j2)) (* 91 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 j2) (* 4
 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6) (* 768 (* h2 h2 h2) (* h3 h3 h3) (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4896 (* h2 h2 h2) (* h3 h3 h3) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 12824 (* h2 h2 h2) (* h3 h3 h3)
 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 17928 (* h2 h2 h2) (* h3 h3 h3) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 14554 (* h2 h2 h2) (* h3 h3 h3) (* h5
 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 6988 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* 
h6 h6) (* j2 j2 j2)) (* 1920 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2
 j2)) (* 268 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) j2) (* 14 (* h2 h2 h2
) (* h3 h3 h3) (* h5 h5) (* h6 h6)) (* 384 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2400 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 6304 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 9016 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 
j2 j2 j2 j2)) (* 7592 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2))
 (* 3792 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 1072 (* h2 
h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 152 (* h2 h2 h2) (* h3 h3 h3) 
h5 (* h6 h6 h6) j2) (* 8 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6)) (* 96 (* h2 
h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 600 (* h2 h2
 h2) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 1576 (* h2 h2 h2)
 (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 2254 (* h2 h2 h2) (* h3 
h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 1898 (* h2 h2 h2) (* h3 h3) (* h4 
h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 948 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 
(* j2 j2 j2)) (* 268 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2)) (* 38 
(* h2 h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 j2) (* 2 (* h2 h2 h2) (* h3 h3) (* h4 
h4 h4 h4) h5) (* 144 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 1200 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 4224 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 8252 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* 
j2 j2 j2 j2 j2 j2)) (* 9847 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 
j2 j2 j2 j2)) (* 7414 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 
j2)) (* 3496 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 982 
(* h2 h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 145 (* h2 h2 h2) (* 
h3 h3) (* h4 h4 h4) (* h5 h5) j2) (* 8 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) (* h5
 h5)) (* 384 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 2400 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2))
 (* 6304 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 
9016 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 7592 (* h2
 h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 3792 (* h2 h2 h2) (* h3
 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 1072 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4
) h5 h6 (* j2 j2)) (* 152 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 j2) (* 8 (* 
h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6) (* 144 (* h2 h2 h2) (* h3 h3) (* h4 h4) 
(* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1200 (* h2 h2 h2) (* h3 h3) (* 
h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4200 (* h2 h2 h2) (* h3 h3) 
(* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 8120 (* h2 h2 h2) (* h3 h3) 
(* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 9549 (* h2 h2 h2) (* h3 h3) (* 
h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 7059 (* h2 h2 h2) (* h3 h3) (* h4 h4)
 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 3258 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5
 h5) (* j2 j2 j2)) (* 894 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2
)) (* 129 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) j2) (* 7 (* h2 h2 h2) 
(* h3 h3) (* h4 h4) (* h5 h5 h5)) (* 432 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3600 (* h2 h2 h2) (* h3 h3) (* h4 h4) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 12672 (* h2 h2 h2) (* h3 h3) (* h4 
h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 24756 (* h2 h2 h2) (* h3 h3) (* h4
 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 29541 (* h2 h2 h2) (* h3 h3) (* h4 
h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 22242 (* h2 h2 h2) (* h3 h3) (* h4 h4) 
(* h5 h5) h6 (* j2 j2 j2 j2)) (* 10488 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5
) h6 (* j2 j2 j2)) (* 2946 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 
j2)) (* 435 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 j2) (* 24 (* h2 h2 h2)
 (* h3 h3) (* h4 h4) (* h5 h5) h6) (* 576 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3600 (* h2 h2 h2) (* h3 h3) (* h4 h4) 
h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 9456 (* h2 h2 h2) (* h3 h3) (* h4 h4) 
h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 13524 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5
 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 11388 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* 
h6 h6) (* j2 j2 j2 j2)) (* 5688 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6) 
(* j2 j2 j2)) (* 1608 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2)) 
(* 228 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6) j2) (* 12 (* h2 h2 h2) (* 
h3 h3) (* h4 h4) h5 (* h6 h6)) (* 72 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 468 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 1266 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* 
j2 j2 j2 j2 j2 j2)) (* 1839 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 
j2 j2 j2)) (* 1541 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2)) 
(* 742 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2)) (* 192 (* h2 h2 
h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2)) (* 23 (* h2 h2 h2) (* h3 h3) h4 (* 
h5 h5 h5 h5) j2) (* (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5)) (* 288 (* h2 h2 
h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2400 (* h2 
h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 8400 (* h2 
h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 16240 (* h2 h2 
h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 19098 (* h2 h2 h2) 
(* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 14118 (* h2 h2 h2) (* h3 h3)
 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 6516 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 
h5) h6 (* j2 j2 j2)) (* 1788 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2)
) (* 258 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 j2) (* 14 (* h2 h2 h2) (* h3 
h3) h4 (* h5 h5 h5) h6) (* 432 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3600 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 12672 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 24756 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 29541 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 22242 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* h6
 h6) (* j2 j2 j2 j2)) (* 10488 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* 
j2 j2 j2)) (* 2946 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 
435 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) j2) (* 24 (* h2 h2 h2) (* h3 
h3) h4 (* h5 h5) (* h6 h6)) (* 384 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 2400 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 6304 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 9016 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 
j2 j2)) (* 7592 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 
3792 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 1072 (* h2 h2 h2
) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2)) (* 152 (* h2 h2 h2) (* h3 h3) h4 h5 
(* h6 h6 h6) j2) (* 8 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6)) (* 72 (* h2 h2 
h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 468 (* h2 h2 h2
) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1266 (* h2 h2 h2) 
(* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 1839 (* h2 h2 h2) (* h3 
h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 1541 (* h2 h2 h2) (* h3 h3) (* h5 
h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 742 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 
(* j2 j2 j2)) (* 192 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 23 
(* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 j2) (* (* h2 h2 h2) (* h3 h3) (* h5 h5
 h5 h5) h6) (* 144 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 1200 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 4200 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 8120 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 9549 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2)) (* 7059 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)
) (* 3258 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 894 (* 
h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 129 (* h2 h2 h2) (* h3 
h3) (* h5 h5 h5) (* h6 h6) j2) (* 7 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6
)) (* 144 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 1200 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 4224 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 8252 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 9847 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)
) (* 7414 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 3496
 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 982 (* h2 h2 h2)
 (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 145 (* h2 h2 h2) (* h3 h3) (* h5
 h5) (* h6 h6 h6) j2) (* 8 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6)) (* 96 
(* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 600 
(* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1576 (* 
h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2254 (* h2 h2 
h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1898 (* h2 h2 h2) (* h3 
h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 948 (* h2 h2 h2) (* h3 h3) h5 (* h6 
h6 h6 h6) (* j2 j2 j2)) (* 268 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 
j2)) (* 38 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) j2) (* 2 (* h2 h2 h2) (* h3
 h3) h5 (* h6 h6 h6 h6)) (* 24 (* h2 h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 180 (* h2 h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 586 (* h2 h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 
j2 j2 j2 j2 j2 j2)) (* 1083 (* h2 h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 
j2 j2 j2 j2)) (* 1246 (* h2 h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 
j2)) (* 919 (* h2 h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 430 
(* h2 h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 121 (* h2 h2 h2) h3 
(* h4 h4 h4 h4) (* h5 h5) (* j2 j2)) (* 18 (* h2 h2 h2) h3 (* h4 h4 h4 h4) (* h5
 h5) j2) (* (* h2 h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5)) (* 48 (* h2 h2 h2) h3 (* 
h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 360 (* h2 h2 h2) h3 
(* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1172 (* h2 h2 h2) h3 
(* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 2166 (* h2 h2 h2) h3 (* 
h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2492 (* h2 h2 h2) h3 (* h4 h4 
h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 1838 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 
h5 h5) (* j2 j2 j2 j2)) (* 860 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 
j2 j2)) (* 242 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2)) (* 36 (* h2 
h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) j2) (* 2 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 
h5 h5)) (* 96 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 720 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2
 j2)) (* 2344 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)
) (* 4332 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
4984 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 3676 (* h2
 h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 1720 (* h2 h2 h2) h3 
(* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 484 (* h2 h2 h2) h3 (* h4 h4 h4) (* 
h5 h5) h6 (* j2 j2)) (* 72 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 j2) (* 4 
(* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6) (* 24 (* h2 h2 h2) h3 (* h4 h4) (* h5
 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 180 (* h2 h2 h2) h3 (* h4 h4) (* 
h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 586 (* h2 h2 h2) h3 (* h4 h4) (* h5
 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1083 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 
h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1246 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) 
(* j2 j2 j2 j2 j2)) (* 919 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2
 j2)) (* 430 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 121 (* 
h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 18 (* h2 h2 h2) h3 (* h4 h4
) (* h5 h5 h5 h5) j2) (* (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5)) (* 144 (* h2
 h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1080 (* 
h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3516 (* 
h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 6498 (* h2 
h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 7476 (* h2 h2 h2) 
h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 5514 (* h2 h2 h2) h3 (* h4 
h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 2580 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 
h5) h6 (* j2 j2 j2)) (* 726 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2))
 (* 108 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 j2) (* 6 (* h2 h2 h2) h3 (* h4
 h4) (* h5 h5 h5) h6) (* 144 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1080 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3516 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 6498 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 7476 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6)
 (* j2 j2 j2 j2 j2)) (* 5514 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2
 j2 j2 j2)) (* 2580 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) 
(* 726 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 108 (* h2 h2 
h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) j2) (* 6 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5
) (* h6 h6)) (* 48 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2
 j2 j2)) (* 360 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 1172 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
2166 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 2492 (* h2 
h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 1838 (* h2 h2 h2) h3 h4 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 860 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) h6
 (* j2 j2 j2)) (* 242 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 36 (* 
h2 h2 h2) h3 h4 (* h5 h5 h5 h5) h6 j2) (* 2 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) 
h6) (* 144 (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 1080 (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 3516 (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2))
 (* 6498 (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
7476 (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 5514 (* h2
 h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 2580 (* h2 h2 h2) h3 h4
 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 726 (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* 
h6 h6) (* j2 j2)) (* 108 (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) j2) (* 6 (* 
h2 h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6)) (* 96 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6
 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 720 (* h2 h2 h2) h3 h4 (* h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2344 (* h2 h2 h2) h3 h4 (* h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4332 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4984 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2)) (* 3676 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2)) (* 1720 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 484 
(* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 72 (* h2 h2 h2) h3 h4 
(* h5 h5) (* h6 h6 h6) j2) (* 4 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6)) (* 24
 (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
180 (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
586 (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1083 
(* h2 h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1246 (* h2 
h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 919 (* h2 h2 h2) h3 
(* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 430 (* h2 h2 h2) h3 (* h5 h5 h5 h5
) (* h6 h6) (* j2 j2 j2)) (* 121 (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2
 j2)) (* 18 (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) j2) (* (* h2 h2 h2) h3 (* 
h5 h5 h5 h5) (* h6 h6)) (* 48 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2
 j2 j2 j2 j2 j2 j2 j2)) (* 360 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 1172 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 2166 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 2492 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2)) (* 1838 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 860 
(* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 242 (* h2 h2 h2) h3 
(* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 36 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6
 h6) j2) (* 2 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6)) (* 24 (* h2 h2 h2) h3 
(* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 180 (* h2 h2 h2) h3
 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 586 (* h2 h2 h2) h3 
(* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1083 (* h2 h2 h2) h3 (* 
h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1246 (* h2 h2 h2) h3 (* h5 h5) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 919 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6
 h6) (* j2 j2 j2 j2)) (* 430 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 
j2)) (* 121 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 18 (* h2 h2 
h2) h3 (* h5 h5) (* h6 h6 h6 h6) j2) (* (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6
)) (* 192 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2))
 (* 1296 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 
3704 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 5808 
(* h2 h2) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 5400 (* h2 h2) 
(* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 2992 (* h2 h2) (* h3 h3 h3 
h3) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 936 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4 h4) 
h5 (* j2 j2)) (* 144 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4 h4) h5 j2) (* 8 (* h2 h2
) (* h3 h3 h3 h3) (* h4 h4 h4) h5) (* 384 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) 
(* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2592 (* h2 h2) (* h3 h3 h3 h3) (* h4 
h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 7216 (* h2 h2) (* h3 h3 h3 h3) (* h4 
h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 10704 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4
) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 9112 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) (* 
h5 h5) (* j2 j2 j2 j2)) (* 4464 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) 
(* j2 j2 j2)) (* 1200 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) 
(* 160 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) j2) (* 8 (* h2 h2) (* h3 h3
 h3 h3) (* h4 h4) (* h5 h5)) (* 576 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 h6 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3888 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 11112 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* 
j2 j2 j2 j2 j2 j2)) (* 17424 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 
j2 j2 j2)) (* 16200 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) 
(* 8976 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 2808 (* h2 h2
) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 432 (* h2 h2) (* h3 h3 h3 h3) 
(* h4 h4) h5 h6 j2) (* 24 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 h6) (* 144 (* 
h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1008 (* 
h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 2892 (* h2 
h2) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 4368 (* h2 h2) (* 
h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 3706 (* h2 h2) (* h3 h3 h3 
h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 1744 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 
h5 h5) (* j2 j2 j2)) (* 424 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2))
 (* 48 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5 h5) j2) (* 2 (* h2 h2) (* h3 h3 h3 
h3) h4 (* h5 h5 h5)) (* 768 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 5184 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2)) (* 14432 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 
j2 j2 j2)) (* 21408 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)
) (* 18224 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 8928 
(* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 2400 (* h2 h2) (* h3 
h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 320 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 
h5) h6 j2) (* 16 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) h6) (* 576 (* h2 h2) (* 
h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3888 (* h2 h2) (* 
h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 11112 (* h2 h2) (* h3 
h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 17424 (* h2 h2) (* h3 h3 h3 
h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 16200 (* h2 h2) (* h3 h3 h3 h3) h4 h5
 (* h6 h6) (* j2 j2 j2 j2)) (* 8976 (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* h6 h6) 
(* j2 j2 j2)) (* 2808 (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 
432 (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* h6 h6) j2) (* 24 (* h2 h2) (* h3 h3 h3 h3
) h4 h5 (* h6 h6)) (* 144 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 1008 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2)) (* 2892 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2)) (* 4368 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) 
(* 3706 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 1744 (* h2
 h2) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 424 (* h2 h2) (* h3 h3 h3 
h3) (* h5 h5 h5) h6 (* j2 j2)) (* 48 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) h6 
j2) (* 2 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) h6) (* 384 (* h2 h2) (* h3 h3 h3
 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2592 (* h2 h2) (* h3 h3
 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 7216 (* h2 h2) (* h3 h3
 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 10704 (* h2 h2) (* h3 h3 
h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 9112 (* h2 h2) (* h3 h3 h3 h3)
 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 4464 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5
) (* h6 h6) (* j2 j2 j2)) (* 1200 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) 
(* j2 j2)) (* 160 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) j2) (* 8 (* h2 
h2) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6)) (* 192 (* h2 h2) (* h3 h3 h3 h3) h5 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1296 (* h2 h2) (* h3 h3 h3 h3) h5 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3704 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 5808 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2)) (* 5400 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 
j2 j2)) (* 2992 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 936 
(* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 144 (* h2 h2) (* h3 h3 
h3 h3) h5 (* h6 h6 h6) j2) (* 8 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6 h6)) (* 96
 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 648 
(* h2 h2) (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 1852 (* 
h2 h2) (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 2904 (* h2 h2) 
(* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 2700 (* h2 h2) (* h3 h3 
h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 1496 (* h2 h2) (* h3 h3 h3) (* h4 h4 
h4 h4) h5 (* j2 j2 j2)) (* 468 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 
j2)) (* 72 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4 h4) h5 j2) (* 4 (* h2 h2) (* h3 h3
 h3) (* h4 h4 h4 h4) h5) (* 144 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1272 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4764 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) 
(* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 9938 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) 
(* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 12700 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) 
(* h5 h5) (* j2 j2 j2 j2 j2)) (* 10258 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* h5
 h5) (* j2 j2 j2 j2)) (* 5188 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* 
j2 j2 j2)) (* 1558 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 
244 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) j2) (* 14 (* h2 h2) (* h3 h3 
h3) (* h4 h4 h4) (* h5 h5)) (* 384 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 2592 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* 
j2 j2 j2 j2 j2 j2 j2)) (* 7408 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 
j2 j2 j2 j2 j2)) (* 11616 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 
j2 j2)) (* 10800 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 
5984 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 1872 (* h2 h2) 
(* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2)) (* 288 (* h2 h2) (* h3 h3 h3) (* h4 
h4 h4) h5 h6 j2) (* 16 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 h6) (* 144 (* h2 
h2) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1272 
(* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
4716 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
9590 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 
11720 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 8859 
(* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 4099 (* h2 h2)
 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 1103 (* h2 h2) (* h3 h3 h3
) (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 153 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* 
h5 h5 h5) j2) (* 8 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5)) (* 432 (* h2 
h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3816 
(* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
14292 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 29814 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 38100 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
30774 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 15564 
(* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 4674 (* h2 h2) 
(* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 732 (* h2 h2) (* h3 h3 h3) (* 
h4 h4) (* h5 h5) h6 j2) (* 42 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6) (* 
576 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 3888 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 11112 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 17424 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
16200 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 8976 (* 
h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 2808 (* h2 h2) (* h3
 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 432 (* h2 h2) (* h3 h3 h3) (* h4 h4
) h5 (* h6 h6) j2) (* 24 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6)) (* 72 
(* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 504 
(* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1446 (* 
h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2184 (* h2 h2) 
(* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 1853 (* h2 h2) (* h3 h3 
h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 872 (* h2 h2) (* h3 h3 h3) h4 (* h5 
h5 h5 h5) (* j2 j2 j2)) (* 212 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 
j2)) (* 24 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5 h5) j2) (* (* h2 h2) (* h3 h3 
h3) h4 (* h5 h5 h5 h5)) (* 288 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 2544 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 9432 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2)) (* 19180 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2)) (* 23440 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2)) (* 17718 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 
8198 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 2206 (* h2 h2) 
(* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2)) (* 306 (* h2 h2) (* h3 h3 h3) h4 (* 
h5 h5 h5) h6 j2) (* 16 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) h6) (* 432 (* h2 
h2) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3816 
(* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
14292 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 29814 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 38100 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
30774 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 15564 
(* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 4674 (* h2 h2) 
(* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 732 (* h2 h2) (* h3 h3 h3) h4 
(* h5 h5) (* h6 h6) j2) (* 42 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6)) (* 
384 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
2592 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 7408
 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 11616 (* h2
 h2) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 10800 (* h2 h2) (* 
h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 5984 (* h2 h2) (* h3 h3 h3) h4 
h5 (* h6 h6 h6) (* j2 j2 j2)) (* 1872 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6 h6) 
(* j2 j2)) (* 288 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6 h6) j2) (* 16 (* h2 h2) 
(* h3 h3 h3) h4 h5 (* h6 h6 h6)) (* 72 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) h6
 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 504 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 1446 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2)) (* 2184 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 
j2 j2 j2)) (* 1853 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) 
(* 872 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 212 (* h2 h2) 
(* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 24 (* h2 h2) (* h3 h3 h3) (* h5 h5
 h5 h5) h6 j2) (* (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) h6) (* 144 (* h2 h2) 
(* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1272 (* 
h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4716 
(* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 9590 
(* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 11720 
(* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 8859 (* h2 
h2) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 4099 (* h2 h2) (* h3
 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 1103 (* h2 h2) (* h3 h3 h3) (* 
h5 h5 h5) (* h6 h6) (* j2 j2)) (* 153 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* h6 
h6) j2) (* 8 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6)) (* 144 (* h2 h2) (* 
h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1272 (* h2 
h2) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4764 (* 
h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 9938 (* 
h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 12700 (* h2
 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 10258 (* h2 h2) 
(* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 5188 (* h2 h2) (* h3 h3 
h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 1558 (* h2 h2) (* h3 h3 h3) (* h5 h5
) (* h6 h6 h6) (* j2 j2)) (* 244 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) 
j2) (* 14 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6)) (* 96 (* h2 h2) (* h3 
h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 648 (* h2 h2) (* h3 h3
 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1852 (* h2 h2) (* h3 h3 h3)
 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2904 (* h2 h2) (* h3 h3 h3) h5 (* 
h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2700 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6 
h6) (* j2 j2 j2 j2)) (* 1496 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 
j2)) (* 468 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2)) (* 72 (* h2 h2)
 (* h3 h3 h3) h5 (* h6 h6 h6 h6) j2) (* 4 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6 
h6)) (* 48 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2
 j2 j2)) (* 396 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 1400 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 
j2 j2 j2)) (* 2781 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 
j2 j2)) (* 3415 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)
) (* 2682 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 1342
 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 409 (* h2 h2) 
(* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2)) (* 67 (* h2 h2) (* h3 h3) (* h4 
h4 h4 h4) (* h5 h5) j2) (* 4 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5)) (* 
96 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (* 780 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 2728 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2
)) (* 5377 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) 
(* 6560 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 
5113 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 2528 (* 
h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 755 (* h2 h2) (* h3 
h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2)) (* 120 (* h2 h2) (* h3 h3) (* h4 h4 h4)
 (* h5 h5 h5) j2) (* 7 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5)) (* 192 (* 
h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
1584 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 5600 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 11124 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 13660 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
10728 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 5368 (* 
h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 1636 (* h2 h2) (* h3
 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 268 (* h2 h2) (* h3 h3) (* h4 h4 h4
) (* h5 h5) h6 j2) (* 16 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6) (* 48 
(* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 384 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 1316 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)
) (* 2524 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) 
(* 2966 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 
2194 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 1008 (* 
h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 272 (* h2 h2) (* h3 
h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 38 (* h2 h2) (* h3 h3) (* h4 h4) (* 
h5 h5 h5 h5) j2) (* 2 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5)) (* 288 (* 
h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
2340 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 8184 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 16131 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 19680 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
15339 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 7584 (* 
h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 2265 (* h2 h2) (* h3
 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 360 (* h2 h2) (* h3 h3) (* h4 h4) 
(* h5 h5 h5) h6 j2) (* 21 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6) (* 288 
(* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 2376 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 8400 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 16686 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 20490 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2)) (* 16092 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* 
j2 j2 j2 j2)) (* 8052 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2
 j2)) (* 2454 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 
402 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) j2) (* 24 (* h2 h2) (* h3 
h3) (* h4 h4) (* h5 h5) (* h6 h6)) (* 96 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 768 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5)
 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2632 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 5048 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 5932 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* 4388 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2))
 (* 2016 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 544 (* h2 h2
) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 76 (* h2 h2) (* h3 h3) h4 (* h5 
h5 h5 h5) h6 j2) (* 4 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) h6) (* 288 (* h2 h2
) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2340 
(* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
8184 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
16131 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
19680 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 15339
 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 7584 (* h2 h2
) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 2265 (* h2 h2) (* h3 h3) 
h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 360 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) 
(* h6 h6) j2) (* 21 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6)) (* 192 (* h2 
h2) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1584 
(* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
5600 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
11124 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
13660 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 10728
 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 5368 (* h2 h2
) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 1636 (* h2 h2) (* h3 h3) 
h4 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 268 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* 
h6 h6 h6) j2) (* 16 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6)) (* 48 (* h2 
h2) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 384 
(* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
1316 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
2524 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
2966 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2194 
(* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 1008 (* h2 h2)
 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 272 (* h2 h2) (* h3 h3) 
(* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 38 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) 
(* h6 h6) j2) (* 2 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6)) (* 96 (* h2 h2
) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 780 (* 
h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2728 
(* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 5377 
(* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6560 (* 
h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 5113 (* h2 h2)
 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 2528 (* h2 h2) (* h3 h3
) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 755 (* h2 h2) (* h3 h3) (* h5 h5 h5
) (* h6 h6 h6) (* j2 j2)) (* 120 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) 
j2) (* 7 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6)) (* 48 (* h2 h2) (* h3 h3
) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 396 (* h2 h2) (* 
h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1400 (* h2 h2) 
(* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2781 (* h2 h2) 
(* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3415 (* h2 h2) (* 
h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2682 (* h2 h2) (* h3 h3)
 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 1342 (* h2 h2) (* h3 h3) (* h5 h5
) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 409 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6
 h6) (* j2 j2)) (* 67 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) j2) (* 4 (* 
h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6)) (* 12 (* h2 h2) h3 (* h4 h4 h4 h4) 
(* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 96 (* h2 h2) h3 (* h4 h4 h4 h4) 
(* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 335 (* h2 h2) h3 (* h4 h4 h4 h4) 
(* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 667 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5
 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 831 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5 h5) 
(* j2 j2 j2 j2 j2)) (* 667 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2
 j2)) (* 341 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 105 (* 
h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2)) (* 17 (* h2 h2) h3 (* h4 h4 h4
 h4) (* h5 h5 h5) j2) (* (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5 h5)) (* 12 (* h2 
h2) h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 96 (* h2 
h2) h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 335 (* h2 h2
) h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 667 (* h2 h2) h3 
(* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 831 (* h2 h2) h3 (* h4 h4
 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 667 (* h2 h2) h3 (* h4 h4 h4) (* h5 
h5 h5 h5) (* j2 j2 j2 j2)) (* 341 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* 
j2 j2 j2)) (* 105 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 17 (* 
h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5 h5) j2) (* (* h2 h2) h3 (* h4 h4 h4) (* h5 h5
 h5 h5)) (* 48 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2
 j2 j2)) (* 384 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 1340 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2)) (* 2668 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 3324 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 2668 
(* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 1364 (* h2 h2) h3 
(* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 420 (* h2 h2) h3 (* h4 h4 h4) (* 
h5 h5 h5) h6 (* j2 j2)) (* 68 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) h6 j2) (* 4
 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) h6) (* 36 (* h2 h2) h3 (* h4 h4) (* h5 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 288 (* h2 h2) h3 (* h4 h4) (* h5
 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1005 (* h2 h2) h3 (* h4 h4) (* h5 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2001 (* h2 h2) h3 (* h4 h4) (* h5 h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 2493 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2)) (* 2001 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 
j2 j2 j2)) (* 1023 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 
315 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 51 (* h2 h2) h3 (* 
h4 h4) (* h5 h5 h5 h5) h6 j2) (* 3 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) h6) 
(* 72 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 576 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 2010 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 4002 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 4986 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 4002 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 2046 
(* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 630 (* h2 h2) h3 
(* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 102 (* h2 h2) h3 (* h4 h4) (* h5 
h5 h5) (* h6 h6) j2) (* 6 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6)) (* 36 
(* h2 h2) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 288
 (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1005 
(* h2 h2) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2001 (* 
h2 h2) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2493 (* h2 h2) 
h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2001 (* h2 h2) h3 h4 (* 
h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 1023 (* h2 h2) h3 h4 (* h5 h5 h5 h5) 
(* h6 h6) (* j2 j2 j2)) (* 315 (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 
j2)) (* 51 (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* h6 h6) j2) (* 3 (* h2 h2) h3 h4 
(* h5 h5 h5 h5) (* h6 h6)) (* 48 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2 j2)) (* 384 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 1340 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 2668 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 3324 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2)) (* 2668 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 
1364 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 420 (* h2 h2) h3
 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 68 (* h2 h2) h3 h4 (* h5 h5 h5) (* 
h6 h6 h6) j2) (* 4 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6 h6)) (* 12 (* h2 h2) h3
 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 96 (* h2 h2) h3
 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 335 (* h2 h2) h3 
(* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 667 (* h2 h2) h3 (* h5
 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 831 (* h2 h2) h3 (* h5 h5 h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 667 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2)) (* 341 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 
j2 j2)) (* 105 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 17 (* h2 
h2) h3 (* h5 h5 h5 h5) (* h6 h6 h6) j2) (* (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6
 h6)) (* 12 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
 j2)) (* 96 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 335 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 667 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 831 
(* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 667 (* h2 h2) 
h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 341 (* h2 h2) h3 (* h5 h5 h5
) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 105 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6 h6)
 (* j2 j2)) (* 17 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6 h6) j2) (* (* h2 h2) h3 
(* h5 h5 h5) (* h6 h6 h6 h6)) (* 48 h2 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 408 h2 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5)
 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1496 h2 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 3092 h2 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* 
j2 j2 j2 j2 j2 j2)) (* 3944 h2 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 
j2 j2 j2)) (* 3188 h2 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) 
(* 1608 h2 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 476 h2 (* h3 
h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 72 h2 (* h3 h3 h3 h3) (* h4 h4 h4
) (* h5 h5) j2) (* 4 h2 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5)) (* 48 h2 (* h3 
h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 408 h2 (* h3
 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1472 h2 (* h3 
h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 2936 h2 (* h3 h3 
h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 3532 h2 (* h3 h3 h3 h3) 
(* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 2622 h2 (* h3 h3 h3 h3) (* h4 h4) 
(* h5 h5 h5) (* j2 j2 j2 j2)) (* 1180 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) 
(* j2 j2 j2)) (* 304 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 40 
h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) j2) (* 2 h2 (* h3 h3 h3 h3) (* h4 h4) 
(* h5 h5 h5)) (* 144 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2
 j2 j2 j2 j2)) (* 1224 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 4488 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2)) (* 9276 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 
j2)) (* 11832 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
9564 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 4824 h2 (* h3
 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 1428 h2 (* h3 h3 h3 h3) (* h4
 h4) (* h5 h5) h6 (* j2 j2)) (* 216 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 j2
) (* 12 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6) (* 96 h2 (* h3 h3 h3 h3) h4 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 816 h2 (* h3 h3 h3 h3) h4 (* 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2944 h2 (* h3 h3 h3 h3) h4 (* h5 h5
 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 5872 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 7064 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2
 j2 j2)) (* 5244 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 2360 
h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 608 h2 (* h3 h3 h3 h3) h4
 (* h5 h5 h5) h6 (* j2 j2)) (* 80 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 j2) (* 4
 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6) (* 144 h2 (* h3 h3 h3 h3) h4 (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1224 h2 (* h3 h3 h3 h3) h4 (* h5 h5
) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4488 h2 (* h3 h3 h3 h3) h4 (* h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 9276 h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 11832 h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6)
 (* j2 j2 j2 j2 j2)) (* 9564 h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2)) (* 4824 h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 1428 
h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 216 h2 (* h3 h3 h3 h3) 
h4 (* h5 h5) (* h6 h6) j2) (* 12 h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6)) (* 
48 h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
408 h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
1472 h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2936
 h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3532 h2 (* 
h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2622 h2 (* h3 h3 h3 
h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 1180 h2 (* h3 h3 h3 h3) (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2)) (* 304 h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* 
j2 j2)) (* 40 h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) j2) (* 2 h2 (* h3 h3 h3 
h3) (* h5 h5 h5) (* h6 h6)) (* 48 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 408 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1496 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 3092 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 3944 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2)) (* 3188 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) 
(* 1608 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 476 h2 (* h3 
h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 72 h2 (* h3 h3 h3 h3) (* h5 h5) 
(* h6 h6 h6) j2) (* 4 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6)) (* 24 h2 (* h3 
h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 204 h2 (* h3
 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 748 h2 (* h3 
h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1546 h2 (* h3 h3 
h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1972 h2 (* h3 h3 h3) (* 
h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 1594 h2 (* h3 h3 h3) (* h4 h4 h4 
h4) (* h5 h5) (* j2 j2 j2 j2)) (* 804 h2 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) 
(* j2 j2 j2)) (* 238 h2 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2)) (* 36 
h2 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) j2) (* 2 h2 (* h3 h3 h3) (* h4 h4 h4 
h4) (* h5 h5)) (* 48 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2
 j2 j2 j2 j2)) (* 408 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 1496 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 
j2 j2 j2)) (* 3092 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 
j2)) (* 3944 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 
3188 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 1608 h2 (* h3
 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 476 h2 (* h3 h3 h3) (* h4 h4 
h4) (* h5 h5 h5) (* j2 j2)) (* 72 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) j2) 
(* 4 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5)) (* 96 h2 (* h3 h3 h3) (* h4 h4 
h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 816 h2 (* h3 h3 h3) (* h4 h4
 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2992 h2 (* h3 h3 h3) (* h4 h4 
h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 6184 h2 (* h3 h3 h3) (* h4 h4 h4) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 7888 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 
h5) h6 (* j2 j2 j2 j2 j2)) (* 6376 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* 
j2 j2 j2 j2)) (* 3216 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) 
(* 952 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 144 h2 (* h3 h3 
h3) (* h4 h4 h4) (* h5 h5) h6 j2) (* 8 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6
) (* 24 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 204 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 736 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
1468 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1766 h2
 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 1311 h2 (* h3 h3 
h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 590 h2 (* h3 h3 h3) (* h4 h4) 
(* h5 h5 h5 h5) (* j2 j2 j2)) (* 152 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) 
(* j2 j2)) (* 20 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) j2) (* h2 (* h3 h3 h3
) (* h4 h4) (* h5 h5 h5 h5)) (* 144 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1224 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4488 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 9276 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 11832 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* 9564 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2))
 (* 4824 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 1428 h2 (* 
h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 216 h2 (* h3 h3 h3) (* h4 h4) 
(* h5 h5 h5) h6 j2) (* 12 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6) (* 144 h2 
(* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
1224 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 4488 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 9276 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
11832 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 9564 
h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 4824 h2 (* h3 
h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 1428 h2 (* h3 h3 h3) (* h4
 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 216 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) 
(* h6 h6) j2) (* 12 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6)) (* 48 h2 (* 
h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 408 h2 (* h3 
h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1472 h2 (* h3 h3 h3
) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2936 h2 (* h3 h3 h3) h4 (* 
h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 3532 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5
) h6 (* j2 j2 j2 j2 j2)) (* 2622 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 
j2 j2)) (* 1180 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 304 h2 
(* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 40 h2 (* h3 h3 h3) h4 (* h5 h5 
h5 h5) h6 j2) (* 2 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6) (* 144 h2 (* h3 h3 h3)
 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1224 h2 (* h3 h3 
h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4488 h2 (* h3 h3 
h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 9276 h2 (* h3 h3 h3) 
h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 11832 h2 (* h3 h3 h3) h4 (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 9564 h2 (* h3 h3 h3) h4 (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2)) (* 4824 h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2)) (* 1428 h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 216 
h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) j2) (* 12 h2 (* h3 h3 h3) h4 (* h5 h5 
h5) (* h6 h6)) (* 96 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2 j2)) (* 816 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 2992 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 6184 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 7888 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
6376 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 3216 h2 (* h3
 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 952 h2 (* h3 h3 h3) h4 (* h5 
h5) (* h6 h6 h6) (* j2 j2)) (* 144 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) j2)
 (* 8 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6)) (* 24 h2 (* h3 h3 h3) (* h5 h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 204 h2 (* h3 h3 h3) (* h5 h5
 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 736 h2 (* h3 h3 h3) (* h5 h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1468 h2 (* h3 h3 h3) (* h5 h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1766 h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2)) (* 1311 h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2)) (* 590 h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 
152 h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 20 h2 (* h3 h3 h3) 
(* h5 h5 h5 h5) (* h6 h6) j2) (* h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6)) (* 
48 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
408 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
1496 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3092
 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3944 h2 (* 
h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 3188 h2 (* h3 h3 h3) 
(* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1608 h2 (* h3 h3 h3) (* h5 h5 h5) 
(* h6 h6 h6) (* j2 j2 j2)) (* 476 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* 
j2 j2)) (* 72 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) j2) (* 4 h2 (* h3 h3 h3)
 (* h5 h5 h5) (* h6 h6 h6)) (* 24 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 204 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 748 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 1546 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 1972 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 
j2 j2 j2)) (* 1594 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) 
(* 804 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 238 h2 (* h3 
h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 36 h2 (* h3 h3 h3) (* h5 h5) (* 
h6 h6 h6 h6) j2) (* 2 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6)) (* 12 h2 (* h3 
h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 102 h2 (* h3
 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 374 h2 (* h3 
h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 773 h2 (* h3 h3) 
(* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 986 h2 (* h3 h3) (* h4 h4
 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 797 h2 (* h3 h3) (* h4 h4 h4 h4) (* 
h5 h5 h5) (* j2 j2 j2 j2)) (* 402 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* 
j2 j2 j2)) (* 119 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2)) (* 18 h2 
(* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) j2) (* h2 (* h3 h3) (* h4 h4 h4 h4) (* h5
 h5 h5)) (* 12 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2
 j2 j2)) (* 102 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 374 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2
)) (* 773 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 
986 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 797 h2 (* 
h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 402 h2 (* h3 h3) (* h4 
h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 119 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 
h5 h5) (* j2 j2)) (* 18 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) j2) (* h2 (* 
h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5)) (* 48 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5
) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 408 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1496 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 3092 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2)) (* 3944 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2)) (* 3188 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 
j2)) (* 1608 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 476 h2 
(* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 72 h2 (* h3 h3) (* h4 h4 h4
) (* h5 h5 h5) h6 j2) (* 4 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6) (* 36 h2 
(* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 306 h2
 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1122 h2 
(* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2319 h2 (* 
h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 2958 h2 (* h3 h3) 
(* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 2391 h2 (* h3 h3) (* h4 h4) 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 1206 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 
h5) h6 (* j2 j2 j2)) (* 357 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2))
 (* 54 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 j2) (* 3 h2 (* h3 h3) (* h4 h4)
 (* h5 h5 h5 h5) h6) (* 72 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 612 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2244 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4638 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 5916 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6)
 (* j2 j2 j2 j2 j2)) (* 4782 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2
 j2 j2 j2)) (* 2412 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) 
(* 714 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 108 h2 (* h3 
h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) j2) (* 6 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5
) (* h6 h6)) (* 36 h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 306 h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 1122 h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 2319 h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2))
 (* 2958 h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2391 
h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 1206 h2 (* h3 h3) 
h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 357 h2 (* h3 h3) h4 (* h5 h5 h5 h5
) (* h6 h6) (* j2 j2)) (* 54 h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) j2) (* 3 
h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6)) (* 48 h2 (* h3 h3) h4 (* h5 h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 408 h2 (* h3 h3) h4 (* h5 h5 h5)
 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1496 h2 (* h3 h3) h4 (* h5 h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3092 h2 (* h3 h3) h4 (* h5 h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3944 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2)) (* 3188 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2)) (* 1608 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 
476 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 72 h2 (* h3 h3) h4 
(* h5 h5 h5) (* h6 h6 h6) j2) (* 4 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6)) 
(* 12 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 102 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 374 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
773 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 986 h2 
(* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 797 h2 (* h3 h3) 
(* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 402 h2 (* h3 h3) (* h5 h5 h5 h5
) (* h6 h6 h6) (* j2 j2 j2)) (* 119 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) 
(* j2 j2)) (* 18 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) j2) (* h2 (* h3 h3) 
(* h5 h5 h5 h5) (* h6 h6 h6)) (* 12 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 102 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 374 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 773 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2
 j2 j2 j2 j2 j2)) (* 986 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 
j2 j2)) (* 797 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 402
 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 119 h2 (* h3 h3) (* 
h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 18 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6
 h6) j2) (* h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6))) 0)))
(check-sat)
(exit)

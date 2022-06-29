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
(set-info :instance |E2E7|)
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
(+ (* 128 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2 j2 j2)) (* 
1664 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2 j2)) (* 8320 (* h1
 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2)) (* 20864 (* h1 h1 h1 h1) 
(* h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2)) (* 27904 (* h1 h1 h1 h1) (* h2 h2 h2) 
(* h3 h3) h5 (* j2 j2)) (* 18944 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 j2) 
(* 5120 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5) (* 64 (* h1 h1 h1 h1) (* h2 
h2 h2) (* h3 h3) h6 (* j2 j2 j2 j2 j2 j2)) (* 832 (* h1 h1 h1 h1) (* h2 h2 h2) 
(* h3 h3) h6 (* j2 j2 j2 j2 j2)) (* 4160 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) 
h6 (* j2 j2 j2 j2)) (* 10432 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h6 (* j2 j2 
j2)) (* 13952 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h6 (* j2 j2)) (* 9472 (* h1
 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h6 j2) (* 2560 (* h1 h1 h1 h1) (* h2 h2 h2) 
(* h3 h3) h6) (* 32 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2 j2)
) (* 384 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2)) (* 1696 (* 
h1 h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* j2 j2 j2)) (* 3520 (* h1 h1 h1 h1) (* 
h2 h2 h2) h3 (* h5 h5) (* j2 j2)) (* 3456 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h5 
h5) j2) (* 1280 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5)) (* 32 (* h1 h1 h1 h1)
 (* h2 h2 h2) h3 h5 h6 (* j2 j2 j2 j2 j2)) (* 384 (* h1 h1 h1 h1) (* h2 h2 h2) 
h3 h5 h6 (* j2 j2 j2 j2)) (* 1696 (* h1 h1 h1 h1) (* h2 h2 h2) h3 h5 h6 (* j2 j2
 j2)) (* 3520 (* h1 h1 h1 h1) (* h2 h2 h2) h3 h5 h6 (* j2 j2)) (* 3456 (* h1 h1 
h1 h1) (* h2 h2 h2) h3 h5 h6 j2) (* 1280 (* h1 h1 h1 h1) (* h2 h2 h2) h3 h5 h6) 
(* 8 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 96 (* h1 
h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6) (* j2 j2 j2 j2)) (* 424 (* h1 h1 h1 h1) (* 
h2 h2 h2) h3 (* h6 h6) (* j2 j2 j2)) (* 880 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* 
h6 h6) (* j2 j2)) (* 864 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6) j2) (* 320 
(* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6)) (* 8 (* h1 h1 h1 h1) (* h2 h2 h2) (* 
h5 h5) h6 (* j2 j2 j2 j2)) (* 88 (* h1 h1 h1 h1) (* h2 h2 h2) (* h5 h5) h6 (* j2
 j2 j2)) (* 336 (* h1 h1 h1 h1) (* h2 h2 h2) (* h5 h5) h6 (* j2 j2)) (* 544 (* 
h1 h1 h1 h1) (* h2 h2 h2) (* h5 h5) h6 j2) (* 320 (* h1 h1 h1 h1) (* h2 h2 h2) 
(* h5 h5) h6) (* 4 (* h1 h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2)) 
(* 44 (* h1 h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6) (* j2 j2 j2)) (* 168 (* h1 h1 h1
 h1) (* h2 h2 h2) h5 (* h6 h6) (* j2 j2)) (* 272 (* h1 h1 h1 h1) (* h2 h2 h2) h5
 (* h6 h6) j2) (* 160 (* h1 h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6)) (* 256 (* h1 h1
 h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 4352 (* h1 h1 h1 
h1) (* h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2 j2 j2)) (* 29184 (* h1 h1 h1 h1) 
(* h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2 j2)) (* 99840 (* h1 h1 h1 h1) (* h2 h2)
 (* h3 h3 h3) h5 (* j2 j2 j2 j2)) (* 189696 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 
h3) h5 (* j2 j2 j2)) (* 201984 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* j2 
j2)) (* 112640 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 j2) (* 25600 (* h1 h1 
h1 h1) (* h2 h2) (* h3 h3 h3) h5) (* 128 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2176 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h6 
(* j2 j2 j2 j2 j2 j2)) (* 14592 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h6 (* j2 
j2 j2 j2 j2)) (* 49920 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2 j2)
) (* 94848 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2)) (* 100992 (* 
h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h6 (* j2 j2)) (* 56320 (* h1 h1 h1 h1) (* h2
 h2) (* h3 h3 h3) h6 j2) (* 12800 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h6) (* 
192 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 2624 (* 
h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 13888 (* h1 h1 h1 
h1) (* h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2)) (* 36800 (* h1 h1 h1 h1) (* h2 h2
) (* h3 h3) h4 h5 (* j2 j2 j2)) (* 51712 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 
h5 (* j2 j2)) (* 36608 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 j2) (* 10240 
(* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5) (* 64 (* h1 h1 h1 h1) (* h2 h2) (* h3
 h3) h4 h6 (* j2 j2 j2 j2 j2 j2)) (* 896 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 
h6 (* j2 j2 j2 j2 j2)) (* 4864 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h6 (* j2 
j2 j2 j2)) (* 13184 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2)) (* 
18880 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h6 (* j2 j2)) (* 13568 (* h1 h1 h1 
h1) (* h2 h2) (* h3 h3) h4 h6 j2) (* 3840 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4
 h6) (* 128 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2))
 (* 1920 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 
11136 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 31872 
(* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2)) (* 47616 (* h1 h1 h1
 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* j2 j2)) (* 35328 (* h1 h1 h1 h1) (* h2 h2)
 (* h3 h3) (* h5 h5) j2) (* 10240 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5))
 (* 192 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 2816
 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 16000 (* h1 h1
 h1 h1) (* h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 45056 (* h1 h1 h1 h1) (* 
h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2)) (* 66496 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3
) h5 h6 (* j2 j2)) (* 48896 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h5 h6 j2) (* 
14080 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h5 h6) (* 64 (* h1 h1 h1 h1) (* h2 h2)
 (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 960 (* h1 h1 h1 h1) (* h2 h2) (* 
h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 5568 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3)
 (* h6 h6) (* j2 j2 j2 j2)) (* 15936 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 
h6) (* j2 j2 j2)) (* 23808 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6) (* j2 
j2)) (* 17664 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6) j2) (* 5120 (* h1 h1
 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6)) (* 48 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* 
h5 h5) (* j2 j2 j2 j2 j2)) (* 592 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* 
j2 j2 j2 j2)) (* 2704 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2)) 
(* 5808 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* j2 j2)) (* 5888 (* h1 h1 h1
 h1) (* h2 h2) h3 h4 (* h5 h5) j2) (* 2240 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h5
 h5)) (* 32 (* h1 h1 h1 h1) (* h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 400 (* 
h1 h1 h1 h1) (* h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2)) (* 1856 (* h1 h1 h1 h1) (* 
h2 h2) h3 h4 h5 h6 (* j2 j2 j2)) (* 4048 (* h1 h1 h1 h1) (* h2 h2) h3 h4 h5 h6 
(* j2 j2)) (* 4160 (* h1 h1 h1 h1) (* h2 h2) h3 h4 h5 h6 j2) (* 1600 (* h1 h1 h1
 h1) (* h2 h2) h3 h4 h5 h6) (* 4 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6) (* j2
 j2 j2 j2 j2)) (* 52 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2 j2)) 
(* 252 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2)) (* 572 (* h1 h1 
h1 h1) (* h2 h2) h3 h4 (* h6 h6) (* j2 j2)) (* 608 (* h1 h1 h1 h1) (* h2 h2) h3 
h4 (* h6 h6) j2) (* 240 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6)) (* 16 (* h1 
h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 224 (* h1 h1 h1 h1) 
(* h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 1168 (* h1 h1 h1 h1) (* h2 h2) h3 
(* h5 h5 h5) (* j2 j2 j2)) (* 2816 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* 
j2 j2)) (* 3136 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) j2) (* 1280 (* h1 h1 
h1 h1) (* h2 h2) h3 (* h5 h5 h5)) (* 48 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5) 
h6 (* j2 j2 j2 j2 j2)) (* 656 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5) h6 (* j2 j2
 j2 j2)) (* 3344 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2)) (* 7920
 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5) h6 (* j2 j2)) (* 8704 (* h1 h1 h1 h1) 
(* h2 h2) h3 (* h5 h5) h6 j2) (* 3520 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5) h6)
 (* 28 (* h1 h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 384 (* 
h1 h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 1964 (* h1 h1 h1 h1) 
(* h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2)) (* 4664 (* h1 h1 h1 h1) (* h2 h2) h3 h5 
(* h6 h6) (* j2 j2)) (* 5136 (* h1 h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6) j2) (* 
2080 (* h1 h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6)) (* 4 (* h1 h1 h1 h1) (* h2 h2) 
h3 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 56 (* h1 h1 h1 h1) (* h2 h2) h3 (* h6 h6 
h6) (* j2 j2 j2 j2)) (* 292 (* h1 h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6) (* j2 j2 
j2)) (* 704 (* h1 h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6) (* j2 j2)) (* 784 (* h1 h1
 h1 h1) (* h2 h2) h3 (* h6 h6 h6) j2) (* 320 (* h1 h1 h1 h1) (* h2 h2) h3 (* h6 
h6 h6)) (* 8 (* h1 h1 h1 h1) (* h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 92 
(* h1 h1 h1 h1) (* h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 372 (* h1 h1 h1 h1) 
(* h2 h2) h4 (* h5 h5) h6 (* j2 j2)) (* 640 (* h1 h1 h1 h1) (* h2 h2) h4 (* h5 
h5) h6 j2) (* 400 (* h1 h1 h1 h1) (* h2 h2) h4 (* h5 h5) h6) (* 2 (* h1 h1 h1 h1
) (* h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 24 (* h1 h1 h1 h1) (* h2 h2) h4 
h5 (* h6 h6) (* j2 j2 j2)) (* 102 (* h1 h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6) (* 
j2 j2)) (* 184 (* h1 h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6) j2) (* 120 (* h1 h1 h1 
h1) (* h2 h2) h4 h5 (* h6 h6)) (* 4 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5 h5) h6 
(* j2 j2 j2 j2)) (* 52 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2)) 
(* 240 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5 h5) h6 (* j2 j2)) (* 464 (* h1 h1 h1 
h1) (* h2 h2) (* h5 h5 h5) h6 j2) (* 320 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5 h5) 
h6) (* 6 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 74 
(* h1 h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 324 (* h1 h1 h1 
h1) (* h2 h2) (* h5 h5) (* h6 h6) (* j2 j2)) (* 600 (* h1 h1 h1 h1) (* h2 h2) 
(* h5 h5) (* h6 h6) j2) (* 400 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6)) 
(* 2 (* h1 h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 26 (* h1 h1 
h1 h1) (* h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 120 (* h1 h1 h1 h1) (* h2 h2) 
h5 (* h6 h6 h6) (* j2 j2)) (* 232 (* h1 h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6) j2) 
(* 160 (* h1 h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6)) (* 256 (* h1 h1 h1 h1) h2 (* 
h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 4480 (* h1 h1 h1 h1) h2 (* h3 h3 h3
) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 31104 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h5 
(* j2 j2 j2 j2 j2)) (* 110592 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h5 (* j2 j2 j2 
j2)) (* 218112 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h5 (* j2 j2 j2)) (* 240000 (* 
h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h5 (* j2 j2)) (* 137600 (* h1 h1 h1 h1) h2 (* h3
 h3 h3) h4 h5 j2) (* 32000 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h5) (* 64 (* h1 h1
 h1 h1) h2 (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1152 (* h1 h1 h1 h1) 
h2 (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2)) (* 8256 (* h1 h1 h1 h1) h2 (* h3 h3
 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 30336 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h6 
(* j2 j2 j2 j2)) (* 61632 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h6 (* j2 j2 j2)) 
(* 69504 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h6 (* j2 j2)) (* 40640 (* h1 h1 h1 
h1) h2 (* h3 h3 h3) h4 h6 j2) (* 9600 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h6) (* 
128 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 2432 
(* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 18432 (* h1 
h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 71424 (* h1 h1 h1 h1)
 h2 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 151680 (* h1 h1 h1 h1) h2 (* h3 
h3 h3) (* h5 h5) (* j2 j2 j2)) (* 177024 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h5 
h5) (* j2 j2)) (* 106240 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) j2) (* 25600 
(* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5)) (* 192 (* h1 h1 h1 h1) h2 (* h3 h3 h3
) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 3520 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h5 h6 
(* j2 j2 j2 j2 j2 j2)) (* 25728 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h5 h6 (* j2 j2 
j2 j2 j2)) (* 96384 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 
199104 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h5 h6 (* j2 j2 j2)) (* 227520 (* h1 h1 h1
 h1) h2 (* h3 h3 h3) h5 h6 (* j2 j2)) (* 134400 (* h1 h1 h1 h1) h2 (* h3 h3 h3) 
h5 h6 j2) (* 32000 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h5 h6) (* 64 (* h1 h1 h1 h1) 
h2 (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1216 (* h1 h1 h1 h1) h2 
(* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 9216 (* h1 h1 h1 h1) h2 (* h3 
h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 35712 (* h1 h1 h1 h1) h2 (* h3 h3 h3) 
(* h6 h6) (* j2 j2 j2 j2)) (* 75840 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6) 
(* j2 j2 j2)) (* 88512 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6) (* j2 j2)) (* 
53120 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6) j2) (* 12800 (* h1 h1 h1 h1) h2 
(* h3 h3 h3) (* h6 h6)) (* 96 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* j2 j2
 j2 j2 j2 j2)) (* 1376 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 
j2)) (* 7680 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 21440
 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 31584 (* h1 h1 h1 h1
) h2 (* h3 h3) (* h4 h4) h5 (* j2 j2)) (* 23264 (* h1 h1 h1 h1) h2 (* h3 h3) (* 
h4 h4) h5 j2) (* 6720 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5) (* 16 (* h1 h1 
h1 h1) h2 (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 240 (* h1 h1 h1 h1) 
h2 (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 1408 (* h1 h1 h1 h1) h2 (* h3 
h3) (* h4 h4) h6 (* j2 j2 j2 j2)) (* 4128 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4)
 h6 (* j2 j2 j2)) (* 6352 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h6 (* j2 j2)) 
(* 4848 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h6 j2) (* 1440 (* h1 h1 h1 h1) h2
 (* h3 h3) (* h4 h4) h6) (* 128 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* j2 
j2 j2 j2 j2 j2)) (* 1984 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 
j2 j2)) (* 11968 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 
35776 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 55744 (* h1 h1 
h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* j2 j2)) (* 42880 (* h1 h1 h1 h1) h2 (* h3 h3
) h4 (* h5 h5) j2) (* 12800 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5)) (* 192 
(* h1 h1 h1 h1) h2 (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 2976 (* h1 h1 h1
 h1) h2 (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 17984 (* h1 h1 h1 h1) h2 (* h3
 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 53952 (* h1 h1 h1 h1) h2 (* h3 h3) h4 h5 h6 
(* j2 j2 j2)) (* 84416 (* h1 h1 h1 h1) h2 (* h3 h3) h4 h5 h6 (* j2 j2)) (* 65184
 (* h1 h1 h1 h1) h2 (* h3 h3) h4 h5 h6 j2) (* 19520 (* h1 h1 h1 h1) h2 (* h3 h3)
 h4 h5 h6) (* 32 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)
) (* 512 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 3200 
(* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 9920 (* h1 h1 h1 
h1) h2 (* h3 h3) h4 (* h6 h6) (* j2 j2 j2)) (* 15968 (* h1 h1 h1 h1) h2 (* h3 h3
) h4 (* h6 h6) (* j2 j2)) (* 12608 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6) j2)
 (* 3840 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6)) (* 32 (* h1 h1 h1 h1) h2 (* 
h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 544 (* h1 h1 h1 h1) h2 (* h3 h3) 
(* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 3616 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5 
h5) (* j2 j2 j2 j2)) (* 11872 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* j2 j2
 j2)) (* 20032 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* j2 j2)) (* 16384 (* 
h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) j2) (* 5120 (* h1 h1 h1 h1) h2 (* h3 h3) 
(* h5 h5 h5)) (* 112 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2
 j2)) (* 1872 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
12240 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 39600 (* h1 
h1 h1 h1) h2 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 66048 (* h1 h1 h1 h1) h2 
(* h3 h3) (* h5 h5) h6 (* j2 j2)) (* 53568 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5
) h6 j2) (* 16640 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5) h6) (* 96 (* h1 h1 h1 
h1) h2 (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1600 (* h1 h1 h1 h1) h2 
(* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 10432 (* h1 h1 h1 h1) h2 (* h3 h3)
 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 33664 (* h1 h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6
) (* j2 j2 j2)) (* 56032 (* h1 h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6) (* j2 j2)) 
(* 45376 (* h1 h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6) j2) (* 14080 (* h1 h1 h1 h1) 
h2 (* h3 h3) h5 (* h6 h6)) (* 16 (* h1 h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2)) (* 272 (* h1 h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 
j2 j2)) (* 1808 (* h1 h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 
5936 (* h1 h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2)) (* 10016 (* h1 h1 
h1 h1) h2 (* h3 h3) (* h6 h6 h6) (* j2 j2)) (* 8192 (* h1 h1 h1 h1) h2 (* h3 h3)
 (* h6 h6 h6) j2) (* 2560 (* h1 h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6)) (* 24 (* h1
 h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 304 (* h1 h1 h1 h1) 
h2 h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 1432 (* h1 h1 h1 h1) h2 h3 (* h4 
h4) (* h5 h5) (* j2 j2 j2)) (* 3168 (* h1 h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) 
(* j2 j2)) (* 3296 (* h1 h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) j2) (* 1280 (* h1 
h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5)) (* 8 (* h1 h1 h1 h1) h2 h3 (* h4 h4) h5 h6 
(* j2 j2 j2 j2 j2)) (* 104 (* h1 h1 h1 h1) h2 h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2)
) (* 504 (* h1 h1 h1 h1) h2 h3 (* h4 h4) h5 h6 (* j2 j2 j2)) (* 1144 (* h1 h1 h1
 h1) h2 h3 (* h4 h4) h5 h6 (* j2 j2)) (* 1216 (* h1 h1 h1 h1) h2 h3 (* h4 h4) h5
 h6 j2) (* 480 (* h1 h1 h1 h1) h2 h3 (* h4 h4) h5 h6) (* 16 (* h1 h1 h1 h1) h2 
h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 224 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5 
h5) (* j2 j2 j2 j2)) (* 1168 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5 h5) (* j2 j2 j2))
 (* 2816 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5 h5) (* j2 j2)) (* 3136 (* h1 h1 h1 h1
) h2 h3 h4 (* h5 h5 h5) j2) (* 1280 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5 h5)) (* 48
 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 680 (* h1 h1 h1 h1
) h2 h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 3616 (* h1 h1 h1 h1) h2 h3 h4 (* h5 
h5) h6 (* j2 j2 j2)) (* 8968 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5) h6 (* j2 j2)) 
(* 10304 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5) h6 j2) (* 4320 (* h1 h1 h1 h1) h2 h3
 h4 (* h5 h5) h6) (* 16 (* h1 h1 h1 h1) h2 h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)
) (* 232 (* h1 h1 h1 h1) h2 h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 1264 (* h1 h1
 h1 h1) h2 h3 h4 h5 (* h6 h6) (* j2 j2 j2)) (* 3208 (* h1 h1 h1 h1) h2 h3 h4 h5 
(* h6 h6) (* j2 j2)) (* 3760 (* h1 h1 h1 h1) h2 h3 h4 h5 (* h6 h6) j2) (* 1600 
(* h1 h1 h1 h1) h2 h3 h4 h5 (* h6 h6)) (* 16 (* h1 h1 h1 h1) h2 h3 (* h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2)) (* 256 (* h1 h1 h1 h1) h2 h3 (* h5 h5 h5) h6 (* j2 j2 j2 
j2)) (* 1552 (* h1 h1 h1 h1) h2 h3 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 4384 (* h1 
h1 h1 h1) h2 h3 (* h5 h5 h5) h6 (* j2 j2)) (* 5632 (* h1 h1 h1 h1) h2 h3 (* h5 
h5 h5) h6 j2) (* 2560 (* h1 h1 h1 h1) h2 h3 (* h5 h5 h5) h6) (* 24 (* h1 h1 h1 
h1) h2 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 376 (* h1 h1 h1 h1) h2 h3 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 2232 (* h1 h1 h1 h1) h2 h3 (* h5 h5) (* 
h6 h6) (* j2 j2 j2)) (* 6184 (* h1 h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6) (* j2 j2)
) (* 7824 (* h1 h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6) j2) (* 3520 (* h1 h1 h1 h1) 
h2 h3 (* h5 h5) (* h6 h6)) (* 8 (* h1 h1 h1 h1) h2 h3 h5 (* h6 h6 h6) (* j2 j2 
j2 j2 j2)) (* 128 (* h1 h1 h1 h1) h2 h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 776 
(* h1 h1 h1 h1) h2 h3 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 2192 (* h1 h1 h1 h1) h2 
h3 h5 (* h6 h6 h6) (* j2 j2)) (* 2816 (* h1 h1 h1 h1) h2 h3 h5 (* h6 h6 h6) j2) 
(* 1280 (* h1 h1 h1 h1) h2 h3 h5 (* h6 h6 h6)) (* 2 (* h1 h1 h1 h1) h2 (* h4 h4)
 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 24 (* h1 h1 h1 h1) h2 (* h4 h4) (* h5 h5) h6 
(* j2 j2 j2)) (* 102 (* h1 h1 h1 h1) h2 (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 184
 (* h1 h1 h1 h1) h2 (* h4 h4) (* h5 h5) h6 j2) (* 120 (* h1 h1 h1 h1) h2 (* h4 
h4) (* h5 h5) h6) (* 2 (* h1 h1 h1 h1) h2 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) 
(* 26 (* h1 h1 h1 h1) h2 h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 120 (* h1 h1 h1 h1)
 h2 h4 (* h5 h5 h5) h6 (* j2 j2)) (* 232 (* h1 h1 h1 h1) h2 h4 (* h5 h5 h5) h6 
j2) (* 160 (* h1 h1 h1 h1) h2 h4 (* h5 h5 h5) h6) (* 4 (* h1 h1 h1 h1) h2 h4 (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 54 (* h1 h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6
) (* j2 j2 j2)) (* 262 (* h1 h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 
540 (* h1 h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6) j2) (* 400 (* h1 h1 h1 h1) h2 h4 
(* h5 h5) (* h6 h6)) (* 2 (* h1 h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2)) (* 30 (* h1 h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 164 (* h1 
h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 384 (* h1 h1 h1 h1) h2 (* h5 
h5 h5) (* h6 h6) j2) (* 320 (* h1 h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6)) (* 2 (* 
h1 h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 30 (* h1 h1 h1 h1) h2
 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 164 (* h1 h1 h1 h1) h2 (* h5 h5) (* h6 
h6 h6) (* j2 j2)) (* 384 (* h1 h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6) j2) (* 320 
(* h1 h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6)) (* 64 (* h1 h1 h1 h1) (* h3 h3 h3) 
(* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 1152 (* h1 h1 h1 h1) (* h3 h3 h3) (* 
h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 8256 (* h1 h1 h1 h1) (* h3 h3 h3) (* h4 h4) 
h5 (* j2 j2 j2 j2 j2)) (* 30336 (* h1 h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* j2 
j2 j2 j2)) (* 61632 (* h1 h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 
69504 (* h1 h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2)) (* 40640 (* h1 h1 h1 
h1) (* h3 h3 h3) (* h4 h4) h5 j2) (* 9600 (* h1 h1 h1 h1) (* h3 h3 h3) (* h4 h4)
 h5) (* 64 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 1216 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 9216
 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 35712 (* h1 h1
 h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 75840 (* h1 h1 h1 h1) (* 
h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 88512 (* h1 h1 h1 h1) (* h3 h3 h3) h4 
(* h5 h5) (* j2 j2)) (* 53120 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) j2) (* 
12800 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5)) (* 128 (* h1 h1 h1 h1) (* h3 h3
 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2496 (* h1 h1 h1 h1) (* h3 h3 h3) h4 
h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 19520 (* h1 h1 h1 h1) (* h3 h3 h3) h4 h5 h6 (* 
j2 j2 j2 j2 j2)) (* 78464 (* h1 h1 h1 h1) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2))
 (* 173312 (* h1 h1 h1 h1) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 209600 (* h1 
h1 h1 h1) (* h3 h3 h3) h4 h5 h6 (* j2 j2)) (* 129600 (* h1 h1 h1 h1) (* h3 h3 h3
) h4 h5 h6 j2) (* 32000 (* h1 h1 h1 h1) (* h3 h3 h3) h4 h5 h6) (* 64 (* h1 h1 h1
 h1) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1344 (* h1 h1 h1 h1)
 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 11392 (* h1 h1 h1 h1) (* h3
 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 49792 (* h1 h1 h1 h1) (* h3 h3 h3) 
(* h5 h5) h6 (* j2 j2 j2 j2)) (* 119104 (* h1 h1 h1 h1) (* h3 h3 h3) (* h5 h5) 
h6 (* j2 j2 j2)) (* 153664 (* h1 h1 h1 h1) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2)) 
(* 99840 (* h1 h1 h1 h1) (* h3 h3 h3) (* h5 h5) h6 j2) (* 25600 (* h1 h1 h1 h1) 
(* h3 h3 h3) (* h5 h5) h6) (* 64 (* h1 h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6) (* j2
 j2 j2 j2 j2 j2 j2)) (* 1344 (* h1 h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 11392 (* h1 h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 49792 (* h1 h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 
119104 (* h1 h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 153664 (* h1 
h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2)) (* 99840 (* h1 h1 h1 h1) (* h3 h3
 h3) h5 (* h6 h6) j2) (* 25600 (* h1 h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6)) (* 16 
(* h1 h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 240 (* h1 h1
 h1 h1) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 1408 (* h1 h1 h1 h1) 
(* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 4128 (* h1 h1 h1 h1) (* h3 h3) (* 
h4 h4 h4) h5 (* j2 j2 j2)) (* 6352 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 (* 
j2 j2)) (* 4848 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 j2) (* 1440 (* h1 h1 
h1 h1) (* h3 h3) (* h4 h4 h4) h5) (* 32 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* 
h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 512 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 
h5) (* j2 j2 j2 j2 j2)) (* 3200 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) 
(* j2 j2 j2 j2)) (* 9920 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 
j2)) (* 15968 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 12608 
(* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) j2) (* 3840 (* h1 h1 h1 h1) (* h3 
h3) (* h4 h4) (* h5 h5)) (* 48 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) h5 h6 (* j2 
j2 j2 j2 j2 j2)) (* 784 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2
 j2)) (* 5024 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 
16032 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 26608 (* h1 h1 
h1 h1) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 21584 (* h1 h1 h1 h1) (* h3 h3) 
(* h4 h4) h5 h6 j2) (* 6720 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) h5 h6) (* 16 (* 
h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 272 (* h1 h1 h1
 h1) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 1808 (* h1 h1 h1 h1) (* h3
 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 5936 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5
 h5 h5) (* j2 j2 j2)) (* 10016 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* j2 
j2)) (* 8192 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) j2) (* 2560 (* h1 h1 h1 
h1) (* h3 h3) h4 (* h5 h5 h5)) (* 64 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 1120 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* 7712 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2))
 (* 26400 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 46624 (* h1
 h1 h1 h1) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 39680 (* h1 h1 h1 h1) (* h3 
h3) h4 (* h5 h5) h6 j2) (* 12800 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5) h6) (* 
48 (* h1 h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 848 (* h1
 h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 5904 (* h1 h1 h1 h1)
 (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 20464 (* h1 h1 h1 h1) (* h3 h3) 
h4 h5 (* h6 h6) (* j2 j2 j2)) (* 36608 (* h1 h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6)
 (* j2 j2)) (* 31488 (* h1 h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6) j2) (* 10240 (* 
h1 h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6)) (* 16 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5
 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 304 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2)) (* 2288 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 
j2 j2)) (* 8592 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 16576
 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2)) (* 15104 (* h1 h1 h1 h1) 
(* h3 h3) (* h5 h5 h5) h6 j2) (* 5120 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5 h5) h6)
 (* 32 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
608 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 4576 
(* h1 h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 17184 (* h1 h1
 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 33152 (* h1 h1 h1 h1) (* 
h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 30208 (* h1 h1 h1 h1) (* h3 h3) (* h5 
h5) (* h6 h6) j2) (* 10240 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6)) (* 16 
(* h1 h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 304 (* h1 h1
 h1 h1) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2288 (* h1 h1 h1 h1) 
(* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 8592 (* h1 h1 h1 h1) (* h3 h3) h5 
(* h6 h6 h6) (* j2 j2 j2)) (* 16576 (* h1 h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6) 
(* j2 j2)) (* 15104 (* h1 h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6) j2) (* 5120 (* h1 
h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6)) (* 4 (* h1 h1 h1 h1) h3 (* h4 h4 h4) (* h5 
h5) (* j2 j2 j2 j2 j2)) (* 52 (* h1 h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2
 j2 j2)) (* 252 (* h1 h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 572 
(* h1 h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 608 (* h1 h1 h1 h1) h3 
(* h4 h4 h4) (* h5 h5) j2) (* 240 (* h1 h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5)) (* 
4 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 56 (* h1 h1 
h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 292 (* h1 h1 h1 h1) h3 (* 
h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 704 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5 
h5) (* j2 j2)) (* 784 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) j2) (* 320 (* h1
 h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5)) (* 12 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 
h5) h6 (* j2 j2 j2 j2 j2)) (* 176 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5) h6 (* 
j2 j2 j2 j2)) (* 972 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 
2504 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 2976 (* h1 h1 h1 h1
) h3 (* h4 h4) (* h5 h5) h6 j2) (* 1280 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5) 
h6) (* 8 (* h1 h1 h1 h1) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 128 (* h1 
h1 h1 h1) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 776 (* h1 h1 h1 h1) h3 h4 
(* h5 h5 h5) h6 (* j2 j2 j2)) (* 2192 (* h1 h1 h1 h1) h3 h4 (* h5 h5 h5) h6 (* 
j2 j2)) (* 2816 (* h1 h1 h1 h1) h3 h4 (* h5 h5 h5) h6 j2) (* 1280 (* h1 h1 h1 h1
) h3 h4 (* h5 h5 h5) h6) (* 12 (* h1 h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2)) (* 196 (* h1 h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) 
(* 1220 (* h1 h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 3564 (* h1 h1
 h1 h1) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 4768 (* h1 h1 h1 h1) h3 h4 (* h5
 h5) (* h6 h6) j2) (* 2240 (* h1 h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6)) (* 4 (* h1
 h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 72 (* h1 h1 h1 h1) 
h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 500 (* h1 h1 h1 h1) h3 (* h5 h5 h5
) (* h6 h6) (* j2 j2 j2)) (* 1648 (* h1 h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6) (* 
j2 j2)) (* 2496 (* h1 h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6) j2) (* 1280 (* h1 h1 
h1 h1) h3 (* h5 h5 h5) (* h6 h6)) (* 4 (* h1 h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6)
 (* j2 j2 j2 j2 j2)) (* 72 (* h1 h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2
 j2)) (* 500 (* h1 h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 1648 (* 
h1 h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 2496 (* h1 h1 h1 h1) h3 (* 
h5 h5) (* h6 h6 h6) j2) (* 1280 (* h1 h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6)) (* 
128 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2 j2 j2)) (* 1280 (* 
h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2 j2)) (* 5248 (* h1 h1 h1) 
(* h2 h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2)) (* 11264 (* h1 h1 h1) (* h2 h2 h2 
h2) (* h3 h3) h5 (* j2 j2 j2)) (* 13312 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) 
h5 (* j2 j2)) (* 8192 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 j2) (* 2048 (* 
h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5) (* 64 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3
 h3) h6 (* j2 j2 j2 j2 j2 j2)) (* 640 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h6 
(* j2 j2 j2 j2 j2)) (* 2624 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h6 (* j2 j2 
j2 j2)) (* 5632 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h6 (* j2 j2 j2)) (* 6656 
(* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h6 (* j2 j2)) (* 4096 (* h1 h1 h1) (* h2 
h2 h2 h2) (* h3 h3) h6 j2) (* 1024 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h6) 
(* 32 (* h1 h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 288 (* h1
 h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2)) (* 1024 (* h1 h1 h1) (* h2
 h2 h2 h2) h3 (* h5 h5) (* j2 j2 j2)) (* 1792 (* h1 h1 h1) (* h2 h2 h2 h2) h3 
(* h5 h5) (* j2 j2)) (* 1536 (* h1 h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) j2) (* 
512 (* h1 h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5)) (* 32 (* h1 h1 h1) (* h2 h2 h2 h2
) h3 h5 h6 (* j2 j2 j2 j2 j2)) (* 288 (* h1 h1 h1) (* h2 h2 h2 h2) h3 h5 h6 (* 
j2 j2 j2 j2)) (* 1024 (* h1 h1 h1) (* h2 h2 h2 h2) h3 h5 h6 (* j2 j2 j2)) (* 
1792 (* h1 h1 h1) (* h2 h2 h2 h2) h3 h5 h6 (* j2 j2)) (* 1536 (* h1 h1 h1) (* h2
 h2 h2 h2) h3 h5 h6 j2) (* 512 (* h1 h1 h1) (* h2 h2 h2 h2) h3 h5 h6) (* 8 (* h1
 h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 72 (* h1 h1 h1) (* 
h2 h2 h2 h2) h3 (* h6 h6) (* j2 j2 j2 j2)) (* 256 (* h1 h1 h1) (* h2 h2 h2 h2) 
h3 (* h6 h6) (* j2 j2 j2)) (* 448 (* h1 h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6) (* 
j2 j2)) (* 384 (* h1 h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6) j2) (* 128 (* h1 h1 h1)
 (* h2 h2 h2 h2) h3 (* h6 h6)) (* 8 (* h1 h1 h1) (* h2 h2 h2 h2) (* h5 h5) h6 
(* j2 j2 j2 j2)) (* 64 (* h1 h1 h1) (* h2 h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2)) 
(* 192 (* h1 h1 h1) (* h2 h2 h2 h2) (* h5 h5) h6 (* j2 j2)) (* 256 (* h1 h1 h1) 
(* h2 h2 h2 h2) (* h5 h5) h6 j2) (* 128 (* h1 h1 h1) (* h2 h2 h2 h2) (* h5 h5) 
h6) (* 4 (* h1 h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 32 (* h1 
h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6) (* j2 j2 j2)) (* 96 (* h1 h1 h1) (* h2 h2 h2
 h2) h5 (* h6 h6) (* j2 j2)) (* 128 (* h1 h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6) j2
) (* 64 (* h1 h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6)) (* 512 (* h1 h1 h1) (* h2 h2 
h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 7168 (* h1 h1 h1) (* h2 h2 h2) 
(* h3 h3 h3) h5 (* j2 j2 j2 j2 j2 j2)) (* 39936 (* h1 h1 h1) (* h2 h2 h2) (* h3 
h3 h3) h5 (* j2 j2 j2 j2 j2)) (* 116736 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) 
h5 (* j2 j2 j2 j2)) (* 195072 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2
 j2)) (* 187392 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2)) (* 96256 
(* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 j2) (* 20480 (* h1 h1 h1) (* h2 h2 h2)
 (* h3 h3 h3) h5) (* 256 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2 
j2 j2 j2 j2)) (* 3584 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2 j2 
j2 j2)) (* 19968 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2 j2 j2)) 
(* 58368 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2 j2)) (* 97536 (* 
h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2)) (* 93696 (* h1 h1 h1) (* h2
 h2 h2) (* h3 h3 h3) h6 (* j2 j2)) (* 48128 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 
h3) h6 j2) (* 10240 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h6) (* 384 (* h1 h1 
h1) (* h2 h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 4672 (* h1 h1 h1) (* 
h2 h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 22400 (* h1 h1 h1) (* h2 h2 h2)
 (* h3 h3) h4 h5 (* j2 j2 j2 j2)) (* 54592 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) 
h4 h5 (* j2 j2 j2)) (* 71552 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 (* j2 j2)
) (* 47872 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 j2) (* 12800 (* h1 h1 h1) 
(* h2 h2 h2) (* h3 h3) h4 h5) (* 128 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h6 
(* j2 j2 j2 j2 j2 j2)) (* 1600 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h6 (* j2 
j2 j2 j2 j2)) (* 7808 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2))
 (* 19264 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2)) (* 25472 (* h1
 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h6 (* j2 j2)) (* 17152 (* h1 h1 h1) (* h2 h2 
h2) (* h3 h3) h4 h6 j2) (* 4608 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h6) (* 
256 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 3200
 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 15616 (* 
h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 38528 (* h1 h1 h1
) (* h2 h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2)) (* 50944 (* h1 h1 h1) (* h2 h2 
h2) (* h3 h3) (* h5 h5) (* j2 j2)) (* 34304 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) 
(* h5 h5) j2) (* 9216 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5)) (* 384 (* 
h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 4800 (* h1 h1 
h1) (* h2 h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 23424 (* h1 h1 h1) (* h2
 h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 57792 (* h1 h1 h1) (* h2 h2 h2) (* 
h3 h3) h5 h6 (* j2 j2 j2)) (* 76416 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 h6 
(* j2 j2)) (* 51456 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 h6 j2) (* 13824 (* h1
 h1 h1) (* h2 h2 h2) (* h3 h3) h5 h6) (* 128 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1632 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 8064 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 
h6) (* j2 j2 j2 j2)) (* 20064 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6) (* 
j2 j2 j2)) (* 26688 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2)) (* 
18048 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6) j2) (* 4864 (* h1 h1 h1) (* 
h2 h2 h2) (* h3 h3) (* h6 h6)) (* 96 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) 
(* j2 j2 j2 j2 j2)) (* 1056 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2 
j2 j2)) (* 4416 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2)) (* 8832 
(* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2)) (* 8448 (* h1 h1 h1) (* h2 
h2 h2) h3 h4 (* h5 h5) j2) (* 3072 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5)) 
(* 64 (* h1 h1 h1) (* h2 h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 720 (* h1 h1 
h1) (* h2 h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2)) (* 3056 (* h1 h1 h1) (* h2 h2 h2) 
h3 h4 h5 h6 (* j2 j2 j2)) (* 6176 (* h1 h1 h1) (* h2 h2 h2) h3 h4 h5 h6 (* j2 j2
)) (* 5952 (* h1 h1 h1) (* h2 h2 h2) h3 h4 h5 h6 j2) (* 2176 (* h1 h1 h1) (* h2 
h2 h2) h3 h4 h5 h6) (* 8 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2 
j2 j2)) (* 96 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2 j2)) (* 424 
(* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2)) (* 880 (* h1 h1 h1) (* 
h2 h2 h2) h3 h4 (* h6 h6) (* j2 j2)) (* 864 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* 
h6 h6) j2) (* 320 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6)) (* 32 (* h1 h1 h1) 
(* h2 h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 368 (* h1 h1 h1) (* h2 h2 h2
) h3 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 1584 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5
 h5) (* j2 j2 j2)) (* 3232 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) (* j2 j2)) 
(* 3136 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) j2) (* 1152 (* h1 h1 h1) (* h2
 h2 h2) h3 (* h5 h5 h5)) (* 96 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* 1104 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2))
 (* 4752 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2)) (* 9696 (* h1 
h1 h1) (* h2 h2 h2) h3 (* h5 h5) h6 (* j2 j2)) (* 9408 (* h1 h1 h1) (* h2 h2 h2)
 h3 (* h5 h5) h6 j2) (* 3456 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) h6) (* 56 
(* h1 h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 652 (* h1 h1 h1
) (* h2 h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 2828 (* h1 h1 h1) (* h2 h2 h2
) h3 h5 (* h6 h6) (* j2 j2 j2)) (* 5800 (* h1 h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6
) (* j2 j2)) (* 5648 (* h1 h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6) j2) (* 2080 (* h1
 h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6)) (* 8 (* h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6
 h6) (* j2 j2 j2 j2 j2)) (* 96 (* h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6) (* j2 
j2 j2 j2)) (* 424 (* h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2)) (* 880
 (* h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6) (* j2 j2)) (* 864 (* h1 h1 h1) (* h2 
h2 h2) h3 (* h6 h6 h6) j2) (* 320 (* h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6)) (* 
16 (* h1 h1 h1) (* h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 164 (* h1 h1 h1
) (* h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 600 (* h1 h1 h1) (* h2 h2 h2) h4
 (* h5 h5) h6 (* j2 j2)) (* 944 (* h1 h1 h1) (* h2 h2 h2) h4 (* h5 h5) h6 j2) 
(* 544 (* h1 h1 h1) (* h2 h2 h2) h4 (* h5 h5) h6) (* 4 (* h1 h1 h1) (* h2 h2 h2)
 h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 44 (* h1 h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6
) (* j2 j2 j2)) (* 168 (* h1 h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6) (* j2 j2)) (* 
272 (* h1 h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6) j2) (* 160 (* h1 h1 h1) (* h2 h2 
h2) h4 h5 (* h6 h6)) (* 8 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 
j2)) (* 84 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 312 (* h1 
h1 h1) (* h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2)) (* 496 (* h1 h1 h1) (* h2 h2 h2) 
(* h5 h5 h5) h6 j2) (* 288 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5 h5) h6) (* 12 (* 
h1 h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 126 (* h1 h1 h1) 
(* h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 468 (* h1 h1 h1) (* h2 h2 h2) 
(* h5 h5) (* h6 h6) (* j2 j2)) (* 744 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 
h6) j2) (* 432 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6)) (* 4 (* h1 h1 h1) 
(* h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 44 (* h1 h1 h1) (* h2 h2 h2) h5
 (* h6 h6 h6) (* j2 j2 j2)) (* 168 (* h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6) (* 
j2 j2)) (* 272 (* h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6) j2) (* 160 (* h1 h1 h1)
 (* h2 h2 h2) h5 (* h6 h6 h6)) (* 1024 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5
 (* j2 j2 j2 j2 j2 j2 j2)) (* 13312 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 
(* j2 j2 j2 j2 j2 j2)) (* 67584 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 (* j2 
j2 j2 j2 j2)) (* 178176 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2 j2 j2
)) (* 267264 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2 j2)) (* 230400 
(* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2)) (* 106496 (* h1 h1 h1) (* 
h2 h2) (* h3 h3 h3 h3) h5 j2) (* 20480 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5
) (* 512 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
6656 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2 j2 j2 j2 j2)) (* 33792 
(* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2 j2 j2 j2)) (* 89088 (* h1 h1 
h1) (* h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2 j2 j2)) (* 133632 (* h1 h1 h1) (* h2 
h2) (* h3 h3 h3 h3) h6 (* j2 j2 j2)) (* 115200 (* h1 h1 h1) (* h2 h2) (* h3 h3 
h3 h3) h6 (* j2 j2)) (* 53248 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h6 j2) (* 
10240 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h6) (* 768 (* h1 h1 h1) (* h2 h2) 
(* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 12288 (* h1 h1 h1) (* h2 h2) (* 
h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 78336 (* h1 h1 h1) (* h2 h2) (* h3 h3 
h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 258048 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 
h5 (* j2 j2 j2 j2)) (* 476928 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2
 j2)) (* 497664 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2)) (* 273408 
(* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 j2) (* 61440 (* h1 h1 h1) (* h2 h2) 
(* h3 h3 h3) h4 h5) (* 192 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2
 j2 j2 j2 j2)) (* 3264 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 
j2 j2)) (* 21888 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) 
(* 74880 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 142272 
(* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2)) (* 151488 (* h1 h1 h1) 
(* h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2)) (* 84480 (* h1 h1 h1) (* h2 h2) (* h3 h3
 h3) h4 h6 j2) (* 19200 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h6) (* 384 (* h1 
h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 6528 (* h1 
h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 43776 (* h1 h1
 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 149760 (* h1 h1 h1)
 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 284544 (* h1 h1 h1) (* h2 
h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2)) (* 302976 (* h1 h1 h1) (* h2 h2) (* h3 
h3 h3) (* h5 h5) (* j2 j2)) (* 168960 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 
h5) j2) (* 38400 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5)) (* 576 (* h1 h1 
h1) (* h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 9664 (* h1 h1 h1) 
(* h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 64128 (* h1 h1 h1) (* h2 
h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 217728 (* h1 h1 h1) (* h2 h2) (* 
h3 h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 411456 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) 
h5 h6 (* j2 j2 j2)) (* 436416 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2
)) (* 242688 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 h6 j2) (* 55040 (* h1 h1 h1)
 (* h2 h2) (* h3 h3 h3) h5 h6) (* 192 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3328 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 22656 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6
) (* j2 j2 j2 j2 j2)) (* 78336 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6) (* 
j2 j2 j2 j2)) (* 149952 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 
j2)) (* 160512 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2)) (* 89856
 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6) j2) (* 20480 (* h1 h1 h1) (* h2 
h2) (* h3 h3 h3) (* h6 h6)) (* 288 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5
 (* j2 j2 j2 j2 j2 j2)) (* 3904 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 
(* j2 j2 j2 j2 j2)) (* 20544 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 (* j2
 j2 j2 j2)) (* 54208 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2))
 (* 75936 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2)) (* 53632 (* 
h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 j2) (* 14976 (* h1 h1 h1) (* h2 h2) 
(* h3 h3) (* h4 h4) h5) (* 48 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h6 (* 
j2 j2 j2 j2 j2 j2)) (* 704 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 
j2 j2 j2 j2)) (* 3936 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 
j2)) (* 10880 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2 j2)) (* 
15792 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2)) (* 11456 (* h1 h1
 h1) (* h2 h2) (* h3 h3) (* h4 h4) h6 j2) (* 3264 (* h1 h1 h1) (* h2 h2) (* h3 
h3) (* h4 h4) h6) (* 384 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 
j2 j2 j2 j2)) (* 5504 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 
j2 j2)) (* 30848 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) 
(* 86144 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 126464 
(* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2)) (* 92672 (* h1 h1 h1) 
(* h2 h2) (* h3 h3) h4 (* h5 h5) j2) (* 26624 (* h1 h1 h1) (* h2 h2) (* h3 h3) 
h4 (* h5 h5)) (* 576 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2
 j2)) (* 8192 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 
45184 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 124160 (* h1
 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 179776 (* h1 h1 h1) (* h2 
h2) (* h3 h3) h4 h5 h6 (* j2 j2)) (* 130304 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 
h5 h6 j2) (* 37120 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6) (* 96 (* h1 h1 h1)
 (* h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1456 (* h1 h1 h1) 
(* h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 8432 (* h1 h1 h1) (* h2 
h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 24016 (* h1 h1 h1) (* h2 h2) (* 
h3 h3) h4 (* h6 h6) (* j2 j2 j2)) (* 35696 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 
(* h6 h6) (* j2 j2)) (* 26368 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6) j2) 
(* 7616 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6)) (* 96 (* h1 h1 h1) (* h2 
h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1472 (* h1 h1 h1) (* h2 h2)
 (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 8672 (* h1 h1 h1) (* h2 h2) (* h3
 h3) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 25088 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* 
h5 h5 h5) (* j2 j2 j2)) (* 37760 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) 
(* j2 j2)) (* 28160 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) j2) (* 8192 
(* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5)) (* 336 (* h1 h1 h1) (* h2 h2) (* 
h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 4992 (* h1 h1 h1) (* h2 h2) (* h3 
h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 28720 (* h1 h1 h1) (* h2 h2) (* h3 h3) 
(* h5 h5) h6 (* j2 j2 j2 j2)) (* 81696 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5
) h6 (* j2 j2 j2)) (* 121504 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) h6 (* j2
 j2)) (* 89856 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) h6 j2) (* 25984 (* h1 
h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) h6) (* 288 (* h1 h1 h1) (* h2 h2) (* h3 h3)
 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4272 (* h1 h1 h1) (* h2 h2) (* h3 h3) h5
 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 24480 (* h1 h1 h1) (* h2 h2) (* h3 h3) h5 (* 
h6 h6) (* j2 j2 j2 j2)) (* 69360 (* h1 h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6) 
(* j2 j2 j2)) (* 102816 (* h1 h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2))
 (* 75840 (* h1 h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6) j2) (* 21888 (* h1 h1 h1
) (* h2 h2) (* h3 h3) h5 (* h6 h6)) (* 48 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h6
 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 752 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 
h6) (* j2 j2 j2 j2 j2)) (* 4496 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6) 
(* j2 j2 j2 j2)) (* 13136 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2
 j2)) (* 19904 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2)) (* 14912
 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6) j2) (* 4352 (* h1 h1 h1) (* h2 h2
) (* h3 h3) (* h6 h6 h6)) (* 72 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) 
(* j2 j2 j2 j2 j2)) (* 872 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 
j2 j2 j2)) (* 3936 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2)) 
(* 8384 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2)) (* 8448 (* h1 
h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) j2) (* 3200 (* h1 h1 h1) (* h2 h2) h3 
(* h4 h4) (* h5 h5)) (* 24 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2
 j2 j2)) (* 312 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 
1480 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2)) (* 3272 (* h1 h1 h1
) (* h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2)) (* 3392 (* h1 h1 h1) (* h2 h2) h3 (* 
h4 h4) h5 h6 j2) (* 1312 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) h5 h6) (* 4 (* h1 
h1 h1) (* h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 32 (* h1 h1 h1) (* 
h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 92 (* h1 h1 h1) (* h2 h2) h3 (* 
h4 h4) (* h6 h6) (* j2 j2)) (* 112 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h6 h6)
 j2) (* 48 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h6 h6)) (* 48 (* h1 h1 h1) (* 
h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 624 (* h1 h1 h1) (* h2 h2) h3 
h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 3072 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5 
h5) (* j2 j2 j2)) (* 7104 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2)) 
(* 7680 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) j2) (* 3072 (* h1 h1 h1) (* h2
 h2) h3 h4 (* h5 h5 h5)) (* 144 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* 1872 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2))
 (* 9096 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2)) (* 20712 (* h1 
h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2)) (* 22080 (* h1 h1 h1) (* h2 h2) 
h3 h4 (* h5 h5) h6 j2) (* 8736 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6) (* 48 
(* h1 h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 656 (* h1 h1 h1
) (* h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 3296 (* h1 h1 h1) (* h2 h2) 
h3 h4 h5 (* h6 h6) (* j2 j2 j2)) (* 7680 (* h1 h1 h1) (* h2 h2) h3 h4 h5 (* h6 
h6) (* j2 j2)) (* 8320 (* h1 h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6) j2) (* 3328 (* 
h1 h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6)) (* 8 (* h1 h1 h1) (* h2 h2) h3 h4 (* h6 
h6 h6) (* j2 j2 j2 j2)) (* 68 (* h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2
 j2)) (* 204 (* h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2)) (* 256 (* h1 
h1 h1) (* h2 h2) h3 h4 (* h6 h6 h6) j2) (* 112 (* h1 h1 h1) (* h2 h2) h3 h4 (* 
h6 h6 h6)) (* 16 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 
144 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) (* j2 j2 j2)) (* 448 (* h1 h1 h1) 
(* h2 h2) h3 (* h5 h5 h5 h5) (* j2 j2)) (* 576 (* h1 h1 h1) (* h2 h2) h3 (* h5 
h5 h5 h5) j2) (* 256 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5)) (* 48 (* h1 h1 
h1) (* h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 672 (* h1 h1 h1) (* h2 
h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 3488 (* h1 h1 h1) (* h2 h2) h3 (* h5 
h5 h5) h6 (* j2 j2 j2)) (* 8368 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) h6 (* j2 
j2)) (* 9280 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) h6 j2) (* 3776 (* h1 h1 h1) 
(* h2 h2) h3 (* h5 h5 h5) h6) (* 72 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6
) (* j2 j2 j2 j2 j2)) (* 988 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6) (* j2
 j2 j2 j2)) (* 5036 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2)) 
(* 11912 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2)) (* 13072 (* h1
 h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6) j2) (* 5280 (* h1 h1 h1) (* h2 h2) h3 
(* h5 h5) (* h6 h6)) (* 24 (* h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2
 j2 j2)) (* 344 (* h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 
1812 (* h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 4388 (* h1 h1 h1
) (* h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2)) (* 4896 (* h1 h1 h1) (* h2 h2) h3 h5 
(* h6 h6 h6) j2) (* 2000 (* h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6)) (* 4 (* h1 
h1 h1) (* h2 h2) h3 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 36 (* h1 h1 h1) (* h2 h2
) h3 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 112 (* h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6 
h6) (* j2 j2)) (* 144 (* h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6 h6) j2) (* 64 (* h1 
h1 h1) (* h2 h2) h3 (* h6 h6 h6 h6)) (* 6 (* h1 h1 h1) (* h2 h2) (* h4 h4) (* h5
 h5) h6 (* j2 j2 j2 j2)) (* 72 (* h1 h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) h6 (* 
j2 j2 j2)) (* 298 (* h1 h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 
520 (* h1 h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) h6 j2) (* 328 (* h1 h1 h1) (* h2 
h2) (* h4 h4) (* h5 h5) h6) (* 2 (* h1 h1 h1) (* h2 h2) (* h4 h4) h5 (* h6 h6) 
(* j2 j2 j2)) (* 14 (* h1 h1 h1) (* h2 h2) (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 
32 (* h1 h1 h1) (* h2 h2) (* h4 h4) h5 (* h6 h6) j2) (* 24 (* h1 h1 h1) (* h2 h2
) (* h4 h4) h5 (* h6 h6)) (* 6 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5 h5) h6 (* j2 
j2 j2 j2)) (* 76 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 348 
(* h1 h1 h1) (* h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2)) (* 672 (* h1 h1 h1) (* h2 
h2) h4 (* h5 h5 h5) h6 j2) (* 464 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5 h5) h6) (* 
12 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 150 (* h1 
h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 654 (* h1 h1 h1) (* h2 
h2) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 1200 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5
) (* h6 h6) j2) (* 792 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6)) (* 4 (* h1
 h1 h1) (* h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 30 (* h1 h1 h1) (* h2 h2) 
h4 h5 (* h6 h6 h6) (* j2 j2)) (* 72 (* h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6 h6) j2
) (* 56 (* h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6 h6)) (* 4 (* h1 h1 h1) (* h2 h2) 
(* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 32 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5 h5) h6
 (* j2 j2)) (* 80 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5 h5) h6 j2) (* 64 (* h1 h1 
h1) (* h2 h2) (* h5 h5 h5 h5) h6) (* 6 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5) (* h6
 h6) (* j2 j2 j2 j2)) (* 78 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 
j2 j2)) (* 356 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 680 
(* h1 h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6) j2) (* 464 (* h1 h1 h1) (* h2 h2) 
(* h5 h5 h5) (* h6 h6)) (* 6 (* h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6) (* j2
 j2 j2 j2)) (* 78 (* h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) 
(* 354 (* h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 672 (* h1 h1 
h1) (* h2 h2) (* h5 h5) (* h6 h6 h6) j2) (* 456 (* h1 h1 h1) (* h2 h2) (* h5 h5)
 (* h6 h6 h6)) (* 2 (* h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 
16 (* h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2)) (* 40 (* h1 h1 h1) (* h2
 h2) h5 (* h6 h6 h6 h6) j2) (* 32 (* h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6 h6)) (* 
1024 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 13824 
(* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 73216 (* h1 h1 
h1) h2 (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 200704 (* h1 h1 h1) h2 (* h3
 h3 h3 h3) h4 h5 (* j2 j2 j2 j2)) (* 311296 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 
h5 (* j2 j2 j2)) (* 275968 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h5 (* j2 j2)) (* 
130560 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h5 j2) (* 25600 (* h1 h1 h1) h2 (* h3 
h3 h3 h3) h4 h5) (* 256 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 3584 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2)) (* 
19712 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 55808 (* h1 
h1 h1) h2 (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 88832 (* h1 h1 h1) h2 (* h3 
h3 h3 h3) h4 h6 (* j2 j2 j2)) (* 80384 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h6 (* 
j2 j2)) (* 38656 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h6 j2) (* 7680 (* h1 h1 h1) 
h2 (* h3 h3 h3 h3) h4 h6) (* 512 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) (* j2
 j2 j2 j2 j2 j2 j2)) (* 7680 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 
j2 j2 j2 j2)) (* 45056 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 
j2)) (* 134144 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 
221696 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2)) (* 206336 (* h1 
h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) (* j2 j2)) (* 101376 (* h1 h1 h1) h2 (* h3 
h3 h3 h3) (* h5 h5) j2) (* 20480 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5)) (* 
768 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 11008 (* 
h1 h1 h1) h2 (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 61952 (* h1 h1 h1) 
h2 (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 178688 (* h1 h1 h1) h2 (* h3 h3 
h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 288512 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h5 h6 
(* j2 j2 j2)) (* 263936 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h5 h6 (* j2 j2)) (* 
128000 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h5 h6 j2) (* 25600 (* h1 h1 h1) h2 (* h3 
h3 h3 h3) h5 h6) (* 256 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2
 j2 j2 j2)) (* 3840 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 22528 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
67072 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 110848 (* h1
 h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2)) (* 103168 (* h1 h1 h1) h2 (* 
h3 h3 h3 h3) (* h6 h6) (* j2 j2)) (* 50688 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h6
 h6) j2) (* 10240 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6)) (* 256 (* h1 h1 h1)
 h2 (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 4672 (* h1 h1 h1) h2 
(* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 33472 (* h1 h1 h1) h2 (* h3 
h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 121600 (* h1 h1 h1) h2 (* h3 h3 h3) 
(* h4 h4) h5 (* j2 j2 j2 j2)) (* 243328 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) 
h5 (* j2 j2 j2)) (* 270400 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 (* j2 j2)) 
(* 156096 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 j2) (* 36480 (* h1 h1 h1) h2
 (* h3 h3 h3) (* h4 h4) h5) (* 128 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h6 (* 
j2 j2 j2 j2 j2 j2)) (* 1664 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 
j2 j2 j2)) (* 8192 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2)) 
(* 19712 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2)) (* 24704 (* h1 
h1 h1) h2 (* h3 h3 h3) (* h4 h4) h6 (* j2 j2)) (* 15488 (* h1 h1 h1) h2 (* h3 h3
 h3) (* h4 h4) h6 j2) (* 3840 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h6) (* 256 
(* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 4992 (* 
h1 h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 38400 (* h1 h1 
h1) h2 (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 149760 (* h1 h1 h1) h2 
(* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 318720 (* h1 h1 h1) h2 (* h3 h3 h3
) h4 (* h5 h5) (* j2 j2 j2)) (* 372096 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5)
 (* j2 j2)) (* 223232 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) j2) (* 53760 (* 
h1 h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5)) (* 512 (* h1 h1 h1) h2 (* h3 h3 h3) h4 
h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 9728 (* h1 h1 h1) h2 (* h3 h3 h3) h4 h5 h6 
(* j2 j2 j2 j2 j2 j2)) (* 72576 (* h1 h1 h1) h2 (* h3 h3 h3) h4 h5 h6 (* j2 j2 
j2 j2 j2)) (* 274176 (* h1 h1 h1) h2 (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 
567552 (* h1 h1 h1) h2 (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 648192 (* h1 h1 h1
) h2 (* h3 h3 h3) h4 h5 h6 (* j2 j2)) (* 382336 (* h1 h1 h1) h2 (* h3 h3 h3) h4 
h5 h6 j2) (* 90880 (* h1 h1 h1) h2 (* h3 h3 h3) h4 h5 h6) (* 256 (* h1 h1 h1) h2
 (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3456 (* h1 h1 h1) h2 (* h3 
h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 17664 (* h1 h1 h1) h2 (* h3 h3 h3) h4
 (* h6 h6) (* j2 j2 j2 j2)) (* 43776 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6) 
(* j2 j2 j2)) (* 56064 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6) (* j2 j2)) (* 
35712 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6) j2) (* 8960 (* h1 h1 h1) h2 (* 
h3 h3 h3) h4 (* h6 h6)) (* 256 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) (* j2 
j2 j2 j2 j2 j2)) (* 3584 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 
j2 j2)) (* 18944 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 
48128 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2)) (* 62720 (* h1 h1 
h1) h2 (* h3 h3 h3) (* h5 h5 h5) (* j2 j2)) (* 40448 (* h1 h1 h1) h2 (* h3 h3 h3
) (* h5 h5 h5) j2) (* 10240 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5)) (* 256 
(* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 5120 (* 
h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 40192 (* h1 h1 
h1) h2 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 159232 (* h1 h1 h1) h2 
(* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 342784 (* h1 h1 h1) h2 (* h3 h3 h3
) (* h5 h5) h6 (* j2 j2 j2)) (* 403456 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) h6
 (* j2 j2)) (* 243456 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) h6 j2) (* 58880 (* 
h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) h6) (* 256 (* h1 h1 h1) h2 (* h3 h3 h3) h5 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 5056 (* h1 h1 h1) h2 (* h3 h3 h3) h5 (* 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 39232 (* h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6)
 (* j2 j2 j2 j2 j2)) (* 153856 (* h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6) (* j2 
j2 j2 j2)) (* 328576 (* h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 
384448 (* h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2)) (* 230976 (* h1 h1 
h1) h2 (* h3 h3 h3) h5 (* h6 h6) j2) (* 55680 (* h1 h1 h1) h2 (* h3 h3 h3) h5 
(* h6 h6)) (* 128 (* h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2
)) (* 1792 (* h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 9472
 (* h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 24064 (* h1 h1 h1
) h2 (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2)) (* 31360 (* h1 h1 h1) h2 (* h3 h3 
h3) (* h6 h6 h6) (* j2 j2)) (* 20224 (* h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6) 
j2) (* 5120 (* h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6)) (* 64 (* h1 h1 h1) h2 (* 
h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 976 (* h1 h1 h1) h2 (* h3 h3) 
(* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 5664 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 
h4) h5 (* j2 j2 j2 j2)) (* 16224 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 (* j2
 j2 j2)) (* 24320 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 (* j2 j2)) (* 18128 
(* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 j2) (* 5280 (* h1 h1 h1) h2 (* h3 h3) 
(* h4 h4 h4) h5) (* 16 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 
j2)) (* 160 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2)) (* 608 
(* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2)) (* 1088 (* h1 h1 h1) h2 
(* h3 h3) (* h4 h4 h4) h6 (* j2 j2)) (* 912 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 
h4) h6 j2) (* 288 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h6) (* 128 (* h1 h1 h1)
 h2 (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2112 (* h1 h1 h1) h2
 (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 13440 (* h1 h1 h1) h2 (* 
h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 41824 (* h1 h1 h1) h2 (* h3 h3) 
(* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 67072 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) 
(* h5 h5) (* j2 j2)) (* 52640 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) j2) 
(* 15936 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5)) (* 192 (* h1 h1 h1) h2 
(* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 3104 (* h1 h1 h1) h2 (* h3 
h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 19200 (* h1 h1 h1) h2 (* h3 h3) (* h4
 h4) h5 h6 (* j2 j2 j2 j2)) (* 58368 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 h6 
(* j2 j2 j2)) (* 92032 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 
71392 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 h6 j2) (* 21440 (* h1 h1 h1) h2 (* 
h3 h3) (* h4 h4) h5 h6) (* 48 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h6 h6) (* 
j2 j2 j2 j2 j2)) (* 512 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 
j2 j2)) (* 2048 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 
3808 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2)) (* 3280 (* h1 h1 
h1) h2 (* h3 h3) (* h4 h4) (* h6 h6) j2) (* 1056 (* h1 h1 h1) h2 (* h3 h3) (* h4
 h4) (* h6 h6)) (* 64 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 
j2 j2)) (* 1136 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) 
(* 7744 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 25776 (* 
h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2)) (* 43808 (* h1 h1 h1) h2 
(* h3 h3) h4 (* h5 h5 h5) (* j2 j2)) (* 35968 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5
 h5 h5) j2) (* 11264 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5)) (* 256 (* h1 h1 
h1) h2 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 4400 (* h1 h1 h1) h2 
(* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 29184 (* h1 h1 h1) h2 (* h3 h3)
 h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 94800 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5
) h6 (* j2 j2 j2)) (* 157984 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2)
) (* 127840 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) h6 j2) (* 39616 (* h1 h1 h1) 
h2 (* h3 h3) h4 (* h5 h5) h6) (* 192 (* h1 h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 3280 (* h1 h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6) (* j2 
j2 j2 j2 j2)) (* 21504 (* h1 h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)
) (* 69040 (* h1 h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 113952 (* 
h1 h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 91552 (* h1 h1 h1) h2 (* h3
 h3) h4 h5 (* h6 h6) j2) (* 28224 (* h1 h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6)) (* 
48 (* h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 544 (* h1 h1
 h1) h2 (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 2288 (* h1 h1 h1) h2 (* h3
 h3) h4 (* h6 h6 h6) (* j2 j2 j2)) (* 4416 (* h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6
 h6) (* j2 j2)) (* 3904 (* h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6 h6) j2) (* 1280 
(* h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6 h6)) (* 32 (* h1 h1 h1) h2 (* h3 h3) (* h5
 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 384 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) 
(* j2 j2 j2 j2)) (* 1696 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2))
 (* 3392 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) (* j2 j2)) (* 3072 (* h1 h1 
h1) h2 (* h3 h3) (* h5 h5 h5 h5) j2) (* 1024 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 
h5 h5)) (* 64 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 1184 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 8384 
(* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 28832 (* h1 h1 h1)
 h2 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 50240 (* h1 h1 h1) h2 (* h3 h3) 
(* h5 h5 h5) h6 (* j2 j2)) (* 41984 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) h6 j2
) (* 13312 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) h6) (* 128 (* h1 h1 h1) h2 (* 
h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2288 (* h1 h1 h1) h2 (* h3 
h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 15776 (* h1 h1 h1) h2 (* h3 h3) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 53136 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5
) (* h6 h6) (* j2 j2 j2)) (* 91200 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6)
 (* j2 j2)) (* 75424 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6) j2) (* 23744 
(* h1 h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6)) (* 64 (* h1 h1 h1) h2 (* h3 h3) 
h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1152 (* h1 h1 h1) h2 (* h3 h3) h5 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 7968 (* h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6) 
(* j2 j2 j2 j2)) (* 26880 (* h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)
) (* 46176 (* h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 38208 (* h1 
h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6) j2) (* 12032 (* h1 h1 h1) h2 (* h3 h3) h5 
(* h6 h6 h6)) (* 16 (* h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)
) (* 192 (* h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 848 (* h1
 h1 h1) h2 (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 1696 (* h1 h1 h1) h2 (* h3
 h3) (* h6 h6 h6 h6) (* j2 j2)) (* 1536 (* h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6 h6
) j2) (* 512 (* h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6 h6)) (* 16 (* h1 h1 h1) h2 h3
 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 216 (* h1 h1 h1) h2 h3 (* h4 h4 
h4) (* h5 h5) (* j2 j2 j2 j2)) (* 1056 (* h1 h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5)
 (* j2 j2 j2)) (* 2392 (* h1 h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 
2528 (* h1 h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) j2) (* 992 (* h1 h1 h1) h2 h3 (* 
h4 h4 h4) (* h5 h5)) (* 8 (* h1 h1 h1) h2 h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2))
 (* 64 (* h1 h1 h1) h2 h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 184 (* h1 h1 h1) 
h2 h3 (* h4 h4 h4) h5 h6 (* j2 j2)) (* 224 (* h1 h1 h1) h2 h3 (* h4 h4 h4) h5 h6
 j2) (* 96 (* h1 h1 h1) h2 h3 (* h4 h4 h4) h5 h6) (* 16 (* h1 h1 h1) h2 h3 (* h4
 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 236 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 
h5 h5) (* j2 j2 j2 j2)) (* 1300 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) (* j2 
j2 j2)) (* 3272 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 3760 (* 
h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) j2) (* 1568 (* h1 h1 h1) h2 h3 (* h4 h4) 
(* h5 h5 h5)) (* 48 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)
) (* 704 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 3792 (* 
h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 9424 (* h1 h1 h1) h2 h3 
(* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 10800 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5
) h6 j2) (* 4512 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) h6) (* 24 (* h1 h1 h1) 
h2 h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 216 (* h1 h1 h1) h2 h3 (* h4 h4
) h5 (* h6 h6) (* j2 j2 j2)) (* 688 (* h1 h1 h1) h2 h3 (* h4 h4) h5 (* h6 h6) 
(* j2 j2)) (* 912 (* h1 h1 h1) h2 h3 (* h4 h4) h5 (* h6 h6) j2) (* 416 (* h1 h1 
h1) h2 h3 (* h4 h4) h5 (* h6 h6)) (* 16 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5 h5) 
(* j2 j2 j2 j2)) (* 144 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2)) (* 
448 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5 h5) (* j2 j2)) (* 576 (* h1 h1 h1) h2 h3 
h4 (* h5 h5 h5 h5) j2) (* 256 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5 h5)) (* 32 (* h1
 h1 h1) h2 h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 512 (* h1 h1 h1) h2 h3 
h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 3056 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5) 
h6 (* j2 j2 j2)) (* 8432 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5) h6 (* j2 j2)) (* 
10592 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5) h6 j2) (* 4736 (* h1 h1 h1) h2 h3 h4 
(* h5 h5 h5) h6) (* 48 (* h1 h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 760 (* h1 h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 4456 
(* h1 h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 12048 (* h1 h1 h1) h2
 h3 h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 14864 (* h1 h1 h1) h2 h3 h4 (* h5 h5) 
(* h6 h6) j2) (* 6560 (* h1 h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6)) (* 24 (* h1 h1 
h1) h2 h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 240 (* h1 h1 h1) h2 h3 h4 h5 
(* h6 h6 h6) (* j2 j2 j2)) (* 840 (* h1 h1 h1) h2 h3 h4 h5 (* h6 h6 h6) (* j2 j2
)) (* 1200 (* h1 h1 h1) h2 h3 h4 h5 (* h6 h6 h6) j2) (* 576 (* h1 h1 h1) h2 h3 
h4 h5 (* h6 h6 h6)) (* 16 (* h1 h1 h1) h2 h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2))
 (* 176 (* h1 h1 h1) h2 h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 672 (* h1 h1 h1) 
h2 h3 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 1024 (* h1 h1 h1) h2 h3 (* h5 h5 h5 h5) 
h6 j2) (* 512 (* h1 h1 h1) h2 h3 (* h5 h5 h5 h5) h6) (* 16 (* h1 h1 h1) h2 h3 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 276 (* h1 h1 h1) h2 h3 (* h5 h5 h5
) (* h6 h6) (* j2 j2 j2 j2)) (* 1772 (* h1 h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2)) (* 5224 (* h1 h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 
6912 (* h1 h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6) j2) (* 3200 (* h1 h1 h1) h2 h3 
(* h5 h5 h5) (* h6 h6)) (* 16 (* h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2
 j2 j2 j2)) (* 272 (* h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) 
(* 1720 (* h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 5000 (* h1 h1
 h1) h2 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 6544 (* h1 h1 h1) h2 h3 (* h5 h5
) (* h6 h6 h6) j2) (* 3008 (* h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6)) (* 8 (* h1
 h1 h1) h2 h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 88 (* h1 h1 h1) h2 h3 h5 
(* h6 h6 h6 h6) (* j2 j2 j2)) (* 336 (* h1 h1 h1) h2 h3 h5 (* h6 h6 h6 h6) (* j2
 j2)) (* 512 (* h1 h1 h1) h2 h3 h5 (* h6 h6 h6 h6) j2) (* 256 (* h1 h1 h1) h2 h3
 h5 (* h6 h6 h6 h6)) (* 2 (* h1 h1 h1) h2 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)
) (* 14 (* h1 h1 h1) h2 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 32 (* h1 h1 h1) 
h2 (* h4 h4 h4) (* h5 h5) h6 j2) (* 24 (* h1 h1 h1) h2 (* h4 h4 h4) (* h5 h5) h6
) (* 4 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 36 (* h1 h1 h1
) h2 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 96 (* h1 h1 h1) h2 (* h4 h4) (* h5 
h5 h5) h6 j2) (* 80 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5 h5) h6) (* 6 (* h1 h1 h1)
 h2 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 48 (* h1 h1 h1) h2 (* h4 h4) 
(* h5 h5) (* h6 h6) (* j2 j2)) (* 124 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 
h6) j2) (* 104 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 h6)) (* 2 (* h1 h1 h1) 
h2 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 16 (* h1 h1 h1) h2 h4 (* h5 h5 h5 h5) 
h6 (* j2 j2)) (* 40 (* h1 h1 h1) h2 h4 (* h5 h5 h5 h5) h6 j2) (* 32 (* h1 h1 h1)
 h2 h4 (* h5 h5 h5 h5) h6) (* 8 (* h1 h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6) (* j2 
j2 j2)) (* 78 (* h1 h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 240 (* h1 
h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6) j2) (* 232 (* h1 h1 h1) h2 h4 (* h5 h5 h5) 
(* h6 h6)) (* 6 (* h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 54 
(* h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 156 (* h1 h1 h1) h2 h4 
(* h5 h5) (* h6 h6 h6) j2) (* 144 (* h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6 h6)) (* 
2 (* h1 h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 20 (* h1 h1 h1) h2 
(* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 64 (* h1 h1 h1) h2 (* h5 h5 h5 h5) (* h6
 h6) j2) (* 64 (* h1 h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6)) (* 4 (* h1 h1 h1) h2 
(* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 42 (* h1 h1 h1) h2 (* h5 h5 h5) (* h6
 h6 h6) (* j2 j2)) (* 140 (* h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6) j2) (* 144 
(* h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6)) (* 2 (* h1 h1 h1) h2 (* h5 h5) (* h6 
h6 h6 h6) (* j2 j2 j2)) (* 20 (* h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2
)) (* 64 (* h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6 h6) j2) (* 64 (* h1 h1 h1) h2 (* 
h5 h5) (* h6 h6 h6 h6)) (* 256 (* h1 h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 
j2 j2 j2 j2 j2 j2)) (* 3584 (* h1 h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 
j2 j2 j2 j2)) (* 19712 (* h1 h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 
j2)) (* 55808 (* h1 h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 
88832 (* h1 h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 80384 (* h1 h1 
h1) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2)) (* 38656 (* h1 h1 h1) (* h3 h3 h3 h3
) (* h4 h4) h5 j2) (* 7680 (* h1 h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5) (* 256 (* 
h1 h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 3840 (* h1 
h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 22528 (* h1 h1 h1)
 (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 67072 (* h1 h1 h1) (* h3 h3
 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 110848 (* h1 h1 h1) (* h3 h3 h3 h3) h4 
(* h5 h5) (* j2 j2 j2)) (* 103168 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) (* 
j2 j2)) (* 50688 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) j2) (* 10240 (* h1 h1
 h1) (* h3 h3 h3 h3) h4 (* h5 h5)) (* 512 (* h1 h1 h1) (* h3 h3 h3 h3) h4 h5 h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 7936 (* h1 h1 h1) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2
 j2 j2 j2 j2)) (* 48384 (* h1 h1 h1) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)
) (* 150016 (* h1 h1 h1) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 257024 (* 
h1 h1 h1) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 246528 (* h1 h1 h1) (* h3 h3
 h3 h3) h4 h5 h6 (* j2 j2)) (* 124160 (* h1 h1 h1) (* h3 h3 h3 h3) h4 h5 h6 j2) 
(* 25600 (* h1 h1 h1) (* h3 h3 h3 h3) h4 h5 h6) (* 256 (* h1 h1 h1) (* h3 h3 h3 
h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 4352 (* h1 h1 h1) (* h3 h3 h3 h3) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 29184 (* h1 h1 h1) (* h3 h3 h3 h3) (* h5 
h5) h6 (* j2 j2 j2 j2 j2)) (* 98816 (* h1 h1 h1) (* h3 h3 h3 h3) (* h5 h5) h6 
(* j2 j2 j2 j2)) (* 181504 (* h1 h1 h1) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2
)) (* 183552 (* h1 h1 h1) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2)) (* 96256 (* h1
 h1 h1) (* h3 h3 h3 h3) (* h5 h5) h6 j2) (* 20480 (* h1 h1 h1) (* h3 h3 h3 h3) 
(* h5 h5) h6) (* 256 (* h1 h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2)) (* 4352 (* h1 h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)
) (* 29184 (* h1 h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
98816 (* h1 h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 181504 (* h1
 h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 183552 (* h1 h1 h1) (* h3 
h3 h3 h3) h5 (* h6 h6) (* j2 j2)) (* 96256 (* h1 h1 h1) (* h3 h3 h3 h3) h5 (* h6
 h6) j2) (* 20480 (* h1 h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6)) (* 128 (* h1 h1 h1)
 (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 1664 (* h1 h1 h1) (* h3 
h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 8192 (* h1 h1 h1) (* h3 h3 h3) (* 
h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 19712 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5
 (* j2 j2 j2)) (* 24704 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2)) (* 
15488 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 j2) (* 3840 (* h1 h1 h1) (* h3 
h3 h3) (* h4 h4 h4) h5) (* 256 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* 
j2 j2 j2 j2 j2 j2)) (* 3648 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 
j2 j2 j2 j2)) (* 19584 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2
 j2)) (* 50304 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 
66048 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 42816 (* h1 h1
 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) j2) (* 10880 (* h1 h1 h1) (* h3 h3 h3) (* 
h4 h4) (* h5 h5)) (* 384 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 
j2 j2 j2)) (* 5376 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2))
 (* 28672 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 74240 
(* h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 98688 (* h1 h1 h1) 
(* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 64768 (* h1 h1 h1) (* h3 h3 h3) (* h4
 h4) h5 h6 j2) (* 16640 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 h6) (* 128 (* h1 
h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1792 (* h1 h1 h1) 
(* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 9472 (* h1 h1 h1) (* h3 h3 
h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 24064 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5
 h5 h5) (* j2 j2 j2)) (* 31360 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 
j2)) (* 20224 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) j2) (* 5120 (* h1 h1 h1)
 (* h3 h3 h3) h4 (* h5 h5 h5)) (* 512 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 7808 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* 45440 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)
) (* 127232 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 179456 
(* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 123008 (* h1 h1 h1) (* 
h3 h3 h3) h4 (* h5 h5) h6 j2) (* 32640 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) h6
) (* 384 (* h1 h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
5760 (* h1 h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 33024 (* 
h1 h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 91392 (* h1 h1 h1) 
(* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 127872 (* h1 h1 h1) (* h3 h3 h3) 
h4 h5 (* h6 h6) (* j2 j2)) (* 87168 (* h1 h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6) j2
) (* 23040 (* h1 h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6)) (* 128 (* h1 h1 h1) (* h3 
h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 2048 (* h1 h1 h1) (* h3 h3 h3) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 12544 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5 
h5) h6 (* j2 j2 j2 j2)) (* 36864 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2
 j2 j2)) (* 53888 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2)) (* 37888 
(* h1 h1 h1) (* h3 h3 h3) (* h5 h5 h5) h6 j2) (* 10240 (* h1 h1 h1) (* h3 h3 h3)
 (* h5 h5 h5) h6) (* 256 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 4160 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2)) (* 25856 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) 
(* 76928 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 113408 
(* h1 h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 80192 (* h1 h1 h1) 
(* h3 h3 h3) (* h5 h5) (* h6 h6) j2) (* 21760 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5
) (* h6 h6)) (* 128 (* h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 2048 (* h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
12544 (* h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 36864 (* h1 
h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 53888 (* h1 h1 h1) (* h3 h3
 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 37888 (* h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6 
h6) j2) (* 10240 (* h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6)) (* 16 (* h1 h1 h1) 
(* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 160 (* h1 h1 h1) (* h3 h3) 
(* h4 h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 608 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4 h4
) h5 (* j2 j2 j2)) (* 1088 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2)) 
(* 912 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4 h4) h5 j2) (* 288 (* h1 h1 h1) (* h3 
h3) (* h4 h4 h4 h4) h5) (* 64 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* 
j2 j2 j2 j2 j2)) (* 752 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 
j2 j2)) (* 3216 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 
6256 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 5552 (* h1 h1 
h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) j2) (* 1824 (* h1 h1 h1) (* h3 h3) (* h4 h4
 h4) (* h5 h5)) (* 64 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 
j2)) (* 704 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 2912 
(* h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 5600 (* h1 h1 h1) (* 
h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2)) (* 4960 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4)
 h5 h6 j2) (* 1632 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 h6) (* 64 (* h1 h1 h1)
 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 800 (* h1 h1 h1) (* h3 
h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 3648 (* h1 h1 h1) (* h3 h3) (* h4
 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 7456 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 
h5 h5) (* j2 j2)) (* 6848 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) j2) (* 
2304 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5)) (* 192 (* h1 h1 h1) (* h3 h3
) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 2432 (* h1 h1 h1) (* h3 h3) (* 
h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 11344 (* h1 h1 h1) (* h3 h3) (* h4 h4) 
(* h5 h5) h6 (* j2 j2 j2)) (* 23968 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) 
h6 (* j2 j2)) (* 22672 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) h6 j2) (* 7808
 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) h6) (* 96 (* h1 h1 h1) (* h3 h3) (* 
h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1152 (* h1 h1 h1) (* h3 h3) (* h4 h4)
 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 5168 (* h1 h1 h1) (* h3 h3) (* h4 h4) h5 (* h6
 h6) (* j2 j2 j2)) (* 10656 (* h1 h1 h1) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 
j2)) (* 9936 (* h1 h1 h1) (* h3 h3) (* h4 h4) h5 (* h6 h6) j2) (* 3392 (* h1 h1 
h1) (* h3 h3) (* h4 h4) h5 (* h6 h6)) (* 16 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 
h5 h5) (* j2 j2 j2 j2 j2)) (* 192 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) (* 
j2 j2 j2 j2)) (* 848 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2)) (* 
1696 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2)) (* 1536 (* h1 h1 h1) 
(* h3 h3) h4 (* h5 h5 h5 h5) j2) (* 512 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5
)) (* 128 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 1728 
(* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 8640 (* h1 h1 h1) 
(* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 19520 (* h1 h1 h1) (* h3 h3) h4 
(* h5 h5 h5) h6 (* j2 j2)) (* 19392 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) h6 j2
) (* 6912 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) h6) (* 192 (* h1 h1 h1) (* h3 
h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2608 (* h1 h1 h1) (* h3 h3) h4
 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 13120 (* h1 h1 h1) (* h3 h3) h4 (* h5 
h5) (* h6 h6) (* j2 j2 j2)) (* 29808 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 
h6) (* j2 j2)) (* 29728 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6) j2) (* 
10624 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6)) (* 64 (* h1 h1 h1) (* h3 h3
) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 832 (* h1 h1 h1) (* h3 h3) h4 h5 (* 
h6 h6 h6) (* j2 j2 j2 j2)) (* 4032 (* h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6) (* 
j2 j2 j2)) (* 8896 (* h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2)) (* 8704 
(* h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6) j2) (* 3072 (* h1 h1 h1) (* h3 h3) h4 
h5 (* h6 h6 h6)) (* 16 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 
j2)) (* 224 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 1168 
(* h1 h1 h1) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 2752 (* h1 h1 h1) (* 
h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 2816 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5 
h5) h6 j2) (* 1024 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5 h5) h6) (* 64 (* h1 h1 h1)
 (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 928 (* h1 h1 h1) (* h3 
h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 4992 (* h1 h1 h1) (* h3 h3) (* h5
 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 12064 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* 
h6 h6) (* j2 j2)) (* 12544 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6) j2) (* 
4608 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6)) (* 64 (* h1 h1 h1) (* h3 h3)
 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 928 (* h1 h1 h1) (* h3 h3) (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 4992 (* h1 h1 h1) (* h3 h3) (* h5 h5) (* h6
 h6 h6) (* j2 j2 j2)) (* 12064 (* h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* 
j2 j2)) (* 12544 (* h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6) j2) (* 4608 (* h1
 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6)) (* 16 (* h1 h1 h1) (* h3 h3) h5 (* h6 
h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 224 (* h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6 h6) 
(* j2 j2 j2 j2)) (* 1168 (* h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2))
 (* 2752 (* h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2)) (* 2816 (* h1 h1 
h1) (* h3 h3) h5 (* h6 h6 h6 h6) j2) (* 1024 (* h1 h1 h1) (* h3 h3) h5 (* h6 h6 
h6 h6)) (* 4 (* h1 h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 32 
(* h1 h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 92 (* h1 h1 h1) h3 
(* h4 h4 h4 h4) (* h5 h5) (* j2 j2)) (* 112 (* h1 h1 h1) h3 (* h4 h4 h4 h4) (* 
h5 h5) j2) (* 48 (* h1 h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5)) (* 8 (* h1 h1 h1) h3
 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 80 (* h1 h1 h1) h3 (* h4 h4 h4) 
(* h5 h5 h5) (* j2 j2 j2)) (* 264 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) (* 
j2 j2)) (* 352 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) j2) (* 160 (* h1 h1 h1)
 h3 (* h4 h4 h4) (* h5 h5 h5)) (* 16 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) h6 
(* j2 j2 j2 j2)) (* 148 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) 
(* 484 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 656 (* h1 h1 h1) 
h3 (* h4 h4 h4) (* h5 h5) h6 j2) (* 304 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) 
h6) (* 4 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 36 (* h1 
h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 112 (* h1 h1 h1) h3 (* h4 
h4) (* h5 h5 h5 h5) (* j2 j2)) (* 144 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) 
j2) (* 64 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5)) (* 24 (* h1 h1 h1) h3 (* h4
 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 268 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 
h5) h6 (* j2 j2 j2)) (* 1028 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)
) (* 1568 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) h6 j2) (* 784 (* h1 h1 h1) h3 
(* h4 h4) (* h5 h5 h5) h6) (* 24 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2)) (* 252 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 
j2)) (* 932 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 1408 (* 
h1 h1 h1) h3 (* h4 h4) (* h5 h5) (* h6 h6) j2) (* 704 (* h1 h1 h1) h3 (* h4 h4) 
(* h5 h5) (* h6 h6)) (* 8 (* h1 h1 h1) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2))
 (* 88 (* h1 h1 h1) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 336 (* h1 h1 h1) 
h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 512 (* h1 h1 h1) h3 h4 (* h5 h5 h5 h5) h6
 j2) (* 256 (* h1 h1 h1) h3 h4 (* h5 h5 h5 h5) h6) (* 24 (* h1 h1 h1) h3 h4 (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 296 (* h1 h1 h1) h3 h4 (* h5 h5 h5) (* 
h6 h6) (* j2 j2 j2)) (* 1280 (* h1 h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)
) (* 2224 (* h1 h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6) j2) (* 1216 (* h1 h1 h1) h3 
h4 (* h5 h5 h5) (* h6 h6)) (* 16 (* h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2
 j2 j2 j2)) (* 188 (* h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 
780 (* h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 1312 (* h1 h1 h1) h3
 h4 (* h5 h5) (* h6 h6 h6) j2) (* 704 (* h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6))
 (* 4 (* h1 h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 52 (* h1 h1 
h1) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 240 (* h1 h1 h1) h3 (* h5 h5 
h5 h5) (* h6 h6) (* j2 j2)) (* 448 (* h1 h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6) j2)
 (* 256 (* h1 h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6)) (* 8 (* h1 h1 h1) h3 (* h5 h5
 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 108 (* h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6 
h6) (* j2 j2 j2)) (* 516 (* h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) 
(* 992 (* h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6) j2) (* 576 (* h1 h1 h1) h3 (* 
h5 h5 h5) (* h6 h6 h6)) (* 4 (* h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 
j2 j2)) (* 52 (* h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 240 (* 
h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 448 (* h1 h1 h1) h3 (* h5 
h5) (* h6 h6 h6 h6) j2) (* 256 (* h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6 h6)) (* 256
 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 2816 (* 
h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2 j2 j2)) (* 13056 (* h1 h1)
 (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2 j2)) (* 33024 (* h1 h1) (* h2 h2
 h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2)) (* 49152 (* h1 h1) (* h2 h2 h2 h2) (* 
h3 h3 h3) h5 (* j2 j2 j2)) (* 43008 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h5 
(* j2 j2)) (* 20480 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h5 j2) (* 4096 (* h1 
h1) (* h2 h2 h2 h2) (* h3 h3 h3) h5) (* 128 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 
h3) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1408 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) 
h6 (* j2 j2 j2 j2 j2 j2)) (* 6528 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h6 (* 
j2 j2 j2 j2 j2)) (* 16512 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2 
j2)) (* 24576 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2)) (* 21504 
(* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2)) (* 10240 (* h1 h1) (* h2 h2
 h2 h2) (* h3 h3 h3) h6 j2) (* 2048 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h6) 
(* 192 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 1920 
(* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 7872 (* h1 h1) 
(* h2 h2 h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2)) (* 16896 (* h1 h1) (* h2 h2 h2 
h2) (* h3 h3) h4 h5 (* j2 j2 j2)) (* 19968 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) 
h4 h5 (* j2 j2)) (* 12288 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h5 j2) (* 3072 
(* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h5) (* 64 (* h1 h1) (* h2 h2 h2 h2) (* h3
 h3) h4 h6 (* j2 j2 j2 j2 j2 j2)) (* 640 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 
h6 (* j2 j2 j2 j2 j2)) (* 2624 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h6 (* j2 
j2 j2 j2)) (* 5632 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2)) (* 
6656 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h6 (* j2 j2)) (* 4096 (* h1 h1) (* 
h2 h2 h2 h2) (* h3 h3) h4 h6 j2) (* 1024 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 
h6) (* 128 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) 
(* 1280 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 
5248 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 11264 (* 
h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2)) (* 13312 (* h1 h1) (* 
h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* j2 j2)) (* 8192 (* h1 h1) (* h2 h2 h2 h2) 
(* h3 h3) (* h5 h5) j2) (* 2048 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h5 h5)) 
(* 192 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 1920 
(* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 7872 (* h1 h1) 
(* h2 h2 h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 16896 (* h1 h1) (* h2 h2 h2 
h2) (* h3 h3) h5 h6 (* j2 j2 j2)) (* 19968 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) 
h5 h6 (* j2 j2)) (* 12288 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 h6 j2) (* 3072 
(* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 h6) (* 64 (* h1 h1) (* h2 h2 h2 h2) (* h3
 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 640 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3)
 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2624 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h6
 h6) (* j2 j2 j2 j2)) (* 5632 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h6 h6) (* 
j2 j2 j2)) (* 6656 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2)) (* 
4096 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h6 h6) j2) (* 1024 (* h1 h1) (* h2 
h2 h2 h2) (* h3 h3) (* h6 h6)) (* 48 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h5 h5) 
(* j2 j2 j2 j2 j2)) (* 432 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2
 j2)) (* 1536 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2)) (* 2688 
(* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2)) (* 2304 (* h1 h1) (* h2 h2 
h2 h2) h3 h4 (* h5 h5) j2) (* 768 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h5 h5)) (* 
32 (* h1 h1) (* h2 h2 h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 288 (* h1 h1) 
(* h2 h2 h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2)) (* 1024 (* h1 h1) (* h2 h2 h2 h2) 
h3 h4 h5 h6 (* j2 j2 j2)) (* 1792 (* h1 h1) (* h2 h2 h2 h2) h3 h4 h5 h6 (* j2 j2
)) (* 1536 (* h1 h1) (* h2 h2 h2 h2) h3 h4 h5 h6 j2) (* 512 (* h1 h1) (* h2 h2 
h2 h2) h3 h4 h5 h6) (* 4 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2 
j2 j2)) (* 36 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2 j2)) (* 128 
(* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2)) (* 224 (* h1 h1) (* h2 
h2 h2 h2) h3 h4 (* h6 h6) (* j2 j2)) (* 192 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* 
h6 h6) j2) (* 64 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h6 h6)) (* 16 (* h1 h1) (* 
h2 h2 h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 144 (* h1 h1) (* h2 h2 h2 h2
) h3 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 512 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5 
h5) (* j2 j2 j2)) (* 896 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* j2 j2)) 
(* 768 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5 h5) j2) (* 256 (* h1 h1) (* h2 h2 
h2 h2) h3 (* h5 h5 h5)) (* 48 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) h6 (* j2 j2
 j2 j2 j2)) (* 432 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2)) 
(* 1536 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2)) (* 2688 (* h1 h1
) (* h2 h2 h2 h2) h3 (* h5 h5) h6 (* j2 j2)) (* 2304 (* h1 h1) (* h2 h2 h2 h2) 
h3 (* h5 h5) h6 j2) (* 768 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) h6) (* 28 (* 
h1 h1) (* h2 h2 h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 252 (* h1 h1) (* 
h2 h2 h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 896 (* h1 h1) (* h2 h2 h2 h2) 
h3 h5 (* h6 h6) (* j2 j2 j2)) (* 1568 (* h1 h1) (* h2 h2 h2 h2) h3 h5 (* h6 h6) 
(* j2 j2)) (* 1344 (* h1 h1) (* h2 h2 h2 h2) h3 h5 (* h6 h6) j2) (* 448 (* h1 h1
) (* h2 h2 h2 h2) h3 h5 (* h6 h6)) (* 4 (* h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6 h6
) (* j2 j2 j2 j2 j2)) (* 36 (* h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6 h6) (* j2 j2 
j2 j2)) (* 128 (* h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2)) (* 224 
(* h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6 h6) (* j2 j2)) (* 192 (* h1 h1) (* h2 h2 
h2 h2) h3 (* h6 h6 h6) j2) (* 64 (* h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6 h6)) (* 8
 (* h1 h1) (* h2 h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 64 (* h1 h1) (* 
h2 h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 192 (* h1 h1) (* h2 h2 h2 h2) h4 
(* h5 h5) h6 (* j2 j2)) (* 256 (* h1 h1) (* h2 h2 h2 h2) h4 (* h5 h5) h6 j2) (* 
128 (* h1 h1) (* h2 h2 h2 h2) h4 (* h5 h5) h6) (* 2 (* h1 h1) (* h2 h2 h2 h2) h4
 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 16 (* h1 h1) (* h2 h2 h2 h2) h4 h5 (* h6 h6) 
(* j2 j2 j2)) (* 48 (* h1 h1) (* h2 h2 h2 h2) h4 h5 (* h6 h6) (* j2 j2)) (* 64 
(* h1 h1) (* h2 h2 h2 h2) h4 h5 (* h6 h6) j2) (* 32 (* h1 h1) (* h2 h2 h2 h2) h4
 h5 (* h6 h6)) (* 4 (* h1 h1) (* h2 h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) 
(* 32 (* h1 h1) (* h2 h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 96 (* h1 h1) 
(* h2 h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2)) (* 128 (* h1 h1) (* h2 h2 h2 h2) (* 
h5 h5 h5) h6 j2) (* 64 (* h1 h1) (* h2 h2 h2 h2) (* h5 h5 h5) h6) (* 6 (* h1 h1)
 (* h2 h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 48 (* h1 h1) (* h2 h2 
h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 144 (* h1 h1) (* h2 h2 h2 h2) (* h5 
h5) (* h6 h6) (* j2 j2)) (* 192 (* h1 h1) (* h2 h2 h2 h2) (* h5 h5) (* h6 h6) j2
) (* 96 (* h1 h1) (* h2 h2 h2 h2) (* h5 h5) (* h6 h6)) (* 2 (* h1 h1) (* h2 h2 
h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 16 (* h1 h1) (* h2 h2 h2 h2) h5 (* h6
 h6 h6) (* j2 j2 j2)) (* 48 (* h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2))
 (* 64 (* h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6 h6) j2) (* 32 (* h1 h1) (* h2 h2 h2
 h2) h5 (* h6 h6 h6)) (* 1024 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2
 j2 j2 j2 j2 j2)) (* 10240 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2 j2
 j2 j2 j2)) (* 43008 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2 j2 j2 j2
)) (* 98304 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2 j2 j2)) (* 132096
 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2 j2)) (* 104448 (* h1 h1) (* 
h2 h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2)) (* 45056 (* h1 h1) (* h2 h2 h2) (* h3 h3
 h3 h3) h5 j2) (* 8192 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h5) (* 512 (* h1 
h1) (* h2 h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 5120 (* h1 h1) 
(* h2 h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2 j2 j2 j2 j2)) (* 21504 (* h1 h1) (* h2 
h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2 j2 j2 j2)) (* 49152 (* h1 h1) (* h2 h2 h2) 
(* h3 h3 h3 h3) h6 (* j2 j2 j2 j2)) (* 66048 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 
h3) h6 (* j2 j2 j2)) (* 52224 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2
)) (* 22528 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h6 j2) (* 4096 (* h1 h1) (* 
h2 h2 h2) (* h3 h3 h3 h3) h6) (* 768 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h5 
(* j2 j2 j2 j2 j2 j2 j2)) (* 10624 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* 
j2 j2 j2 j2 j2 j2)) (* 58752 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 
j2 j2 j2)) (* 170880 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2)) 
(* 284544 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2)) (* 272640 (* 
h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2)) (* 139776 (* h1 h1) (* h2 h2 
h2) (* h3 h3 h3) h4 h5 j2) (* 29696 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h5) 
(* 192 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
2816 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2)) (* 16128 
(* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 48000 (* h1 h1)
 (* h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 81216 (* h1 h1) (* h2 h2 h2
) (* h3 h3 h3) h4 h6 (* j2 j2 j2)) (* 78720 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) 
h4 h6 (* j2 j2)) (* 40704 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h6 j2) (* 8704 
(* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h6) (* 384 (* h1 h1) (* h2 h2 h2) (* h3 
h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 5504 (* h1 h1) (* h2 h2 h2) (* h3 
h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 31104 (* h1 h1) (* h2 h2 h2) (* h3 h3
 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 91776 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) 
(* h5 h5) (* j2 j2 j2 j2)) (* 154368 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h5 
h5) (* j2 j2 j2)) (* 148992 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 
j2)) (* 76800 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) j2) (* 16384 (* h1 
h1) (* h2 h2 h2) (* h3 h3 h3) (* h5 h5)) (* 576 (* h1 h1) (* h2 h2 h2) (* h3 h3 
h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 8256 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) 
h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 46656 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 h6 
(* j2 j2 j2 j2 j2)) (* 137664 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2
 j2 j2)) (* 231552 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2)) (* 
223488 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2)) (* 115200 (* h1 h1) 
(* h2 h2 h2) (* h3 h3 h3) h5 h6 j2) (* 24576 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3)
 h5 h6) (* 192 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 2816 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 16128 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 48000 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 81216
 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2)) (* 78720 (* h1 h1) 
(* h2 h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2)) (* 40704 (* h1 h1) (* h2 h2 h2) 
(* h3 h3 h3) (* h6 h6) j2) (* 8704 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h6 h6)
) (* 288 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) 
(* 3488 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 
16672 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 40544 
(* h1 h1) (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 53056 (* h1 h1) 
(* h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2)) (* 35456 (* h1 h1) (* h2 h2 h2) 
(* h3 h3) (* h4 h4) h5 j2) (* 9472 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h4 h4) h5
) (* 48 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 
624 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 3120 
(* h1 h1) (* h2 h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2)) (* 7824 (* h1 h1)
 (* h2 h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2 j2)) (* 10464 (* h1 h1) (* h2 h2 
h2) (* h3 h3) (* h4 h4) h6 (* j2 j2)) (* 7104 (* h1 h1) (* h2 h2 h2) (* h3 h3) 
(* h4 h4) h6 j2) (* 1920 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h4 h4) h6) (* 384 
(* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 4800 (* 
h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 23424 (* h1 h1
) (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 57792 (* h1 h1) (* h2 
h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 76416 (* h1 h1) (* h2 h2 h2) (* 
h3 h3) h4 (* h5 h5) (* j2 j2)) (* 51456 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* 
h5 h5) j2) (* 13824 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h5 h5)) (* 576 (* h1 
h1) (* h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 7136 (* h1 h1) (* 
h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 34624 (* h1 h1) (* h2 h2 h2)
 (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 85088 (* h1 h1) (* h2 h2 h2) (* h3 h3) 
h4 h5 h6 (* j2 j2 j2)) (* 112192 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2
 j2)) (* 75392 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 h6 j2) (* 20224 (* h1 h1) 
(* h2 h2 h2) (* h3 h3) h4 h5 h6) (* 96 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h6
 h6) (* j2 j2 j2 j2 j2 j2)) (* 1264 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h6 h6
) (* j2 j2 j2 j2 j2)) (* 6368 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h6 h6) (* 
j2 j2 j2 j2)) (* 16048 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2
)) (* 21536 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2)) (* 14656 
(* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h6 h6) j2) (* 3968 (* h1 h1) (* h2 h2 h2)
 (* h3 h3) h4 (* h6 h6)) (* 96 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* 
j2 j2 j2 j2 j2 j2)) (* 1248 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 
j2 j2 j2 j2)) (* 6240 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 
j2)) (* 15648 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2)) (* 
20928 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2)) (* 14208 (* h1 h1
) (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) j2) (* 3840 (* h1 h1) (* h2 h2 h2) (* h3 
h3) (* h5 h5 h5)) (* 336 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 
j2 j2 j2 j2)) (* 4240 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 
j2 j2)) (* 20816 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) 
(* 51568 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 68384 
(* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2)) (* 46144 (* h1 h1) (* 
h2 h2 h2) (* h3 h3) (* h5 h5) h6 j2) (* 12416 (* h1 h1) (* h2 h2 h2) (* h3 h3) 
(* h5 h5) h6) (* 288 (* h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 3632 (* h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 17824 (* h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 
44144 (* h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 58528 (* h1
 h1) (* h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2)) (* 39488 (* h1 h1) (* h2 h2 
h2) (* h3 h3) h5 (* h6 h6) j2) (* 10624 (* h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* 
h6 h6)) (* 48 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2
)) (* 640 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
3248 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 8224 (* 
h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2)) (* 11072 (* h1 h1) (* 
h2 h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2)) (* 7552 (* h1 h1) (* h2 h2 h2) (* h3
 h3) (* h6 h6 h6) j2) (* 2048 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6 h6)) (* 
72 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 784 (* 
h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 3256 (* h1 h1) 
(* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 6480 (* h1 h1) (* h2 h2 h2)
 h3 (* h4 h4) (* h5 h5) (* j2 j2)) (* 6176 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) 
(* h5 h5) j2) (* 2240 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h5 h5)) (* 24 (* h1
 h1) (* h2 h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 280 (* h1 h1) (* h2 
h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 1216 (* h1 h1) (* h2 h2 h2) h3 (* 
h4 h4) h5 h6 (* j2 j2 j2)) (* 2496 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) h5 h6 (* 
j2 j2)) (* 2432 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) h5 h6 j2) (* 896 (* h1 h1) 
(* h2 h2 h2) h3 (* h4 h4) h5 h6) (* 4 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h6 
h6) (* j2 j2 j2 j2)) (* 28 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 
j2 j2)) (* 72 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 j2)) (* 80 (* 
h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h6 h6) j2) (* 32 (* h1 h1) (* h2 h2 h2) h3 
(* h4 h4) (* h6 h6)) (* 48 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2
 j2 j2)) (* 544 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 
2320 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2)) (* 4704 (* h1 h1) 
(* h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2)) (* 4544 (* h1 h1) (* h2 h2 h2) h3 h4 
(* h5 h5 h5) j2) (* 1664 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5 h5)) (* 144 (* h1
 h1) (* h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 1624 (* h1 h1) (* h2
 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 6904 (* h1 h1) (* h2 h2 h2) h3 h4
 (* h5 h5) h6 (* j2 j2 j2)) (* 13968 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) h6 
(* j2 j2)) (* 13472 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) h6 j2) (* 4928 (* h1 
h1) (* h2 h2 h2) h3 h4 (* h5 h5) h6) (* 48 (* h1 h1) (* h2 h2 h2) h3 h4 h5 (* h6
 h6) (* j2 j2 j2 j2 j2)) (* 568 (* h1 h1) (* h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 
j2 j2 j2)) (* 2488 (* h1 h1) (* h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2)) (* 
5136 (* h1 h1) (* h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2)) (* 5024 (* h1 h1) (* 
h2 h2 h2) h3 h4 h5 (* h6 h6) j2) (* 1856 (* h1 h1) (* h2 h2 h2) h3 h4 h5 (* h6 
h6)) (* 8 (* h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 56 (* h1
 h1) (* h2 h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2 j2)) (* 144 (* h1 h1) (* h2 h2 h2)
 h3 h4 (* h6 h6 h6) (* j2 j2)) (* 160 (* h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6 h6) 
j2) (* 64 (* h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6 h6)) (* 16 (* h1 h1) (* h2 h2 h2
) h3 (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 112 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 
h5 h5) (* j2 j2 j2)) (* 288 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* j2 j2))
 (* 320 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5 h5) j2) (* 128 (* h1 h1) (* h2 h2 
h2) h3 (* h5 h5 h5 h5)) (* 48 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2
 j2 j2 j2)) (* 560 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) 
(* 2432 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 4992 (* h1 h1
) (* h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2)) (* 4864 (* h1 h1) (* h2 h2 h2) h3 
(* h5 h5 h5) h6 j2) (* 1792 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) h6) (* 72 (* 
h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 828 (* h1 h1) 
(* h2 h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 3564 (* h1 h1) (* h2 h2 
h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 7272 (* h1 h1) (* h2 h2 h2) h3 (* h5
 h5) (* h6 h6) (* j2 j2)) (* 7056 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* h6 h6) 
j2) (* 2592 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* h6 h6)) (* 24 (* h1 h1) (* h2
 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 288 (* h1 h1) (* h2 h2 h2) h3 
h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1272 (* h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6 
h6) (* j2 j2 j2)) (* 2640 (* h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2)) 
(* 2592 (* h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6 h6) j2) (* 960 (* h1 h1) (* h2 h2 
h2) h3 h5 (* h6 h6 h6)) (* 4 (* h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6 h6) (* j2 j2 
j2 j2)) (* 28 (* h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 72 (* 
h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6 h6) (* j2 j2)) (* 80 (* h1 h1) (* h2 h2 h2) 
h3 (* h6 h6 h6 h6) j2) (* 32 (* h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6 h6)) (* 6 (* 
h1 h1) (* h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 64 (* h1 h1) (* 
h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 240 (* h1 h1) (* h2 h2 h2) (* 
h4 h4) (* h5 h5) h6 (* j2 j2)) (* 384 (* h1 h1) (* h2 h2 h2) (* h4 h4) (* h5 h5)
 h6 j2) (* 224 (* h1 h1) (* h2 h2 h2) (* h4 h4) (* h5 h5) h6) (* 2 (* h1 h1) (* 
h2 h2 h2) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 12 (* h1 h1) (* h2 h2 h2) (* 
h4 h4) h5 (* h6 h6) (* j2 j2)) (* 24 (* h1 h1) (* h2 h2 h2) (* h4 h4) h5 (* h6 
h6) j2) (* 16 (* h1 h1) (* h2 h2 h2) (* h4 h4) h5 (* h6 h6)) (* 6 (* h1 h1) (* 
h2 h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 66 (* h1 h1) (* h2 h2 h2) h4 
(* h5 h5 h5) h6 (* j2 j2 j2)) (* 252 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5 h5) h6 
(* j2 j2)) (* 408 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5 h5) h6 j2) (* 240 (* h1 h1)
 (* h2 h2 h2) h4 (* h5 h5 h5) h6) (* 12 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2)) (* 128 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* 
j2 j2 j2)) (* 480 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 
768 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5) (* h6 h6) j2) (* 448 (* h1 h1) (* h2 h2 
h2) h4 (* h5 h5) (* h6 h6)) (* 4 (* h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6 h6) (* j2
 j2 j2)) (* 24 (* h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2)) (* 48 (* h1 
h1) (* h2 h2 h2) h4 h5 (* h6 h6 h6) j2) (* 32 (* h1 h1) (* h2 h2 h2) h4 h5 (* h6
 h6 h6)) (* 4 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 24 (* 
h1 h1) (* h2 h2 h2) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 48 (* h1 h1) (* h2 h2 h2) 
(* h5 h5 h5 h5) h6 j2) (* 32 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5 h5) h6) (* 6 (* 
h1 h1) (* h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 64 (* h1 h1) (* 
h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 240 (* h1 h1) (* h2 h2 h2) (* 
h5 h5 h5) (* h6 h6) (* j2 j2)) (* 384 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5) (* h6 
h6) j2) (* 224 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5) (* h6 h6)) (* 6 (* h1 h1) (* 
h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 64 (* h1 h1) (* h2 h2 h2) 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 240 (* h1 h1) (* h2 h2 h2) (* h5 h5) (* 
h6 h6 h6) (* j2 j2)) (* 384 (* h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6 h6) j2) 
(* 224 (* h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6 h6)) (* 2 (* h1 h1) (* h2 h2 h2
) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 12 (* h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6 
h6) (* j2 j2)) (* 24 (* h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6 h6) j2) (* 16 (* h1 
h1) (* h2 h2 h2) h5 (* h6 h6 h6 h6)) (* 2048 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3)
 h4 h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 25088 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4
 h5 (* j2 j2 j2 j2 j2 j2)) (* 122880 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h5 
(* j2 j2 j2 j2 j2)) (* 316416 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2
 j2 j2)) (* 466944 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2)) (* 
397824 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2)) (* 182272 (* h1 h1) 
(* h2 h2) (* h3 h3 h3 h3) h4 h5 j2) (* 34816 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3)
 h4 h5) (* 512 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2
)) (* 6656 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2)) (* 
33792 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 89088 (* 
h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 133632 (* h1 h1) (* 
h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2)) (* 115200 (* h1 h1) (* h2 h2) (* h3 
h3 h3 h3) h4 h6 (* j2 j2)) (* 53248 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h6 j2
) (* 10240 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h6) (* 1024 (* h1 h1) (* h2 h2
) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 12800 (* h1 h1) (* h2 
h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 63488 (* h1 h1) (* h2 h2
) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 164864 (* h1 h1) (* h2 h2) 
(* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 244736 (* h1 h1) (* h2 h2) (* h3 
h3 h3 h3) (* h5 h5) (* j2 j2 j2)) (* 209408 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) 
(* h5 h5) (* j2 j2)) (* 96256 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) j2) 
(* 18432 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h5 h5)) (* 1536 (* h1 h1) (* h2 
h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 19200 (* h1 h1) (* h2 h2)
 (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 95232 (* h1 h1) (* h2 h2) (* h3
 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 247296 (* h1 h1) (* h2 h2) (* h3 h3 h3 
h3) h5 h6 (* j2 j2 j2 j2)) (* 367104 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 h6 
(* j2 j2 j2)) (* 314112 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2)) (* 
144384 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 h6 j2) (* 27648 (* h1 h1) (* h2 h2
) (* h3 h3 h3 h3) h5 h6) (* 512 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 6656 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 33792 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* 89088 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2
 j2 j2 j2)) (* 133632 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2)
) (* 115200 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2)) (* 53248 
(* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h6 h6) j2) (* 10240 (* h1 h1) (* h2 h2) 
(* h3 h3 h3 h3) (* h6 h6)) (* 384 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 
(* j2 j2 j2 j2 j2 j2 j2)) (* 6592 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 
(* j2 j2 j2 j2 j2 j2)) (* 43904 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 
(* j2 j2 j2 j2 j2)) (* 148736 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* 
j2 j2 j2 j2)) (* 280064 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 
j2)) (* 296000 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2)) (* 
164096 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 j2) (* 37120 (* h1 h1) (* 
h2 h2) (* h3 h3 h3) (* h4 h4) h5) (* 256 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 
h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 2944 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4)
 h6 (* j2 j2 j2 j2 j2)) (* 12928 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h6 
(* j2 j2 j2 j2)) (* 28288 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2
 j2)) (* 32896 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2)) (* 19456
 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h6 j2) (* 4608 (* h1 h1) (* h2 h2) 
(* h3 h3 h3) (* h4 h4) h6) (* 384 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 7040 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) 
(* j2 j2 j2 j2 j2 j2)) (* 49600 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) 
(* j2 j2 j2 j2 j2)) (* 175168 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* 
j2 j2 j2 j2)) (* 339904 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 
j2)) (* 367168 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2)) (* 
206848 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) j2) (* 47360 (* h1 h1) (* 
h2 h2) (* h3 h3 h3) h4 (* h5 h5)) (* 768 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 13376 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 h6 
(* j2 j2 j2 j2 j2 j2)) (* 90432 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 
j2 j2 j2 j2)) (* 310080 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2
)) (* 589248 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 627072 
(* h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2)) (* 349440 (* h1 h1) (* h2 
h2) (* h3 h3 h3) h4 h5 h6 j2) (* 79360 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 h6
) (* 512 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 5952 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
26304 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 57792 
(* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2)) (* 67392 (* h1 h1) 
(* h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2)) (* 39936 (* h1 h1) (* h2 h2) (* 
h3 h3 h3) h4 (* h6 h6) j2) (* 9472 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h6 h6)
) (* 512 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) 
(* 5888 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 
25856 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 56576 
(* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2)) (* 65792 (* h1 h1) 
(* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2)) (* 38912 (* h1 h1) (* h2 h2) (* 
h3 h3 h3) (* h5 h5 h5) j2) (* 9216 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5 h5)
) (* 384 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2))
 (* 6912 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 47936 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
167360 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 322112 
(* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 345920 (* h1 h1) 
(* h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2)) (* 194048 (* h1 h1) (* h2 h2) (* 
h3 h3 h3) (* h5 h5) h6 j2) (* 44288 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) 
h6) (* 384 (* h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2
)) (* 6784 (* h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 46464 (* h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
160896 (* h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 307968 
(* h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 329472 (* h1 h1) 
(* h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2)) (* 184320 (* h1 h1) (* h2 h2) (* 
h3 h3 h3) h5 (* h6 h6) j2) (* 41984 (* h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* h6 h6
)) (* 256 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 3008 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
13376 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 29504 
(* h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2)) (* 34496 (* h1 h1) 
(* h2 h2) (* h3 h3 h3) (* h6 h6 h6) (* j2 j2)) (* 20480 (* h1 h1) (* h2 h2) (* 
h3 h3 h3) (* h6 h6 h6) j2) (* 4864 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6 h6)
) (* 96 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 
1392 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 7632 
(* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 20688 (* h1 h1
) (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 29520 (* h1 h1) (* h2 h2)
 (* h3 h3) (* h4 h4 h4) h5 (* j2 j2)) (* 21120 (* h1 h1) (* h2 h2) (* h3 h3) (* 
h4 h4 h4) h5 j2) (* 5952 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4 h4) h5) (* 32 
(* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 288 (* h1 
h1) (* h2 h2) (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2)) (* 992 (* h1 h1) (* h2 
h2) (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2)) (* 1632 (* h1 h1) (* h2 h2) (* h3 h3
) (* h4 h4 h4) h6 (* j2 j2)) (* 1280 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4 h4) 
h6 j2) (* 384 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4 h4) h6) (* 192 (* h1 h1) 
(* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 3008 (* h1 h1)
 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 17888 (* h1 h1) 
(* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 51968 (* h1 h1) (* 
h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 78368 (* h1 h1) (* h2 h2) 
(* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 58496 (* h1 h1) (* h2 h2) (* h3 h3) 
(* h4 h4) (* h5 h5) j2) (* 17024 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h5 
h5)) (* 288 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2))
 (* 4336 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 
24688 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 69136 
(* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 101296 (* h1 h1) 
(* h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 73984 (* h1 h1) (* h2 h2) (* 
h3 h3) (* h4 h4) h5 h6 j2) (* 21184 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 
h6) (* 96 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 896 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 
3168 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 5312 (* 
h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2)) (* 4224 (* h1 h1) (* 
h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) j2) (* 1280 (* h1 h1) (* h2 h2) (* h3 h3) 
(* h4 h4) (* h6 h6)) (* 96 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 
j2 j2 j2 j2 j2)) (* 1616 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 
j2 j2 j2)) (* 10144 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2
)) (* 30608 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2)) (* 47392
 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2)) (* 36032 (* h1 h1) (* 
h2 h2) (* h3 h3) h4 (* h5 h5 h5) j2) (* 10624 (* h1 h1) (* h2 h2) (* h3 h3) h4 
(* h5 h5 h5)) (* 384 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 
j2 j2 j2)) (* 6080 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 
j2)) (* 36512 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 
106880 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 162080 (* 
h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 121472 (* h1 h1) (* h2 
h2) (* h3 h3) h4 (* h5 h5) h6 j2) (* 35456 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* 
h5 h5) h6) (* 288 (* h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 4496 (* h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)
) (* 26480 (* h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 
76208 (* h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 114032 (* 
h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 84608 (* h1 h1) (* h2 
h2) (* h3 h3) h4 h5 (* h6 h6) j2) (* 24512 (* h1 h1) (* h2 h2) (* h3 h3) h4 h5 
(* h6 h6)) (* 96 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2
)) (* 928 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 3360
 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2)) (* 5728 (* h1 h1) 
(* h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2)) (* 4608 (* h1 h1) (* h2 h2) (* h3
 h3) h4 (* h6 h6 h6) j2) (* 1408 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6 h6)) 
(* 64 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 640 
(* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 2368 (* h1 h1)
 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 4096 (* h1 h1) (* h2 h2) 
(* h3 h3) (* h5 h5 h5 h5) (* j2 j2)) (* 3328 (* h1 h1) (* h2 h2) (* h3 h3) (* h5
 h5 h5 h5) j2) (* 1024 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5 h5)) (* 96 (* 
h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 1616 (* h1 
h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 10112 (* h1 h1) 
(* h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 30416 (* h1 h1) (* h2 h2
) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 46976 (* h1 h1) (* h2 h2) (* h3 h3)
 (* h5 h5 h5) h6 (* j2 j2)) (* 35648 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) 
h6 j2) (* 10496 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) h6) (* 192 (* h1 h1) 
(* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3072 (* h1 h1)
 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 18592 (* h1 h1) 
(* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 54720 (* h1 h1) (* 
h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 83296 (* h1 h1) (* h2 h2) 
(* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 62592 (* h1 h1) (* h2 h2) (* h3 h3) 
(* h5 h5) (* h6 h6) j2) (* 18304 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* h6 
h6)) (* 96 (* h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 1552 (* h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
9424 (* h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 27760 (* 
h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 42256 (* h1 h1) (* 
h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 31744 (* h1 h1) (* h2 h2) (* h3 
h3) h5 (* h6 h6 h6) j2) (* 9280 (* h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6 h6)) 
(* 32 (* h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 320 
(* h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 1184 (* h1 h1)
 (* h2 h2) (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 2048 (* h1 h1) (* h2 h2) 
(* h3 h3) (* h6 h6 h6 h6) (* j2 j2)) (* 1664 (* h1 h1) (* h2 h2) (* h3 h3) (* h6
 h6 h6 h6) j2) (* 512 (* h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6 h6)) (* 24 (* h1
 h1) (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 312 (* h1 h1) 
(* h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 1468 (* h1 h1) (* h2 h2)
 h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 3212 (* h1 h1) (* h2 h2) h3 (* h4 h4
 h4) (* h5 h5) (* j2 j2)) (* 3296 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) 
j2) (* 1264 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) (* h5 h5)) (* 16 (* h1 h1) (* h2
 h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 120 (* h1 h1) (* h2 h2) h3 (* h4 
h4 h4) h5 h6 (* j2 j2 j2)) (* 328 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) h5 h6 (* 
j2 j2)) (* 384 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) h5 h6 j2) (* 160 (* h1 h1) 
(* h2 h2) h3 (* h4 h4 h4) h5 h6) (* 24 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5
 h5) (* j2 j2 j2 j2 j2)) (* 340 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) 
(* j2 j2 j2 j2)) (* 1772 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 
j2)) (* 4256 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 4720 
(* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) j2) (* 1920 (* h1 h1) (* h2 h2) h3
 (* h4 h4) (* h5 h5 h5)) (* 72 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* 
j2 j2 j2 j2 j2)) (* 988 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 
j2 j2)) (* 4924 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 
11352 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 12176 (* h1 h1
) (* h2 h2) h3 (* h4 h4) (* h5 h5) h6 j2) (* 4832 (* h1 h1) (* h2 h2) h3 (* h4 
h4) (* h5 h5) h6) (* 48 (* h1 h1) (* h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 
j2 j2)) (* 380 (* h1 h1) (* h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 
1084 (* h1 h1) (* h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 1312 (* h1 h1) 
(* h2 h2) h3 (* h4 h4) h5 (* h6 h6) j2) (* 560 (* h1 h1) (* h2 h2) h3 (* h4 h4) 
h5 (* h6 h6)) (* 32 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2)) 
(* 272 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2)) (* 816 (* h1 h1) 
(* h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2)) (* 1024 (* h1 h1) (* h2 h2) h3 h4 (* 
h5 h5 h5 h5) j2) (* 448 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5 h5)) (* 48 (* h1 
h1) (* h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 712 (* h1 h1) (* h2 
h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 3848 (* h1 h1) (* h2 h2) h3 h4 (* 
h5 h5 h5) h6 (* j2 j2 j2)) (* 9488 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) h6 (* 
j2 j2)) (* 10720 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) h6 j2) (* 4416 (* h1 h1)
 (* h2 h2) h3 h4 (* h5 h5 h5) h6) (* 72 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2)) (* 1040 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* h6 h6)
 (* j2 j2 j2 j2)) (* 5440 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2
 j2)) (* 13048 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 14432
 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* h6 h6) j2) (* 5856 (* h1 h1) (* h2 h2) 
h3 h4 (* h5 h5) (* h6 h6)) (* 48 (* h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2
 j2 j2 j2)) (* 400 (* h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 
1184 (* h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2)) (* 1472 (* h1 h1) (* 
h2 h2) h3 h4 h5 (* h6 h6 h6) j2) (* 640 (* h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6 h6
)) (* 32 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 288 (* h1
 h1) (* h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 896 (* h1 h1) (* h2 h2) h3
 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 1152 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) h6
 j2) (* 512 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) h6) (* 24 (* h1 h1) (* h2 h2)
 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 372 (* h1 h1) (* h2 h2) h3 (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 2068 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5)
 (* h6 h6) (* j2 j2 j2)) (* 5192 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* h6 h6) 
(* j2 j2)) (* 5936 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* h6 h6) j2) (* 2464 (* 
h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* h6 h6)) (* 24 (* h1 h1) (* h2 h2) h3 (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 364 (* h1 h1) (* h2 h2) h3 (* h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2)) (* 1984 (* h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6 h6)
 (* j2 j2 j2)) (* 4908 (* h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2)) 
(* 5552 (* h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6 h6) j2) (* 2288 (* h1 h1) (* 
h2 h2) h3 (* h5 h5) (* h6 h6 h6)) (* 16 (* h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6 h6
) (* j2 j2 j2 j2)) (* 140 (* h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2)
) (* 428 (* h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2)) (* 544 (* h1 h1) 
(* h2 h2) h3 h5 (* h6 h6 h6 h6) j2) (* 240 (* h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6
 h6)) (* 4 (* h1 h1) (* h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 26 (* 
h1 h1) (* h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 56 (* h1 h1) (* h2 h2) 
(* h4 h4 h4) (* h5 h5) h6 j2) (* 40 (* h1 h1) (* h2 h2) (* h4 h4 h4) (* h5 h5) 
h6) (* 8 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 64 (* h1
 h1) (* h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 160 (* h1 h1) (* h2 h2) 
(* h4 h4) (* h5 h5 h5) h6 j2) (* 128 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5 h5) 
h6) (* 12 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 82 
(* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 184 (* h1 h1) 
(* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) j2) (* 136 (* h1 h1) (* h2 h2) (* h4 h4)
 (* h5 h5) (* h6 h6)) (* 4 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2
)) (* 32 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 80 (* h1 h1) 
(* h2 h2) h4 (* h5 h5 h5 h5) h6 j2) (* 64 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5 h5)
 h6) (* 16 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 128 
(* h1 h1) (* h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 320 (* h1 h1) (* h2 
h2) h4 (* h5 h5 h5) (* h6 h6) j2) (* 256 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5) (* 
h6 h6)) (* 12 (* h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 86 
(* h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 200 (* h1 h1) (* h2 
h2) h4 (* h5 h5) (* h6 h6 h6) j2) (* 152 (* h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 
h6 h6)) (* 4 (* h1 h1) (* h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 32 
(* h1 h1) (* h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 80 (* h1 h1) (* h2 
h2) (* h5 h5 h5 h5) (* h6 h6) j2) (* 64 (* h1 h1) (* h2 h2) (* h5 h5 h5 h5) (* 
h6 h6)) (* 8 (* h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 64 
(* h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 160 (* h1 h1) (* h2 
h2) (* h5 h5 h5) (* h6 h6 h6) j2) (* 128 (* h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 
h6 h6)) (* 4 (* h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 30 
(* h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 72 (* h1 h1) (* h2 
h2) (* h5 h5) (* h6 h6 h6 h6) j2) (* 56 (* h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 
h6 h6)) (* 768 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2
)) (* 10752 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 
58112 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 161280 
(* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 252160 (* h1 h1) 
h2 (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 224768 (* h1 h1) h2 (* h3 h3 h3
 h3) (* h4 h4) h5 (* j2 j2)) (* 106752 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h5
 j2) (* 20992 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h5) (* 256 (* h1 h1) h2 (* 
h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 2304 (* h1 h1) h2 (* h3 h3 
h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 8192 (* h1 h1) h2 (* h3 h3 h3 h3) (* 
h4 h4) h6 (* j2 j2 j2 j2)) (* 14848 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h6 
(* j2 j2 j2)) (* 14592 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2)) (* 
7424 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h6 j2) (* 1536 (* h1 h1) h2 (* h3 h3
 h3 h3) (* h4 h4) h6) (* 768 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 
j2 j2 j2 j2 j2)) (* 11264 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 
j2 j2 j2)) (* 65536 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)
) (* 194560 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 321280
 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 299008 (* h1 h1) h2 
(* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2)) (* 146944 (* h1 h1) h2 (* h3 h3 h3 h3) 
h4 (* h5 h5) j2) (* 29696 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h5 h5)) (* 1536 (* 
h1 h1) h2 (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 22272 (* h1 h1) 
h2 (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 125184 (* h1 h1) h2 (* h3 
h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 359424 (* h1 h1) h2 (* h3 h3 h3 h3) h4
 h5 h6 (* j2 j2 j2 j2)) (* 577536 (* h1 h1) h2 (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2
 j2)) (* 526080 (* h1 h1) h2 (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2)) (* 254208 (* h1
 h1) h2 (* h3 h3 h3 h3) h4 h5 h6 j2) (* 50688 (* h1 h1) h2 (* h3 h3 h3 h3) h4 h5
 h6) (* 512 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
4864 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 17920 (* 
h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 33280 (* h1 h1) h2 
(* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2)) (* 33280 (* h1 h1) h2 (* h3 h3 h3 h3)
 h4 (* h6 h6) (* j2 j2)) (* 17152 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6) j2) 
(* 3584 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6)) (* 512 (* h1 h1) h2 (* h3 h3 
h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 5120 (* h1 h1) h2 (* h3 h3 h3 h3) 
(* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 19456 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5 
h5) (* j2 j2 j2 j2)) (* 36864 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2
 j2)) (* 37376 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2)) (* 19456 (* 
h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5 h5) j2) (* 4096 (* h1 h1) h2 (* h3 h3 h3 h3) 
(* h5 h5 h5)) (* 768 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2
 j2 j2)) (* 11520 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2
)) (* 67072 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
198144 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 325376 (* 
h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 301312 (* h1 h1) h2 (* 
h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2)) (* 147456 (* h1 h1) h2 (* h3 h3 h3 h3) (* 
h5 h5) h6 j2) (* 29696 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) h6) (* 768 (* h1 
h1) h2 (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 11520 (* h1 h1)
 h2 (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 66816 (* h1 h1) h2 
(* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 196608 (* h1 h1) h2 (* h3 h3
 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 321792 (* h1 h1) h2 (* h3 h3 h3 h3) h5 
(* h6 h6) (* j2 j2 j2)) (* 297216 (* h1 h1) h2 (* h3 h3 h3 h3) h5 (* h6 h6) (* 
j2 j2)) (* 145152 (* h1 h1) h2 (* h3 h3 h3 h3) h5 (* h6 h6) j2) (* 29184 (* h1 
h1) h2 (* h3 h3 h3 h3) h5 (* h6 h6)) (* 256 (* h1 h1) h2 (* h3 h3 h3 h3) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2560 (* h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2)) (* 9728 (* h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2 
j2 j2)) (* 18432 (* h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2)) (* 
18688 (* h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2)) (* 9728 (* h1 h1) h2 
(* h3 h3 h3 h3) (* h6 h6 h6) j2) (* 2048 (* h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6 
h6)) (* 384 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 
4736 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 22144 (* 
h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 51072 (* h1 h1) h2 
(* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 61952 (* h1 h1) h2 (* h3 h3 h3) 
(* h4 h4 h4) h5 (* j2 j2)) (* 37888 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h5 j2
) (* 9216 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h5) (* 64 (* h1 h1) h2 (* h3 h3
 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 512 (* h1 h1) h2 (* h3 h3 h3) (* h4 
h4 h4) h6 (* j2 j2 j2 j2)) (* 1536 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h6 (* 
j2 j2 j2)) (* 2176 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2)) (* 1472 
(* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h6 j2) (* 384 (* h1 h1) h2 (* h3 h3 h3) 
(* h4 h4 h4) h6) (* 768 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 
j2 j2 j2 j2)) (* 10240 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2
 j2 j2)) (* 51648 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2))
 (* 126656 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 160960
 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 101952 (* h1 h1) h2
 (* h3 h3 h3) (* h4 h4) (* h5 h5) j2) (* 25472 (* h1 h1) h2 (* h3 h3 h3) (* h4 
h4) (* h5 h5)) (* 1152 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 
j2 j2)) (* 14784 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) 
(* 71744 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 170560 
(* h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 211776 (* h1 h1) h2 
(* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 131840 (* h1 h1) h2 (* h3 h3 h3) (* 
h4 h4) h5 h6 j2) (* 32512 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 h6) (* 192 (* 
h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1600 (* h1 h1)
 h2 (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 4928 (* h1 h1) h2 (* h3
 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 7104 (* h1 h1) h2 (* h3 h3 h3) (* 
h4 h4) (* h6 h6) (* j2 j2)) (* 4864 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h6 h6
) j2) (* 1280 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h6 h6)) (* 384 (* h1 h1) h2
 (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 5248 (* h1 h1) h2 (* h3 
h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 27392 (* h1 h1) h2 (* h3 h3 h3) h4
 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 69120 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5 h5
) (* j2 j2 j2)) (* 89728 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2)) 
(* 57728 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5 h5) j2) (* 14592 (* h1 h1) h2 (* 
h3 h3 h3) h4 (* h5 h5 h5)) (* 1536 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2)) (* 20928 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 
j2 j2 j2)) (* 107776 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) 
(* 268544 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 345216 (* 
h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 220480 (* h1 h1) h2 (* h3 
h3 h3) h4 (* h5 h5) h6 j2) (* 55424 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6) 
(* 1152 (* h1 h1) h2 (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
15360 (* h1 h1) h2 (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 77184 (* 
h1 h1) h2 (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 188544 (* h1 h1) h2 
(* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 238848 (* h1 h1) h2 (* h3 h3 h3) 
h4 h5 (* h6 h6) (* j2 j2)) (* 150912 (* h1 h1) h2 (* h3 h3 h3) h4 h5 (* h6 h6) 
j2) (* 37632 (* h1 h1) h2 (* h3 h3 h3) h4 h5 (* h6 h6)) (* 192 (* h1 h1) h2 (* 
h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1664 (* h1 h1) h2 (* h3 h3 h3) 
h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 5248 (* h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6 
h6) (* j2 j2 j2)) (* 7680 (* h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2)) 
(* 5312 (* h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6 h6) j2) (* 1408 (* h1 h1) h2 (* h3
 h3 h3) h4 (* h6 h6 h6)) (* 128 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 
j2 j2 j2 j2)) (* 1152 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2))
 (* 3712 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 5504 (* h1 
h1) h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2)) (* 3840 (* h1 h1) h2 (* h3 h3 h3)
 (* h5 h5 h5 h5) j2) (* 1024 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5 h5)) (* 384 
(* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 5440 (* h1 
h1) h2 (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 28864 (* h1 h1) h2 
(* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 73408 (* h1 h1) h2 (* h3 h3 h3)
 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 95680 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) 
h6 (* j2 j2)) (* 61696 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) h6 j2) (* 15616 
(* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) h6) (* 768 (* h1 h1) h2 (* h3 h3 h3) (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 10688 (* h1 h1) h2 (* h3 h3 h3) (* h5
 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 55936 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2)) (* 140928 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* h6 
h6) (* j2 j2 j2)) (* 182528 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 
j2)) (* 117184 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* h6 h6) j2) (* 29568 (* h1 
h1) h2 (* h3 h3 h3) (* h5 h5) (* h6 h6)) (* 384 (* h1 h1) h2 (* h3 h3 h3) h5 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 5312 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6 
h6) (* j2 j2 j2 j2 j2)) (* 27584 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6 h6) (* j2
 j2 j2 j2)) (* 69056 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 
89024 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 56960 (* h1 h1) h2
 (* h3 h3 h3) h5 (* h6 h6 h6) j2) (* 14336 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6
 h6)) (* 64 (* h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 576
 (* h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 1856 (* h1 h1) h2
 (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 2752 (* h1 h1) h2 (* h3 h3 h3) 
(* h6 h6 h6 h6) (* j2 j2)) (* 1920 (* h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6 h6) j2)
 (* 512 (* h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6 h6)) (* 48 (* h1 h1) h2 (* h3 h3) 
(* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 448 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4
 h4) h5 (* j2 j2 j2 j2)) (* 1600 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4 h4) h5 (* j2
 j2 j2)) (* 2720 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2)) (* 2192 
(* h1 h1) h2 (* h3 h3) (* h4 h4 h4 h4) h5 j2) (* 672 (* h1 h1) h2 (* h3 h3) (* 
h4 h4 h4 h4) h5) (* 192 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 
j2 j2 j2)) (* 2144 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)
) (* 8688 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 16160 
(* h1 h1) h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 13872 (* h1 h1) h2 
(* h3 h3) (* h4 h4 h4) (* h5 h5) j2) (* 4448 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4)
 (* h5 h5)) (* 192 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2))
 (* 1920 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 7264 (* 
h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 12928 (* h1 h1) h2 (* h3
 h3) (* h4 h4 h4) h5 h6 (* j2 j2)) (* 10784 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) 
h5 h6 j2) (* 3392 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 h6) (* 192 (* h1 h1) h2
 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 2272 (* h1 h1) h2 (* h3
 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 9824 (* h1 h1) h2 (* h3 h3) (* 
h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 19296 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* 
h5 h5 h5) (* j2 j2)) (* 17248 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) j2) 
(* 5696 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5 h5)) (* 576 (* h1 h1) h2 (* h3
 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 6672 (* h1 h1) h2 (* h3 h3) 
(* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 28160 (* h1 h1) h2 (* h3 h3) (* h4 h4
) (* h5 h5) h6 (* j2 j2 j2)) (* 54224 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5)
 h6 (* j2 j2)) (* 47776 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) h6 j2) (* 
15616 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) h6) (* 288 (* h1 h1) h2 (* h3 
h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 3072 (* h1 h1) h2 (* h3 h3) 
(* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 12272 (* h1 h1) h2 (* h3 h3) (* h4 h4
) h5 (* h6 h6) (* j2 j2 j2)) (* 22784 (* h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* h6 
h6) (* j2 j2)) (* 19600 (* h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* h6 h6) j2) (* 
6304 (* h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* h6 h6)) (* 48 (* h1 h1) h2 (* h3 h3)
 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 576 (* h1 h1) h2 (* h3 h3) h4 (* h5 
h5 h5 h5) (* j2 j2 j2 j2)) (* 2544 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* 
j2 j2 j2)) (* 5088 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2)) (* 4608 
(* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5 h5) j2) (* 1536 (* h1 h1) h2 (* h3 h3) h4 
(* h5 h5 h5 h5)) (* 384 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2
 j2)) (* 4672 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 
20768 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 41664 (* h1 h1)
 h2 (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2)) (* 37792 (* h1 h1) h2 (* h3 h3) h4 
(* h5 h5 h5) h6 j2) (* 12608 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) h6) (* 576 
(* h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 6912 (* h1 
h1) h2 (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 30240 (* h1 h1) h2 
(* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 59904 (* h1 h1) h2 (* h3 h3) 
h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 53856 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5) 
(* h6 h6) j2) (* 17856 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* h6 h6)) (* 192 (* 
h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2176 (* h1 h1) h2 
(* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 9152 (* h1 h1) h2 (* h3 h3) h4 
h5 (* h6 h6 h6) (* j2 j2 j2)) (* 17664 (* h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6)
 (* j2 j2)) (* 15616 (* h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6) j2) (* 5120 (* h1
 h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6)) (* 48 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5 
h5) h6 (* j2 j2 j2 j2 j2)) (* 608 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) h6 (* 
j2 j2 j2 j2)) (* 2800 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) 
(* 5760 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 5312 (* h1 h1) 
h2 (* h3 h3) (* h5 h5 h5 h5) h6 j2) (* 1792 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5 
h5) h6) (* 192 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2))
 (* 2400 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 10912
 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 22240 (* h1 h1) 
h2 (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 20384 (* h1 h1) h2 (* h3 h3) 
(* h5 h5 h5) (* h6 h6) j2) (* 6848 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* h6 h6)
) (* 192 (* h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
2384 (* h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 10768 (* 
h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 21840 (* h1 h1) h2 
(* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 19952 (* h1 h1) h2 (* h3 h3) (* 
h5 h5) (* h6 h6 h6) j2) (* 6688 (* h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6 h6)) 
(* 48 (* h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 576 (* h1
 h1) h2 (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 2544 (* h1 h1) h2 (* h3
 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 5088 (* h1 h1) h2 (* h3 h3) h5 (* h6 h6
 h6 h6) (* j2 j2)) (* 4608 (* h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6 h6) j2) (* 1536
 (* h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6 h6)) (* 12 (* h1 h1) h2 h3 (* h4 h4 h4 h4
) (* h5 h5) (* j2 j2 j2 j2)) (* 92 (* h1 h1) h2 h3 (* h4 h4 h4 h4) (* h5 h5) (* 
j2 j2 j2)) (* 256 (* h1 h1) h2 h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2)) (* 304 
(* h1 h1) h2 h3 (* h4 h4 h4 h4) (* h5 h5) j2) (* 128 (* h1 h1) h2 h3 (* h4 h4 h4
 h4) (* h5 h5)) (* 24 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2))
 (* 232 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 752 (* h1 h1)
 h2 h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2)) (* 992 (* h1 h1) h2 h3 (* h4 h4 h4) 
(* h5 h5 h5) j2) (* 448 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5 h5)) (* 48 (* h1 
h1) h2 h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 408 (* h1 h1) h2 h3 (* 
h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 1240 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 
h5) h6 (* j2 j2)) (* 1584 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) h6 j2) (* 704 
(* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) h6) (* 12 (* h1 h1) h2 h3 (* h4 h4) (* h5
 h5 h5 h5) (* j2 j2 j2 j2)) (* 116 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5 h5) (* 
j2 j2 j2)) (* 376 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 496 
(* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5 h5) j2) (* 224 (* h1 h1) h2 h3 (* h4 h4) 
(* h5 h5 h5 h5)) (* 72 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)
) (* 744 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 2624 (* h1 
h1) h2 h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 3744 (* h1 h1) h2 h3 (* h4 h4)
 (* h5 h5 h5) h6 j2) (* 1792 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) h6) (* 72 
(* h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 672 (* h1 h1) 
h2 h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 2216 (* h1 h1) h2 h3 (* h4 
h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 3024 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5) 
(* h6 h6) j2) (* 1408 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* h6 h6)) (* 24 (* h1
 h1) h2 h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 256 (* h1 h1) h2 h3 h4 (* 
h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 936 (* h1 h1) h2 h3 h4 (* h5 h5 h5 h5) h6 (* j2
 j2)) (* 1376 (* h1 h1) h2 h3 h4 (* h5 h5 h5 h5) h6 j2) (* 672 (* h1 h1) h2 h3 
h4 (* h5 h5 h5 h5) h6) (* 72 (* h1 h1) h2 h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2)) (* 792 (* h1 h1) h2 h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 2992 
(* h1 h1) h2 h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 4512 (* h1 h1) h2 h3 h4 
(* h5 h5 h5) (* h6 h6) j2) (* 2240 (* h1 h1) h2 h3 h4 (* h5 h5 h5) (* h6 h6)) 
(* 48 (* h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 488 (* h1 h1
) h2 h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 1736 (* h1 h1) h2 h3 h4 (* h5
 h5) (* h6 h6 h6) (* j2 j2)) (* 2512 (* h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6 h6) 
j2) (* 1216 (* h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6 h6)) (* 12 (* h1 h1) h2 h3 (* 
h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 140 (* h1 h1) h2 h3 (* h5 h5 h5 h5) 
(* h6 h6) (* j2 j2 j2)) (* 560 (* h1 h1) h2 h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 
j2)) (* 880 (* h1 h1) h2 h3 (* h5 h5 h5 h5) (* h6 h6) j2) (* 448 (* h1 h1) h2 h3
 (* h5 h5 h5 h5) (* h6 h6)) (* 24 (* h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2)) (* 280 (* h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 
1120 (* h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 1760 (* h1 h1) h2 
h3 (* h5 h5 h5) (* h6 h6 h6) j2) (* 896 (* h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6 h6
)) (* 12 (* h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 132 (* h1
 h1) h2 h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 504 (* h1 h1) h2 h3 (* h5 
h5) (* h6 h6 h6 h6) (* j2 j2)) (* 768 (* h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6 h6) 
j2) (* 384 (* h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6 h6)) (* 2 (* h1 h1) h2 (* h4 h4
 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 8 (* h1 h1) h2 (* h4 h4 h4) (* h5 h5 h5) h6 
j2) (* 8 (* h1 h1) h2 (* h4 h4 h4) (* h5 h5 h5) h6) (* 2 (* h1 h1) h2 (* h4 h4) 
(* h5 h5 h5 h5) h6 (* j2 j2)) (* 8 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5 h5) h6 j2)
 (* 8 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5 h5) h6) (* 6 (* h1 h1) h2 (* h4 h4) (* 
h5 h5 h5) (* h6 h6) (* j2 j2)) (* 28 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5) (* h6 
h6) j2) (* 32 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5) (* h6 h6)) (* 4 (* h1 h1) h2 
h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 20 (* h1 h1) h2 h4 (* h5 h5 h5 h5) 
(* h6 h6) j2) (* 24 (* h1 h1) h2 h4 (* h5 h5 h5 h5) (* h6 h6)) (* 6 (* h1 h1) h2
 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 32 (* h1 h1) h2 h4 (* h5 h5 h5) (* 
h6 h6 h6) j2) (* 40 (* h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6 h6)) (* 2 (* h1 h1) h2
 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 12 (* h1 h1) h2 (* h5 h5 h5 h5) (* 
h6 h6 h6) j2) (* 16 (* h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6 h6)) (* 2 (* h1 h1) h2
 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 12 (* h1 h1) h2 (* h5 h5 h5) (* h6 
h6 h6 h6) j2) (* 16 (* h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6 h6)) (* 256 (* h1 h1) 
(* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 2304 (* h1 h1) (* h3 
h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 8192 (* h1 h1) (* h3 h3 h3 h3) 
(* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 14848 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4 h4)
 h5 (* j2 j2 j2)) (* 14592 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2)) 
(* 7424 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4 h4) h5 j2) (* 1536 (* h1 h1) (* h3 h3
 h3 h3) (* h4 h4 h4) h5) (* 512 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) 
(* j2 j2 j2 j2 j2 j2)) (* 5632 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* 
j2 j2 j2 j2 j2)) (* 22528 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2
 j2 j2)) (* 44032 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2)) 
(* 45568 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 24064 (* h1
 h1) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) j2) (* 5120 (* h1 h1) (* h3 h3 h3 h3) 
(* h4 h4) (* h5 h5)) (* 768 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 
j2 j2 j2 j2)) (* 7680 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 
j2)) (* 29696 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 
57344 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 59136 (* h1 h1)
 (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 31232 (* h1 h1) (* h3 h3 h3 h3) 
(* h4 h4) h5 h6 j2) (* 6656 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 h6) (* 256 
(* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2560 (* h1 
h1) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 9728 (* h1 h1) (* h3 
h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 18432 (* h1 h1) (* h3 h3 h3 h3) h4
 (* h5 h5 h5) (* j2 j2 j2)) (* 18688 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5 h5) 
(* j2 j2)) (* 9728 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5 h5) j2) (* 2048 (* h1 
h1) (* h3 h3 h3 h3) h4 (* h5 h5 h5)) (* 1024 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 
h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 12032 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) h6
 (* j2 j2 j2 j2 j2)) (* 52736 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2
 j2 j2)) (* 111104 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 
121856 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 67328 (* h1 h1) 
(* h3 h3 h3 h3) h4 (* h5 h5) h6 j2) (* 14848 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 
h5) h6) (* 768 (* h1 h1) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 8448 (* h1 h1) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 35328 
(* h1 h1) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 72192 (* h1 h1) 
(* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 77568 (* h1 h1) (* h3 h3 h3 h3)
 h4 h5 (* h6 h6) (* j2 j2)) (* 42240 (* h1 h1) (* h3 h3 h3 h3) h4 h5 (* h6 h6) 
j2) (* 9216 (* h1 h1) (* h3 h3 h3 h3) h4 h5 (* h6 h6)) (* 256 (* h1 h1) (* h3 h3
 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 3072 (* h1 h1) (* h3 h3 h3 h3)
 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 13824 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5
 h5) h6 (* j2 j2 j2 j2)) (* 29696 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* 
j2 j2 j2)) (* 33024 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2)) (* 
18432 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5 h5) h6 j2) (* 4096 (* h1 h1) (* h3 h3 
h3 h3) (* h5 h5 h5) h6) (* 512 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 6400 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2)) (* 29696 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2
 j2)) (* 65024 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 
73216 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 41216 (* h1 h1
) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) j2) (* 9216 (* h1 h1) (* h3 h3 h3 h3) (* 
h5 h5) (* h6 h6)) (* 256 (* h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 3072 (* h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2))
 (* 13824 (* h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 29696 
(* h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 33024 (* h1 h1) (* h3
 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 18432 (* h1 h1) (* h3 h3 h3 h3) h5 (* 
h6 h6 h6) j2) (* 4096 (* h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6 h6)) (* 64 (* h1 h1)
 (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 512 (* h1 h1) (* h3 h3 
h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 1536 (* h1 h1) (* h3 h3 h3) (* h4 h4 
h4 h4) h5 (* j2 j2 j2)) (* 2176 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 
j2)) (* 1472 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4 h4) h5 j2) (* 384 (* h1 h1) (* 
h3 h3 h3) (* h4 h4 h4 h4) h5) (* 256 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h5 
h5) (* j2 j2 j2 j2 j2)) (* 2432 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) 
(* j2 j2 j2 j2)) (* 8064 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 
j2)) (* 12160 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 8576 
(* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) j2) (* 2304 (* h1 h1) (* h3 h3 h3)
 (* h4 h4 h4) (* h5 h5)) (* 256 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 
j2 j2 j2 j2)) (* 2240 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2))
 (* 7232 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 10816 (* h1 
h1) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2)) (* 7616 (* h1 h1) (* h3 h3 h3) 
(* h4 h4 h4) h5 h6 j2) (* 2048 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 h6) (* 256
 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 2496 (* h1
 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 8384 (* h1 h1) (* 
h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 12736 (* h1 h1) (* h3 h3 h3) 
(* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 9024 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5
 h5 h5) j2) (* 2432 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5)) (* 768 (* h1 
h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 7808 (* h1 h1) 
(* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 28032 (* h1 h1) (* h3 h3
 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 44928 (* h1 h1) (* h3 h3 h3) (* h4 
h4) (* h5 h5) h6 (* j2 j2)) (* 33152 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) 
h6 j2) (* 9216 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6) (* 384 (* h1 h1) 
(* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 3648 (* h1 h1) (* h3 
h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 12608 (* h1 h1) (* h3 h3 h3) 
(* h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 19776 (* h1 h1) (* h3 h3 h3) (* h4 h4) 
h5 (* h6 h6) (* j2 j2)) (* 14400 (* h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) 
j2) (* 3968 (* h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6)) (* 64 (* h1 h1) (* h3
 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 576 (* h1 h1) (* h3 h3 h3) h4 
(* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 1856 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5 
h5) (* j2 j2 j2)) (* 2752 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2)) 
(* 1920 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5 h5) j2) (* 512 (* h1 h1) (* h3 h3 
h3) h4 (* h5 h5 h5 h5)) (* 512 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* 5440 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2))
 (* 20416 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 33728 (* h1
 h1) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2)) (* 25408 (* h1 h1) (* h3 h3 h3) 
h4 (* h5 h5 h5) h6 j2) (* 7168 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) h6) (* 768
 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 8320 (* h1
 h1) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 31872 (* h1 h1) (* 
h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 53376 (* h1 h1) (* h3 h3 h3) 
h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 40576 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5) 
(* h6 h6) j2) (* 11520 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6)) (* 256 (* 
h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2624 (* h1 h1) (* 
h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 9664 (* h1 h1) (* h3 h3 h3) h4 
h5 (* h6 h6 h6) (* j2 j2 j2)) (* 15808 (* h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6 h6)
 (* j2 j2)) (* 11840 (* h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6 h6) j2) (* 3328 (* h1
 h1) (* h3 h3 h3) h4 h5 (* h6 h6 h6)) (* 64 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5 
h5) h6 (* j2 j2 j2 j2 j2)) (* 704 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* 
j2 j2 j2 j2)) (* 2752 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) 
(* 4672 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 3584 (* h1 h1) 
(* h3 h3 h3) (* h5 h5 h5 h5) h6 j2) (* 1024 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5 
h5) h6) (* 256 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2))
 (* 2944 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 11904
 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 20608 (* h1 h1) 
(* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 16000 (* h1 h1) (* h3 h3 h3) 
(* h5 h5 h5) (* h6 h6) j2) (* 4608 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6)
) (* 256 (* h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
2944 (* h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 11904 (* 
h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 20608 (* h1 h1) (* 
h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 16000 (* h1 h1) (* h3 h3 h3) (* 
h5 h5) (* h6 h6 h6) j2) (* 4608 (* h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6)) 
(* 64 (* h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 704 (* h1
 h1) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 2752 (* h1 h1) (* h3 h3
 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 4672 (* h1 h1) (* h3 h3 h3) h5 (* h6 h6
 h6 h6) (* j2 j2)) (* 3584 (* h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6 h6) j2) (* 1024
 (* h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6 h6)) (* 32 (* h1 h1) (* h3 h3) (* h4 h4 
h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 224 (* h1 h1) (* h3 h3) (* h4 h4 h4 h4) (* 
h5 h5) (* j2 j2 j2)) (* 544 (* h1 h1) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 
j2)) (* 544 (* h1 h1) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) j2) (* 192 (* h1 h1) 
(* h3 h3) (* h4 h4 h4 h4) (* h5 h5)) (* 64 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* 
h5 h5 h5) (* j2 j2 j2 j2)) (* 528 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) 
(* j2 j2 j2)) (* 1408 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2)) 
(* 1488 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) j2) (* 544 (* h1 h1) (* h3
 h3) (* h4 h4 h4) (* h5 h5 h5)) (* 128 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5
) h6 (* j2 j2 j2 j2)) (* 992 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2
 j2 j2)) (* 2624 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 
2784 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 j2) (* 1024 (* h1 h1) (* h3 
h3) (* h4 h4 h4) (* h5 h5) h6) (* 32 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5 
h5) (* j2 j2 j2 j2)) (* 256 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 
j2 j2)) (* 672 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 704 
(* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) j2) (* 256 (* h1 h1) (* h3 h3) (* 
h4 h4) (* h5 h5 h5 h5)) (* 192 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* 
j2 j2 j2 j2)) (* 1712 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)
) (* 5024 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 5680 (* h1
 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 j2) (* 2176 (* h1 h1) (* h3 h3) (* h4 
h4) (* h5 h5 h5) h6) (* 192 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2)) (* 1632 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2
 j2 j2)) (* 4672 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) 
(* 5216 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) j2) (* 1984 (* h1 h1) 
(* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6)) (* 64 (* h1 h1) (* h3 h3) h4 (* h5 h5 
h5 h5) h6 (* j2 j2 j2 j2)) (* 576 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* 
j2 j2 j2)) (* 1728 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 1984 
(* h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) h6 j2) (* 768 (* h1 h1) (* h3 h3) h4 (* 
h5 h5 h5 h5) h6) (* 192 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2)) (* 1840 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 
5824 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 6896 (* h1 h1) 
(* h3 h3) h4 (* h5 h5 h5) (* h6 h6) j2) (* 2720 (* h1 h1) (* h3 h3) h4 (* h5 h5 
h5) (* h6 h6)) (* 128 (* h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2)) (* 1184 (* h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 3648
 (* h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 4256 (* h1 h1) (* 
h3 h3) h4 (* h5 h5) (* h6 h6 h6) j2) (* 1664 (* h1 h1) (* h3 h3) h4 (* h5 h5) 
(* h6 h6 h6)) (* 32 (* h1 h1) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2
)) (* 320 (* h1 h1) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 1056 
(* h1 h1) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 1280 (* h1 h1) (* h3
 h3) (* h5 h5 h5 h5) (* h6 h6) j2) (* 512 (* h1 h1) (* h3 h3) (* h5 h5 h5 h5) 
(* h6 h6)) (* 64 (* h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) 
(* 656 (* h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 2208 (* h1
 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 2704 (* h1 h1) (* h3 h3) 
(* h5 h5 h5) (* h6 h6 h6) j2) (* 1088 (* h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 
h6)) (* 32 (* h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 320
 (* h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 1056 (* h1 h1) 
(* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 1280 (* h1 h1) (* h3 h3) (* h5
 h5) (* h6 h6 h6 h6) j2) (* 512 (* h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6)) 
(* 4 (* h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 20 (* h1 h1) h3 
(* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2)) (* 32 (* h1 h1) h3 (* h4 h4 h4 h4) (* h5
 h5 h5) j2) (* 16 (* h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5 h5)) (* 4 (* h1 h1) h3 
(* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 20 (* h1 h1) h3 (* h4 h4 h4) (* h5
 h5 h5 h5) (* j2 j2)) (* 32 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5 h5) j2) (* 16 
(* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5 h5)) (* 16 (* h1 h1) h3 (* h4 h4 h4) (* h5
 h5 h5) h6 (* j2 j2 j2)) (* 96 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 
j2)) (* 176 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) h6 j2) (* 96 (* h1 h1) h3 (* 
h4 h4 h4) (* h5 h5 h5) h6) (* 12 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2
 j2 j2)) (* 76 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 144 (* h1
 h1) h3 (* h4 h4) (* h5 h5 h5 h5) h6 j2) (* 80 (* h1 h1) h3 (* h4 h4) (* h5 h5 
h5 h5) h6) (* 24 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 
168 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 352 (* h1 h1) h3
 (* h4 h4) (* h5 h5 h5) (* h6 h6) j2) (* 208 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5)
 (* h6 h6)) (* 12 (* h1 h1) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 92 
(* h1 h1) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 208 (* h1 h1) h3 h4 (* 
h5 h5 h5 h5) (* h6 h6) j2) (* 128 (* h1 h1) h3 h4 (* h5 h5 h5 h5) (* h6 h6)) (* 
16 (* h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 128 (* h1 h1) h3 
h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 304 (* h1 h1) h3 h4 (* h5 h5 h5) (* 
h6 h6 h6) j2) (* 192 (* h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6 h6)) (* 4 (* h1 h1) 
h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 36 (* h1 h1) h3 (* h5 h5 h5 h5)
 (* h6 h6 h6) (* j2 j2)) (* 96 (* h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6 h6) j2) (* 
64 (* h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6 h6)) (* 4 (* h1 h1) h3 (* h5 h5 h5) (* 
h6 h6 h6 h6) (* j2 j2 j2)) (* 36 (* h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2
 j2)) (* 96 (* h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6 h6) j2) (* 64 (* h1 h1) h3 (* 
h5 h5 h5) (* h6 h6 h6 h6)) (* 256 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2
 j2 j2 j2 j2 j2)) (* 2816 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 
j2 j2)) (* 13056 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 
33024 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2)) (* 49152 h1 (* h2 
h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2)) (* 43008 h1 (* h2 h2 h2 h2) (* h3 h3 
h3) h4 h5 (* j2 j2)) (* 20480 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 j2) (* 4096 
h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5) (* 64 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 704 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 
j2 j2 j2 j2 j2)) (* 3264 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2
)) (* 8256 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 12288 h1 
(* h2 h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2)) (* 10752 h1 (* h2 h2 h2 h2) (* 
h3 h3 h3) h4 h6 (* j2 j2)) (* 5120 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h6 j2) (* 
1024 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h6) (* 128 h1 (* h2 h2 h2 h2) (* h3 h3 
h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1408 h1 (* h2 h2 h2 h2) (* h3 h3 h3) 
(* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 6528 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 
h5) (* j2 j2 j2 j2 j2)) (* 16512 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* j2
 j2 j2 j2)) (* 24576 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2)) (* 
21504 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2)) (* 10240 h1 (* h2 h2 
h2 h2) (* h3 h3 h3) (* h5 h5) j2) (* 2048 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 
h5)) (* 192 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
2112 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 9792 h1 (* 
h2 h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 24768 h1 (* h2 h2 h2 h2) 
(* h3 h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 36864 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h5 
h6 (* j2 j2 j2)) (* 32256 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2)) (* 
15360 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h5 h6 j2) (* 3072 h1 (* h2 h2 h2 h2) (* h3
 h3 h3) h5 h6) (* 64 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2)) (* 704 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2))
 (* 3264 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 8256 
h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 12288 h1 (* h2 h2 
h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2)) (* 10752 h1 (* h2 h2 h2 h2) (* h3 h3
 h3) (* h6 h6) (* j2 j2)) (* 5120 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h6 h6) j2) 
(* 1024 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h6 h6)) (* 96 h1 (* h2 h2 h2 h2) (* 
h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 960 h1 (* h2 h2 h2 h2) (* h3 h3) 
(* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 3936 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) 
h5 (* j2 j2 j2 j2)) (* 8448 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 
j2)) (* 9984 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2)) (* 6144 h1 (* 
h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 j2) (* 1536 h1 (* h2 h2 h2 h2) (* h3 h3) (* 
h4 h4) h5) (* 16 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2)
) (* 160 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 656 h1
 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2)) (* 1408 h1 (* h2 h2 h2 
h2) (* h3 h3) (* h4 h4) h6 (* j2 j2 j2)) (* 1664 h1 (* h2 h2 h2 h2) (* h3 h3) 
(* h4 h4) h6 (* j2 j2)) (* 1024 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h6 j2) 
(* 256 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h6) (* 128 h1 (* h2 h2 h2 h2) (* 
h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1280 h1 (* h2 h2 h2 h2) (* h3 h3) 
h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 5248 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 
h5) (* j2 j2 j2 j2)) (* 11264 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2
 j2)) (* 13312 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2)) (* 8192 h1 
(* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) j2) (* 2048 h1 (* h2 h2 h2 h2) (* h3 h3) 
h4 (* h5 h5)) (* 192 h1 (* h2 h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)
) (* 1920 h1 (* h2 h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 7872 h1 
(* h2 h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 16896 h1 (* h2 h2 h2 h2) 
(* h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 19968 h1 (* h2 h2 h2 h2) (* h3 h3) h4 h5 h6 
(* j2 j2)) (* 12288 h1 (* h2 h2 h2 h2) (* h3 h3) h4 h5 h6 j2) (* 3072 h1 (* h2 
h2 h2 h2) (* h3 h3) h4 h5 h6) (* 32 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 320 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2
 j2 j2 j2)) (* 1312 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) 
(* 2816 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2)) (* 3328 h1 (* h2
 h2 h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2)) (* 2048 h1 (* h2 h2 h2 h2) (* h3 h3
) h4 (* h6 h6) j2) (* 512 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h6 h6)) (* 32 h1 
(* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 320 h1 (* h2 h2
 h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 1312 h1 (* h2 h2 h2 h2) 
(* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 2816 h1 (* h2 h2 h2 h2) (* h3 h3) (* 
h5 h5 h5) (* j2 j2 j2)) (* 3328 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 
j2)) (* 2048 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) j2) (* 512 h1 (* h2 h2 h2
 h2) (* h3 h3) (* h5 h5 h5)) (* 112 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 1120 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* 4592 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2))
 (* 9856 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 11648 h1 (* 
h2 h2 h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2)) (* 7168 h1 (* h2 h2 h2 h2) (* h3 
h3) (* h5 h5) h6 j2) (* 1792 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) h6) (* 96 h1
 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 960 h1 (* h2 
h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 3936 h1 (* h2 h2 h2 h2) 
(* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 8448 h1 (* h2 h2 h2 h2) (* h3 h3) h5 
(* h6 h6) (* j2 j2 j2)) (* 9984 h1 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 
j2)) (* 6144 h1 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6) j2) (* 1536 h1 (* h2 h2 
h2 h2) (* h3 h3) h5 (* h6 h6)) (* 16 h1 (* h2 h2 h2 h2) (* h3 h3) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 160 h1 (* h2 h2 h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2
 j2 j2 j2)) (* 656 h1 (* h2 h2 h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2)) 
(* 1408 h1 (* h2 h2 h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2)) (* 1664 h1 (* h2
 h2 h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2)) (* 1024 h1 (* h2 h2 h2 h2) (* h3 h3
) (* h6 h6 h6) j2) (* 256 h1 (* h2 h2 h2 h2) (* h3 h3) (* h6 h6 h6)) (* 24 h1 
(* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 216 h1 (* h2 h2 h2
 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 768 h1 (* h2 h2 h2 h2) h3 (* h4 
h4) (* h5 h5) (* j2 j2 j2)) (* 1344 h1 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) 
(* j2 j2)) (* 1152 h1 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) j2) (* 384 h1 (* h2
 h2 h2 h2) h3 (* h4 h4) (* h5 h5)) (* 8 h1 (* h2 h2 h2 h2) h3 (* h4 h4) h5 h6 
(* j2 j2 j2 j2 j2)) (* 72 h1 (* h2 h2 h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2))
 (* 256 h1 (* h2 h2 h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2)) (* 448 h1 (* h2 h2 
h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2)) (* 384 h1 (* h2 h2 h2 h2) h3 (* h4 h4) h5 
h6 j2) (* 128 h1 (* h2 h2 h2 h2) h3 (* h4 h4) h5 h6) (* 16 h1 (* h2 h2 h2 h2) h3
 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 144 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5
) (* j2 j2 j2 j2)) (* 512 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2)) 
(* 896 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2)) (* 768 h1 (* h2 h2 h2 h2
) h3 h4 (* h5 h5 h5) j2) (* 256 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5)) (* 48 h1 
(* h2 h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 432 h1 (* h2 h2 h2 h2)
 h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 1536 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5) 
h6 (* j2 j2 j2)) (* 2688 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2)) (* 
2304 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5) h6 j2) (* 768 h1 (* h2 h2 h2 h2) h3 h4 
(* h5 h5) h6) (* 16 h1 (* h2 h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 144 h1 (* h2 h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 512 h1 (* h2 h2
 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2)) (* 896 h1 (* h2 h2 h2 h2) h3 h4 h5 (* 
h6 h6) (* j2 j2)) (* 768 h1 (* h2 h2 h2 h2) h3 h4 h5 (* h6 h6) j2) (* 256 h1 (* 
h2 h2 h2 h2) h3 h4 h5 (* h6 h6)) (* 16 h1 (* h2 h2 h2 h2) h3 (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2)) (* 144 h1 (* h2 h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) 
(* 512 h1 (* h2 h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 896 h1 (* h2 h2 h2
 h2) h3 (* h5 h5 h5) h6 (* j2 j2)) (* 768 h1 (* h2 h2 h2 h2) h3 (* h5 h5 h5) h6 
j2) (* 256 h1 (* h2 h2 h2 h2) h3 (* h5 h5 h5) h6) (* 24 h1 (* h2 h2 h2 h2) h3 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 216 h1 (* h2 h2 h2 h2) h3 (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2)) (* 768 h1 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6) (* 
j2 j2 j2)) (* 1344 h1 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2)) (* 1152 
h1 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6) j2) (* 384 h1 (* h2 h2 h2 h2) h3 (* h5
 h5) (* h6 h6)) (* 8 h1 (* h2 h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 72 h1 (* h2 h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 256 h1 (* h2 h2 
h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 448 h1 (* h2 h2 h2 h2) h3 h5 (* h6 h6
 h6) (* j2 j2)) (* 384 h1 (* h2 h2 h2 h2) h3 h5 (* h6 h6 h6) j2) (* 128 h1 (* h2
 h2 h2 h2) h3 h5 (* h6 h6 h6)) (* 2 h1 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5) h6 
(* j2 j2 j2 j2)) (* 16 h1 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) 
(* 48 h1 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 64 h1 (* h2 h2 h2 
h2) (* h4 h4) (* h5 h5) h6 j2) (* 32 h1 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5) h6) 
(* 2 h1 (* h2 h2 h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 16 h1 (* h2 h2 h2
 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 48 h1 (* h2 h2 h2 h2) h4 (* h5 h5 h5) 
h6 (* j2 j2)) (* 64 h1 (* h2 h2 h2 h2) h4 (* h5 h5 h5) h6 j2) (* 32 h1 (* h2 h2 
h2 h2) h4 (* h5 h5 h5) h6) (* 4 h1 (* h2 h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 
j2 j2 j2)) (* 32 h1 (* h2 h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 96 
h1 (* h2 h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 128 h1 (* h2 h2 h2 h2) 
h4 (* h5 h5) (* h6 h6) j2) (* 64 h1 (* h2 h2 h2 h2) h4 (* h5 h5) (* h6 h6)) (* 2
 h1 (* h2 h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 16 h1 (* h2 h2 h2
 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 48 h1 (* h2 h2 h2 h2) (* h5 h5 h5) 
(* h6 h6) (* j2 j2)) (* 64 h1 (* h2 h2 h2 h2) (* h5 h5 h5) (* h6 h6) j2) (* 32 
h1 (* h2 h2 h2 h2) (* h5 h5 h5) (* h6 h6)) (* 2 h1 (* h2 h2 h2 h2) (* h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2)) (* 16 h1 (* h2 h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2
 j2 j2)) (* 48 h1 (* h2 h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 64 h1 (* 
h2 h2 h2 h2) (* h5 h5) (* h6 h6 h6) j2) (* 32 h1 (* h2 h2 h2 h2) (* h5 h5) (* h6
 h6 h6)) (* 1024 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2))
 (* 10240 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 43008 
h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 98304 h1 (* h2 h2 
h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2)) (* 132096 h1 (* h2 h2 h2) (* h3 h3 h3
 h3) h4 h5 (* j2 j2 j2)) (* 104448 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 
j2)) (* 45056 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 j2) (* 8192 h1 (* h2 h2 h2) 
(* h3 h3 h3 h3) h4 h5) (* 256 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 
j2 j2 j2 j2)) (* 2560 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2
)) (* 10752 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 24576 
h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 33024 h1 (* h2 h2 h2) 
(* h3 h3 h3 h3) h4 h6 (* j2 j2 j2)) (* 26112 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 
h6 (* j2 j2)) (* 11264 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h6 j2) (* 2048 h1 (* 
h2 h2 h2) (* h3 h3 h3 h3) h4 h6) (* 512 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5
) (* j2 j2 j2 j2 j2 j2 j2)) (* 5120 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) 
(* j2 j2 j2 j2 j2 j2)) (* 21504 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 
j2 j2 j2 j2)) (* 49152 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2)
) (* 66048 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2)) (* 52224 h1 
(* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2)) (* 22528 h1 (* h2 h2 h2) (* h3
 h3 h3 h3) (* h5 h5) j2) (* 4096 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5)) (* 
768 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 7680 h1 
(* h2 h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 32256 h1 (* h2 h2 
h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 73728 h1 (* h2 h2 h2) (* h3 h3 
h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 99072 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h5 h6 (* 
j2 j2 j2)) (* 78336 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2)) (* 33792 h1
 (* h2 h2 h2) (* h3 h3 h3 h3) h5 h6 j2) (* 6144 h1 (* h2 h2 h2) (* h3 h3 h3 h3) 
h5 h6) (* 256 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 2560 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
10752 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 24576 h1 
(* h2 h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 33024 h1 (* h2 h2 h2)
 (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2)) (* 26112 h1 (* h2 h2 h2) (* h3 h3 h3 h3
) (* h6 h6) (* j2 j2)) (* 11264 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h6 h6) j2) 
(* 2048 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h6 h6)) (* 256 h1 (* h2 h2 h2) (* h3 
h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 3776 h1 (* h2 h2 h2) (* h3 h3 
h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 21696 h1 (* h2 h2 h2) (* h3 h3 h3) 
(* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 64704 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4)
 h5 (* j2 j2 j2 j2)) (* 109632 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 
j2 j2)) (* 106368 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2)) (* 55040 
h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 j2) (* 11776 h1 (* h2 h2 h2) (* h3 h3 
h3) (* h4 h4) h5) (* 128 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 
j2 j2 j2)) (* 1152 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2))
 (* 4224 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2)) (* 8064 h1 
(* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2)) (* 8448 h1 (* h2 h2 h2) (* 
h3 h3 h3) (* h4 h4) h6 (* j2 j2)) (* 4608 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4)
 h6 j2) (* 1024 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h6) (* 256 h1 (* h2 h2 h2
) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 3968 h1 (* h2 h2 h2) 
(* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 23424 h1 (* h2 h2 h2) (* h3 
h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 71040 h1 (* h2 h2 h2) (* h3 h3 h3) h4
 (* h5 h5) (* j2 j2 j2 j2)) (* 121728 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) 
(* j2 j2 j2)) (* 119040 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2)) (* 
61952 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) j2) (* 13312 h1 (* h2 h2 h2) (* 
h3 h3 h3) h4 (* h5 h5)) (* 512 h1 (* h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2
 j2 j2 j2 j2)) (* 7552 h1 (* h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 
j2)) (* 43392 h1 (* h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 
129408 h1 (* h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 219264 h1 (* h2
 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 212736 h1 (* h2 h2 h2) (* h3 h3 
h3) h4 h5 h6 (* j2 j2)) (* 110080 h1 (* h2 h2 h2) (* h3 h3 h3) h4 h5 h6 j2) (* 
23552 h1 (* h2 h2 h2) (* h3 h3 h3) h4 h5 h6) (* 256 h1 (* h2 h2 h2) (* h3 h3 h3)
 h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2304 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* 
h6 h6) (* j2 j2 j2 j2 j2)) (* 8448 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* 
j2 j2 j2 j2)) (* 16128 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2)) 
(* 16896 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2)) (* 9216 h1 (* h2 
h2 h2) (* h3 h3 h3) h4 (* h6 h6) j2) (* 2048 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* 
h6 h6)) (* 256 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) 
(* 2304 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 8448 h1
 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 16128 h1 (* h2 h2 h2
) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2)) (* 16896 h1 (* h2 h2 h2) (* h3 h3 h3) 
(* h5 h5 h5) (* j2 j2)) (* 9216 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) j2) 
(* 2048 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5)) (* 256 h1 (* h2 h2 h2) (* h3 
h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 3840 h1 (* h2 h2 h2) (* h3 h3 
h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 22272 h1 (* h2 h2 h2) (* h3 h3 h3) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 66816 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5)
 h6 (* j2 j2 j2 j2)) (* 113664 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 
j2 j2)) (* 110592 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2)) (* 57344 
h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 j2) (* 12288 h1 (* h2 h2 h2) (* h3 h3 
h3) (* h5 h5) h6) (* 256 h1 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 3776 h1 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 21696 h1 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 64704 h1 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 109632 h1
 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 106368 h1 (* h2 h2 h2) 
(* h3 h3 h3) h5 (* h6 h6) (* j2 j2)) (* 55040 h1 (* h2 h2 h2) (* h3 h3 h3) h5 
(* h6 h6) j2) (* 11776 h1 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6)) (* 128 h1 (* 
h2 h2 h2) (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1152 h1 (* h2 h2 
h2) (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 4224 h1 (* h2 h2 h2) (* h3 
h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 8064 h1 (* h2 h2 h2) (* h3 h3 h3) (* h6 
h6 h6) (* j2 j2 j2)) (* 8448 h1 (* h2 h2 h2) (* h3 h3 h3) (* h6 h6 h6) (* j2 j2)
) (* 4608 h1 (* h2 h2 h2) (* h3 h3 h3) (* h6 h6 h6) j2) (* 1024 h1 (* h2 h2 h2) 
(* h3 h3 h3) (* h6 h6 h6)) (* 64 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2
 j2 j2 j2 j2 j2)) (* 816 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 
j2 j2)) (* 4032 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 
10032 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 13344 h1 (* h2 
h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2)) (* 9024 h1 (* h2 h2 h2) (* h3 h3) 
(* h4 h4 h4) h5 j2) (* 2432 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5) (* 16 h1 
(* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 128 h1 (* h2 h2 h2
) (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2)) (* 400 h1 (* h2 h2 h2) (* h3 h3) 
(* h4 h4 h4) h6 (* j2 j2 j2)) (* 608 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h6 
(* j2 j2)) (* 448 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h6 j2) (* 128 h1 (* h2 
h2 h2) (* h3 h3) (* h4 h4 h4) h6) (* 128 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* 
h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1728 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 
h5) (* j2 j2 j2 j2 j2)) (* 8832 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) 
(* j2 j2 j2 j2)) (* 22464 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2
 j2)) (* 30336 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 20736
 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) j2) (* 5632 h1 (* h2 h2 h2) (* h3
 h3) (* h4 h4) (* h5 h5)) (* 192 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2
 j2 j2 j2 j2 j2)) (* 2496 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 
j2 j2)) (* 12480 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 
31296 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 41856 h1 (* h2 
h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 28416 h1 (* h2 h2 h2) (* h3 h3) 
(* h4 h4) h5 h6 j2) (* 7680 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6) (* 48 h1 
(* h2 h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 384 h1 (* h2 
h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 1200 h1 (* h2 h2 h2) 
(* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 1824 h1 (* h2 h2 h2) (* h3 h3) 
(* h4 h4) (* h6 h6) (* j2 j2)) (* 1344 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h6
 h6) j2) (* 384 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h6 h6)) (* 64 h1 (* h2 h2
 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 912 h1 (* h2 h2 h2) (* 
h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 4800 h1 (* h2 h2 h2) (* h3 h3) h4 
(* h5 h5 h5) (* j2 j2 j2 j2)) (* 12432 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5)
 (* j2 j2 j2)) (* 16992 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2)) (* 
11712 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) j2) (* 3200 h1 (* h2 h2 h2) (* 
h3 h3) h4 (* h5 h5 h5)) (* 256 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 
j2 j2 j2 j2 j2)) (* 3440 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 
j2 j2)) (* 17536 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 
44528 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 60064 h1 (* h2 
h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 41024 h1 (* h2 h2 h2) (* h3 h3) 
h4 (* h5 h5) h6 j2) (* 11136 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6) (* 192 
h1 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2544 h1 (* 
h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 12864 h1 (* h2 h2 h2)
 (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 32496 h1 (* h2 h2 h2) (* h3 h3) 
h4 h5 (* h6 h6) (* j2 j2 j2)) (* 43680 h1 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6)
 (* j2 j2)) (* 29760 h1 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) j2) (* 8064 h1 
(* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6)) (* 48 h1 (* h2 h2 h2) (* h3 h3) h4 (* h6
 h6 h6) (* j2 j2 j2 j2 j2)) (* 384 h1 (* h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* 
j2 j2 j2 j2)) (* 1200 h1 (* h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2)) 
(* 1824 h1 (* h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2)) (* 1344 h1 (* h2 h2
 h2) (* h3 h3) h4 (* h6 h6 h6) j2) (* 384 h1 (* h2 h2 h2) (* h3 h3) h4 (* h6 h6 
h6)) (* 32 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 256 
h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 800 h1 (* h2 h2 h2
) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 1216 h1 (* h2 h2 h2) (* h3 h3) (* 
h5 h5 h5 h5) (* j2 j2)) (* 896 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) j2) (* 
256 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5)) (* 64 h1 (* h2 h2 h2) (* h3 h3) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 896 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5
 h5) h6 (* j2 j2 j2 j2 j2)) (* 4672 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 
(* j2 j2 j2 j2)) (* 12032 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)
) (* 16384 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2)) (* 11264 h1 (* 
h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 j2) (* 3072 h1 (* h2 h2 h2) (* h3 h3) (* h5 
h5 h5) h6) (* 128 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 1712 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)
) (* 8704 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 
22064 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 29728 h1 
(* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 20288 h1 (* h2 h2 h2) 
(* h3 h3) (* h5 h5) (* h6 h6) j2) (* 5504 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5) 
(* h6 h6)) (* 64 h1 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)
) (* 864 h1 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 4416 
h1 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 11232 h1 (* h2 h2 
h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 15168 h1 (* h2 h2 h2) (* h3 h3) 
h5 (* h6 h6 h6) (* j2 j2)) (* 10368 h1 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) j2
) (* 2816 h1 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6)) (* 16 h1 (* h2 h2 h2) (* h3
 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 128 h1 (* h2 h2 h2) (* h3 h3) (* h6 
h6 h6 h6) (* j2 j2 j2 j2)) (* 400 h1 (* h2 h2 h2) (* h3 h3) (* h6 h6 h6 h6) (* 
j2 j2 j2)) (* 608 h1 (* h2 h2 h2) (* h3 h3) (* h6 h6 h6 h6) (* j2 j2)) (* 448 h1
 (* h2 h2 h2) (* h3 h3) (* h6 h6 h6 h6) j2) (* 128 h1 (* h2 h2 h2) (* h3 h3) (* 
h6 h6 h6 h6)) (* 16 h1 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)
) (* 184 h1 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 792 h1 
(* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 1616 h1 (* h2 h2 h2) h3 
(* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 1568 h1 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 
h5) j2) (* 576 h1 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5)) (* 8 h1 (* h2 h2 h2) 
h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 56 h1 (* h2 h2 h2) h3 (* h4 h4 h4) h5 
h6 (* j2 j2 j2)) (* 144 h1 (* h2 h2 h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2)) (* 160 
h1 (* h2 h2 h2) h3 (* h4 h4 h4) h5 h6 j2) (* 64 h1 (* h2 h2 h2) h3 (* h4 h4 h4) 
h5 h6) (* 16 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 
196 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 876 h1 (* h2 
h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 1832 h1 (* h2 h2 h2) h3 (* h4 
h4) (* h5 h5 h5) (* j2 j2)) (* 1808 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) j2
) (* 672 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5)) (* 48 h1 (* h2 h2 h2) h3 (* 
h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 568 h1 (* h2 h2 h2) h3 (* h4 h4) (* 
h5 h5) h6 (* j2 j2 j2 j2)) (* 2488 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* 
j2 j2 j2)) (* 5136 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 5024 
h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 j2) (* 1856 h1 (* h2 h2 h2) h3 (* h4 
h4) (* h5 h5) h6) (* 24 h1 (* h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2
)) (* 168 h1 (* h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 432 h1 (* 
h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 480 h1 (* h2 h2 h2) h3 (* h4 
h4) h5 (* h6 h6) j2) (* 192 h1 (* h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6)) (* 16 h1 
(* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 112 h1 (* h2 h2 h2) h3 h4
 (* h5 h5 h5 h5) (* j2 j2 j2)) (* 288 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) (* 
j2 j2)) (* 320 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) j2) (* 128 h1 (* h2 h2 h2) 
h3 h4 (* h5 h5 h5 h5)) (* 32 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2)) (* 400 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 1808 h1
 (* h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 3808 h1 (* h2 h2 h2) h3 h4 
(* h5 h5 h5) h6 (* j2 j2)) (* 3776 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5) h6 j2) (* 
1408 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5) h6) (* 48 h1 (* h2 h2 h2) h3 h4 (* h5 h5
) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 584 h1 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6)
 (* j2 j2 j2 j2)) (* 2600 h1 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)
) (* 5424 h1 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 5344 h1 (* h2 
h2 h2) h3 h4 (* h5 h5) (* h6 h6) j2) (* 1984 h1 (* h2 h2 h2) h3 h4 (* h5 h5) (* 
h6 h6)) (* 24 h1 (* h2 h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 168 h1 
(* h2 h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 432 h1 (* h2 h2 h2) h3 h4 h5
 (* h6 h6 h6) (* j2 j2)) (* 480 h1 (* h2 h2 h2) h3 h4 h5 (* h6 h6 h6) j2) (* 192
 h1 (* h2 h2 h2) h3 h4 h5 (* h6 h6 h6)) (* 16 h1 (* h2 h2 h2) h3 (* h5 h5 h5 h5)
 h6 (* j2 j2 j2 j2)) (* 112 h1 (* h2 h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) 
(* 288 h1 (* h2 h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 320 h1 (* h2 h2 h2) 
h3 (* h5 h5 h5 h5) h6 j2) (* 128 h1 (* h2 h2 h2) h3 (* h5 h5 h5 h5) h6) (* 16 h1
 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 204 h1 (* h2 h2 
h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 932 h1 (* h2 h2 h2) h3 (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2)) (* 1976 h1 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6)
 (* j2 j2)) (* 1968 h1 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) j2) (* 736 h1 (* 
h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6)) (* 16 h1 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6
 h6) (* j2 j2 j2 j2 j2)) (* 200 h1 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2)) (* 904 h1 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 
1904 h1 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 1888 h1 (* h2 h2 h2
) h3 (* h5 h5) (* h6 h6 h6) j2) (* 704 h1 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6)
) (* 8 h1 (* h2 h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 56 h1 (* h2 h2 
h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 144 h1 (* h2 h2 h2) h3 h5 (* h6 h6 h6
 h6) (* j2 j2)) (* 160 h1 (* h2 h2 h2) h3 h5 (* h6 h6 h6 h6) j2) (* 64 h1 (* h2 
h2 h2) h3 h5 (* h6 h6 h6 h6)) (* 2 h1 (* h2 h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* 
j2 j2 j2)) (* 12 h1 (* h2 h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 24 h1 
(* h2 h2 h2) (* h4 h4 h4) (* h5 h5) h6 j2) (* 16 h1 (* h2 h2 h2) (* h4 h4 h4) 
(* h5 h5) h6) (* 4 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 24
 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 48 h1 (* h2 h2 h2) (* 
h4 h4) (* h5 h5 h5) h6 j2) (* 32 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5) h6) (* 6
 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 36 h1 (* h2 h2 
h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 72 h1 (* h2 h2 h2) (* h4 h4) (* 
h5 h5) (* h6 h6) j2) (* 48 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6)) (* 2 
h1 (* h2 h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 12 h1 (* h2 h2 h2) h4 (* 
h5 h5 h5 h5) h6 (* j2 j2)) (* 24 h1 (* h2 h2 h2) h4 (* h5 h5 h5 h5) h6 j2) (* 16
 h1 (* h2 h2 h2) h4 (* h5 h5 h5 h5) h6) (* 8 h1 (* h2 h2 h2) h4 (* h5 h5 h5) (* 
h6 h6) (* j2 j2 j2)) (* 48 h1 (* h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) 
(* 96 h1 (* h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6) j2) (* 64 h1 (* h2 h2 h2) h4 (* 
h5 h5 h5) (* h6 h6)) (* 6 h1 (* h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)
) (* 36 h1 (* h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 72 h1 (* h2 h2 
h2) h4 (* h5 h5) (* h6 h6 h6) j2) (* 48 h1 (* h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6
)) (* 2 h1 (* h2 h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 12 h1 (* h2 
h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 24 h1 (* h2 h2 h2) (* h5 h5 h5 h5
) (* h6 h6) j2) (* 16 h1 (* h2 h2 h2) (* h5 h5 h5 h5) (* h6 h6)) (* 4 h1 (* h2 
h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 24 h1 (* h2 h2 h2) (* h5 h5 h5
) (* h6 h6 h6) (* j2 j2)) (* 48 h1 (* h2 h2 h2) (* h5 h5 h5) (* h6 h6 h6) j2) 
(* 32 h1 (* h2 h2 h2) (* h5 h5 h5) (* h6 h6 h6)) (* 2 h1 (* h2 h2 h2) (* h5 h5) 
(* h6 h6 h6 h6) (* j2 j2 j2)) (* 12 h1 (* h2 h2 h2) (* h5 h5) (* h6 h6 h6 h6) 
(* j2 j2)) (* 24 h1 (* h2 h2 h2) (* h5 h5) (* h6 h6 h6 h6) j2) (* 16 h1 (* h2 h2
 h2) (* h5 h5) (* h6 h6 h6 h6)) (* 768 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5
 (* j2 j2 j2 j2 j2 j2 j2)) (* 9728 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* 
j2 j2 j2 j2 j2 j2)) (* 48640 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 
j2 j2 j2)) (* 126976 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) 
(* 189184 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 162304 h1 
(* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2)) (* 74752 h1 (* h2 h2) (* h3 h3
 h3 h3) (* h4 h4) h5 j2) (* 14336 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5) (* 
256 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 2048 h1 
(* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 6656 h1 (* h2 h2) 
(* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2)) (* 11264 h1 (* h2 h2) (* h3 h3 h3 
h3) (* h4 h4) h6 (* j2 j2 j2)) (* 10496 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) 
h6 (* j2 j2)) (* 5120 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h6 j2) (* 1024 h1 
(* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h6) (* 768 h1 (* h2 h2) (* h3 h3 h3 h3) h4 
(* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 9984 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* 
h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 50688 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5)
 (* j2 j2 j2 j2 j2)) (* 133632 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 
j2 j2 j2)) (* 200448 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 
172800 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2)) (* 79872 h1 (* h2 h2
) (* h3 h3 h3 h3) h4 (* h5 h5) j2) (* 15360 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* 
h5 h5)) (* 1536 h1 (* h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 19456 h1 (* h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 97280 
h1 (* h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 253952 h1 (* h2 h2)
 (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 378368 h1 (* h2 h2) (* h3 h3 h3 h3
) h4 h5 h6 (* j2 j2 j2)) (* 324608 h1 (* h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 
j2)) (* 149504 h1 (* h2 h2) (* h3 h3 h3 h3) h4 h5 h6 j2) (* 28672 h1 (* h2 h2) 
(* h3 h3 h3 h3) h4 h5 h6) (* 512 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6) (* j2
 j2 j2 j2 j2 j2)) (* 4096 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 
j2 j2)) (* 13312 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 
22528 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2)) (* 20992 h1 (* h2 
h2) (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2)) (* 10240 h1 (* h2 h2) (* h3 h3 h3 h3
) h4 (* h6 h6) j2) (* 2048 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6)) (* 512 h1 
(* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 4096 h1 (* h2 
h2) (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 13312 h1 (* h2 h2) (* h3
 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 22528 h1 (* h2 h2) (* h3 h3 h3 h3) 
(* h5 h5 h5) (* j2 j2 j2)) (* 20992 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) 
(* j2 j2)) (* 10240 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) j2) (* 2048 h1 (* 
h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5)) (* 768 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 9728 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2)) (* 48640 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* 
j2 j2 j2 j2 j2)) (* 126976 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2
 j2)) (* 189184 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 
162304 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2)) (* 74752 h1 (* h2 h2
) (* h3 h3 h3 h3) (* h5 h5) h6 j2) (* 14336 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 
h5) h6) (* 768 h1 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2
)) (* 9728 h1 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
48640 h1 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 126976 h1
 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 189184 h1 (* h2 h2) 
(* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 162304 h1 (* h2 h2) (* h3 h3 h3 h3
) h5 (* h6 h6) (* j2 j2)) (* 74752 h1 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) j2)
 (* 14336 h1 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6)) (* 256 h1 (* h2 h2) (* h3 
h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2048 h1 (* h2 h2) (* h3 h3 h3 
h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 6656 h1 (* h2 h2) (* h3 h3 h3 h3) (* h6 
h6 h6) (* j2 j2 j2 j2)) (* 11264 h1 (* h2 h2) (* h3 h3 h3 h3) (* h6 h6 h6) (* j2
 j2 j2)) (* 10496 h1 (* h2 h2) (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2)) (* 5120 
h1 (* h2 h2) (* h3 h3 h3 h3) (* h6 h6 h6) j2) (* 1024 h1 (* h2 h2) (* h3 h3 h3 
h3) (* h6 h6 h6)) (* 384 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 
j2 j2 j2)) (* 4224 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2))
 (* 18048 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 38784 h1
 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 44544 h1 (* h2 h2) (* 
h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2)) (* 26112 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4
 h4) h5 j2) (* 6144 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5) (* 64 h1 (* h2 h2
) (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 448 h1 (* h2 h2) (* h3 h3 
h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2)) (* 1216 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 
h4) h6 (* j2 j2 j2)) (* 1600 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2)
) (* 1024 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h6 j2) (* 256 h1 (* h2 h2) (* 
h3 h3 h3) (* h4 h4 h4) h6) (* 768 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) 
(* j2 j2 j2 j2 j2 j2)) (* 8896 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* 
j2 j2 j2 j2 j2)) (* 39232 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2
 j2 j2)) (* 86080 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2)) 
(* 100288 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 59392 h1 
(* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) j2) (* 14080 h1 (* h2 h2) (* h3 h3 h3
) (* h4 h4) (* h5 h5)) (* 1152 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 
j2 j2 j2 j2 j2)) (* 12864 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 
j2 j2)) (* 55488 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 
120000 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 138432 h1 (* 
h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 81408 h1 (* h2 h2) (* h3 h3 h3
) (* h4 h4) h5 h6 j2) (* 19200 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6) (* 192
 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1344 h1 
(* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 3648 h1 (* h2 h2)
 (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 4800 h1 (* h2 h2) (* h3 h3 h3
) (* h4 h4) (* h6 h6) (* j2 j2)) (* 3072 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* 
h6 h6) j2) (* 768 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6)) (* 384 h1 (* h2
 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 4608 h1 (* h2 h2) 
(* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 20736 h1 (* h2 h2) (* h3 h3 
h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 46080 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5
 h5 h5) (* j2 j2 j2)) (* 54144 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 
j2)) (* 32256 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) j2) (* 7680 h1 (* h2 h2)
 (* h3 h3 h3) h4 (* h5 h5 h5)) (* 1536 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6
 (* j2 j2 j2 j2 j2 j2)) (* 17728 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2
 j2 j2 j2 j2)) (* 78016 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2
)) (* 170944 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 198976 
h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 117760 h1 (* h2 h2) (* 
h3 h3 h3) h4 (* h5 h5) h6 j2) (* 27904 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6
) (* 1152 h1 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
13056 h1 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 56832 h1 
(* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 123648 h1 (* h2 h2) 
(* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 143232 h1 (* h2 h2) (* h3 h3 h3) 
h4 h5 (* h6 h6) (* j2 j2)) (* 84480 h1 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) j2
) (* 19968 h1 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6)) (* 192 h1 (* h2 h2) (* h3 
h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1344 h1 (* h2 h2) (* h3 h3 h3) h4 
(* h6 h6 h6) (* j2 j2 j2 j2)) (* 3648 h1 (* h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6) 
(* j2 j2 j2)) (* 4800 h1 (* h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2)) (* 
3072 h1 (* h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6) j2) (* 768 h1 (* h2 h2) (* h3 h3 
h3) h4 (* h6 h6 h6)) (* 128 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 
j2 j2 j2)) (* 896 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 
2432 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 3200 h1 (* h2 h2
) (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2)) (* 2048 h1 (* h2 h2) (* h3 h3 h3) (* 
h5 h5 h5 h5) j2) (* 512 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5)) (* 384 h1 (* 
h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 4544 h1 (* h2 h2) 
(* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 20288 h1 (* h2 h2) (* h3 h3 
h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 44864 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5
 h5) h6 (* j2 j2 j2)) (* 52544 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 
j2)) (* 31232 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 j2) (* 7424 h1 (* h2 h2)
 (* h3 h3 h3) (* h5 h5 h5) h6) (* 768 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 8832 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6)
 (* j2 j2 j2 j2 j2)) (* 38784 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* 
j2 j2 j2 j2)) (* 84864 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2
)) (* 98688 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 58368 h1
 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) j2) (* 13824 h1 (* h2 h2) (* h3 h3 
h3) (* h5 h5) (* h6 h6)) (* 384 h1 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 4416 h1 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 
j2 j2)) (* 19392 h1 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 
42432 h1 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 49344 h1 (* h2 
h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 29184 h1 (* h2 h2) (* h3 h3 h3) 
h5 (* h6 h6 h6) j2) (* 6912 h1 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6)) (* 64 h1 
(* h2 h2) (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 448 h1 (* h2 h2) 
(* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 1216 h1 (* h2 h2) (* h3 h3 h3) 
(* h6 h6 h6 h6) (* j2 j2 j2)) (* 1600 h1 (* h2 h2) (* h3 h3 h3) (* h6 h6 h6 h6) 
(* j2 j2)) (* 1024 h1 (* h2 h2) (* h3 h3 h3) (* h6 h6 h6 h6) j2) (* 256 h1 (* h2
 h2) (* h3 h3 h3) (* h6 h6 h6 h6)) (* 48 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) 
h5 (* j2 j2 j2 j2 j2)) (* 416 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2
 j2 j2)) (* 1392 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2)) (* 2240
 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2)) (* 1728 h1 (* h2 h2) (* h3
 h3) (* h4 h4 h4 h4) h5 j2) (* 512 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5) 
(* 192 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 1904
 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 7008 h1 (* h2
 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 12080 h1 (* h2 h2) (* h3 
h3) (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 9792 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4
) (* h5 h5) j2) (* 3008 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5)) (* 192 h1
 (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 1728 h1 (* h2 h2)
 (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 5952 h1 (* h2 h2) (* h3 h3) 
(* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 9792 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 
h6 (* j2 j2)) (* 7680 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 j2) (* 2304 h1 
(* h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6) (* 192 h1 (* h2 h2) (* h3 h3) (* h4 h4) 
(* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 1984 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 
h5 h5) (* j2 j2 j2 j2)) (* 7488 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) 
(* j2 j2 j2)) (* 13120 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2)) 
(* 10752 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) j2) (* 3328 h1 (* h2 h2) 
(* h3 h3) (* h4 h4) (* h5 h5 h5)) (* 576 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 
h5) h6 (* j2 j2 j2 j2 j2)) (* 5776 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6
 (* j2 j2 j2 j2)) (* 21408 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 
j2 j2)) (* 37072 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 
30144 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 j2) (* 9280 h1 (* h2 h2) (* 
h3 h3) (* h4 h4) (* h5 h5) h6) (* 288 h1 (* h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 
h6) (* j2 j2 j2 j2 j2)) (* 2688 h1 (* h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6) 
(* j2 j2 j2 j2)) (* 9504 h1 (* h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 
j2)) (* 15936 h1 (* h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 12672 
h1 (* h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6) j2) (* 3840 h1 (* h2 h2) (* h3 h3)
 (* h4 h4) h5 (* h6 h6)) (* 48 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 
j2 j2 j2 j2)) (* 512 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2)) 
(* 1968 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2)) (* 3488 h1 (* h2
 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2)) (* 2880 h1 (* h2 h2) (* h3 h3) h4 
(* h5 h5 h5 h5) j2) (* 896 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5)) (* 384 h1 
(* h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 3968 h1 (* h2 h2) 
(* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 14976 h1 (* h2 h2) (* h3 h3) h4
 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 26240 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) 
h6 (* j2 j2)) (* 21504 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 j2) (* 6656 h1 
(* h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6) (* 576 h1 (* h2 h2) (* h3 h3) h4 (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 5840 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2)) (* 21792 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6
) (* j2 j2 j2)) (* 37904 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2)
) (* 30912 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) j2) (* 9536 h1 (* h2 h2
) (* h3 h3) h4 (* h5 h5) (* h6 h6)) (* 192 h1 (* h2 h2) (* h3 h3) h4 h5 (* h6 h6
 h6) (* j2 j2 j2 j2 j2)) (* 1856 h1 (* h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2
 j2 j2 j2)) (* 6720 h1 (* h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 
11456 h1 (* h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2)) (* 9216 h1 (* h2 h2) 
(* h3 h3) h4 h5 (* h6 h6 h6) j2) (* 2816 h1 (* h2 h2) (* h3 h3) h4 h5 (* h6 h6 
h6)) (* 48 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 512 
h1 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 1968 h1 (* h2 h2) 
(* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 3488 h1 (* h2 h2) (* h3 h3) (* h5 
h5 h5 h5) h6 (* j2 j2)) (* 2880 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 j2) 
(* 896 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6) (* 192 h1 (* h2 h2) (* h3 h3) 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1984 h1 (* h2 h2) (* h3 h3) (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 7488 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2)) (* 13120 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) 
(* j2 j2)) (* 10752 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) j2) (* 3328 h1
 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6)) (* 192 h1 (* h2 h2) (* h3 h3) (* h5
 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1968 h1 (* h2 h2) (* h3 h3) (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2)) (* 7392 h1 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2)) (* 12912 h1 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 
j2)) (* 10560 h1 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) j2) (* 3264 h1 (* h2
 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6)) (* 48 h1 (* h2 h2) (* h3 h3) h5 (* h6 h6 
h6 h6) (* j2 j2 j2 j2 j2)) (* 480 h1 (* h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* 
j2 j2 j2 j2)) (* 1776 h1 (* h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) 
(* 3072 h1 (* h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2)) (* 2496 h1 (* h2 h2
) (* h3 h3) h5 (* h6 h6 h6 h6) j2) (* 768 h1 (* h2 h2) (* h3 h3) h5 (* h6 h6 h6 
h6)) (* 12 h1 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 88 h1 
(* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 236 h1 (* h2 h2) h3 (* 
h4 h4 h4 h4) (* h5 h5) (* j2 j2)) (* 272 h1 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 
h5) j2) (* 112 h1 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5)) (* 24 h1 (* h2 h2) h3 
(* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 208 h1 (* h2 h2) h3 (* h4 h4 h4) 
(* h5 h5 h5) (* j2 j2 j2)) (* 632 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) (* 
j2 j2)) (* 800 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) j2) (* 352 h1 (* h2 h2)
 h3 (* h4 h4 h4) (* h5 h5 h5)) (* 48 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 
(* j2 j2 j2 j2)) (* 372 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) 
(* 1044 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 1248 h1 (* h2 h2
) h3 (* h4 h4 h4) (* h5 h5) h6 j2) (* 528 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5)
 h6) (* 12 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 108 h1 
(* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 336 h1 (* h2 h2) h3 (* 
h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 432 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 
h5) j2) (* 192 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5)) (* 72 h1 (* h2 h2) h3 
(* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 644 h1 (* h2 h2) h3 (* h4 h4) (* 
h5 h5 h5) h6 (* j2 j2 j2)) (* 1996 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* 
j2 j2)) (* 2560 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 j2) (* 1136 h1 (* h2 
h2) h3 (* h4 h4) (* h5 h5 h5) h6) (* 72 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2)) (* 588 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* 
j2 j2 j2)) (* 1716 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 
2112 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) j2) (* 912 h1 (* h2 h2) h3 
(* h4 h4) (* h5 h5) (* h6 h6)) (* 24 h1 (* h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2
 j2 j2 j2)) (* 224 h1 (* h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 712 h1
 (* h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 928 h1 (* h2 h2) h3 h4 (* h5 
h5 h5 h5) h6 j2) (* 416 h1 (* h2 h2) h3 h4 (* h5 h5 h5 h5) h6) (* 72 h1 (* h2 h2
) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 664 h1 (* h2 h2) h3 h4 (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2)) (* 2096 h1 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6)
 (* j2 j2)) (* 2720 h1 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) j2) (* 1216 h1 (* 
h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6)) (* 48 h1 (* h2 h2) h3 h4 (* h5 h5) (* h6 h6
 h6) (* j2 j2 j2 j2)) (* 412 h1 (* h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 
j2)) (* 1244 h1 (* h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 1568 h1 (* 
h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) j2) (* 688 h1 (* h2 h2) h3 h4 (* h5 h5) (* 
h6 h6 h6)) (* 12 h1 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 
116 h1 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 376 h1 (* h2 h2) 
h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 496 h1 (* h2 h2) h3 (* h5 h5 h5 h5) 
(* h6 h6) j2) (* 224 h1 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6)) (* 24 h1 (* h2 
h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 228 h1 (* h2 h2) h3 (* h5 
h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 732 h1 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 
h6) (* j2 j2)) (* 960 h1 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) j2) (* 432 h1 
(* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6)) (* 12 h1 (* h2 h2) h3 (* h5 h5) (* h6 h6
 h6 h6) (* j2 j2 j2 j2)) (* 108 h1 (* h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 
j2 j2)) (* 336 h1 (* h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 432 h1 
(* h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) j2) (* 192 h1 (* h2 h2) h3 (* h5 h5) (* 
h6 h6 h6 h6)) (* 2 h1 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 8 h1 
(* h2 h2) (* h4 h4 h4) (* h5 h5 h5) h6 j2) (* 8 h1 (* h2 h2) (* h4 h4 h4) (* h5 
h5 h5) h6) (* 2 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 8 h1 (* 
h2 h2) (* h4 h4) (* h5 h5 h5 h5) h6 j2) (* 8 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5 
h5) h6) (* 6 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 24 h1 
(* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6) j2) (* 24 h1 (* h2 h2) (* h4 h4) (* 
h5 h5 h5) (* h6 h6)) (* 4 h1 (* h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) 
(* 16 h1 (* h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6) j2) (* 16 h1 (* h2 h2) h4 (* h5 
h5 h5 h5) (* h6 h6)) (* 6 h1 (* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) 
(* 24 h1 (* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6) j2) (* 24 h1 (* h2 h2) h4 (* h5 
h5 h5) (* h6 h6 h6)) (* 2 h1 (* h2 h2) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2)) 
(* 8 h1 (* h2 h2) (* h5 h5 h5 h5) (* h6 h6 h6) j2) (* 8 h1 (* h2 h2) (* h5 h5 h5
 h5) (* h6 h6 h6)) (* 2 h1 (* h2 h2) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 
8 h1 (* h2 h2) (* h5 h5 h5) (* h6 h6 h6 h6) j2) (* 8 h1 (* h2 h2) (* h5 h5 h5) 
(* h6 h6 h6 h6)) (* 512 h1 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 
j2)) (* 4352 h1 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 14848 
h1 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 26112 h1 h2 (* h3 h3 
h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 25088 h1 h2 (* h3 h3 h3 h3) (* h4 h4 h4)
 h5 (* j2 j2)) (* 12544 h1 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h5 j2) (* 2560 h1 h2 
(* h3 h3 h3 h3) (* h4 h4 h4) h5) (* 1024 h1 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 
h5) (* j2 j2 j2 j2 j2 j2)) (* 10240 h1 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) 
(* j2 j2 j2 j2 j2)) (* 38912 h1 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 
j2 j2)) (* 73728 h1 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 
74752 h1 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 38912 h1 h2 (* h3 
h3 h3 h3) (* h4 h4) (* h5 h5) j2) (* 8192 h1 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 
h5)) (* 1536 h1 h2 (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 
13568 h1 h2 (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 47616 h1 h2 
(* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 85504 h1 h2 (* h3 h3 h3 h3) 
(* h4 h4) h5 h6 (* j2 j2 j2)) (* 83456 h1 h2 (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* 
j2 j2)) (* 42240 h1 h2 (* h3 h3 h3 h3) (* h4 h4) h5 h6 j2) (* 8704 h1 h2 (* h3 
h3 h3 h3) (* h4 h4) h5 h6) (* 512 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2
 j2 j2 j2 j2)) (* 5120 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2))
 (* 19456 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 36864 h1 h2 
(* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2)) (* 37376 h1 h2 (* h3 h3 h3 h3) h4 
(* h5 h5 h5) (* j2 j2)) (* 19456 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) j2) (* 
4096 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5)) (* 2048 h1 h2 (* h3 h3 h3 h3) h4 (* 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 20480 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5) h6 
(* j2 j2 j2 j2 j2)) (* 77824 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 
j2)) (* 147456 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 149504 h1 
h2 (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 77824 h1 h2 (* h3 h3 h3 h3) h4 
(* h5 h5) h6 j2) (* 16384 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5) h6) (* 1536 h1 h2 
(* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 14080 h1 h2 (* h3 h3 
h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 50688 h1 h2 (* h3 h3 h3 h3) h4 h5 
(* h6 h6) (* j2 j2 j2 j2)) (* 92672 h1 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 
j2 j2)) (* 91648 h1 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 46848 h1 h2
 (* h3 h3 h3 h3) h4 h5 (* h6 h6) j2) (* 9728 h1 h2 (* h3 h3 h3 h3) h4 h5 (* h6 
h6)) (* 512 h1 h2 (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 5120
 h1 h2 (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 19456 h1 h2 (* h3 
h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 36864 h1 h2 (* h3 h3 h3 h3) (* h5 
h5 h5) h6 (* j2 j2 j2)) (* 37376 h1 h2 (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2)
) (* 19456 h1 h2 (* h3 h3 h3 h3) (* h5 h5 h5) h6 j2) (* 4096 h1 h2 (* h3 h3 h3 
h3) (* h5 h5 h5) h6) (* 1024 h1 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 10240 h1 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 38912 h1 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 
73728 h1 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 74752 h1 h2 (* 
h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 38912 h1 h2 (* h3 h3 h3 h3) (* h5
 h5) (* h6 h6) j2) (* 8192 h1 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6)) (* 512 h1 
h2 (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4864 h1 h2 (* h3 h3
 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 17920 h1 h2 (* h3 h3 h3 h3) h5 
(* h6 h6 h6) (* j2 j2 j2 j2)) (* 33280 h1 h2 (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* 
j2 j2 j2)) (* 33280 h1 h2 (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 17152 h1
 h2 (* h3 h3 h3 h3) h5 (* h6 h6 h6) j2) (* 3584 h1 h2 (* h3 h3 h3 h3) h5 (* h6 
h6 h6)) (* 128 h1 h2 (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 960 
h1 h2 (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 2752 h1 h2 (* h3 h3 h3
) (* h4 h4 h4 h4) h5 (* j2 j2 j2)) (* 3776 h1 h2 (* h3 h3 h3) (* h4 h4 h4 h4) h5
 (* j2 j2)) (* 2496 h1 h2 (* h3 h3 h3) (* h4 h4 h4 h4) h5 j2) (* 640 h1 h2 (* h3
 h3 h3) (* h4 h4 h4 h4) h5) (* 512 h1 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* 
j2 j2 j2 j2 j2)) (* 4352 h1 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 
j2)) (* 13568 h1 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 19712 
h1 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 13568 h1 h2 (* h3 h3 h3)
 (* h4 h4 h4) (* h5 h5) j2) (* 3584 h1 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5)) 
(* 512 h1 h2 (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 3968 h1 h2 
(* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 11648 h1 h2 (* h3 h3 h3) (* 
h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 16256 h1 h2 (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* 
j2 j2)) (* 10880 h1 h2 (* h3 h3 h3) (* h4 h4 h4) h5 h6 j2) (* 2816 h1 h2 (* h3 
h3 h3) (* h4 h4 h4) h5 h6) (* 512 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* 
j2 j2 j2 j2 j2)) (* 4544 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 
j2)) (* 14528 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 21440 
h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 14912 h1 h2 (* h3 h3 h3)
 (* h4 h4) (* h5 h5 h5) j2) (* 3968 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5)) 
(* 1536 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 13312 
h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 41984 h1 h2 (* h3 
h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 61440 h1 h2 (* h3 h3 h3) (* h4 h4
) (* h5 h5) h6 (* j2 j2)) (* 42496 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 j2)
 (* 11264 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) h6) (* 768 h1 h2 (* h3 h3 h3) 
(* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 6144 h1 h2 (* h3 h3 h3) (* h4 h4) 
h5 (* h6 h6) (* j2 j2 j2 j2)) (* 18432 h1 h2 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6)
 (* j2 j2 j2)) (* 26112 h1 h2 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 
17664 h1 h2 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) j2) (* 4608 h1 h2 (* h3 h3 h3) 
(* h4 h4) h5 (* h6 h6)) (* 128 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2
 j2 j2)) (* 1152 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 3712 
h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2)) (* 5504 h1 h2 (* h3 h3 h3) 
h4 (* h5 h5 h5 h5) (* j2 j2)) (* 3840 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) j2) 
(* 1024 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5)) (* 1024 h1 h2 (* h3 h3 h3) h4 (* 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 9216 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5) h6 
(* j2 j2 j2 j2)) (* 29696 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) 
(* 44032 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2)) (* 30720 h1 h2 (* h3 
h3 h3) h4 (* h5 h5 h5) h6 j2) (* 8192 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5) h6) (* 
1536 h1 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 13568 h1 
h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 43264 h1 h2 (* h3 h3 
h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 63744 h1 h2 (* h3 h3 h3) h4 (* h5 h5
) (* h6 h6) (* j2 j2)) (* 44288 h1 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) j2) 
(* 11776 h1 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6)) (* 512 h1 h2 (* h3 h3 h3) h4
 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 4224 h1 h2 (* h3 h3 h3) h4 h5 (* h6 h6 
h6) (* j2 j2 j2 j2)) (* 12928 h1 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2)
) (* 18560 h1 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2)) (* 12672 h1 h2 (* h3
 h3 h3) h4 h5 (* h6 h6 h6) j2) (* 3328 h1 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6)) 
(* 128 h1 h2 (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 1152 h1 h2 
(* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 3712 h1 h2 (* h3 h3 h3) (* 
h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 5504 h1 h2 (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* 
j2 j2)) (* 3840 h1 h2 (* h3 h3 h3) (* h5 h5 h5 h5) h6 j2) (* 1024 h1 h2 (* h3 h3
 h3) (* h5 h5 h5 h5) h6) (* 512 h1 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2)) (* 4672 h1 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2))
 (* 15168 h1 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 22592 h1 h2
 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 15808 h1 h2 (* h3 h3 h3) (* 
h5 h5 h5) (* h6 h6) j2) (* 4224 h1 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6)) (* 
512 h1 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 4608 h1 h2 
(* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 14848 h1 h2 (* h3 h3 h3)
 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 22016 h1 h2 (* h3 h3 h3) (* h5 h5) (* 
h6 h6 h6) (* j2 j2)) (* 15360 h1 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) j2) (* 
4096 h1 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6)) (* 128 h1 h2 (* h3 h3 h3) h5 (* 
h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1088 h1 h2 (* h3 h3 h3) h5 (* h6 h6 h6 h6) 
(* j2 j2 j2 j2)) (* 3392 h1 h2 (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 
4928 h1 h2 (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2)) (* 3392 h1 h2 (* h3 h3 h3)
 h5 (* h6 h6 h6 h6) j2) (* 896 h1 h2 (* h3 h3 h3) h5 (* h6 h6 h6 h6)) (* 64 h1 
h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 416 h1 h2 (* h3 h3) 
(* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 960 h1 h2 (* h3 h3) (* h4 h4 h4 h4) 
(* h5 h5) (* j2 j2)) (* 928 h1 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) j2) (* 320
 h1 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5)) (* 128 h1 h2 (* h3 h3) (* h4 h4 h4) 
(* h5 h5 h5) (* j2 j2 j2 j2)) (* 944 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) 
(* j2 j2 j2)) (* 2368 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2)) (* 
2416 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) j2) (* 864 h1 h2 (* h3 h3) (* h4 
h4 h4) (* h5 h5 h5)) (* 256 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 
j2 j2)) (* 1744 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 4160 
h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 4112 h1 h2 (* h3 h3) (* 
h4 h4 h4) (* h5 h5) h6 j2) (* 1440 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) h6) 
(* 64 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 480 h1 h2 
(* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 1216 h1 h2 (* h3 h3) (* h4 
h4) (* h5 h5 h5 h5) (* j2 j2)) (* 1248 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5)
 j2) (* 448 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5)) (* 384 h1 h2 (* h3 h3) 
(* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 2912 h1 h2 (* h3 h3) (* h4 h4) (* 
h5 h5 h5) h6 (* j2 j2 j2)) (* 7424 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* 
j2 j2)) (* 7648 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 j2) (* 2752 h1 h2 (* 
h3 h3) (* h4 h4) (* h5 h5 h5) h6) (* 384 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2)) (* 2736 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) 
(* j2 j2 j2)) (* 6720 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) 
(* 6768 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) j2) (* 2400 h1 h2 (* h3 h3
) (* h4 h4) (* h5 h5) (* h6 h6)) (* 128 h1 h2 (* h3 h3) h4 (* h5 h5 h5 h5) h6 
(* j2 j2 j2 j2)) (* 992 h1 h2 (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 
2560 h1 h2 (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 2656 h1 h2 (* h3 h3) h4
 (* h5 h5 h5 h5) h6 j2) (* 960 h1 h2 (* h3 h3) h4 (* h5 h5 h5 h5) h6) (* 384 h1 
h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 2992 h1 h2 (* h3 h3) 
h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 7744 h1 h2 (* h3 h3) h4 (* h5 h5 h5) 
(* h6 h6) (* j2 j2)) (* 8048 h1 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) j2) (* 
2912 h1 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6)) (* 256 h1 h2 (* h3 h3) h4 (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1904 h1 h2 (* h3 h3) h4 (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2)) (* 4800 h1 h2 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2)) 
(* 4912 h1 h2 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) j2) (* 1760 h1 h2 (* h3 h3) h4
 (* h5 h5) (* h6 h6 h6)) (* 64 h1 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2)) (* 512 h1 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 
1344 h1 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 1408 h1 h2 (* h3 h3
) (* h5 h5 h5 h5) (* h6 h6) j2) (* 512 h1 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6)
) (* 128 h1 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1024 h1 
h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 2688 h1 h2 (* h3 h3) (* 
h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 2816 h1 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 
h6) j2) (* 1024 h1 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6)) (* 64 h1 h2 (* h3 h3)
 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 496 h1 h2 (* h3 h3) (* h5 h5) (* 
h6 h6 h6 h6) (* j2 j2 j2)) (* 1280 h1 h2 (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* 
j2 j2)) (* 1328 h1 h2 (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) j2) (* 480 h1 h2 (* h3
 h3) (* h5 h5) (* h6 h6 h6 h6)) (* 8 h1 h2 h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2
 j2 j2)) (* 40 h1 h2 h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2)) (* 64 h1 h2 h3 
(* h4 h4 h4 h4) (* h5 h5 h5) j2) (* 32 h1 h2 h3 (* h4 h4 h4 h4) (* h5 h5 h5)) 
(* 8 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 40 h1 h2 h3 (* h4 h4
 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 64 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5 h5) j2) 
(* 32 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5 h5)) (* 32 h1 h2 h3 (* h4 h4 h4) (* h5 
h5 h5) h6 (* j2 j2 j2)) (* 176 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2)) 
(* 304 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5) h6 j2) (* 160 h1 h2 h3 (* h4 h4 h4) 
(* h5 h5 h5) h6) (* 24 h1 h2 h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 
136 h1 h2 h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 240 h1 h2 h3 (* h4 h4) 
(* h5 h5 h5 h5) h6 j2) (* 128 h1 h2 h3 (* h4 h4) (* h5 h5 h5 h5) h6) (* 48 h1 h2
 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 288 h1 h2 h3 (* h4 h4) (* 
h5 h5 h5) (* h6 h6) (* j2 j2)) (* 528 h1 h2 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) 
j2) (* 288 h1 h2 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6)) (* 24 h1 h2 h3 h4 (* h5 h5
 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 152 h1 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* 
j2 j2)) (* 288 h1 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6) j2) (* 160 h1 h2 h3 h4 (* 
h5 h5 h5 h5) (* h6 h6)) (* 32 h1 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)
) (* 208 h1 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 400 h1 h2 h3 h4 (* 
h5 h5 h5) (* h6 h6 h6) j2) (* 224 h1 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6)) (* 8 h1
 h2 h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 56 h1 h2 h3 (* h5 h5 h5 h5)
 (* h6 h6 h6) (* j2 j2)) (* 112 h1 h2 h3 (* h5 h5 h5 h5) (* h6 h6 h6) j2) (* 64 
h1 h2 h3 (* h5 h5 h5 h5) (* h6 h6 h6)) (* 8 h1 h2 h3 (* h5 h5 h5) (* h6 h6 h6 h6
) (* j2 j2 j2)) (* 56 h1 h2 h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 112 h1
 h2 h3 (* h5 h5 h5) (* h6 h6 h6 h6) j2) (* 64 h1 h2 h3 (* h5 h5 h5) (* h6 h6 h6 
h6)) (* 256 h1 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 
1536 h1 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 3584 h1 (* h3
 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 4096 h1 (* h3 h3 h3 h3) (* h4
 h4 h4) (* h5 h5) (* j2 j2)) (* 2304 h1 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) 
j2) (* 512 h1 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5)) (* 256 h1 (* h3 h3 h3 h3) 
(* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 1536 h1 (* h3 h3 h3 h3) (* h4 h4) 
(* h5 h5 h5) (* j2 j2 j2 j2)) (* 3584 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) 
(* j2 j2 j2)) (* 4096 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 
2304 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) j2) (* 512 h1 (* h3 h3 h3 h3) (* 
h4 h4) (* h5 h5 h5)) (* 768 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 
j2 j2 j2)) (* 5120 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) 
(* 12800 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 15360 h1 (* 
h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 8960 h1 (* h3 h3 h3 h3) (* h4 
h4) (* h5 h5) h6 j2) (* 2048 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6) (* 512 
h1 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 3584 h1 (* h3 h3 h3
 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 9216 h1 (* h3 h3 h3 h3) h4 (* h5 h5 
h5) h6 (* j2 j2 j2)) (* 11264 h1 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2)) 
(* 6656 h1 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 j2) (* 1536 h1 (* h3 h3 h3 h3) h4 
(* h5 h5 h5) h6) (* 768 h1 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2
 j2)) (* 5632 h1 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 
14848 h1 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 18432 h1 (* h3 
h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 11008 h1 (* h3 h3 h3 h3) h4 (* h5
 h5) (* h6 h6) j2) (* 2560 h1 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6)) (* 256 h1 
(* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2048 h1 (* h3 h3 
h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 5632 h1 (* h3 h3 h3 h3) (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2)) (* 7168 h1 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6)
 (* j2 j2)) (* 4352 h1 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) j2) (* 1024 h1 (* 
h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6)) (* 256 h1 (* h3 h3 h3 h3) (* h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2)) (* 2048 h1 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2)) (* 5632 h1 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) 
(* 7168 h1 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 4352 h1 (* h3 h3
 h3 h3) (* h5 h5) (* h6 h6 h6) j2) (* 1024 h1 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6
 h6)) (* 64 h1 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 320 h1
 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 576 h1 (* h3 h3 h3) (* 
h4 h4 h4 h4) (* h5 h5) (* j2 j2)) (* 448 h1 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 
h5) j2) (* 128 h1 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5)) (* 128 h1 (* h3 h3 h3)
 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 640 h1 (* h3 h3 h3) (* h4 h4 h4) 
(* h5 h5 h5) (* j2 j2 j2)) (* 1152 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* 
j2 j2)) (* 896 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) j2) (* 256 h1 (* h3 h3 
h3) (* h4 h4 h4) (* h5 h5 h5)) (* 256 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 
(* j2 j2 j2 j2)) (* 1408 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2))
 (* 2688 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 2176 h1 (* h3 
h3 h3) (* h4 h4 h4) (* h5 h5) h6 j2) (* 640 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 
h5) h6) (* 64 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 320 
h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 576 h1 (* h3 h3 h3) 
(* h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 448 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 
h5 h5) j2) (* 128 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5)) (* 384 h1 (* h3 h3 
h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 2176 h1 (* h3 h3 h3) (* h4 h4)
 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 4224 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6
 (* j2 j2)) (* 3456 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 j2) (* 1024 h1 (* 
h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6) (* 384 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2)) (* 2304 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6)
 (* j2 j2 j2)) (* 4608 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) 
(* 3840 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) j2) (* 1152 h1 (* h3 h3 h3
) (* h4 h4) (* h5 h5) (* h6 h6)) (* 128 h1 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 
(* j2 j2 j2 j2)) (* 768 h1 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 
1536 h1 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 1280 h1 (* h3 h3 h3) h4
 (* h5 h5 h5 h5) h6 j2) (* 384 h1 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6) (* 384 h1 
(* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 2432 h1 (* h3 h3 h3) 
h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 4992 h1 (* h3 h3 h3) h4 (* h5 h5 h5) 
(* h6 h6) (* j2 j2)) (* 4224 h1 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) j2) (* 
1280 h1 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6)) (* 256 h1 (* h3 h3 h3) h4 (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1664 h1 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2)) (* 3456 h1 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2)) 
(* 2944 h1 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) j2) (* 896 h1 (* h3 h3 h3) h4 
(* h5 h5) (* h6 h6 h6)) (* 64 h1 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2
 j2 j2)) (* 448 h1 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 960 
h1 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 832 h1 (* h3 h3 h3) (* 
h5 h5 h5 h5) (* h6 h6) j2) (* 256 h1 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6)) (* 
128 h1 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 896 h1 (* h3 
h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 1920 h1 (* h3 h3 h3) (* h5 h5 
h5) (* h6 h6 h6) (* j2 j2)) (* 1664 h1 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) j2
) (* 512 h1 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6)) (* 64 h1 (* h3 h3 h3) (* h5 
h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 448 h1 (* h3 h3 h3) (* h5 h5) (* h6 h6 
h6 h6) (* j2 j2 j2)) (* 960 h1 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2))
 (* 832 h1 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) j2) (* 256 h1 (* h3 h3 h3) (* 
h5 h5) (* h6 h6 h6 h6)) (* 16 h1 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2
 j2)) (* 64 h1 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2)) (* 80 h1 (* h3 
h3) (* h4 h4 h4 h4) (* h5 h5 h5) j2) (* 32 h1 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5
 h5)) (* 16 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 64 h1 (* 
h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 80 h1 (* h3 h3) (* h4 h4 h4) 
(* h5 h5 h5 h5) j2) (* 32 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5)) (* 64 h1 
(* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 288 h1 (* h3 h3) (* h4 
h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 384 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) 
h6 j2) (* 160 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6) (* 48 h1 (* h3 h3) (* 
h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 224 h1 (* h3 h3) (* h4 h4) (* h5 h5 
h5 h5) h6 (* j2 j2)) (* 304 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 j2) (* 128
 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6) (* 96 h1 (* h3 h3) (* h4 h4) (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2)) (* 480 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 
h6) (* j2 j2)) (* 672 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) j2) (* 288 
h1 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6)) (* 48 h1 (* h3 h3) h4 (* h5 h5 h5
 h5) (* h6 h6) (* j2 j2 j2)) (* 256 h1 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) 
(* j2 j2)) (* 368 h1 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) j2) (* 160 h1 (* h3 
h3) h4 (* h5 h5 h5 h5) (* h6 h6)) (* 64 h1 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6
) (* j2 j2 j2)) (* 352 h1 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 
512 h1 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) j2) (* 224 h1 (* h3 h3) h4 (* h5 
h5 h5) (* h6 h6 h6)) (* 16 h1 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2
)) (* 96 h1 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 144 h1 (* h3 h3
) (* h5 h5 h5 h5) (* h6 h6 h6) j2) (* 64 h1 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 
h6)) (* 16 h1 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 96 h1 (* 
h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 144 h1 (* h3 h3) (* h5 h5 h5) 
(* h6 h6 h6 h6) j2) (* 64 h1 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6)) (* 64 (* h2
 h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 704 (* h2 h2 
h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 3264 (* h2 h2 h2 h2) 
(* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 8256 (* h2 h2 h2 h2) (* h3 h3 
h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 12288 (* h2 h2 h2 h2) (* h3 h3 h3) (* h4 h4
) h5 (* j2 j2 j2)) (* 10752 (* h2 h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2))
 (* 5120 (* h2 h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 j2) (* 1024 (* h2 h2 h2 h2) 
(* h3 h3 h3) (* h4 h4) h5) (* 64 (* h2 h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2
 j2 j2 j2 j2 j2 j2)) (* 704 (* h2 h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 
j2 j2 j2 j2)) (* 3264 (* h2 h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 
j2)) (* 8256 (* h2 h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 12288
 (* h2 h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 10752 (* h2 h2 h2 h2
) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2)) (* 5120 (* h2 h2 h2 h2) (* h3 h3 h3) h4 
(* h5 h5) j2) (* 1024 (* h2 h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5)) (* 128 (* h2 h2
 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1408 (* h2 h2 h2 h2) 
(* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 6528 (* h2 h2 h2 h2) (* h3 h3 h3
) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 16512 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 h6 
(* j2 j2 j2 j2)) (* 24576 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2)) 
(* 21504 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2)) (* 10240 (* h2 h2 h2 
h2) (* h3 h3 h3) h4 h5 h6 j2) (* 2048 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 h6) (* 
64 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 704 
(* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 3264 (* h2 
h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 8256 (* h2 h2 h2 h2) 
(* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 12288 (* h2 h2 h2 h2) (* h3 h3 h3)
 (* h5 h5) h6 (* j2 j2 j2)) (* 10752 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 
(* j2 j2)) (* 5120 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 j2) (* 1024 (* h2 
h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6) (* 64 (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* h6
 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 704 (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 3264 (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 
j2 j2 j2 j2)) (* 8256 (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2))
 (* 12288 (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 10752 (* h2
 h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2)) (* 5120 (* h2 h2 h2 h2) (* h3 h3
 h3) h5 (* h6 h6) j2) (* 1024 (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6)) (* 16 
(* h2 h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 160 (* h2 h2
 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 656 (* h2 h2 h2 h2) (* 
h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 1408 (* h2 h2 h2 h2) (* h3 h3) (* h4 
h4 h4) h5 (* j2 j2 j2)) (* 1664 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 
j2)) (* 1024 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 j2) (* 256 (* h2 h2 h2 h2
) (* h3 h3) (* h4 h4 h4) h5) (* 32 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5)
 (* j2 j2 j2 j2 j2 j2)) (* 320 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* 
j2 j2 j2 j2 j2)) (* 1312 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 
j2 j2)) (* 2816 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 
3328 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 2048 (* h2 h2 
h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) j2) (* 512 (* h2 h2 h2 h2) (* h3 h3) (* h4 
h4) (* h5 h5)) (* 48 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2
 j2)) (* 480 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 
1968 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 4224 (* h2 h2
 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 4992 (* h2 h2 h2 h2) (* h3 h3
) (* h4 h4) h5 h6 (* j2 j2)) (* 3072 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 
j2) (* 768 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6) (* 16 (* h2 h2 h2 h2) (* 
h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 160 (* h2 h2 h2 h2) (* h3 h3) 
h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 656 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5
 h5) (* j2 j2 j2 j2)) (* 1408 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2
 j2)) (* 1664 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2)) (* 1024 (* h2
 h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) j2) (* 256 (* h2 h2 h2 h2) (* h3 h3) h4 (* 
h5 h5 h5)) (* 64 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)
) (* 640 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 2624 
(* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 5632 (* h2 h2 h2 
h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 6656 (* h2 h2 h2 h2) (* h3 h3) h4
 (* h5 h5) h6 (* j2 j2)) (* 4096 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 j2) 
(* 1024 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6) (* 48 (* h2 h2 h2 h2) (* h3 
h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 480 (* h2 h2 h2 h2) (* h3 h3) h4 
h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1968 (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* h6 
h6) (* j2 j2 j2 j2)) (* 4224 (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 
j2)) (* 4992 (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 3072 (* h2 
h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) j2) (* 768 (* h2 h2 h2 h2) (* h3 h3) h4 h5 
(* h6 h6)) (* 16 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)
) (* 160 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 656 
(* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 1408 (* h2 h2 h2 
h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 1664 (* h2 h2 h2 h2) (* h3 h3) 
(* h5 h5 h5) h6 (* j2 j2)) (* 1024 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 j2)
 (* 256 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6) (* 32 (* h2 h2 h2 h2) (* h3 
h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 320 (* h2 h2 h2 h2) (* h3 h3) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1312 (* h2 h2 h2 h2) (* h3 h3) (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2)) (* 2816 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* h6
 h6) (* j2 j2 j2)) (* 3328 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 
j2)) (* 2048 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) j2) (* 512 (* h2 h2 
h2 h2) (* h3 h3) (* h5 h5) (* h6 h6)) (* 16 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 160 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2)) (* 656 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2
 j2)) (* 1408 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 1664 
(* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 1024 (* h2 h2 h2 h2) (* 
h3 h3) h5 (* h6 h6 h6) j2) (* 256 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6)) (* 
4 (* h2 h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 36 (* h2 h2 
h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 128 (* h2 h2 h2 h2) h3 (* 
h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 224 (* h2 h2 h2 h2) h3 (* h4 h4 h4) (* h5 
h5) (* j2 j2)) (* 192 (* h2 h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) j2) (* 64 (* h2 
h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5)) (* 4 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5 
h5) (* j2 j2 j2 j2 j2)) (* 36 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2
 j2 j2)) (* 128 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 224 
(* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 192 (* h2 h2 h2 h2) h3 
(* h4 h4) (* h5 h5 h5) j2) (* 64 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5)) (* 
12 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 108 (* h2 h2
 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 384 (* h2 h2 h2 h2) h3 (* 
h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 672 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) 
h6 (* j2 j2)) (* 576 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 j2) (* 192 (* h2 
h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6) (* 8 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2)) (* 72 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2))
 (* 256 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 448 (* h2 h2 h2 
h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2)) (* 384 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) 
h6 j2) (* 128 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) h6) (* 12 (* h2 h2 h2 h2) h3 h4
 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 108 (* h2 h2 h2 h2) h3 h4 (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2)) (* 384 (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* 
j2 j2 j2)) (* 672 (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 576 
(* h2 h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) j2) (* 192 (* h2 h2 h2 h2) h3 h4 (* h5
 h5) (* h6 h6)) (* 4 (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2
)) (* 36 (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 128 (* h2
 h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 224 (* h2 h2 h2 h2) h3 (* 
h5 h5 h5) (* h6 h6) (* j2 j2)) (* 192 (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) 
j2) (* 64 (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6)) (* 4 (* h2 h2 h2 h2) h3 (* 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 36 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6
 h6 h6) (* j2 j2 j2 j2)) (* 128 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 
j2 j2)) (* 224 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 192 (* h2
 h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) j2) (* 64 (* h2 h2 h2 h2) h3 (* h5 h5) (* 
h6 h6 h6)) (* 256 (* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2
 j2)) (* 2560 (* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) 
(* 10752 (* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 24576 
(* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 33024 (* h2 h2 h2)
 (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 26112 (* h2 h2 h2) (* h3 h3 h3 h3
) (* h4 h4) h5 (* j2 j2)) (* 11264 (* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 j2)
 (* 2048 (* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5) (* 256 (* h2 h2 h2) (* h3 h3
 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 2560 (* h2 h2 h2) (* h3 h3 h3 
h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 10752 (* h2 h2 h2) (* h3 h3 h3 h3) h4
 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 24576 (* h2 h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5
) (* j2 j2 j2 j2)) (* 33024 (* h2 h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 
j2)) (* 26112 (* h2 h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2)) (* 11264 (* 
h2 h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) j2) (* 2048 (* h2 h2 h2) (* h3 h3 h3 h3) 
h4 (* h5 h5)) (* 512 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 
j2)) (* 5120 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 
21504 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 49152 (* h2 
h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 66048 (* h2 h2 h2) (* h3 h3 
h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 52224 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* 
j2 j2)) (* 22528 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 h6 j2) (* 4096 (* h2 h2 h2) 
(* h3 h3 h3 h3) h4 h5 h6) (* 256 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2
 j2 j2 j2 j2 j2 j2)) (* 2560 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 
j2 j2 j2 j2)) (* 10752 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 
j2)) (* 24576 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 
33024 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 26112 (* h2 h2 
h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2)) (* 11264 (* h2 h2 h2) (* h3 h3 h3 h3
) (* h5 h5) h6 j2) (* 2048 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6) (* 256 (* 
h2 h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2560 (* h2 
h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 10752 (* h2 h2 h2)
 (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 24576 (* h2 h2 h2) (* h3 h3
 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 33024 (* h2 h2 h2) (* h3 h3 h3 h3) h5 
(* h6 h6) (* j2 j2 j2)) (* 26112 (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2
 j2)) (* 11264 (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) j2) (* 2048 (* h2 h2 h2
) (* h3 h3 h3 h3) h5 (* h6 h6)) (* 128 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5
 (* j2 j2 j2 j2 j2 j2)) (* 1152 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 
j2 j2 j2 j2)) (* 4224 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2))
 (* 8064 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 8448 (* h2 
h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2)) (* 4608 (* h2 h2 h2) (* h3 h3 h3)
 (* h4 h4 h4) h5 j2) (* 1024 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5) (* 256 
(* h2 h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2304 (* 
h2 h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 8448 (* h2 h2 
h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 16128 (* h2 h2 h2) (* 
h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 16896 (* h2 h2 h2) (* h3 h3 h3) 
(* h4 h4) (* h5 h5) (* j2 j2)) (* 9216 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) (* h5
 h5) j2) (* 2048 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5)) (* 384 (* h2 h2 
h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 3456 (* h2 h2 h2) (* 
h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 12672 (* h2 h2 h2) (* h3 h3 h3)
 (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 24192 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) 
h5 h6 (* j2 j2 j2)) (* 25344 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2)
) (* 13824 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 j2) (* 3072 (* h2 h2 h2) 
(* h3 h3 h3) (* h4 h4) h5 h6) (* 128 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2)) (* 1152 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 
j2 j2 j2 j2)) (* 4224 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2))
 (* 8064 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2)) (* 8448 (* h2 
h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2)) (* 4608 (* h2 h2 h2) (* h3 h3 h3)
 h4 (* h5 h5 h5) j2) (* 1024 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5)) (* 512 
(* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 4608 (* h2 
h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 16896 (* h2 h2 h2) 
(* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 32256 (* h2 h2 h2) (* h3 h3 h3)
 h4 (* h5 h5) h6 (* j2 j2 j2)) (* 33792 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) 
h6 (* j2 j2)) (* 18432 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 j2) (* 4096 (* 
h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6) (* 384 (* h2 h2 h2) (* h3 h3 h3) h4 h5 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3456 (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* h6 
h6) (* j2 j2 j2 j2 j2)) (* 12672 (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2
 j2 j2 j2)) (* 24192 (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 
25344 (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 13824 (* h2 h2 h2)
 (* h3 h3 h3) h4 h5 (* h6 h6) j2) (* 3072 (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* h6 
h6)) (* 128 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
1152 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 4224 (* h2
 h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 8064 (* h2 h2 h2) (* h3
 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 8448 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5
 h5) h6 (* j2 j2)) (* 4608 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 j2) (* 1024
 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6) (* 256 (* h2 h2 h2) (* h3 h3 h3) (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2304 (* h2 h2 h2) (* h3 h3 h3) (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 8448 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2)) (* 16128 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6
) (* j2 j2 j2)) (* 16896 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)
) (* 9216 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) j2) (* 2048 (* h2 h2 h2)
 (* h3 h3 h3) (* h5 h5) (* h6 h6)) (* 128 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 1152 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* 
j2 j2 j2 j2 j2)) (* 4224 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 
j2)) (* 8064 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 8448 (* 
h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 4608 (* h2 h2 h2) (* h3 h3 
h3) h5 (* h6 h6 h6) j2) (* 1024 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6)) (* 16
 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 128 (* h2 h2 
h2) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 400 (* h2 h2 h2) (* h3 h3) 
(* h4 h4 h4 h4) h5 (* j2 j2 j2)) (* 608 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4 h4) 
h5 (* j2 j2)) (* 448 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 j2) (* 128 (* h2 
h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5) (* 64 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) 
(* h5 h5) (* j2 j2 j2 j2 j2)) (* 512 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 
h5) (* j2 j2 j2 j2)) (* 1600 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2
 j2 j2)) (* 2432 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 
1792 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) j2) (* 512 (* h2 h2 h2) (* h3
 h3) (* h4 h4 h4) (* h5 h5)) (* 64 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* 
j2 j2 j2 j2 j2)) (* 512 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2
)) (* 1600 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 2432 (* h2
 h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2)) (* 1792 (* h2 h2 h2) (* h3 h3) 
(* h4 h4 h4) h5 h6 j2) (* 512 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6) (* 64 
(* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 512 (* h2 
h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 1600 (* h2 h2 h2) 
(* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 2432 (* h2 h2 h2) (* h3 h3) 
(* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 1792 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5
 h5 h5) j2) (* 512 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5)) (* 192 (* h2 
h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 1536 (* h2 h2 h2)
 (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 4800 (* h2 h2 h2) (* h3 h3
) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 7296 (* h2 h2 h2) (* h3 h3) (* h4 h4) 
(* h5 h5) h6 (* j2 j2)) (* 5376 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 j2
) (* 1536 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6) (* 96 (* h2 h2 h2) (* 
h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 768 (* h2 h2 h2) (* h3 h3) 
(* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 2400 (* h2 h2 h2) (* h3 h3) (* h4 h4)
 h5 (* h6 h6) (* j2 j2 j2)) (* 3648 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6
) (* j2 j2)) (* 2688 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6) j2) (* 768 
(* h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6)) (* 16 (* h2 h2 h2) (* h3 h3) h4 
(* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 128 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5
 h5) (* j2 j2 j2 j2)) (* 400 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 
j2)) (* 608 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2)) (* 448 (* h2 h2
 h2) (* h3 h3) h4 (* h5 h5 h5 h5) j2) (* 128 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 
h5 h5)) (* 128 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
1024 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 3200 (* h2 h2
 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 4864 (* h2 h2 h2) (* h3 h3) 
h4 (* h5 h5 h5) h6 (* j2 j2)) (* 3584 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 
j2) (* 1024 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6) (* 192 (* h2 h2 h2) (* h3
 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1536 (* h2 h2 h2) (* h3 h3) 
h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 4800 (* h2 h2 h2) (* h3 h3) h4 (* h5 
h5) (* h6 h6) (* j2 j2 j2)) (* 7296 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6
) (* j2 j2)) (* 5376 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) j2) (* 1536 
(* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6)) (* 64 (* h2 h2 h2) (* h3 h3) h4 
h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 512 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6
 h6) (* j2 j2 j2 j2)) (* 1600 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2
 j2)) (* 2432 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2)) (* 1792 (* h2
 h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) j2) (* 512 (* h2 h2 h2) (* h3 h3) h4 h5 (* 
h6 h6 h6)) (* 16 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) 
(* 128 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 400 (* h2 
h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 608 (* h2 h2 h2) (* h3 h3) 
(* h5 h5 h5 h5) h6 (* j2 j2)) (* 448 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 
j2) (* 128 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6) (* 64 (* h2 h2 h2) (* h3 
h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 512 (* h2 h2 h2) (* h3 h3) (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 1600 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5)
 (* h6 h6) (* j2 j2 j2)) (* 2432 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) 
(* j2 j2)) (* 1792 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) j2) (* 512 (* 
h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6)) (* 64 (* h2 h2 h2) (* h3 h3) (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 512 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2)) (* 1600 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6)
 (* j2 j2 j2)) (* 2432 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2)) 
(* 1792 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) j2) (* 512 (* h2 h2 h2) 
(* h3 h3) (* h5 h5) (* h6 h6 h6)) (* 16 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6
) (* j2 j2 j2 j2 j2)) (* 128 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 
j2 j2)) (* 400 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 608 
(* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2)) (* 448 (* h2 h2 h2) (* h3 
h3) h5 (* h6 h6 h6 h6) j2) (* 128 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6)) (* 
4 (* h2 h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 28 (* h2 h2 h2) 
h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 72 (* h2 h2 h2) h3 (* h4 h4 h4 h4)
 (* h5 h5) (* j2 j2)) (* 80 (* h2 h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) j2) (* 32 
(* h2 h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5)) (* 8 (* h2 h2 h2) h3 (* h4 h4 h4) (* 
h5 h5 h5) (* j2 j2 j2 j2)) (* 56 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2
 j2 j2)) (* 144 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2)) (* 160 (* 
h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) j2) (* 64 (* h2 h2 h2) h3 (* h4 h4 h4) 
(* h5 h5 h5)) (* 16 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) 
(* 112 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 288 (* h2 h2 
h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 320 (* h2 h2 h2) h3 (* h4 h4 h4) 
(* h5 h5) h6 j2) (* 128 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6) (* 4 (* h2 h2
 h2) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 28 (* h2 h2 h2) h3 (* h4 
h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 72 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5
) (* j2 j2)) (* 80 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) j2) (* 32 (* h2 h2 
h2) h3 (* h4 h4) (* h5 h5 h5 h5)) (* 24 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) 
h6 (* j2 j2 j2 j2)) (* 168 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2
)) (* 432 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 480 (* h2 h2 
h2) h3 (* h4 h4) (* h5 h5 h5) h6 j2) (* 192 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 
h5) h6) (* 24 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 
168 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 432 (* h2 h2 
h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 480 (* h2 h2 h2) h3 (* h4 h4)
 (* h5 h5) (* h6 h6) j2) (* 192 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6)) 
(* 8 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 56 (* h2 h2 h2) 
h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 144 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5)
 h6 (* j2 j2)) (* 160 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) h6 j2) (* 64 (* h2 h2 
h2) h3 h4 (* h5 h5 h5 h5) h6) (* 24 (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2)) (* 168 (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) 
(* 432 (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 480 (* h2 h2 h2) 
h3 h4 (* h5 h5 h5) (* h6 h6) j2) (* 192 (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6
)) (* 16 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 112 (* h2
 h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 288 (* h2 h2 h2) h3 h4 (* 
h5 h5) (* h6 h6 h6) (* j2 j2)) (* 320 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) 
j2) (* 128 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6)) (* 4 (* h2 h2 h2) h3 (* h5
 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 28 (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* 
h6 h6) (* j2 j2 j2)) (* 72 (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) 
(* 80 (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) j2) (* 32 (* h2 h2 h2) h3 (* h5 
h5 h5 h5) (* h6 h6)) (* 8 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2)) (* 56 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 144 (* h2 
h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 160 (* h2 h2 h2) h3 (* h5 h5 
h5) (* h6 h6 h6) j2) (* 64 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6)) (* 4 (* h2
 h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 28 (* h2 h2 h2) h3 (* 
h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 72 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6
 h6) (* j2 j2)) (* 80 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) j2) (* 32 (* h2 
h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6)) (* 256 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4 
h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 2048 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4 h4) h5 
(* j2 j2 j2 j2 j2)) (* 6656 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 
j2 j2)) (* 11264 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 
10496 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2)) (* 5120 (* h2 h2) (* 
h3 h3 h3 h3) (* h4 h4 h4) h5 j2) (* 1024 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4 h4) 
h5) (* 512 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) 
(* 4096 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 
13312 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 22528 
(* h2 h2) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 20992 (* h2 h2) 
(* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 10240 (* h2 h2) (* h3 h3 h3 h3
) (* h4 h4) (* h5 h5) j2) (* 2048 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5))
 (* 768 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 6144
 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 19968 (* h2 h2
) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 33792 (* h2 h2) (* h3 h3 
h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 31488 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4
) h5 h6 (* j2 j2)) (* 15360 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 h6 j2) (* 
3072 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 h6) (* 256 (* h2 h2) (* h3 h3 h3 h3)
 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2048 (* h2 h2) (* h3 h3 h3 h3) h4 (* 
h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 6656 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5 h5) 
(* j2 j2 j2 j2)) (* 11264 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2)
) (* 10496 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2)) (* 5120 (* h2 h2
) (* h3 h3 h3 h3) h4 (* h5 h5 h5) j2) (* 1024 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5
 h5 h5)) (* 1024 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)
) (* 8192 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 26624
 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 45056 (* h2 h2) 
(* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 41984 (* h2 h2) (* h3 h3 h3 h3)
 h4 (* h5 h5) h6 (* j2 j2)) (* 20480 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) h6 
j2) (* 4096 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) h6) (* 768 (* h2 h2) (* h3 h3
 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6144 (* h2 h2) (* h3 h3 h3 h3)
 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 19968 (* h2 h2) (* h3 h3 h3 h3) h4 h5 
(* h6 h6) (* j2 j2 j2 j2)) (* 33792 (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* h6 h6) 
(* j2 j2 j2)) (* 31488 (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 
15360 (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* h6 h6) j2) (* 3072 (* h2 h2) (* h3 h3 
h3 h3) h4 h5 (* h6 h6)) (* 256 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2)) (* 2048 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2)) (* 6656 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 
11264 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 10496 (* h2 h2)
 (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2)) (* 5120 (* h2 h2) (* h3 h3 h3 h3) 
(* h5 h5 h5) h6 j2) (* 1024 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) h6) (* 512 
(* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4096 (* 
h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 13312 (* h2 h2
) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 22528 (* h2 h2) (* h3 
h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 20992 (* h2 h2) (* h3 h3 h3 h3) 
(* h5 h5) (* h6 h6) (* j2 j2)) (* 10240 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* 
h6 h6) j2) (* 2048 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6)) (* 256 (* h2 
h2) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2048 (* h2 h2) (* 
h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 6656 (* h2 h2) (* h3 h3 h3 
h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 11264 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6
 h6 h6) (* j2 j2 j2)) (* 10496 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 
j2)) (* 5120 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6 h6) j2) (* 1024 (* h2 h2) (* 
h3 h3 h3 h3) h5 (* h6 h6 h6)) (* 64 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4 h4) h5 
(* j2 j2 j2 j2 j2)) (* 448 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2
 j2)) (* 1216 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2)) (* 1600 
(* h2 h2) (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2)) (* 1024 (* h2 h2) (* h3 h3 
h3) (* h4 h4 h4 h4) h5 j2) (* 256 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4 h4) h5) (* 
256 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 1792 
(* h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 4864 (* h2 h2)
 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 6400 (* h2 h2) (* h3 h3 h3
) (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 4096 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) 
(* h5 h5) j2) (* 1024 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5)) (* 256 (* 
h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 1792 (* h2 h2) (* 
h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 4864 (* h2 h2) (* h3 h3 h3) (* 
h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 6400 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 h6 
(* j2 j2)) (* 4096 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 h6 j2) (* 1024 (* h2 
h2) (* h3 h3 h3) (* h4 h4 h4) h5 h6) (* 256 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* 
h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 1792 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5 
h5) (* j2 j2 j2 j2)) (* 4864 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2
 j2 j2)) (* 6400 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 
4096 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) j2) (* 1024 (* h2 h2) (* h3 
h3 h3) (* h4 h4) (* h5 h5 h5)) (* 768 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5)
 h6 (* j2 j2 j2 j2 j2)) (* 5376 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 
(* j2 j2 j2 j2)) (* 14592 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2
 j2)) (* 19200 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 12288
 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 j2) (* 3072 (* h2 h2) (* h3 h3 h3
) (* h4 h4) (* h5 h5) h6) (* 384 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* 2688 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 
j2 j2 j2)) (* 7296 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2)) 
(* 9600 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 6144 (* h2 
h2) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) j2) (* 1536 (* h2 h2) (* h3 h3 h3) (* h4
 h4) h5 (* h6 h6)) (* 64 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 
j2 j2)) (* 448 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 
1216 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2)) (* 1600 (* h2 h2) 
(* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2)) (* 1024 (* h2 h2) (* h3 h3 h3) h4 (* 
h5 h5 h5 h5) j2) (* 256 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5 h5)) (* 512 (* h2 
h2) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 3584 (* h2 h2) (* h3 
h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 9728 (* h2 h2) (* h3 h3 h3) h4 (* 
h5 h5 h5) h6 (* j2 j2 j2)) (* 12800 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) h6 
(* j2 j2)) (* 8192 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) h6 j2) (* 2048 (* h2 
h2) (* h3 h3 h3) h4 (* h5 h5 h5) h6) (* 768 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 5376 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* h6 
h6) (* j2 j2 j2 j2)) (* 14592 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* 
j2 j2 j2)) (* 19200 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 
12288 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) j2) (* 3072 (* h2 h2) (* h3 
h3 h3) h4 (* h5 h5) (* h6 h6)) (* 256 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2)) (* 1792 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 
j2 j2)) (* 4864 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 6400 
(* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2)) (* 4096 (* h2 h2) (* h3 h3 
h3) h4 h5 (* h6 h6 h6) j2) (* 1024 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6 h6)) 
(* 64 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 448 (* h2
 h2) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 1216 (* h2 h2) (* h3 h3
 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 1600 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5
 h5) h6 (* j2 j2)) (* 1024 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) h6 j2) (* 256 
(* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) h6) (* 256 (* h2 h2) (* h3 h3 h3) (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1792 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5)
 (* h6 h6) (* j2 j2 j2 j2)) (* 4864 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6
) (* j2 j2 j2)) (* 6400 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2))
 (* 4096 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) j2) (* 1024 (* h2 h2) (* 
h3 h3 h3) (* h5 h5 h5) (* h6 h6)) (* 256 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2)) (* 1792 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6)
 (* j2 j2 j2 j2)) (* 4864 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2
 j2)) (* 6400 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 4096 
(* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) j2) (* 1024 (* h2 h2) (* h3 h3 h3)
 (* h5 h5) (* h6 h6 h6)) (* 64 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 
j2 j2 j2 j2)) (* 448 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) 
(* 1216 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 1600 (* h2 h2
) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2)) (* 1024 (* h2 h2) (* h3 h3 h3) h5 
(* h6 h6 h6 h6) j2) (* 256 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6 h6)) (* 32 (* 
h2 h2) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 192 (* h2 h2) (* 
h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 416 (* h2 h2) (* h3 h3) (* h4 
h4 h4 h4) (* h5 h5) (* j2 j2)) (* 384 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) (* h5 
h5) j2) (* 128 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5)) (* 64 (* h2 h2) 
(* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 384 (* h2 h2) (* h3 h3) 
(* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 832 (* h2 h2) (* h3 h3) (* h4 h4 h4) 
(* h5 h5 h5) (* j2 j2)) (* 768 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) j2)
 (* 256 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5)) (* 128 (* h2 h2) (* h3 h3
) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 768 (* h2 h2) (* h3 h3) (* h4 h4
 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 1664 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 
h5) h6 (* j2 j2)) (* 1536 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 j2) (* 
512 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6) (* 32 (* h2 h2) (* h3 h3) (* 
h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 192 (* h2 h2) (* h3 h3) (* h4 h4) (* 
h5 h5 h5 h5) (* j2 j2 j2)) (* 416 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) 
(* j2 j2)) (* 384 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) j2) (* 128 (* h2
 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5)) (* 192 (* h2 h2) (* h3 h3) (* h4 h4) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 1152 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 
h5) h6 (* j2 j2 j2)) (* 2496 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2
 j2)) (* 2304 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 j2) (* 768 (* h2 h2)
 (* h3 h3) (* h4 h4) (* h5 h5 h5) h6) (* 192 (* h2 h2) (* h3 h3) (* h4 h4) (* h5
 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 1152 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) 
(* h6 h6) (* j2 j2 j2)) (* 2496 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6
) (* j2 j2)) (* 2304 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) j2) (* 
768 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6)) (* 64 (* h2 h2) (* h3 h3)
 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 384 (* h2 h2) (* h3 h3) h4 (* h5 h5 
h5 h5) h6 (* j2 j2 j2)) (* 832 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 
j2)) (* 768 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) h6 j2) (* 256 (* h2 h2) (* h3
 h3) h4 (* h5 h5 h5 h5) h6) (* 192 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6)
 (* j2 j2 j2 j2)) (* 1152 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2
 j2)) (* 2496 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 2304 
(* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) j2) (* 768 (* h2 h2) (* h3 h3) h4 
(* h5 h5 h5) (* h6 h6)) (* 128 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2)) (* 768 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2))
 (* 1664 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 1536 (* h2 
h2) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) j2) (* 512 (* h2 h2) (* h3 h3) h4 (* h5 
h5) (* h6 h6 h6)) (* 32 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2)) (* 192 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 
416 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 384 (* h2 h2) 
(* h3 h3) (* h5 h5 h5 h5) (* h6 h6) j2) (* 128 (* h2 h2) (* h3 h3) (* h5 h5 h5 
h5) (* h6 h6)) (* 64 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2)) (* 384 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 832 
(* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 768 (* h2 h2) (* h3 
h3) (* h5 h5 h5) (* h6 h6 h6) j2) (* 256 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 
h6 h6)) (* 32 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 
192 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 416 (* h2 h2)
 (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 384 (* h2 h2) (* h3 h3) (* h5
 h5) (* h6 h6 h6 h6) j2) (* 128 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6)) 
(* 4 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 20 (* h2 h2) h3 
(* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2)) (* 32 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5
 h5 h5) j2) (* 16 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5 h5)) (* 4 (* h2 h2) h3 
(* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 20 (* h2 h2) h3 (* h4 h4 h4) (* h5
 h5 h5 h5) (* j2 j2)) (* 32 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5 h5) j2) (* 16 
(* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5 h5)) (* 16 (* h2 h2) h3 (* h4 h4 h4) (* h5
 h5 h5) h6 (* j2 j2 j2)) (* 80 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 
j2)) (* 128 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) h6 j2) (* 64 (* h2 h2) h3 (* 
h4 h4 h4) (* h5 h5 h5) h6) (* 12 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2
 j2 j2)) (* 60 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 96 (* h2 
h2) h3 (* h4 h4) (* h5 h5 h5 h5) h6 j2) (* 48 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5
 h5) h6) (* 24 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 
120 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 192 (* h2 h2) h3
 (* h4 h4) (* h5 h5 h5) (* h6 h6) j2) (* 96 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) 
(* h6 h6)) (* 12 (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 60 
(* h2 h2) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 96 (* h2 h2) h3 h4 (* h5
 h5 h5 h5) (* h6 h6) j2) (* 48 (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* h6 h6)) (* 16 
(* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 80 (* h2 h2) h3 h4 
(* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 128 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 
h6 h6) j2) (* 64 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6 h6)) (* 4 (* h2 h2) h3 
(* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 20 (* h2 h2) h3 (* h5 h5 h5 h5) 
(* h6 h6 h6) (* j2 j2)) (* 32 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6 h6) j2) (* 
16 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6 h6)) (* 4 (* h2 h2) h3 (* h5 h5 h5) (* 
h6 h6 h6 h6) (* j2 j2 j2)) (* 20 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2
 j2)) (* 32 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6 h6) j2) (* 16 (* h2 h2) h3 (* 
h5 h5 h5) (* h6 h6 h6 h6)) (* 256 h2 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* 
j2 j2 j2 j2 j2)) (* 1536 h2 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 
j2)) (* 3584 h2 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 4096 h2 
(* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 2304 h2 (* h3 h3 h3 h3) (* 
h4 h4 h4) (* h5 h5) j2) (* 512 h2 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5)) (* 256
 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 1536 h2 (* h3 
h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 3584 h2 (* h3 h3 h3 h3) (* 
h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 4096 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 
h5) (* j2 j2)) (* 2304 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) j2) (* 512 h2 
(* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5)) (* 768 h2 (* h3 h3 h3 h3) (* h4 h4) (* 
h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 4608 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 
(* j2 j2 j2 j2)) (* 10752 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)
) (* 12288 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 6912 h2 (* h3
 h3 h3 h3) (* h4 h4) (* h5 h5) h6 j2) (* 1536 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5
 h5) h6) (* 512 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
3072 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 7168 h2 (* h3 h3 
h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 8192 h2 (* h3 h3 h3 h3) h4 (* h5 h5 
h5) h6 (* j2 j2)) (* 4608 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 j2) (* 1024 h2 
(* h3 h3 h3 h3) h4 (* h5 h5 h5) h6) (* 768 h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6
 h6) (* j2 j2 j2 j2 j2)) (* 4608 h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2
 j2 j2 j2)) (* 10752 h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 
12288 h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 6912 h2 (* h3 h3 
h3 h3) h4 (* h5 h5) (* h6 h6) j2) (* 1536 h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 
h6)) (* 256 h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
1536 h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 3584 h2 (* h3
 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 4096 h2 (* h3 h3 h3 h3) (* h5
 h5 h5) (* h6 h6) (* j2 j2)) (* 2304 h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) 
j2) (* 512 h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6)) (* 256 h2 (* h3 h3 h3 h3) 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1536 h2 (* h3 h3 h3 h3) (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2)) (* 3584 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2)) (* 4096 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 
2304 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) j2) (* 512 h2 (* h3 h3 h3 h3) (* 
h5 h5) (* h6 h6 h6)) (* 64 h2 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2
 j2)) (* 320 h2 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 576 h2 
(* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2)) (* 448 h2 (* h3 h3 h3) (* h4 
h4 h4 h4) (* h5 h5) j2) (* 128 h2 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5)) (* 128
 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 640 h2 (* h3 h3 
h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 1152 h2 (* h3 h3 h3) (* h4 h4 h4)
 (* h5 h5 h5) (* j2 j2)) (* 896 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) j2) 
(* 256 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5)) (* 256 h2 (* h3 h3 h3) (* h4 
h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 1280 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 
h5) h6 (* j2 j2 j2)) (* 2304 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)
) (* 1792 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 j2) (* 512 h2 (* h3 h3 h3) 
(* h4 h4 h4) (* h5 h5) h6) (* 64 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2
 j2 j2 j2)) (* 320 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 
576 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 448 h2 (* h3 h3 h3) 
(* h4 h4) (* h5 h5 h5 h5) j2) (* 128 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5)) 
(* 384 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 1920 h2 (* 
h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 3456 h2 (* h3 h3 h3) (* h4 
h4) (* h5 h5 h5) h6 (* j2 j2)) (* 2688 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6
 j2) (* 768 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6) (* 384 h2 (* h3 h3 h3) 
(* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 1920 h2 (* h3 h3 h3) (* h4 h4)
 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 3456 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) 
(* h6 h6) (* j2 j2)) (* 2688 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) j2) 
(* 768 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6)) (* 128 h2 (* h3 h3 h3) h4 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 640 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6
 (* j2 j2 j2)) (* 1152 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 896 
h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 j2) (* 256 h2 (* h3 h3 h3) h4 (* h5 h5 h5 
h5) h6) (* 384 h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 
1920 h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 3456 h2 (* h3 h3
 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 2688 h2 (* h3 h3 h3) h4 (* h5 h5 h5
) (* h6 h6) j2) (* 768 h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6)) (* 256 h2 (* 
h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1280 h2 (* h3 h3 h3) h4 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 2304 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 
h6 h6) (* j2 j2)) (* 1792 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) j2) (* 512 
h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6)) (* 64 h2 (* h3 h3 h3) (* h5 h5 h5 h5)
 (* h6 h6) (* j2 j2 j2 j2)) (* 320 h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* 
j2 j2 j2)) (* 576 h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 448 h2
 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) j2) (* 128 h2 (* h3 h3 h3) (* h5 h5 h5 
h5) (* h6 h6)) (* 128 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2))
 (* 640 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 1152 h2 (* h3
 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 896 h2 (* h3 h3 h3) (* h5 h5 h5)
 (* h6 h6 h6) j2) (* 256 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6)) (* 64 h2 (* 
h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 320 h2 (* h3 h3 h3) (* 
h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 576 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 
h6 h6) (* j2 j2)) (* 448 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) j2) (* 128 h2
 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6)) (* 16 h2 (* h3 h3) (* h4 h4 h4 h4) (* 
h5 h5 h5) (* j2 j2 j2)) (* 64 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2
)) (* 80 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) j2) (* 32 h2 (* h3 h3) (* h4 
h4 h4 h4) (* h5 h5 h5)) (* 16 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2
 j2)) (* 64 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 80 h2 (* h3 
h3) (* h4 h4 h4) (* h5 h5 h5 h5) j2) (* 32 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5
 h5)) (* 64 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 256 h2 
(* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 320 h2 (* h3 h3) (* h4 h4 
h4) (* h5 h5 h5) h6 j2) (* 128 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6) (* 48 
h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 192 h2 (* h3 h3) (* 
h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 240 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 
h5) h6 j2) (* 96 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6) (* 96 h2 (* h3 h3) 
(* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 384 h2 (* h3 h3) (* h4 h4) (* 
h5 h5 h5) (* h6 h6) (* j2 j2)) (* 480 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 
h6) j2) (* 192 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6)) (* 48 h2 (* h3 h3)
 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 192 h2 (* h3 h3) h4 (* h5 h5 h5 
h5) (* h6 h6) (* j2 j2)) (* 240 h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) j2) 
(* 96 h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6)) (* 64 h2 (* h3 h3) h4 (* h5 h5 
h5) (* h6 h6 h6) (* j2 j2 j2)) (* 256 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) 
(* j2 j2)) (* 320 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) j2) (* 128 h2 (* h3 
h3) h4 (* h5 h5 h5) (* h6 h6 h6)) (* 16 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6
) (* j2 j2 j2)) (* 64 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 80
 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) j2) (* 32 h2 (* h3 h3) (* h5 h5 h5 h5
) (* h6 h6 h6)) (* 16 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) 
(* 64 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 80 h2 (* h3 h3) 
(* h5 h5 h5) (* h6 h6 h6 h6) j2) (* 32 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6)
)) 0)))
(check-sat)
(exit)

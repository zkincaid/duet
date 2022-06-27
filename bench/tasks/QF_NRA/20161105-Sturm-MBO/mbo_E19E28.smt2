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
(set-info :instance |E19E28|)
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
(+ (* 512 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2)) (* 896 (* h1 
h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* j2 j2)) (* 192 (* h1 h1 h1 h1) (* h2 h2 
h2) (* h3 h3) h5 j2) (* 512 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h6 (* j2 j2 
j2)) (* 640 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h6 (* j2 j2)) (* 128 (* h1 h1
 h1 h1) (* h2 h2 h2) (* h3 h3) h6 j2) (* 128 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* 
h5 h5) (* j2 j2 j2)) (* 320 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* j2 j2))
 (* 192 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) j2) (* 256 (* h1 h1 h1 h1) (* 
h2 h2 h2) h3 h5 h6 (* j2 j2 j2)) (* 544 (* h1 h1 h1 h1) (* h2 h2 h2) h3 h5 h6 
(* j2 j2)) (* 320 (* h1 h1 h1 h1) (* h2 h2 h2) h3 h5 h6 j2) (* 32 (* h1 h1 h1 h1
) (* h2 h2 h2) h3 h5 h6) (* 128 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6) (* j2 
j2 j2)) (* 256 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6) (* j2 j2)) (* 128 (* h1
 h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6) j2) (* 32 (* h1 h1 h1 h1) (* h2 h2 h2) (* 
h5 h5) h6 (* j2 j2 j2)) (* 96 (* h1 h1 h1 h1) (* h2 h2 h2) (* h5 h5) h6 (* j2 j2
)) (* 96 (* h1 h1 h1 h1) (* h2 h2 h2) (* h5 h5) h6 j2) (* 32 (* h1 h1 h1 h1) (* 
h2 h2 h2) (* h5 h5) h6) (* 32 (* h1 h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6) (* j2 j2
 j2)) (* 96 (* h1 h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6) (* j2 j2)) (* 96 (* h1 h1 
h1 h1) (* h2 h2 h2) h5 (* h6 h6) j2) (* 32 (* h1 h1 h1 h1) (* h2 h2 h2) h5 (* h6
 h6)) (* 4096 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2)) (* 8192
 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2)) (* 3328 (* h1 h1 h1 h1)
 (* h2 h2) (* h3 h3 h3) h5 (* j2 j2)) (* 384 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 
h3) h5 j2) (* 4096 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2 j2)) 
(* 6144 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2)) (* 2304 (* h1 h1
 h1 h1) (* h2 h2) (* h3 h3 h3) h6 (* j2 j2)) (* 256 (* h1 h1 h1 h1) (* h2 h2) 
(* h3 h3 h3) h6 j2) (* 1536 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* j2 j2 
j2)) (* 2688 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* j2 j2)) (* 576 (* h1 
h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 j2) (* 1536 (* h1 h1 h1 h1) (* h2 h2) (* h3 
h3) h4 h6 (* j2 j2 j2)) (* 1408 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h6 (* j2 
j2)) (* 256 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h6 j2) (* 2048 (* h1 h1 h1 h1
) (* h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 5632 (* h1 h1 h1 h1) (* h2 
h2) (* h3 h3) (* h5 h5) (* j2 j2 j2)) (* 4352 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3
) (* h5 h5) (* j2 j2)) (* 768 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) j2) 
(* 4096 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 9984 (* h1
 h1 h1 h1) (* h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2)) (* 7616 (* h1 h1 h1 h1) (* h2
 h2) (* h3 h3) h5 h6 (* j2 j2)) (* 1920 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h5 
h6 j2) (* 64 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h5 h6) (* 2048 (* h1 h1 h1 h1) 
(* h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 4608 (* h1 h1 h1 h1) (* h2 h2)
 (* h3 h3) (* h6 h6) (* j2 j2 j2)) (* 3328 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) 
(* h6 h6) (* j2 j2)) (* 768 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6) j2) 
(* 384 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2)) (* 960 (* h1 h1 
h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* j2 j2)) (* 576 (* h1 h1 h1 h1) (* h2 h2) h3 
h4 (* h5 h5) j2) (* 768 (* h1 h1 h1 h1) (* h2 h2) h3 h4 h5 h6 (* j2 j2 j2)) (* 
1376 (* h1 h1 h1 h1) (* h2 h2) h3 h4 h5 h6 (* j2 j2)) (* 672 (* h1 h1 h1 h1) (* 
h2 h2) h3 h4 h5 h6 j2) (* 64 (* h1 h1 h1 h1) (* h2 h2) h3 h4 h5 h6) (* 384 (* h1
 h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2)) (* 512 (* h1 h1 h1 h1) (* h2 
h2) h3 h4 (* h6 h6) (* j2 j2)) (* 128 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6) 
j2) (* 256 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 896 (* 
h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2)) (* 1024 (* h1 h1 h1 h1) (* 
h2 h2) h3 (* h5 h5 h5) (* j2 j2)) (* 384 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5 
h5) j2) (* 1024 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 
3328 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2)) (* 3712 (* h1 h1 h1
 h1) (* h2 h2) h3 (* h5 h5) h6 (* j2 j2)) (* 1536 (* h1 h1 h1 h1) (* h2 h2) h3 
(* h5 h5) h6 j2) (* 128 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5) h6) (* 1024 (* h1
 h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 3200 (* h1 h1 h1 h1) 
(* h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2)) (* 3520 (* h1 h1 h1 h1) (* h2 h2) h3 h5 
(* h6 h6) (* j2 j2)) (* 1536 (* h1 h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6) j2) (* 
192 (* h1 h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6)) (* 256 (* h1 h1 h1 h1) (* h2 h2) 
h3 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 768 (* h1 h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6
) (* j2 j2 j2)) (* 768 (* h1 h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6) (* j2 j2)) (* 
256 (* h1 h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6) j2) (* 96 (* h1 h1 h1 h1) (* h2 h2
) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 256 (* h1 h1 h1 h1) (* h2 h2) h4 (* h5 h5) h6
 (* j2 j2)) (* 224 (* h1 h1 h1 h1) (* h2 h2) h4 (* h5 h5) h6 j2) (* 64 (* h1 h1 
h1 h1) (* h2 h2) h4 (* h5 h5) h6) (* 96 (* h1 h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6
) (* j2 j2 j2)) (* 224 (* h1 h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6) (* j2 j2)) (* 
160 (* h1 h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6) j2) (* 32 (* h1 h1 h1 h1) (* h2 h2
) h4 h5 (* h6 h6)) (* 64 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 
j2)) (* 256 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 384 (* h1
 h1 h1 h1) (* h2 h2) (* h5 h5 h5) h6 (* j2 j2)) (* 256 (* h1 h1 h1 h1) (* h2 h2)
 (* h5 h5 h5) h6 j2) (* 64 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5 h5) h6) (* 128 (* 
h1 h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 512 (* h1 h1 h1 
h1) (* h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 768 (* h1 h1 h1 h1) (* h2 h2)
 (* h5 h5) (* h6 h6) (* j2 j2)) (* 512 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5) (* h6
 h6) j2) (* 128 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6)) (* 64 (* h1 h1 h1
 h1) (* h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 256 (* h1 h1 h1 h1) (* h2 h2)
 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 384 (* h1 h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6) 
(* j2 j2)) (* 256 (* h1 h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6) j2) (* 64 (* h1 h1 
h1 h1) (* h2 h2) h5 (* h6 h6 h6)) (* 8192 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h5 
(* j2 j2 j2 j2)) (* 16384 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h5 (* j2 j2 j2)) 
(* 6656 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h5 (* j2 j2)) (* 768 (* h1 h1 h1 h1) 
h2 (* h3 h3 h3) h4 h5 j2) (* 8192 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h6 (* j2 j2
 j2 j2)) (* 8192 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h6 (* j2 j2 j2)) (* 2560 (* 
h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h6 (* j2 j2)) (* 256 (* h1 h1 h1 h1) h2 (* h3 h3
 h3) h4 h6 j2) (* 8192 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 
j2)) (* 26624 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 
24576 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2)) (* 4608 (* h1 h1 
h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* j2 j2)) (* 16384 (* h1 h1 h1 h1) h2 (* h3 h3
 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 45056 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h5 h6 
(* j2 j2 j2 j2)) (* 36864 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h5 h6 (* j2 j2 j2)) 
(* 9728 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h5 h6 (* j2 j2)) (* 768 (* h1 h1 h1 h1) 
h2 (* h3 h3 h3) h5 h6 j2) (* 8192 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6) (* 
j2 j2 j2 j2 j2)) (* 18432 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 
j2)) (* 14336 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6) (* j2 j2 j2)) (* 4608 
(* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6) (* j2 j2)) (* 512 (* h1 h1 h1 h1) h2 
(* h3 h3 h3) (* h6 h6) j2) (* 1536 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* 
j2 j2 j2)) (* 2688 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* j2 j2)) (* 576 
(* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 j2) (* 1536 (* h1 h1 h1 h1) h2 (* h3 
h3) (* h4 h4) h6 (* j2 j2 j2)) (* 896 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h6 
(* j2 j2)) (* 128 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h6 j2) (* 4096 (* h1 h1
 h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 11264 (* h1 h1 h1 h1) h2 
(* h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 8704 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* 
h5 h5) (* j2 j2)) (* 1536 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) j2) (* 8192 
(* h1 h1 h1 h1) h2 (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 18944 (* h1 h1 h1 h1) 
h2 (* h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 14464 (* h1 h1 h1 h1) h2 (* h3 h3) h4 h5 
h6 (* j2 j2)) (* 3136 (* h1 h1 h1 h1) h2 (* h3 h3) h4 h5 h6 j2) (* 64 (* h1 h1 
h1 h1) h2 (* h3 h3) h4 h5 h6) (* 4096 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6) 
(* j2 j2 j2 j2)) (* 7168 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6) (* j2 j2 j2))
 (* 3840 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6) (* j2 j2)) (* 512 (* h1 h1 h1
 h1) h2 (* h3 h3) h4 (* h6 h6) j2) (* 2048 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5
 h5) (* j2 j2 j2 j2 j2)) (* 8192 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* j2
 j2 j2 j2)) (* 10752 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* j2 j2 j2)) (* 
4608 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* j2 j2)) (* 8192 (* h1 h1 h1 h1
) h2 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 29696 (* h1 h1 h1 h1) h2 (* 
h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 36864 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5
 h5) h6 (* j2 j2 j2)) (* 17664 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5) h6 (* j2 
j2)) (* 2304 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5) h6 j2) (* 8192 (* h1 h1 h1 
h1) h2 (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 26624 (* h1 h1 h1 h1) h2 
(* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 31744 (* h1 h1 h1 h1) h2 (* h3 h3) h5
 (* h6 h6) (* j2 j2 j2)) (* 17024 (* h1 h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6) (* 
j2 j2)) (* 3840 (* h1 h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6) j2) (* 128 (* h1 h1 h1
 h1) h2 (* h3 h3) h5 (* h6 h6)) (* 2048 (* h1 h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6
) (* j2 j2 j2 j2 j2)) (* 6144 (* h1 h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6) (* j2 j2
 j2 j2)) (* 6656 (* h1 h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2)) (* 3072
 (* h1 h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6) (* j2 j2)) (* 512 (* h1 h1 h1 h1) h2 
(* h3 h3) (* h6 h6 h6) j2) (* 384 (* h1 h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* 
j2 j2 j2)) (* 960 (* h1 h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* j2 j2)) (* 576 
(* h1 h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) j2) (* 768 (* h1 h1 h1 h1) h2 h3 (* h4
 h4) h5 h6 (* j2 j2 j2)) (* 1120 (* h1 h1 h1 h1) h2 h3 (* h4 h4) h5 h6 (* j2 j2)
) (* 384 (* h1 h1 h1 h1) h2 h3 (* h4 h4) h5 h6 j2) (* 32 (* h1 h1 h1 h1) h2 h3 
(* h4 h4) h5 h6) (* 384 (* h1 h1 h1 h1) h2 h3 (* h4 h4) (* h6 h6) (* j2 j2 j2)) 
(* 256 (* h1 h1 h1 h1) h2 h3 (* h4 h4) (* h6 h6) (* j2 j2)) (* 512 (* h1 h1 h1 
h1) h2 h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 1792 (* h1 h1 h1 h1) h2 h3 h4 (* 
h5 h5 h5) (* j2 j2 j2)) (* 2048 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5 h5) (* j2 j2))
 (* 768 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5 h5) j2) (* 2048 (* h1 h1 h1 h1) h2 h3 
h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 6400 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5) h6 
(* j2 j2 j2)) (* 7040 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5) h6 (* j2 j2)) (* 2816 
(* h1 h1 h1 h1) h2 h3 h4 (* h5 h5) h6 j2) (* 128 (* h1 h1 h1 h1) h2 h3 h4 (* h5 
h5) h6) (* 2048 (* h1 h1 h1 h1) h2 h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 5376 
(* h1 h1 h1 h1) h2 h3 h4 h5 (* h6 h6) (* j2 j2 j2)) (* 4800 (* h1 h1 h1 h1) h2 
h3 h4 h5 (* h6 h6) (* j2 j2)) (* 1600 (* h1 h1 h1 h1) h2 h3 h4 h5 (* h6 h6) j2) 
(* 128 (* h1 h1 h1 h1) h2 h3 h4 h5 (* h6 h6)) (* 512 (* h1 h1 h1 h1) h2 h3 h4 
(* h6 h6 h6) (* j2 j2 j2 j2)) (* 1024 (* h1 h1 h1 h1) h2 h3 h4 (* h6 h6 h6) (* 
j2 j2 j2)) (* 512 (* h1 h1 h1 h1) h2 h3 h4 (* h6 h6 h6) (* j2 j2)) (* 1024 (* h1
 h1 h1 h1) h2 h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 4608 (* h1 h1 h1 h1) h2 
h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 7680 (* h1 h1 h1 h1) h2 h3 (* h5 h5 h5) 
h6 (* j2 j2 j2)) (* 5632 (* h1 h1 h1 h1) h2 h3 (* h5 h5 h5) h6 (* j2 j2)) (* 
1536 (* h1 h1 h1 h1) h2 h3 (* h5 h5 h5) h6 j2) (* 2048 (* h1 h1 h1 h1) h2 h3 (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 8576 (* h1 h1 h1 h1) h2 h3 (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2)) (* 13696 (* h1 h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6) (* j2
 j2 j2)) (* 10112 (* h1 h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6) (* j2 j2)) (* 3200 
(* h1 h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6) j2) (* 256 (* h1 h1 h1 h1) h2 h3 (* h5
 h5) (* h6 h6)) (* 1024 (* h1 h1 h1 h1) h2 h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)
) (* 4096 (* h1 h1 h1 h1) h2 h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 6272 (* h1 
h1 h1 h1) h2 h3 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 4480 (* h1 h1 h1 h1) h2 h3 h5 
(* h6 h6 h6) (* j2 j2)) (* 1408 (* h1 h1 h1 h1) h2 h3 h5 (* h6 h6 h6) j2) (* 128
 (* h1 h1 h1 h1) h2 h3 h5 (* h6 h6 h6)) (* 96 (* h1 h1 h1 h1) h2 (* h4 h4) (* h5
 h5) h6 (* j2 j2 j2)) (* 224 (* h1 h1 h1 h1) h2 (* h4 h4) (* h5 h5) h6 (* j2 j2)
) (* 160 (* h1 h1 h1 h1) h2 (* h4 h4) (* h5 h5) h6 j2) (* 32 (* h1 h1 h1 h1) h2 
(* h4 h4) (* h5 h5) h6) (* 96 (* h1 h1 h1 h1) h2 (* h4 h4) h5 (* h6 h6) (* j2 j2
 j2)) (* 160 (* h1 h1 h1 h1) h2 (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 64 (* h1 h1
 h1 h1) h2 (* h4 h4) h5 (* h6 h6) j2) (* 128 (* h1 h1 h1 h1) h2 h4 (* h5 h5 h5) 
h6 (* j2 j2 j2 j2)) (* 448 (* h1 h1 h1 h1) h2 h4 (* h5 h5 h5) h6 (* j2 j2 j2)) 
(* 576 (* h1 h1 h1 h1) h2 h4 (* h5 h5 h5) h6 (* j2 j2)) (* 320 (* h1 h1 h1 h1) 
h2 h4 (* h5 h5 h5) h6 j2) (* 64 (* h1 h1 h1 h1) h2 h4 (* h5 h5 h5) h6) (* 256 
(* h1 h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 896 (* h1 h1 h1 h1
) h2 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 1152 (* h1 h1 h1 h1) h2 h4 (* h5 h5
) (* h6 h6) (* j2 j2)) (* 640 (* h1 h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6) j2) (* 
128 (* h1 h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6)) (* 128 (* h1 h1 h1 h1) h2 h4 h5 
(* h6 h6 h6) (* j2 j2 j2 j2)) (* 384 (* h1 h1 h1 h1) h2 h4 h5 (* h6 h6 h6) (* j2
 j2 j2)) (* 384 (* h1 h1 h1 h1) h2 h4 h5 (* h6 h6 h6) (* j2 j2)) (* 128 (* h1 h1
 h1 h1) h2 h4 h5 (* h6 h6 h6) j2) (* 128 (* h1 h1 h1 h1) h2 (* h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2)) (* 640 (* h1 h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2)) (* 1280 (* h1 h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 
1280 (* h1 h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 640 (* h1 h1 h1 h1)
 h2 (* h5 h5 h5) (* h6 h6) j2) (* 128 (* h1 h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6))
 (* 128 (* h1 h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 640 (* 
h1 h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1280 (* h1 h1 h1 h1) 
h2 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 1280 (* h1 h1 h1 h1) h2 (* h5 h5) (* 
h6 h6 h6) (* j2 j2)) (* 640 (* h1 h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6) j2) (* 128
 (* h1 h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6)) (* 4096 (* h1 h1 h1 h1) (* h3 h3 h3)
 (* h4 h4) h5 (* j2 j2 j2 j2)) (* 8192 (* h1 h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5
 (* j2 j2 j2)) (* 3328 (* h1 h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2)) (* 
384 (* h1 h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 j2) (* 4096 (* h1 h1 h1 h1) (* h3 
h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2)) (* 2048 (* h1 h1 h1 h1) (* h3 h3 h3) (* h4 
h4) h6 (* j2 j2 j2)) (* 256 (* h1 h1 h1 h1) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2))
 (* 8192 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 26624 
(* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 24576 (* h1 h1 h1 
h1) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 4608 (* h1 h1 h1 h1) (* h3 h3 h3)
 h4 (* h5 h5) (* j2 j2)) (* 16384 (* h1 h1 h1 h1) (* h3 h3 h3) h4 h5 h6 (* j2 j2
 j2 j2 j2)) (* 45056 (* h1 h1 h1 h1) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 
38912 (* h1 h1 h1 h1) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 13312 (* h1 h1 h1 
h1) (* h3 h3 h3) h4 h5 h6 (* j2 j2)) (* 1536 (* h1 h1 h1 h1) (* h3 h3 h3) h4 h5 
h6 j2) (* 8192 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
10240 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 4096 (* h1 
h1 h1 h1) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2)) (* 512 (* h1 h1 h1 h1) (* h3 
h3 h3) h4 (* h6 h6) (* j2 j2)) (* 16384 (* h1 h1 h1 h1) (* h3 h3 h3) (* h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2)) (* 69632 (* h1 h1 h1 h1) (* h3 h3 h3) (* h5 h5) h6 (* 
j2 j2 j2 j2 j2)) (* 102400 (* h1 h1 h1 h1) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2
 j2)) (* 58368 (* h1 h1 h1 h1) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 9216 
(* h1 h1 h1 h1) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2)) (* 16384 (* h1 h1 h1 h1) 
(* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 61440 (* h1 h1 h1 h1) (* h3 
h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 83968 (* h1 h1 h1 h1) (* h3 h3 h3) h5
 (* h6 h6) (* j2 j2 j2 j2)) (* 52224 (* h1 h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6) 
(* j2 j2 j2)) (* 14848 (* h1 h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2)) (* 
1536 (* h1 h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6) j2) (* 512 (* h1 h1 h1 h1) (* h3 
h3) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 896 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4 h4) 
h5 (* j2 j2)) (* 192 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 j2) (* 512 (* h1 
h1 h1 h1) (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2)) (* 128 (* h1 h1 h1 h1) (* h3 
h3) (* h4 h4 h4) h6 (* j2 j2)) (* 2048 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h5
 h5) (* j2 j2 j2 j2)) (* 5632 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* 
j2 j2 j2)) (* 4352 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 
768 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) j2) (* 4096 (* h1 h1 h1 h1) 
(* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 8960 (* h1 h1 h1 h1) (* h3 h3) (* 
h4 h4) h5 h6 (* j2 j2 j2)) (* 6848 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) h5 h6 (* 
j2 j2)) (* 1216 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) h5 h6 j2) (* 2048 (* h1 h1 
h1 h1) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 2560 (* h1 h1 h1 h1) 
(* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 512 (* h1 h1 h1 h1) (* h3 h3) (* 
h4 h4) (* h6 h6) (* j2 j2)) (* 2048 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) 
(* j2 j2 j2 j2 j2)) (* 8192 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 
j2 j2)) (* 10752 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2)) (* 4608
 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2)) (* 8192 (* h1 h1 h1 h1) 
(* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 29696 (* h1 h1 h1 h1) (* h3 h3)
 h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 37376 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5
) h6 (* j2 j2 j2)) (* 18944 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2))
 (* 3072 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5) h6 j2) (* 8192 (* h1 h1 h1 h1) 
(* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 24576 (* h1 h1 h1 h1) (* h3 h3)
 h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 29184 (* h1 h1 h1 h1) (* h3 h3) h4 h5 (* h6
 h6) (* j2 j2 j2)) (* 15232 (* h1 h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2))
 (* 2432 (* h1 h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6) j2) (* 2048 (* h1 h1 h1 h1) 
(* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 4096 (* h1 h1 h1 h1) (* h3 h3) 
h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 2560 (* h1 h1 h1 h1) (* h3 h3) h4 (* h6 h6 
h6) (* j2 j2 j2)) (* 512 (* h1 h1 h1 h1) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2)) 
(* 4096 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
20480 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 37888 (* 
h1 h1 h1 h1) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 30720 (* h1 h1 h1 h1)
 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 9216 (* h1 h1 h1 h1) (* h3 h3) (* h5
 h5 h5) h6 (* j2 j2)) (* 8192 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 37888 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6) (* j2
 j2 j2 j2 j2)) (* 67072 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2)) (* 56320 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 
22016 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 3072 (* h1 h1 
h1 h1) (* h3 h3) (* h5 h5) (* h6 h6) j2) (* 4096 (* h1 h1 h1 h1) (* h3 h3) h5 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 18432 (* h1 h1 h1 h1) (* h3 h3) h5 (* h6 
h6 h6) (* j2 j2 j2 j2 j2)) (* 31744 (* h1 h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6) 
(* j2 j2 j2 j2)) (* 26112 (* h1 h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)
) (* 10240 (* h1 h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 1536 (* h1 h1
 h1 h1) (* h3 h3) h5 (* h6 h6 h6) j2) (* 128 (* h1 h1 h1 h1) h3 (* h4 h4 h4) (* 
h5 h5) (* j2 j2 j2)) (* 320 (* h1 h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2))
 (* 192 (* h1 h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) j2) (* 256 (* h1 h1 h1 h1) h3 
(* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 288 (* h1 h1 h1 h1) h3 (* h4 h4 h4) h5 h6 
(* j2 j2)) (* 32 (* h1 h1 h1 h1) h3 (* h4 h4 h4) h5 h6 j2) (* 128 (* h1 h1 h1 h1
) h3 (* h4 h4 h4) (* h6 h6) (* j2 j2 j2)) (* 256 (* h1 h1 h1 h1) h3 (* h4 h4) 
(* h5 h5 h5) (* j2 j2 j2 j2)) (* 896 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) 
(* j2 j2 j2)) (* 1024 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 
384 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) j2) (* 1024 (* h1 h1 h1 h1) h3 (* 
h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 3072 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 
h5) h6 (* j2 j2 j2)) (* 3328 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2)
) (* 1280 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5) h6 j2) (* 1024 (* h1 h1 h1 h1) 
h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 2176 (* h1 h1 h1 h1) h3 (* h4 h4) 
h5 (* h6 h6) (* j2 j2 j2)) (* 1280 (* h1 h1 h1 h1) h3 (* h4 h4) h5 (* h6 h6) (* 
j2 j2)) (* 128 (* h1 h1 h1 h1) h3 (* h4 h4) h5 (* h6 h6) j2) (* 256 (* h1 h1 h1 
h1) h3 (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 256 (* h1 h1 h1 h1) h3 (* h4 
h4) (* h6 h6 h6) (* j2 j2 j2)) (* 1024 (* h1 h1 h1 h1) h3 h4 (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2)) (* 4608 (* h1 h1 h1 h1) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) 
(* 7680 (* h1 h1 h1 h1) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 5632 (* h1 h1 h1 
h1) h3 h4 (* h5 h5 h5) h6 (* j2 j2)) (* 1536 (* h1 h1 h1 h1) h3 h4 (* h5 h5 h5) 
h6 j2) (* 2048 (* h1 h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
8064 (* h1 h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 12544 (* h1 
h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 9088 (* h1 h1 h1 h1) h3 h4 
(* h5 h5) (* h6 h6) (* j2 j2)) (* 2560 (* h1 h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6)
 j2) (* 1024 (* h1 h1 h1 h1) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 3072 
(* h1 h1 h1 h1) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 3200 (* h1 h1 h1 h1) 
h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 1280 (* h1 h1 h1 h1) h3 h4 h5 (* h6 h6 h6
) (* j2 j2)) (* 128 (* h1 h1 h1 h1) h3 h4 h5 (* h6 h6 h6) j2) (* 1024 (* h1 h1 
h1 h1) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 5632 (* h1 h1 h1 h1) 
h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 12288 (* h1 h1 h1 h1) h3 (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 13312 (* h1 h1 h1 h1) h3 (* h5 h5 h5) (* h6
 h6) (* j2 j2 j2)) (* 7168 (* h1 h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2)) 
(* 1536 (* h1 h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6) j2) (* 1024 (* h1 h1 h1 h1) h3
 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 5632 (* h1 h1 h1 h1) h3 (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 12288 (* h1 h1 h1 h1) h3 (* h5 h5) (* h6
 h6 h6) (* j2 j2 j2 j2)) (* 13312 (* h1 h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6) (* 
j2 j2 j2)) (* 7168 (* h1 h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 1536 
(* h1 h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6) j2) (* 32 (* h1 h1 h1 h1) (* h4 h4 h4)
 (* h5 h5) h6 (* j2 j2 j2)) (* 64 (* h1 h1 h1 h1) (* h4 h4 h4) (* h5 h5) h6 (* 
j2 j2)) (* 32 (* h1 h1 h1 h1) (* h4 h4 h4) (* h5 h5) h6 j2) (* 32 (* h1 h1 h1 h1
) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 32 (* h1 h1 h1 h1) (* h4 h4 h4) h5 
(* h6 h6) (* j2 j2)) (* 64 (* h1 h1 h1 h1) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2
 j2)) (* 192 (* h1 h1 h1 h1) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 192 (* 
h1 h1 h1 h1) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 64 (* h1 h1 h1 h1) (* h4 h4
) (* h5 h5 h5) h6 j2) (* 128 (* h1 h1 h1 h1) (* h4 h4) (* h5 h5) (* h6 h6) (* j2
 j2 j2 j2)) (* 384 (* h1 h1 h1 h1) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) 
(* 384 (* h1 h1 h1 h1) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 128 (* h1 h1 
h1 h1) (* h4 h4) (* h5 h5) (* h6 h6) j2) (* 64 (* h1 h1 h1 h1) (* h4 h4) h5 (* 
h6 h6 h6) (* j2 j2 j2 j2)) (* 128 (* h1 h1 h1 h1) (* h4 h4) h5 (* h6 h6 h6) (* 
j2 j2 j2)) (* 64 (* h1 h1 h1 h1) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2)) (* 128 (* 
h1 h1 h1 h1) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 512 (* h1 h1 h1 h1
) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 768 (* h1 h1 h1 h1) h4 (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2)) (* 512 (* h1 h1 h1 h1) h4 (* h5 h5 h5) (* h6 h6) (* 
j2 j2)) (* 128 (* h1 h1 h1 h1) h4 (* h5 h5 h5) (* h6 h6) j2) (* 128 (* h1 h1 h1 
h1) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 512 (* h1 h1 h1 h1) h4 (* 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 768 (* h1 h1 h1 h1) h4 (* h5 h5) (* h6 
h6 h6) (* j2 j2 j2)) (* 512 (* h1 h1 h1 h1) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2))
 (* 128 (* h1 h1 h1 h1) h4 (* h5 h5) (* h6 h6 h6) j2) (* 128 (* h1 h1 h1) (* h2 
h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2)) (* 224 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3 
h3) h5 (* j2 j2)) (* 48 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 j2) (* 128 (* 
h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h6 (* j2 j2 j2)) (* 160 (* h1 h1 h1) (* h2 
h2 h2 h2) (* h3 h3) h6 (* j2 j2)) (* 32 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) 
h6 j2) (* 32 (* h1 h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) (* j2 j2 j2)) (* 80 (* h1
 h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) (* j2 j2)) (* 48 (* h1 h1 h1) (* h2 h2 h2 
h2) h3 (* h5 h5) j2) (* 64 (* h1 h1 h1) (* h2 h2 h2 h2) h3 h5 h6 (* j2 j2 j2)) 
(* 136 (* h1 h1 h1) (* h2 h2 h2 h2) h3 h5 h6 (* j2 j2)) (* 80 (* h1 h1 h1) (* h2
 h2 h2 h2) h3 h5 h6 j2) (* 8 (* h1 h1 h1) (* h2 h2 h2 h2) h3 h5 h6) (* 32 (* h1 
h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6) (* j2 j2 j2)) (* 64 (* h1 h1 h1) (* h2 h2 h2
 h2) h3 (* h6 h6) (* j2 j2)) (* 32 (* h1 h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6) j2)
 (* 8 (* h1 h1 h1) (* h2 h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2)) (* 24 (* h1 h1 h1)
 (* h2 h2 h2 h2) (* h5 h5) h6 (* j2 j2)) (* 24 (* h1 h1 h1) (* h2 h2 h2 h2) (* 
h5 h5) h6 j2) (* 8 (* h1 h1 h1) (* h2 h2 h2 h2) (* h5 h5) h6) (* 8 (* h1 h1 h1) 
(* h2 h2 h2 h2) h5 (* h6 h6) (* j2 j2 j2)) (* 24 (* h1 h1 h1) (* h2 h2 h2 h2) h5
 (* h6 h6) (* j2 j2)) (* 24 (* h1 h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6) j2) (* 8 
(* h1 h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6)) (* 2048 (* h1 h1 h1) (* h2 h2 h2) (* 
h3 h3 h3) h5 (* j2 j2 j2 j2)) (* 4096 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 
(* j2 j2 j2)) (* 1664 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2)) (* 
192 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 j2) (* 2048 (* h1 h1 h1) (* h2 h2 
h2) (* h3 h3 h3) h6 (* j2 j2 j2 j2)) (* 3072 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 
h3) h6 (* j2 j2 j2)) (* 1152 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2)
) (* 128 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h6 j2) (* 1280 (* h1 h1 h1) (* 
h2 h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2)) (* 2240 (* h1 h1 h1) (* h2 h2 h2) (* h3 
h3) h4 h5 (* j2 j2)) (* 480 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 j2) (* 
1280 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2)) (* 1216 (* h1 h1 h1
) (* h2 h2 h2) (* h3 h3) h4 h6 (* j2 j2)) (* 224 (* h1 h1 h1) (* h2 h2 h2) (* h3
 h3) h4 h6 j2) (* 1024 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2
 j2)) (* 2816 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2)) (* 
2176 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) (* j2 j2)) (* 384 (* h1 h1 h1
) (* h2 h2 h2) (* h3 h3) (* h5 h5) j2) (* 2048 (* h1 h1 h1) (* h2 h2 h2) (* h3 
h3) h5 h6 (* j2 j2 j2 j2)) (* 4992 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 h6 (* 
j2 j2 j2)) (* 3808 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 h6 (* j2 j2)) (* 960 
(* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 h6 j2) (* 32 (* h1 h1 h1) (* h2 h2 h2) 
(* h3 h3) h5 h6) (* 1024 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 
j2 j2)) (* 2304 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2)) (* 
1664 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2)) (* 384 (* h1 h1 h1
) (* h2 h2 h2) (* h3 h3) (* h6 h6) j2) (* 320 (* h1 h1 h1) (* h2 h2 h2) h3 h4 
(* h5 h5) (* j2 j2 j2)) (* 800 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) (* j2 
j2)) (* 480 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) j2) (* 640 (* h1 h1 h1) 
(* h2 h2 h2) h3 h4 h5 h6 (* j2 j2 j2)) (* 1168 (* h1 h1 h1) (* h2 h2 h2) h3 h4 
h5 h6 (* j2 j2)) (* 584 (* h1 h1 h1) (* h2 h2 h2) h3 h4 h5 h6 j2) (* 56 (* h1 h1
 h1) (* h2 h2 h2) h3 h4 h5 h6) (* 320 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6) 
(* j2 j2 j2)) (* 448 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6) (* j2 j2)) (* 128
 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6) j2) (* 128 (* h1 h1 h1) (* h2 h2 h2) 
h3 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 448 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5
) (* j2 j2 j2)) (* 512 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) (* j2 j2)) (* 
192 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) j2) (* 512 (* h1 h1 h1) (* h2 h2 
h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 1664 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 
h5) h6 (* j2 j2 j2)) (* 1856 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) h6 (* j2 j2)
) (* 768 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) h6 j2) (* 64 (* h1 h1 h1) (* h2 
h2 h2) h3 (* h5 h5) h6) (* 512 (* h1 h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6) (* j2 
j2 j2 j2)) (* 1600 (* h1 h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2)) (* 
1760 (* h1 h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6) (* j2 j2)) (* 768 (* h1 h1 h1) 
(* h2 h2 h2) h3 h5 (* h6 h6) j2) (* 96 (* h1 h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6)
) (* 128 (* h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 384 (* h1
 h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2)) (* 384 (* h1 h1 h1) (* h2 h2 
h2) h3 (* h6 h6 h6) (* j2 j2)) (* 128 (* h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6) 
j2) (* 80 (* h1 h1 h1) (* h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 216 (* h1 
h1 h1) (* h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2)) (* 192 (* h1 h1 h1) (* h2 h2 h2) 
h4 (* h5 h5) h6 j2) (* 56 (* h1 h1 h1) (* h2 h2 h2) h4 (* h5 h5) h6) (* 80 (* h1
 h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 192 (* h1 h1 h1) (* h2 h2 
h2) h4 h5 (* h6 h6) (* j2 j2)) (* 144 (* h1 h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6) 
j2) (* 32 (* h1 h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6)) (* 32 (* h1 h1 h1) (* h2 h2
 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 128 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5 
h5) h6 (* j2 j2 j2)) (* 192 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2))
 (* 128 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5 h5) h6 j2) (* 32 (* h1 h1 h1) (* h2 
h2 h2) (* h5 h5 h5) h6) (* 64 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6) (* 
j2 j2 j2 j2)) (* 256 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2))
 (* 384 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 j2)) (* 256 (* h1 h1
 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6) j2) (* 64 (* h1 h1 h1) (* h2 h2 h2) (* h5 
h5) (* h6 h6)) (* 32 (* h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) 
(* 128 (* h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 192 (* h1 h1 
h1) (* h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2)) (* 128 (* h1 h1 h1) (* h2 h2 h2) h5 
(* h6 h6 h6) j2) (* 32 (* h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6)) (* 4096 (* h1 
h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2 j2 j2 j2)) (* 9216 (* h1 h1 h1) (* 
h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2 j2 j2)) (* 5376 (* h1 h1 h1) (* h2 h2) (* h3 
h3 h3 h3) h5 (* j2 j2 j2)) (* 1216 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 (* 
j2 j2)) (* 96 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 j2) (* 4096 (* h1 h1 h1)
 (* h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2 j2 j2 j2)) (* 7168 (* h1 h1 h1) (* h2 h2)
 (* h3 h3 h3 h3) h6 (* j2 j2 j2 j2)) (* 3840 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 
h3) h6 (* j2 j2 j2)) (* 832 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2))
 (* 64 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h6 j2) (* 10240 (* h1 h1 h1) (* h2
 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2)) (* 20480 (* h1 h1 h1) (* h2 h2) (* h3 
h3 h3) h4 h5 (* j2 j2 j2)) (* 8320 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 (* 
j2 j2)) (* 960 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 j2) (* 10240 (* h1 h1 
h1) (* h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 11264 (* h1 h1 h1) (* h2 h2
) (* h3 h3 h3) h4 h6 (* j2 j2 j2)) (* 3712 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) 
h4 h6 (* j2 j2)) (* 384 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h6 j2) (* 7168 
(* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 22528 (* h1
 h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 20928 (* h1 h1 h1) 
(* h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2)) (* 5088 (* h1 h1 h1) (* h2 h2) 
(* h3 h3 h3) (* h5 h5) (* j2 j2)) (* 288 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* 
h5 h5) j2) (* 14336 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2)
) (* 39168 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 33792 
(* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2)) (* 10704 (* h1 h1 h1) 
(* h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2)) (* 1184 (* h1 h1 h1) (* h2 h2) (* h3 h3 
h3) h5 h6 j2) (* 16 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 h6) (* 7168 (* h1 h1 
h1) (* h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 16896 (* h1 h1 h1) 
(* h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 14016 (* h1 h1 h1) (* h2 h2
) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2)) (* 4864 (* h1 h1 h1) (* h2 h2) (* h3 h3 
h3) (* h6 h6) (* j2 j2)) (* 576 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6) j2
) (* 2304 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 4032 
(* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2)) (* 864 (* h1 h1 h1) (* 
h2 h2) (* h3 h3) (* h4 h4) h5 j2) (* 2304 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4
 h4) h6 (* j2 j2 j2)) (* 1472 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h6 (* 
j2 j2)) (* 224 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h6 j2) (* 5120 (* h1 
h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 14080 (* h1 h1 h1) 
(* h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 10880 (* h1 h1 h1) (* h2 h2) 
(* h3 h3) h4 (* h5 h5) (* j2 j2)) (* 1920 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 
(* h5 h5) j2) (* 10240 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2)
) (* 23296 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 17152 (* 
h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2)) (* 3856 (* h1 h1 h1) (* h2 h2)
 (* h3 h3) h4 h5 h6 j2) (* 96 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6) (* 5120
 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 9088 (* h1 h1
 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2)) (* 5024 (* h1 h1 h1) (* h2 
h2) (* h3 h3) h4 (* h6 h6) (* j2 j2)) (* 800 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4
 (* h6 h6) j2) (* 1792 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2
 j2 j2)) (* 6976 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2)) 
(* 9120 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2)) (* 4224 (* 
h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2)) (* 288 (* h1 h1 h1) (* h2 
h2) (* h3 h3) (* h5 h5 h5) j2) (* 6656 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5
) h6 (* j2 j2 j2 j2 j2)) (* 23872 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) h6 
(* j2 j2 j2 j2)) (* 29936 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2
 j2)) (* 15120 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2)) (* 2448 
(* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) h6 j2) (* 48 (* h1 h1 h1) (* h2 h2) 
(* h3 h3) (* h5 h5) h6) (* 6656 (* h1 h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* 21952 (* h1 h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6) (* j2
 j2 j2 j2)) (* 26832 (* h1 h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2))
 (* 14928 (* h1 h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2)) (* 3536 (* h1
 h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6) j2) (* 144 (* h1 h1 h1) (* h2 h2) (* h3
 h3) h5 (* h6 h6)) (* 1792 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 
j2 j2 j2 j2)) (* 5568 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 
j2)) (* 6336 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2)) (* 3136
 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2)) (* 576 (* h1 h1 h1) 
(* h2 h2) (* h3 h3) (* h6 h6 h6) j2) (* 576 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) 
(* h5 h5) (* j2 j2 j2)) (* 1440 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) 
(* j2 j2)) (* 864 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) j2) (* 1152 (* 
h1 h1 h1) (* h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2)) (* 1744 (* h1 h1 h1) (* h2 
h2) h3 (* h4 h4) h5 h6 (* j2 j2)) (* 648 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) h5 
h6 j2) (* 56 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) h5 h6) (* 576 (* h1 h1 h1) (* 
h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 448 (* h1 h1 h1) (* h2 h2) h3 (* 
h4 h4) (* h6 h6) (* j2 j2)) (* 32 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h6 h6) 
j2) (* 640 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 2240 
(* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2)) (* 2560 (* h1 h1 h1) (* 
h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2)) (* 960 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 
h5 h5) j2) (* 2560 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2)) 
(* 7904 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2)) (* 8496 (* h1 h1
 h1) (* h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2)) (* 3344 (* h1 h1 h1) (* h2 h2) h3 
h4 (* h5 h5) h6 j2) (* 192 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6) (* 2560 
(* h1 h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 6784 (* h1 h1 h1) 
(* h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2)) (* 6152 (* h1 h1 h1) (* h2 h2) h3 h4 
h5 (* h6 h6) (* j2 j2)) (* 2128 (* h1 h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6) j2) 
(* 200 (* h1 h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6)) (* 640 (* h1 h1 h1) (* h2 h2) 
h3 h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1376 (* h1 h1 h1) (* h2 h2) h3 h4 (* h6 
h6 h6) (* j2 j2 j2)) (* 832 (* h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2))
 (* 96 (* h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6 h6) j2) (* 64 (* h1 h1 h1) (* h2 h2
) h3 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 288 (* h1 h1 h1) (* h2 h2) h3 (* h5 
h5 h5 h5) (* j2 j2 j2 j2)) (* 480 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) (* 
j2 j2 j2)) (* 352 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) (* j2 j2)) (* 96 (* 
h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) j2) (* 896 (* h1 h1 h1) (* h2 h2) h3 (* 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 3952 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) 
h6 (* j2 j2 j2 j2)) (* 6528 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 
j2)) (* 4832 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2)) (* 1408 (* h1 
h1 h1) (* h2 h2) h3 (* h5 h5 h5) h6 j2) (* 48 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5
 h5) h6) (* 1664 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2
)) (* 6976 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 
11200 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 8384 (* h1 
h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2)) (* 2752 (* h1 h1 h1) (* h2 h2
) h3 (* h5 h5) (* h6 h6) j2) (* 256 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6
)) (* 896 (* h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 3632 
(* h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 5664 (* h1 h1 h1) 
(* h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 4160 (* h1 h1 h1) (* h2 h2) h3 h5 
(* h6 h6 h6) (* j2 j2)) (* 1376 (* h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6) j2) 
(* 144 (* h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6)) (* 64 (* h1 h1 h1) (* h2 h2) 
h3 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 256 (* h1 h1 h1) (* h2 h2) h3 (* h6 h6
 h6 h6) (* j2 j2 j2 j2)) (* 384 (* h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6 h6) (* j2 
j2 j2)) (* 256 (* h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6 h6) (* j2 j2)) (* 64 (* h1 
h1 h1) (* h2 h2) h3 (* h6 h6 h6 h6) j2) (* 144 (* h1 h1 h1) (* h2 h2) (* h4 h4) 
(* h5 h5) h6 (* j2 j2 j2)) (* 344 (* h1 h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) h6 
(* j2 j2)) (* 256 (* h1 h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) h6 j2) (* 56 (* h1 
h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) h6) (* 144 (* h1 h1 h1) (* h2 h2) (* h4 h4)
 h5 (* h6 h6) (* j2 j2 j2)) (* 256 (* h1 h1 h1) (* h2 h2) (* h4 h4) h5 (* h6 h6)
 (* j2 j2)) (* 120 (* h1 h1 h1) (* h2 h2) (* h4 h4) h5 (* h6 h6) j2) (* 8 (* h1 
h1 h1) (* h2 h2) (* h4 h4) h5 (* h6 h6)) (* 160 (* h1 h1 h1) (* h2 h2) h4 (* h5 
h5 h5) h6 (* j2 j2 j2 j2)) (* 576 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5 h5) h6 (* 
j2 j2 j2)) (* 768 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2)) (* 448 
(* h1 h1 h1) (* h2 h2) h4 (* h5 h5 h5) h6 j2) (* 96 (* h1 h1 h1) (* h2 h2) h4 
(* h5 h5 h5) h6) (* 320 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2)) (* 1128 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 
1464 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 824 (* h1 h1 h1
) (* h2 h2) h4 (* h5 h5) (* h6 h6) j2) (* 168 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5
) (* h6 h6)) (* 160 (* h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) 
(* 504 (* h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 552 (* h1 h1 
h1) (* h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2)) (* 232 (* h1 h1 h1) (* h2 h2) h4 h5 
(* h6 h6 h6) j2) (* 24 (* h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6 h6)) (* 16 (* h1 h1
 h1) (* h2 h2) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 80 (* h1 h1 h1) (* h2 
h2) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 160 (* h1 h1 h1) (* h2 h2) (* h5 h5 
h5 h5) h6 (* j2 j2 j2)) (* 160 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5 h5) h6 (* j2 
j2)) (* 80 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5 h5) h6 j2) (* 16 (* h1 h1 h1) (* 
h2 h2) (* h5 h5 h5 h5) h6) (* 112 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* 560 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2)) (* 1120 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) 
(* 1120 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 560 (* h1 h1
 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6) j2) (* 112 (* h1 h1 h1) (* h2 h2) (* h5 h5
 h5) (* h6 h6)) (* 112 (* h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2
 j2 j2)) (* 560 (* h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) 
(* 1120 (* h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 1120 (* 
h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 560 (* h1 h1 h1) (* h2 
h2) (* h5 h5) (* h6 h6 h6) j2) (* 112 (* h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 
h6)) (* 16 (* h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 80 
(* h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 160 (* h1 h1 h1) 
(* h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 160 (* h1 h1 h1) (* h2 h2) h5 (* 
h6 h6 h6 h6) (* j2 j2)) (* 80 (* h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6 h6) j2) (* 
16 (* h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6 h6)) (* 8192 (* h1 h1 h1) h2 (* h3 h3 
h3 h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 18432 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h5 
(* j2 j2 j2 j2)) (* 10752 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2)) 
(* 2432 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h5 (* j2 j2)) (* 192 (* h1 h1 h1) h2 
(* h3 h3 h3 h3) h4 h5 j2) (* 8192 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h6 (* j2 j2
 j2 j2 j2)) (* 10240 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 
4608 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2)) (* 896 (* h1 h1 h1) h2 
(* h3 h3 h3 h3) h4 h6 (* j2 j2)) (* 64 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h6 j2)
 (* 8192 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 
28672 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 31232 (* 
h1 h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 10752 (* h1 h1 h1) h2
 (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2)) (* 1152 (* h1 h1 h1) h2 (* h3 h3 h3 h3)
 (* h5 h5) (* j2 j2)) (* 16384 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2
 j2 j2 j2)) (* 49152 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) 
(* 48128 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 18944 (* h1 
h1 h1) h2 (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2)) (* 3200 (* h1 h1 h1) h2 (* h3 h3 
h3 h3) h5 h6 (* j2 j2)) (* 192 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h5 h6 j2) (* 8192
 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 20480 (* h1
 h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 18944 (* h1 h1 h1) 
h2 (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 8192 (* h1 h1 h1) h2 (* h3 h3 
h3 h3) (* h6 h6) (* j2 j2 j2)) (* 1664 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6)
 (* j2 j2)) (* 128 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6) j2) (* 10240 (* h1 
h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 20480 (* h1 h1 h1) h2 
(* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 8320 (* h1 h1 h1) h2 (* h3 h3 h3) (* 
h4 h4) h5 (* j2 j2)) (* 960 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 j2) (* 
10240 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2)) (* 7168 (* h1 
h1 h1) h2 (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2)) (* 1664 (* h1 h1 h1) h2 (* h3 
h3 h3) (* h4 h4) h6 (* j2 j2)) (* 128 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h6 
j2) (* 18432 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 
58368 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 54144 (* h1 
h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 12480 (* h1 h1 h1) h2 (* h3
 h3 h3) h4 (* h5 h5) (* j2 j2)) (* 576 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5)
 j2) (* 36864 (* h1 h1 h1) h2 (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 96768
 (* h1 h1 h1) h2 (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 81152 (* h1 h1 h1) h2
 (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 26272 (* h1 h1 h1) h2 (* h3 h3 h3) h4 h5
 h6 (* j2 j2)) (* 2928 (* h1 h1 h1) h2 (* h3 h3 h3) h4 h5 h6 j2) (* 16 (* h1 h1 
h1) h2 (* h3 h3 h3) h4 h5 h6) (* 18432 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6)
 (* j2 j2 j2 j2 j2)) (* 30720 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6) (* j2 j2
 j2 j2)) (* 18304 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2)) (* 
4480 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6) (* j2 j2)) (* 384 (* h1 h1 h1) h2
 (* h3 h3 h3) h4 (* h6 h6) j2) (* 4096 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5)
 (* j2 j2 j2 j2 j2 j2)) (* 17408 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) (* j2
 j2 j2 j2 j2)) (* 25600 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2
)) (* 14592 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2)) (* 2304 (* 
h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) (* j2 j2)) (* 24576 (* h1 h1 h1) h2 (* h3
 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 99328 (* h1 h1 h1) h2 (* h3 h3 h3
) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 141568 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 
h5) h6 (* j2 j2 j2 j2)) (* 82304 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) h6 (* j2
 j2 j2)) (* 16256 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2)) (* 768 
(* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) h6 j2) (* 24576 (* h1 h1 h1) h2 (* h3 h3 
h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 89088 (* h1 h1 h1) h2 (* h3 h3 h3) h5
 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 120064 (* h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6 
h6) (* j2 j2 j2 j2)) (* 75392 (* h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2
 j2)) (* 22368 (* h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2)) (* 2560 (* 
h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6) j2) (* 32 (* h1 h1 h1) h2 (* h3 h3 h3) h5
 (* h6 h6)) (* 4096 (* h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 13312 (* h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
16384 (* h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 9472 (* h1 
h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2)) (* 2560 (* h1 h1 h1) h2 (* h3 
h3 h3) (* h6 h6 h6) (* j2 j2)) (* 256 (* h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6) 
j2) (* 1280 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 2240 (* 
h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 (* j2 j2)) (* 480 (* h1 h1 h1) h2 (* h3 
h3) (* h4 h4 h4) h5 j2) (* 1280 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h6 (* j2 
j2 j2)) (* 448 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h6 (* j2 j2)) (* 32 (* h1 
h1 h1) h2 (* h3 h3) (* h4 h4 h4) h6 j2) (* 5120 (* h1 h1 h1) h2 (* h3 h3) (* h4 
h4) (* h5 h5) (* j2 j2 j2 j2)) (* 14080 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* 
h5 h5) (* j2 j2 j2)) (* 10880 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) (* 
j2 j2)) (* 1920 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) j2) (* 10240 (* h1
 h1 h1) h2 (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 21632 (* h1 h1 h1) h2 
(* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 15264 (* h1 h1 h1) h2 (* h3 h3) (* h4
 h4) h5 h6 (* j2 j2)) (* 2912 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 h6 j2) (* 
32 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 h6) (* 5120 (* h1 h1 h1) h2 (* h3 h3) 
(* h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 6656 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4)
 (* h6 h6) (* j2 j2 j2)) (* 2112 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h6 h6) 
(* j2 j2)) (* 160 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h6 h6) j2) (* 4608 (* 
h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 18048 (* h1 h1 h1)
 h2 (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 23616 (* h1 h1 h1) h2 (* h3 h3
) h4 (* h5 h5 h5) (* j2 j2 j2)) (* 10752 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5 
h5) (* j2 j2)) (* 576 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) j2) (* 17408 (* 
h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 61056 (* h1 h1 h1)
 h2 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 75040 (* h1 h1 h1) h2 (* h3 h3
) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 37296 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) 
h6 (* j2 j2)) (* 5952 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) h6 j2) (* 48 (* h1 
h1 h1) h2 (* h3 h3) h4 (* h5 h5) h6) (* 17408 (* h1 h1 h1) h2 (* h3 h3) h4 h5 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 51584 (* h1 h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6)
 (* j2 j2 j2 j2)) (* 58016 (* h1 h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2
)) (* 29056 (* h1 h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 5248 (* h1 
h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6) j2) (* 96 (* h1 h1 h1) h2 (* h3 h3) h4 h5 
(* h6 h6)) (* 4608 (* h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2))
 (* 10624 (* h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 8384 (* 
h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2)) (* 2624 (* h1 h1 h1) h2 (* 
h3 h3) h4 (* h6 h6 h6) (* j2 j2)) (* 256 (* h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6 
h6) j2) (* 512 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) 
(* 2560 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 4736 
(* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 3840 (* h1 h1 h1) 
h2 (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 1152 (* h1 h1 h1) h2 (* h3 h3) (* 
h5 h5 h5 h5) (* j2 j2)) (* 6144 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2)) (* 29696 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2)) (* 53888 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 
44224 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 14848 (* h1 h1 
h1) h2 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2)) (* 960 (* h1 h1 h1) h2 (* h3 h3) (* 
h5 h5 h5) h6 j2) (* 11264 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2
 j2 j2 j2 j2)) (* 50944 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2)) (* 89120 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2
)) (* 75008 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 30208
 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 4736 (* h1 h1 h1) 
h2 (* h3 h3) (* h5 h5) (* h6 h6) j2) (* 96 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5) 
(* h6 h6)) (* 6144 (* h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 26624 (* h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
45056 (* h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 37440 (* h1 
h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 15552 (* h1 h1 h1) h2 (* h3
 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 2752 (* h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6
) j2) (* 64 (* h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6)) (* 512 (* h1 h1 h1) h2 
(* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2048 (* h1 h1 h1) h2 (* h3 
h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 3200 (* h1 h1 h1) h2 (* h3 h3) (* h6 
h6 h6 h6) (* j2 j2 j2 j2)) (* 2432 (* h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6 h6) (* 
j2 j2 j2)) (* 896 (* h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6 h6) (* j2 j2)) (* 128 
(* h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6 h6) j2) (* 320 (* h1 h1 h1) h2 h3 (* h4 h4
 h4) (* h5 h5) (* j2 j2 j2)) (* 800 (* h1 h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) 
(* j2 j2)) (* 480 (* h1 h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) j2) (* 640 (* h1 h1 
h1) h2 h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 784 (* h1 h1 h1) h2 h3 (* h4 h4 h4
) h5 h6 (* j2 j2)) (* 152 (* h1 h1 h1) h2 h3 (* h4 h4 h4) h5 h6 j2) (* 8 (* h1 
h1 h1) h2 h3 (* h4 h4 h4) h5 h6) (* 320 (* h1 h1 h1) h2 h3 (* h4 h4 h4) (* h6 h6
) (* j2 j2 j2)) (* 64 (* h1 h1 h1) h2 h3 (* h4 h4 h4) (* h6 h6) (* j2 j2)) (* 
640 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 2240 (* h1 h1 
h1) h2 h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 2560 (* h1 h1 h1) h2 h3 (* h4 
h4) (* h5 h5 h5) (* j2 j2)) (* 960 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) j2)
 (* 2560 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 7488 (* 
h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 7712 (* h1 h1 h1) h2 h3 
(* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 2848 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5)
 h6 j2) (* 64 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) h6) (* 2560 (* h1 h1 h1) h2
 h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 5568 (* h1 h1 h1) h2 h3 (* h4 h4)
 h5 (* h6 h6) (* j2 j2 j2)) (* 3696 (* h1 h1 h1) h2 h3 (* h4 h4) h5 (* h6 h6) 
(* j2 j2)) (* 728 (* h1 h1 h1) h2 h3 (* h4 h4) h5 (* h6 h6) j2) (* 40 (* h1 h1 
h1) h2 h3 (* h4 h4) h5 (* h6 h6)) (* 640 (* h1 h1 h1) h2 h3 (* h4 h4) (* h6 h6 
h6) (* j2 j2 j2 j2)) (* 832 (* h1 h1 h1) h2 h3 (* h4 h4) (* h6 h6 h6) (* j2 j2 
j2)) (* 192 (* h1 h1 h1) h2 h3 (* h4 h4) (* h6 h6 h6) (* j2 j2)) (* 128 (* h1 h1
 h1) h2 h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 576 (* h1 h1 h1) h2 h3 h4 
(* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 960 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5 h5) 
(* j2 j2 j2)) (* 704 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5 h5) (* j2 j2)) (* 192 (* 
h1 h1 h1) h2 h3 h4 (* h5 h5 h5 h5) j2) (* 2304 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5
) h6 (* j2 j2 j2 j2 j2)) (* 9952 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5) h6 (* j2 j2 
j2 j2)) (* 16080 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 11568 
(* h1 h1 h1) h2 h3 h4 (* h5 h5 h5) h6 (* j2 j2)) (* 3184 (* h1 h1 h1) h2 h3 h4 
(* h5 h5 h5) h6 j2) (* 48 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5) h6) (* 4352 (* h1 
h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 16832 (* h1 h1 h1) h2
 h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 25184 (* h1 h1 h1) h2 h3 h4 (* h5
 h5) (* h6 h6) (* j2 j2 j2)) (* 17472 (* h1 h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6) 
(* j2 j2)) (* 4960 (* h1 h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6) j2) (* 192 (* h1 h1
 h1) h2 h3 h4 (* h5 h5) (* h6 h6)) (* 2304 (* h1 h1 h1) h2 h3 h4 h5 (* h6 h6 h6)
 (* j2 j2 j2 j2 j2)) (* 7520 (* h1 h1 h1) h2 h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 
j2)) (* 8976 (* h1 h1 h1) h2 h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 4672 (* h1 
h1 h1) h2 h3 h4 h5 (* h6 h6 h6) (* j2 j2)) (* 976 (* h1 h1 h1) h2 h3 h4 h5 (* h6
 h6 h6) j2) (* 64 (* h1 h1 h1) h2 h3 h4 h5 (* h6 h6 h6)) (* 128 (* h1 h1 h1) h2 
h3 h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 384 (* h1 h1 h1) h2 h3 h4 (* h6 h6 
h6 h6) (* j2 j2 j2 j2)) (* 384 (* h1 h1 h1) h2 h3 h4 (* h6 h6 h6 h6) (* j2 j2 j2
)) (* 128 (* h1 h1 h1) h2 h3 h4 (* h6 h6 h6 h6) (* j2 j2)) (* 256 (* h1 h1 h1) 
h2 h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 1408 (* h1 h1 h1) h2 h3 (* h5
 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 3072 (* h1 h1 h1) h2 h3 (* h5 h5 h5 h5) h6 
(* j2 j2 j2 j2)) (* 3328 (* h1 h1 h1) h2 h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 
1792 (* h1 h1 h1) h2 h3 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 384 (* h1 h1 h1) h2 h3 
(* h5 h5 h5 h5) h6 j2) (* 1536 (* h1 h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 8256 (* h1 h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2)) (* 17760 (* h1 h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 
19200 (* h1 h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 10560 (* h1 h1 
h1) h2 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 2496 (* h1 h1 h1) h2 h3 (* h5 h5 
h5) (* h6 h6) j2) (* 96 (* h1 h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6)) (* 1536 (* h1
 h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 8128 (* h1 h1 h1)
 h2 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 17280 (* h1 h1 h1) h2 h3 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 18560 (* h1 h1 h1) h2 h3 (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2)) (* 10240 (* h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6) 
(* j2 j2)) (* 2496 (* h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6) j2) (* 128 (* h1 h1
 h1) h2 h3 (* h5 h5) (* h6 h6 h6)) (* 256 (* h1 h1 h1) h2 h3 h5 (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 1280 (* h1 h1 h1) h2 h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2
 j2 j2)) (* 2592 (* h1 h1 h1) h2 h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 2688 
(* h1 h1 h1) h2 h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 1472 (* h1 h1 h1) h2 h3 
h5 (* h6 h6 h6 h6) (* j2 j2)) (* 384 (* h1 h1 h1) h2 h3 h5 (* h6 h6 h6 h6) j2) 
(* 32 (* h1 h1 h1) h2 h3 h5 (* h6 h6 h6 h6)) (* 80 (* h1 h1 h1) h2 (* h4 h4 h4) 
(* h5 h5) h6 (* j2 j2 j2)) (* 168 (* h1 h1 h1) h2 (* h4 h4 h4) (* h5 h5) h6 (* 
j2 j2)) (* 96 (* h1 h1 h1) h2 (* h4 h4 h4) (* h5 h5) h6 j2) (* 8 (* h1 h1 h1) h2
 (* h4 h4 h4) (* h5 h5) h6) (* 80 (* h1 h1 h1) h2 (* h4 h4 h4) h5 (* h6 h6) (* 
j2 j2 j2)) (* 96 (* h1 h1 h1) h2 (* h4 h4 h4) h5 (* h6 h6) (* j2 j2)) (* 16 (* 
h1 h1 h1) h2 (* h4 h4 h4) h5 (* h6 h6) j2) (* 160 (* h1 h1 h1) h2 (* h4 h4) (* 
h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 512 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5 h5) h6 
(* j2 j2 j2)) (* 576 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 256
 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5 h5) h6 j2) (* 32 (* h1 h1 h1) h2 (* h4 h4) 
(* h5 h5 h5) h6) (* 320 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2)) (* 976 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 
1032 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 416 (* h1 h1 h1
) h2 (* h4 h4) (* h5 h5) (* h6 h6) j2) (* 40 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5)
 (* h6 h6)) (* 160 (* h1 h1 h1) h2 (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) 
(* 368 (* h1 h1 h1) h2 (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 256 (* h1 h1 
h1) h2 (* h4 h4) h5 (* h6 h6 h6) (* j2 j2)) (* 48 (* h1 h1 h1) h2 (* h4 h4) h5 
(* h6 h6 h6) j2) (* 32 (* h1 h1 h1) h2 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2))
 (* 144 (* h1 h1 h1) h2 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 256 (* h1 h1 
h1) h2 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 224 (* h1 h1 h1) h2 h4 (* h5 h5 h5
 h5) h6 (* j2 j2)) (* 96 (* h1 h1 h1) h2 h4 (* h5 h5 h5 h5) h6 j2) (* 16 (* h1 
h1 h1) h2 h4 (* h5 h5 h5 h5) h6) (* 288 (* h1 h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6
) (* j2 j2 j2 j2 j2)) (* 1248 (* h1 h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2
 j2 j2)) (* 2112 (* h1 h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 1728
 (* h1 h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 672 (* h1 h1 h1) h2 h4 
(* h5 h5 h5) (* h6 h6) j2) (* 96 (* h1 h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6)) (* 
288 (* h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1216 (* h1 
h1 h1) h2 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1984 (* h1 h1 h1) h2 h4 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 1536 (* h1 h1 h1) h2 h4 (* h5 h5) (* h6 
h6 h6) (* j2 j2)) (* 544 (* h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6 h6) j2) (* 64 (* 
h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6 h6)) (* 32 (* h1 h1 h1) h2 h4 h5 (* h6 h6 h6 
h6) (* j2 j2 j2 j2 j2)) (* 128 (* h1 h1 h1) h2 h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2
 j2)) (* 192 (* h1 h1 h1) h2 h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 128 (* h1 h1
 h1) h2 h4 h5 (* h6 h6 h6 h6) (* j2 j2)) (* 32 (* h1 h1 h1) h2 h4 h5 (* h6 h6 h6
 h6) j2) (* 32 (* h1 h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 192 (* h1 h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 480 (* 
h1 h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 640 (* h1 h1 h1) h2 
(* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 480 (* h1 h1 h1) h2 (* h5 h5 h5 h5) 
(* h6 h6) (* j2 j2)) (* 192 (* h1 h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6) j2) (* 32 
(* h1 h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6)) (* 64 (* h1 h1 h1) h2 (* h5 h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 384 (* h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6
 h6) (* j2 j2 j2 j2 j2)) (* 960 (* h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2)) (* 1280 (* h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 
960 (* h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 384 (* h1 h1 h1) h2 
(* h5 h5 h5) (* h6 h6 h6) j2) (* 64 (* h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6)) 
(* 32 (* h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 192 
(* h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 480 (* h1 h1 h1
) h2 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 640 (* h1 h1 h1) h2 (* h5 h5)
 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 480 (* h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6 h6) 
(* j2 j2)) (* 192 (* h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6 h6) j2) (* 32 (* h1 h1 
h1) h2 (* h5 h5) (* h6 h6 h6 h6)) (* 4096 (* h1 h1 h1) (* h3 h3 h3 h3) (* h4 h4)
 h5 (* j2 j2 j2 j2 j2)) (* 9216 (* h1 h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 
j2 j2 j2)) (* 5376 (* h1 h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 
1216 (* h1 h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2)) (* 96 (* h1 h1 h1) (* 
h3 h3 h3 h3) (* h4 h4) h5 j2) (* 4096 (* h1 h1 h1) (* h3 h3 h3 h3) (* h4 h4) h6 
(* j2 j2 j2 j2 j2)) (* 3072 (* h1 h1 h1) (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 
j2 j2)) (* 768 (* h1 h1 h1) (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2)) (* 64 (* 
h1 h1 h1) (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2)) (* 8192 (* h1 h1 h1) (* h3 h3 
h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 28672 (* h1 h1 h1) (* h3 h3 h3 h3)
 h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 31232 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h5
 h5) (* j2 j2 j2 j2)) (* 10752 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 
j2 j2)) (* 1152 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2)) (* 16384 
(* h1 h1 h1) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 49152 (* h1 h1 
h1) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 50176 (* h1 h1 h1) (* h3 h3 
h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 23040 (* h1 h1 h1) (* h3 h3 h3 h3) h4 h5 h6 
(* j2 j2 j2)) (* 4864 (* h1 h1 h1) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2)) (* 384 
(* h1 h1 h1) (* h3 h3 h3 h3) h4 h5 h6 j2) (* 8192 (* h1 h1 h1) (* h3 h3 h3 h3) 
h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 12288 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* 
h6 h6) (* j2 j2 j2 j2 j2)) (* 6656 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h6 h6) (* 
j2 j2 j2 j2)) (* 1536 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2)) 
(* 128 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2)) (* 16384 (* h1 h1 h1
) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 73728 (* h1 h1 h1) 
(* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 119808 (* h1 h1 h1) (* h3
 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 83968 (* h1 h1 h1) (* h3 h3 h3 h3
) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 23808 (* h1 h1 h1) (* h3 h3 h3 h3) (* h5 h5) 
h6 (* j2 j2 j2)) (* 2304 (* h1 h1 h1) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2)) 
(* 16384 (* h1 h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
65536 (* h1 h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 99328 
(* h1 h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 73216 (* h1 h1 
h1) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 27904 (* h1 h1 h1) (* h3 h3
 h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 5248 (* h1 h1 h1) (* h3 h3 h3 h3) h5 (* h6
 h6) (* j2 j2)) (* 384 (* h1 h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6) j2) (* 2048 (* 
h1 h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 4096 (* h1 h1 h1) (* 
h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 1664 (* h1 h1 h1) (* h3 h3 h3) (* h4 
h4 h4) h5 (* j2 j2)) (* 192 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 j2) (* 
2048 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2)) (* 1024 (* h1 h1
 h1) (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2)) (* 128 (* h1 h1 h1) (* h3 h3 h3)
 (* h4 h4 h4) h6 (* j2 j2)) (* 7168 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5
) (* j2 j2 j2 j2 j2)) (* 22528 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* 
j2 j2 j2 j2)) (* 20928 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2
)) (* 5088 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 288 (* h1
 h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) j2) (* 14336 (* h1 h1 h1) (* h3 h3 h3) 
(* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 35072 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4)
 h5 h6 (* j2 j2 j2 j2)) (* 27904 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2
 j2 j2)) (* 8912 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 976 (* 
h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 h6 j2) (* 7168 (* h1 h1 h1) (* h3 h3 h3) (* 
h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 8704 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4)
 (* h6 h6) (* j2 j2 j2 j2)) (* 3264 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) (* h6 h6
) (* j2 j2 j2)) (* 384 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2)) 
(* 4096 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 
17408 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 25600 (* 
h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 14592 (* h1 h1 h1) 
(* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2)) (* 2304 (* h1 h1 h1) (* h3 h3 h3) h4 
(* h5 h5 h5) (* j2 j2)) (* 24576 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2
 j2 j2 j2 j2 j2)) (* 97280 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2
 j2 j2)) (* 135936 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) 
(* 78976 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 17280 (* h1 
h1 h1) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 1152 (* h1 h1 h1) (* h3 h3 h3)
 h4 (* h5 h5) h6 j2) (* 24576 (* h1 h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2
 j2 j2 j2 j2)) (* 80896 (* h1 h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2
 j2)) (* 100608 (* h1 h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 
58752 (* h1 h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 15840 (* h1 h1 
h1) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 1568 (* h1 h1 h1) (* h3 h3 h3) h4
 h5 (* h6 h6) j2) (* 4096 (* h1 h1 h1) (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 9216 (* h1 h1 h1) (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2))
 (* 7168 (* h1 h1 h1) (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 2304 (* 
h1 h1 h1) (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2)) (* 256 (* h1 h1 h1) (* h3 
h3 h3) h4 (* h6 h6 h6) (* j2 j2)) (* 8192 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5 h5)
 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 43008 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5 h5) h6
 (* j2 j2 j2 j2 j2 j2)) (* 86016 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2
 j2 j2 j2 j2)) (* 80384 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2
)) (* 33792 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 4608 (* 
h1 h1 h1) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2)) (* 16384 (* h1 h1 h1) (* h3 h3
 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 80896 (* h1 h1 h1) (* h3 
h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 155904 (* h1 h1 h1) (* h3 
h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 147328 (* h1 h1 h1) (* h3 h3 
h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 69760 (* h1 h1 h1) (* h3 h3 h3) (* 
h5 h5) (* h6 h6) (* j2 j2 j2)) (* 14976 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5) (* 
h6 h6) (* j2 j2)) (* 1152 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6) j2) (* 
8192 (* h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
38912 (* h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 72704 
(* h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 68096 (* h1 h1 
h1) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 33536 (* h1 h1 h1) (* h3 h3
 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 8192 (* h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6
 h6) (* j2 j2)) (* 768 (* h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6) j2) (* 128 (* 
h1 h1 h1) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2)) (* 224 (* h1 h1 h1) (* h3 
h3) (* h4 h4 h4 h4) h5 (* j2 j2)) (* 48 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4 h4) 
h5 j2) (* 128 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4 h4) h6 (* j2 j2 j2)) (* 32 (* 
h1 h1 h1) (* h3 h3) (* h4 h4 h4 h4) h6 (* j2 j2)) (* 1024 (* h1 h1 h1) (* h3 h3)
 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 2816 (* h1 h1 h1) (* h3 h3) (* h4 h4
 h4) (* h5 h5) (* j2 j2 j2)) (* 2176 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 
h5) (* j2 j2)) (* 384 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) j2) (* 2048 
(* h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 3840 (* h1 h1 h1) 
(* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 2304 (* h1 h1 h1) (* h3 h3) (* h4 
h4 h4) h5 h6 (* j2 j2)) (* 368 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 h6 j2) (* 
1024 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 896 (* h1
 h1 h1) (* h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2)) (* 160 (* h1 h1 h1) (* h3
 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2)) (* 1792 (* h1 h1 h1) (* h3 h3) (* h4 h4) 
(* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 6976 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 
h5 h5) (* j2 j2 j2 j2)) (* 9120 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) 
(* j2 j2 j2)) (* 4224 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2)) 
(* 288 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) j2) (* 6656 (* h1 h1 h1) 
(* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 22336 (* h1 h1 h1) (* h3
 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 26416 (* h1 h1 h1) (* h3 h3) (* 
h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 12704 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* 
h5 h5) h6 (* j2 j2)) (* 1968 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) h6 j2) 
(* 6656 (* h1 h1 h1) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
17344 (* h1 h1 h1) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 16848 
(* h1 h1 h1) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 6960 (* h1 h1 h1)
 (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 960 (* h1 h1 h1) (* h3 h3) (* h4
 h4) h5 (* h6 h6) j2) (* 1792 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2)) (* 3008 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 
j2 j2)) (* 1536 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2)) (* 
256 (* h1 h1 h1) (* h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2)) (* 512 (* h1 h1 h1)
 (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2560 (* h1 h1 h1) (* h3 
h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 4736 (* h1 h1 h1) (* h3 h3) h4 (* 
h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 3840 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) 
(* j2 j2 j2)) (* 1152 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2)) (* 
6144 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 29184 
(* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 51968 (* h1 h1 
h1) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 41984 (* h1 h1 h1) (* h3 h3
) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 14208 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 
h5) h6 (* j2 j2)) (* 1152 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) h6 j2) (* 11264
 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 47872 
(* h1 h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 79136 (* h1
 h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 62944 (* h1 h1 h1) 
(* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 23584 (* h1 h1 h1) (* h3 h3) 
h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 3168 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5) 
(* h6 h6) j2) (* 6144 (* h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 23040 (* h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 33408 (* h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 23424 (* 
h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 7936 (* h1 h1 h1) (* h3 
h3) h4 h5 (* h6 h6 h6) (* j2 j2)) (* 1024 (* h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6 
h6) j2) (* 512 (* h1 h1 h1) (* h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 1536 (* h1 h1 h1) (* h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1664 
(* h1 h1 h1) (* h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 768 (* h1 h1 h1) 
(* h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 128 (* h1 h1 h1) (* h3 h3) h4 (* 
h6 h6 h6 h6) (* j2 j2)) (* 1024 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2)) (* 6144 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2)) (* 14592 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 
j2)) (* 17152 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 9984
 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 2304 (* h1 h1 h1) 
(* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 4096 (* h1 h1 h1) (* h3 h3) (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 23552 (* h1 h1 h1) (* h3 h3) (* h5 h5
 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 54528 (* h1 h1 h1) (* h3 h3) (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 64384 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2)) (* 40064 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6
) (* j2 j2 j2)) (* 11904 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2)
) (* 1152 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6) j2) (* 4096 (* h1 h1 h1)
 (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 23040 (* h1 h1 h1
) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 52480 (* h1 h1 h1) 
(* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 61696 (* h1 h1 h1) (* h3
 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 39168 (* h1 h1 h1) (* h3 h3) (* 
h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 12544 (* h1 h1 h1) (* h3 h3) (* h5 h5) (* 
h6 h6 h6) (* j2 j2)) (* 1536 (* h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6) j2) 
(* 1024 (* h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
5632 (* h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 12544 
(* h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 14464 (* h1 h1 
h1) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 9088 (* h1 h1 h1) (* h3 h3)
 h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 2944 (* h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6 
h6) (* j2 j2)) (* 384 (* h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6 h6) j2) (* 32 (* h1 
h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 80 (* h1 h1 h1) h3 (* h4 h4
 h4 h4) (* h5 h5) (* j2 j2)) (* 48 (* h1 h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5) j2)
 (* 64 (* h1 h1 h1) h3 (* h4 h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 72 (* h1 h1 h1) h3
 (* h4 h4 h4 h4) h5 h6 (* j2 j2)) (* 8 (* h1 h1 h1) h3 (* h4 h4 h4 h4) h5 h6 j2)
 (* 32 (* h1 h1 h1) h3 (* h4 h4 h4 h4) (* h6 h6) (* j2 j2 j2)) (* 128 (* h1 h1 
h1) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 448 (* h1 h1 h1) h3 (* h4 
h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 512 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5 
h5) (* j2 j2)) (* 192 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) j2) (* 512 (* h1
 h1 h1) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 1376 (* h1 h1 h1) h3 
(* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 1264 (* h1 h1 h1) h3 (* h4 h4 h4) (* 
h5 h5) h6 (* j2 j2)) (* 400 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) h6 j2) (* 512
 (* h1 h1 h1) h3 (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 896 (* h1 h1 h1) 
h3 (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 424 (* h1 h1 h1) h3 (* h4 h4 h4) 
h5 (* h6 h6) (* j2 j2)) (* 40 (* h1 h1 h1) h3 (* h4 h4 h4) h5 (* h6 h6) j2) (* 
128 (* h1 h1 h1) h3 (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 96 (* h1 h1 h1
) h3 (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2)) (* 64 (* h1 h1 h1) h3 (* h4 h4) (* 
h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 288 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5
) (* j2 j2 j2 j2)) (* 480 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)
) (* 352 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 96 (* h1 h1 h1)
 h3 (* h4 h4) (* h5 h5 h5 h5) j2) (* 896 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2)) (* 3696 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 
j2 j2 j2)) (* 5712 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 
3920 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 1008 (* h1 h1 h1) 
h3 (* h4 h4) (* h5 h5 h5) h6 j2) (* 1664 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2)) (* 5824 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5) (* h6 h6)
 (* j2 j2 j2 j2)) (* 7776 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2
 j2)) (* 4672 (* h1 h1 h1) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 1056 
(* h1 h1 h1) h3 (* h4 h4) (* h5 h5) (* h6 h6) j2) (* 896 (* h1 h1 h1) h3 (* h4 
h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2352 (* h1 h1 h1) h3 (* h4 h4) h5 (* 
h6 h6 h6) (* j2 j2 j2 j2)) (* 2096 (* h1 h1 h1) h3 (* h4 h4) h5 (* h6 h6 h6) (* 
j2 j2 j2)) (* 704 (* h1 h1 h1) h3 (* h4 h4) h5 (* h6 h6 h6) (* j2 j2)) (* 64 (* 
h1 h1 h1) h3 (* h4 h4) h5 (* h6 h6 h6) j2) (* 64 (* h1 h1 h1) h3 (* h4 h4) (* h6
 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 128 (* h1 h1 h1) h3 (* h4 h4) (* h6 h6 h6 h6) 
(* j2 j2 j2 j2)) (* 64 (* h1 h1 h1) h3 (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2)) 
(* 256 (* h1 h1 h1) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 1408 (* 
h1 h1 h1) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 3072 (* h1 h1 h1) h3 
h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 3328 (* h1 h1 h1) h3 h4 (* h5 h5 h5 h5
) h6 (* j2 j2 j2)) (* 1792 (* h1 h1 h1) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 
384 (* h1 h1 h1) h3 h4 (* h5 h5 h5 h5) h6 j2) (* 1536 (* h1 h1 h1) h3 h4 (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 7744 (* h1 h1 h1) h3 h4 (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 15648 (* h1 h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6)
 (* j2 j2 j2 j2)) (* 15840 (* h1 h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2
)) (* 8032 (* h1 h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 1632 (* h1 h1
 h1) h3 h4 (* h5 h5 h5) (* h6 h6) j2) (* 1536 (* h1 h1 h1) h3 h4 (* h5 h5) (* h6
 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 7232 (* h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6)
 (* j2 j2 j2 j2 j2)) (* 13568 (* h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2
 j2 j2)) (* 12672 (* h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 
5888 (* h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 1088 (* h1 h1 h1) 
h3 h4 (* h5 h5) (* h6 h6 h6) j2) (* 256 (* h1 h1 h1) h3 h4 h5 (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 1024 (* h1 h1 h1) h3 h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2
 j2 j2)) (* 1568 (* h1 h1 h1) h3 h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 1120 
(* h1 h1 h1) h3 h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 352 (* h1 h1 h1) h3 h4 h5
 (* h6 h6 h6 h6) (* j2 j2)) (* 32 (* h1 h1 h1) h3 h4 h5 (* h6 h6 h6 h6) j2) (* 
256 (* h1 h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1664 
(* h1 h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4480 (* h1 
h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 6400 (* h1 h1 h1) h3 
(* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 5120 (* h1 h1 h1) h3 (* h5 h5 h5 
h5) (* h6 h6) (* j2 j2 j2)) (* 2176 (* h1 h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6) 
(* j2 j2)) (* 384 (* h1 h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6) j2) (* 512 (* h1 h1 
h1) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3328 (* h1 h1 h1) 
h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 8960 (* h1 h1 h1) h3 (* 
h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 12800 (* h1 h1 h1) h3 (* h5 h5 h5)
 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 10240 (* h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6
) (* j2 j2 j2)) (* 4352 (* h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 
768 (* h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6) j2) (* 256 (* h1 h1 h1) h3 (* h5 
h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1664 (* h1 h1 h1) h3 (* h5 h5) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4480 (* h1 h1 h1) h3 (* h5 h5) (* h6 
h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 6400 (* h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6 h6) 
(* j2 j2 j2 j2)) (* 5120 (* h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2))
 (* 2176 (* h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 384 (* h1 h1 h1
) h3 (* h5 h5) (* h6 h6 h6 h6) j2) (* 8 (* h1 h1 h1) (* h4 h4 h4 h4) (* h5 h5) 
h6 (* j2 j2 j2)) (* 16 (* h1 h1 h1) (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 8
 (* h1 h1 h1) (* h4 h4 h4 h4) (* h5 h5) h6 j2) (* 8 (* h1 h1 h1) (* h4 h4 h4 h4)
 h5 (* h6 h6) (* j2 j2 j2)) (* 8 (* h1 h1 h1) (* h4 h4 h4 h4) h5 (* h6 h6) (* j2
 j2)) (* 32 (* h1 h1 h1) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 96 (* 
h1 h1 h1) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 96 (* h1 h1 h1) (* h4 h4
 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 32 (* h1 h1 h1) (* h4 h4 h4) (* h5 h5 h5) h6 
j2) (* 64 (* h1 h1 h1) (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 168 
(* h1 h1 h1) (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 144 (* h1 h1 h1) 
(* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 40 (* h1 h1 h1) (* h4 h4 h4) (* 
h5 h5) (* h6 h6) j2) (* 32 (* h1 h1 h1) (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2
 j2)) (* 56 (* h1 h1 h1) (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 24 (* h1 
h1 h1) (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2)) (* 16 (* h1 h1 h1) (* h4 h4) (* 
h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 64 (* h1 h1 h1) (* h4 h4) (* h5 h5 h5 h5)
 h6 (* j2 j2 j2 j2)) (* 96 (* h1 h1 h1) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2
)) (* 64 (* h1 h1 h1) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 16 (* h1 h1 h1)
 (* h4 h4) (* h5 h5 h5 h5) h6 j2) (* 112 (* h1 h1 h1) (* h4 h4) (* h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2)) (* 432 (* h1 h1 h1) (* h4 h4) (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2)) (* 624 (* h1 h1 h1) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 
j2)) (* 400 (* h1 h1 h1) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 96 (* h1
 h1 h1) (* h4 h4) (* h5 h5 h5) (* h6 h6) j2) (* 112 (* h1 h1 h1) (* h4 h4) (* h5
 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 400 (* h1 h1 h1) (* h4 h4) (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2)) (* 528 (* h1 h1 h1) (* h4 h4) (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2)) (* 304 (* h1 h1 h1) (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2)
) (* 64 (* h1 h1 h1) (* h4 h4) (* h5 h5) (* h6 h6 h6) j2) (* 16 (* h1 h1 h1) (* 
h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 48 (* h1 h1 h1) (* h4 h4) h5 
(* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 48 (* h1 h1 h1) (* h4 h4) h5 (* h6 h6 h6 h6)
 (* j2 j2 j2)) (* 16 (* h1 h1 h1) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2)) (* 32 
(* h1 h1 h1) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 160 (* h1 h1
 h1) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 320 (* h1 h1 h1) h4 (* 
h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 320 (* h1 h1 h1) h4 (* h5 h5 h5 h5) 
(* h6 h6) (* j2 j2 j2)) (* 160 (* h1 h1 h1) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 
j2)) (* 32 (* h1 h1 h1) h4 (* h5 h5 h5 h5) (* h6 h6) j2) (* 64 (* h1 h1 h1) h4 
(* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 320 (* h1 h1 h1) h4 (* h5 h5
 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 640 (* h1 h1 h1) h4 (* h5 h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2)) (* 640 (* h1 h1 h1) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 
j2 j2)) (* 320 (* h1 h1 h1) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 64 (* h1 
h1 h1) h4 (* h5 h5 h5) (* h6 h6 h6) j2) (* 32 (* h1 h1 h1) h4 (* h5 h5) (* h6 h6
 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 160 (* h1 h1 h1) h4 (* h5 h5) (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2)) (* 320 (* h1 h1 h1) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2
 j2)) (* 320 (* h1 h1 h1) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 160 (* 
h1 h1 h1) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 32 (* h1 h1 h1) h4 (* h5 h5
) (* h6 h6 h6 h6) j2) (* 256 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2 
j2 j2)) (* 512 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2)) (* 208 
(* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2)) (* 24 (* h1 h1) (* h2 h2 h2
 h2) (* h3 h3 h3) h5 j2) (* 256 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h6 (* j2 
j2 j2 j2)) (* 384 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2)) (* 144
 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2)) (* 16 (* h1 h1) (* h2 h2 
h2 h2) (* h3 h3 h3) h6 j2) (* 192 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* 
j2 j2 j2)) (* 336 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* j2 j2)) (* 72 (* 
h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h5 j2) (* 192 (* h1 h1) (* h2 h2 h2 h2) (* 
h3 h3) h4 h6 (* j2 j2 j2)) (* 176 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h6 (* 
j2 j2)) (* 32 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h6 j2) (* 128 (* h1 h1) (* 
h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 352 (* h1 h1) (* h2 h2 h2 
h2) (* h3 h3) (* h5 h5) (* j2 j2 j2)) (* 272 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3)
 (* h5 h5) (* j2 j2)) (* 48 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) j2) 
(* 256 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 624 (* h1 
h1) (* h2 h2 h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2)) (* 476 (* h1 h1) (* h2 h2 h2 
h2) (* h3 h3) h5 h6 (* j2 j2)) (* 120 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 h6 
j2) (* 4 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 h6) (* 128 (* h1 h1) (* h2 h2 h2
 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 288 (* h1 h1) (* h2 h2 h2 h2) (* h3
 h3) (* h6 h6) (* j2 j2 j2)) (* 208 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h6 h6
) (* j2 j2)) (* 48 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h6 h6) j2) (* 48 (* h1
 h1) (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2)) (* 120 (* h1 h1) (* h2 h2 h2 
h2) h3 h4 (* h5 h5) (* j2 j2)) (* 72 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h5 h5) 
j2) (* 96 (* h1 h1) (* h2 h2 h2 h2) h3 h4 h5 h6 (* j2 j2 j2)) (* 172 (* h1 h1) 
(* h2 h2 h2 h2) h3 h4 h5 h6 (* j2 j2)) (* 84 (* h1 h1) (* h2 h2 h2 h2) h3 h4 h5 
h6 j2) (* 8 (* h1 h1) (* h2 h2 h2 h2) h3 h4 h5 h6) (* 48 (* h1 h1) (* h2 h2 h2 
h2) h3 h4 (* h6 h6) (* j2 j2 j2)) (* 64 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h6 h6
) (* j2 j2)) (* 16 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h6 h6) j2) (* 16 (* h1 h1)
 (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 56 (* h1 h1) (* h2 h2 h2 h2
) h3 (* h5 h5 h5) (* j2 j2 j2)) (* 64 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5 h5) 
(* j2 j2)) (* 24 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5 h5) j2) (* 64 (* h1 h1) 
(* h2 h2 h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 208 (* h1 h1) (* h2 h2 h2 h2
) h3 (* h5 h5) h6 (* j2 j2 j2)) (* 232 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) h6
 (* j2 j2)) (* 96 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) h6 j2) (* 8 (* h1 h1) 
(* h2 h2 h2 h2) h3 (* h5 h5) h6) (* 64 (* h1 h1) (* h2 h2 h2 h2) h3 h5 (* h6 h6)
 (* j2 j2 j2 j2)) (* 200 (* h1 h1) (* h2 h2 h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2))
 (* 220 (* h1 h1) (* h2 h2 h2 h2) h3 h5 (* h6 h6) (* j2 j2)) (* 96 (* h1 h1) (* 
h2 h2 h2 h2) h3 h5 (* h6 h6) j2) (* 12 (* h1 h1) (* h2 h2 h2 h2) h3 h5 (* h6 h6)
) (* 16 (* h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 48 (* h1 
h1) (* h2 h2 h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2)) (* 48 (* h1 h1) (* h2 h2 h2 h2
) h3 (* h6 h6 h6) (* j2 j2)) (* 16 (* h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6 h6) j2)
 (* 12 (* h1 h1) (* h2 h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 32 (* h1 h1) 
(* h2 h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2)) (* 28 (* h1 h1) (* h2 h2 h2 h2) h4 
(* h5 h5) h6 j2) (* 8 (* h1 h1) (* h2 h2 h2 h2) h4 (* h5 h5) h6) (* 12 (* h1 h1)
 (* h2 h2 h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 28 (* h1 h1) (* h2 h2 h2 h2) 
h4 h5 (* h6 h6) (* j2 j2)) (* 20 (* h1 h1) (* h2 h2 h2 h2) h4 h5 (* h6 h6) j2) 
(* 4 (* h1 h1) (* h2 h2 h2 h2) h4 h5 (* h6 h6)) (* 4 (* h1 h1) (* h2 h2 h2 h2) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 16 (* h1 h1) (* h2 h2 h2 h2) (* h5 h5 h5) h6
 (* j2 j2 j2)) (* 24 (* h1 h1) (* h2 h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2)) (* 16 
(* h1 h1) (* h2 h2 h2 h2) (* h5 h5 h5) h6 j2) (* 4 (* h1 h1) (* h2 h2 h2 h2) (* 
h5 h5 h5) h6) (* 8 (* h1 h1) (* h2 h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)
) (* 32 (* h1 h1) (* h2 h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 48 (* h1 
h1) (* h2 h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 j2)) (* 32 (* h1 h1) (* h2 h2 h2 
h2) (* h5 h5) (* h6 h6) j2) (* 8 (* h1 h1) (* h2 h2 h2 h2) (* h5 h5) (* h6 h6)) 
(* 4 (* h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 16 (* h1 h1) 
(* h2 h2 h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 24 (* h1 h1) (* h2 h2 h2 h2) h5
 (* h6 h6 h6) (* j2 j2)) (* 16 (* h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6 h6) j2) (* 
4 (* h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6 h6)) (* 1024 (* h1 h1) (* h2 h2 h2) (* 
h3 h3 h3 h3) h5 (* j2 j2 j2 j2 j2)) (* 2304 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 
h3) h5 (* j2 j2 j2 j2)) (* 1344 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* j2 
j2 j2)) (* 304 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2)) (* 24 (* h1 
h1) (* h2 h2 h2) (* h3 h3 h3 h3) h5 j2) (* 1024 (* h1 h1) (* h2 h2 h2) (* h3 h3 
h3 h3) h6 (* j2 j2 j2 j2 j2)) (* 1792 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h6 
(* j2 j2 j2 j2)) (* 960 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2 j2)) 
(* 208 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2)) (* 16 (* h1 h1) (* 
h2 h2 h2) (* h3 h3 h3 h3) h6 j2) (* 3072 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 
h5 (* j2 j2 j2 j2)) (* 6144 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 
j2)) (* 2496 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2)) (* 288 (* h1 
h1) (* h2 h2 h2) (* h3 h3 h3) h4 h5 j2) (* 3072 (* h1 h1) (* h2 h2 h2) (* h3 h3 
h3) h4 h6 (* j2 j2 j2 j2)) (* 3328 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h6 (* 
j2 j2 j2)) (* 1088 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2)) (* 112 
(* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h6 j2) (* 1792 (* h1 h1) (* h2 h2 h2) (* 
h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 5632 (* h1 h1) (* h2 h2 h2) (* h3 h3 
h3) (* h5 h5) (* j2 j2 j2 j2)) (* 5232 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h5
 h5) (* j2 j2 j2)) (* 1272 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 
j2)) (* 72 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) j2) (* 3584 (* h1 h1) 
(* h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 9792 (* h1 h1) (* h2 h2 
h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 8448 (* h1 h1) (* h2 h2 h2) (* h3 h3 
h3) h5 h6 (* j2 j2 j2)) (* 2676 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 
j2)) (* 296 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 h6 j2) (* 4 (* h1 h1) (* h2 
h2 h2) (* h3 h3 h3) h5 h6) (* 1792 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h6 h6)
 (* j2 j2 j2 j2 j2)) (* 4224 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h6 h6) (* j2
 j2 j2 j2)) (* 3504 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2)) 
(* 1216 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2)) (* 144 (* h1 h1
) (* h2 h2 h2) (* h3 h3 h3) (* h6 h6) j2) (* 960 (* h1 h1) (* h2 h2 h2) (* h3 h3
) (* h4 h4) h5 (* j2 j2 j2)) (* 1680 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h4 h4) 
h5 (* j2 j2)) (* 360 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 j2) (* 960 
(* h1 h1) (* h2 h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2 j2)) (* 624 (* h1 h1) (* 
h2 h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2)) (* 96 (* h1 h1) (* h2 h2 h2) (* h3 
h3) (* h4 h4) h6 j2) (* 1536 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* j2
 j2 j2 j2)) (* 4224 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2)) 
(* 3264 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2)) (* 576 (* h1 h1
) (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) j2) (* 3072 (* h1 h1) (* h2 h2 h2) (* h3 
h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 7040 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 h6 
(* j2 j2 j2)) (* 5248 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2)) (* 
1172 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 h6 j2) (* 28 (* h1 h1) (* h2 h2 h2) 
(* h3 h3) h4 h5 h6) (* 1536 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 
j2 j2 j2)) (* 2752 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2)) 
(* 1536 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2)) (* 240 (* h1 h1
) (* h2 h2 h2) (* h3 h3) h4 (* h6 h6) j2) (* 448 (* h1 h1) (* h2 h2 h2) (* h3 h3
) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 1744 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* 
h5 h5 h5) (* j2 j2 j2 j2)) (* 2280 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5 h5)
 (* j2 j2 j2)) (* 1056 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2)) 
(* 72 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) j2) (* 1664 (* h1 h1) (* h2 
h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 5968 (* h1 h1) (* h2 h2 h2)
 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 7484 (* h1 h1) (* h2 h2 h2) (* h3 h3
) (* h5 h5) h6 (* j2 j2 j2)) (* 3780 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) 
h6 (* j2 j2)) (* 612 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) h6 j2) (* 12 (* 
h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) h6) (* 1664 (* h1 h1) (* h2 h2 h2) (* h3
 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 5488 (* h1 h1) (* h2 h2 h2) (* h3 h3) 
h5 (* h6 h6) (* j2 j2 j2 j2)) (* 6708 (* h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* h6 
h6) (* j2 j2 j2)) (* 3732 (* h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2
)) (* 884 (* h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* h6 h6) j2) (* 36 (* h1 h1) (* 
h2 h2 h2) (* h3 h3) h5 (* h6 h6)) (* 448 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 
h6 h6) (* j2 j2 j2 j2 j2)) (* 1392 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6 h6)
 (* j2 j2 j2 j2)) (* 1584 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2
 j2)) (* 784 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2)) (* 144 (* 
h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6 h6) j2) (* 240 (* h1 h1) (* h2 h2 h2) h3 
(* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 600 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* 
h5 h5) (* j2 j2)) (* 360 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) j2) (* 
480 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2)) (* 732 (* h1 h1) (* 
h2 h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2)) (* 276 (* h1 h1) (* h2 h2 h2) h3 (* h4 
h4) h5 h6 j2) (* 24 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) h5 h6) (* 240 (* h1 h1) 
(* h2 h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 192 (* h1 h1) (* h2 h2 h2) 
h3 (* h4 h4) (* h6 h6) (* j2 j2)) (* 16 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* 
h6 h6) j2) (* 192 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 
672 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2)) (* 768 (* h1 h1) (* 
h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2)) (* 288 (* h1 h1) (* h2 h2 h2) h3 h4 (* 
h5 h5 h5) j2) (* 768 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2)) 
(* 2384 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2)) (* 2584 (* h1 h1
) (* h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2)) (* 1024 (* h1 h1) (* h2 h2 h2) h3 
h4 (* h5 h5) h6 j2) (* 56 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) h6) (* 768 (* 
h1 h1) (* h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 2048 (* h1 h1) (* h2 
h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2)) (* 1872 (* h1 h1) (* h2 h2 h2) h3 h4 h5 
(* h6 h6) (* j2 j2)) (* 652 (* h1 h1) (* h2 h2 h2) h3 h4 h5 (* h6 h6) j2) (* 60 
(* h1 h1) (* h2 h2 h2) h3 h4 h5 (* h6 h6)) (* 192 (* h1 h1) (* h2 h2 h2) h3 h4 
(* h6 h6 h6) (* j2 j2 j2 j2)) (* 416 (* h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6 h6) 
(* j2 j2 j2)) (* 256 (* h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2)) (* 32 
(* h1 h1) (* h2 h2 h2) h3 h4 (* h6 h6 h6) j2) (* 16 (* h1 h1) (* h2 h2 h2) h3 
(* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 72 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5 
h5) (* j2 j2 j2 j2)) (* 120 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* j2 j2 
j2)) (* 88 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* j2 j2)) (* 24 (* h1 h1) 
(* h2 h2 h2) h3 (* h5 h5 h5 h5) j2) (* 224 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5
) h6 (* j2 j2 j2 j2 j2)) (* 988 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 
j2 j2 j2)) (* 1632 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 
1208 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2)) (* 352 (* h1 h1) (* h2
 h2 h2) h3 (* h5 h5 h5) h6 j2) (* 12 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) h6) 
(* 416 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1744
 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 2800 (* h1 h1
) (* h2 h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 2096 (* h1 h1) (* h2 h2 
h2) h3 (* h5 h5) (* h6 h6) (* j2 j2)) (* 688 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5)
 (* h6 h6) j2) (* 64 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* h6 h6)) (* 224 (* h1
 h1) (* h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 908 (* h1 h1) (* h2 
h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1416 (* h1 h1) (* h2 h2 h2) h3 h5 
(* h6 h6 h6) (* j2 j2 j2)) (* 1040 (* h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6 h6) (* 
j2 j2)) (* 344 (* h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6 h6) j2) (* 36 (* h1 h1) (* 
h2 h2 h2) h3 h5 (* h6 h6 h6)) (* 16 (* h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2)) (* 64 (* h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6 h6) (* j2 j2 j2 
j2)) (* 96 (* h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 64 (* h1 
h1) (* h2 h2 h2) h3 (* h6 h6 h6 h6) (* j2 j2)) (* 16 (* h1 h1) (* h2 h2 h2) h3 
(* h6 h6 h6 h6) j2) (* 60 (* h1 h1) (* h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2
 j2)) (* 144 (* h1 h1) (* h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 108 (* 
h1 h1) (* h2 h2 h2) (* h4 h4) (* h5 h5) h6 j2) (* 24 (* h1 h1) (* h2 h2 h2) (* 
h4 h4) (* h5 h5) h6) (* 60 (* h1 h1) (* h2 h2 h2) (* h4 h4) h5 (* h6 h6) (* j2 
j2 j2)) (* 108 (* h1 h1) (* h2 h2 h2) (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 52 
(* h1 h1) (* h2 h2 h2) (* h4 h4) h5 (* h6 h6) j2) (* 4 (* h1 h1) (* h2 h2 h2) 
(* h4 h4) h5 (* h6 h6)) (* 48 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2
 j2 j2)) (* 172 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 228 
(* h1 h1) (* h2 h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2)) (* 132 (* h1 h1) (* h2 h2 
h2) h4 (* h5 h5 h5) h6 j2) (* 28 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5 h5) h6) (* 
96 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 340 (* h1 
h1) (* h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 444 (* h1 h1) (* h2 h2 
h2) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 252 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5)
 (* h6 h6) j2) (* 52 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5) (* h6 h6)) (* 48 (* h1 
h1) (* h2 h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 152 (* h1 h1) (* h2 h2 
h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 168 (* h1 h1) (* h2 h2 h2) h4 h5 (* h6 
h6 h6) (* j2 j2)) (* 72 (* h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6 h6) j2) (* 8 (* h1
 h1) (* h2 h2 h2) h4 h5 (* h6 h6 h6)) (* 4 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5 h5
) h6 (* j2 j2 j2 j2 j2)) (* 20 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5 h5) h6 (* j2 
j2 j2 j2)) (* 40 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 40 
(* h1 h1) (* h2 h2 h2) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 20 (* h1 h1) (* h2 h2 h2
) (* h5 h5 h5 h5) h6 j2) (* 4 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5 h5) h6) (* 28 
(* h1 h1) (* h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 140 (* h1 
h1) (* h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 280 (* h1 h1) (* h2 
h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 280 (* h1 h1) (* h2 h2 h2) (* h5 
h5 h5) (* h6 h6) (* j2 j2)) (* 140 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5) (* h6 h6)
 j2) (* 28 (* h1 h1) (* h2 h2 h2) (* h5 h5 h5) (* h6 h6)) (* 28 (* h1 h1) (* h2 
h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 140 (* h1 h1) (* h2 h2 h2) 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 280 (* h1 h1) (* h2 h2 h2) (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2)) (* 280 (* h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6 h6) 
(* j2 j2)) (* 140 (* h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6 h6) j2) (* 28 (* h1 
h1) (* h2 h2 h2) (* h5 h5) (* h6 h6 h6)) (* 4 (* h1 h1) (* h2 h2 h2) h5 (* h6 h6
 h6 h6) (* j2 j2 j2 j2 j2)) (* 20 (* h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6 h6) (* 
j2 j2 j2 j2)) (* 40 (* h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 
40 (* h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2)) (* 20 (* h1 h1) (* h2 h2
 h2) h5 (* h6 h6 h6 h6) j2) (* 4 (* h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6 h6)) (* 
7168 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 16128 (* 
h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2)) (* 9408 (* h1 h1) (* h2 
h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2)) (* 2128 (* h1 h1) (* h2 h2) (* h3 h3 h3 
h3) h4 h5 (* j2 j2)) (* 168 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h5 j2) (* 
7168 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 9472 (* h1
 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 4416 (* h1 h1) (* h2 h2
) (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2)) (* 880 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3)
 h4 h6 (* j2 j2)) (* 64 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h6 j2) (* 4096 
(* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 14336 
(* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 15616 (* h1
 h1) (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 5376 (* h1 h1) (* 
h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2)) (* 576 (* h1 h1) (* h2 h2) (* h3 
h3 h3 h3) (* h5 h5) (* j2 j2)) (* 8192 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 h6
 (* j2 j2 j2 j2 j2 j2)) (* 24576 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2
 j2 j2 j2 j2)) (* 24320 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2
)) (* 9984 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2)) (* 1808 (* h1
 h1) (* h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2)) (* 120 (* h1 h1) (* h2 h2) (* h3
 h3 h3 h3) h5 h6 j2) (* 4096 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2
 j2 j2 j2 j2 j2)) (* 10240 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 
j2 j2 j2 j2)) (* 9728 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 
j2)) (* 4480 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2)) (* 976 
(* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2)) (* 80 (* h1 h1) (* h2 
h2) (* h3 h3 h3 h3) (* h6 h6) j2) (* 6656 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4
 h4) h5 (* j2 j2 j2 j2)) (* 13312 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 
(* j2 j2 j2)) (* 5408 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2)) 
(* 624 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 j2) (* 6656 (* h1 h1) (* h2
 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2)) (* 5120 (* h1 h1) (* h2 h2) (* 
h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2)) (* 1312 (* h1 h1) (* h2 h2) (* h3 h3 h3) 
(* h4 h4) h6 (* j2 j2)) (* 112 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h6 j2)
 (* 9472 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 
29440 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 27408 
(* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 7176 (* h1 h1) 
(* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2)) (* 504 (* h1 h1) (* h2 h2) (* h3 
h3 h3) h4 (* h5 h5) j2) (* 18944 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2
 j2 j2 j2 j2)) (* 49600 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2
)) (* 42944 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 14572 (* 
h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2)) (* 1724 (* h1 h1) (* h2 h2) 
(* h3 h3 h3) h4 h5 h6 j2) (* 16 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 h6) (* 
9472 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 17024 
(* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 11088 (* h1 h1
) (* h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2)) (* 2944 (* h1 h1) (* h2 h2) 
(* h3 h3 h3) h4 (* h6 h6) (* j2 j2)) (* 272 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 
(* h6 h6) j2) (* 2048 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 
j2 j2 j2)) (* 8704 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 
j2)) (* 12800 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 
7296 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2)) (* 1152 (* h1 
h1) (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2)) (* 10240 (* h1 h1) (* h2 h2) 
(* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 40960 (* h1 h1) (* h2 h2) 
(* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 58112 (* h1 h1) (* h2 h2) (* h3
 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 34208 (* h1 h1) (* h2 h2) (* h3 h3 h3) 
(* h5 h5) h6 (* j2 j2 j2)) (* 7248 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) h6
 (* j2 j2)) (* 432 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) h6 j2) (* 10240 
(* h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 36864 
(* h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 49792 (* h1
 h1) (* h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 31792 (* h1 h1) (* 
h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 9788 (* h1 h1) (* h2 h2) (* h3
 h3 h3) h5 (* h6 h6) (* j2 j2)) (* 1184 (* h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* 
h6 h6) j2) (* 20 (* h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* h6 h6)) (* 2048 (* h1 h1
) (* h2 h2) (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6656 (* h1 h1) 
(* h2 h2) (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 8320 (* h1 h1) (* h2 
h2) (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 5024 (* h1 h1) (* h2 h2) (* h3
 h3 h3) (* h6 h6 h6) (* j2 j2 j2)) (* 1472 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* 
h6 h6 h6) (* j2 j2)) (* 160 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6 h6) j2) 
(* 960 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 1680 (* h1
 h1) (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2)) (* 360 (* h1 h1) (* h2 h2) 
(* h3 h3) (* h4 h4 h4) h5 j2) (* 960 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4 h4) 
h6 (* j2 j2 j2)) (* 368 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4 h4) h6 (* j2 j2))
 (* 32 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4 h4) h6 j2) (* 3328 (* h1 h1) (* h2
 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 9152 (* h1 h1) (* h2 h2) 
(* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 7072 (* h1 h1) (* h2 h2) (* h3 h3
) (* h4 h4) (* h5 h5) (* j2 j2)) (* 1248 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4)
 (* h5 h5) j2) (* 6656 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2
 j2)) (* 13920 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 
9560 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 1876 (* h1 h1) 
(* h2 h2) (* h3 h3) (* h4 h4) h5 h6 j2) (* 28 (* h1 h1) (* h2 h2) (* h3 h3) (* 
h4 h4) h5 h6) (* 3328 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2
 j2 j2)) (* 4416 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2))
 (* 1520 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2)) (* 144 (* 
h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) j2) (* 2368 (* h1 h1) (* h2 h2) 
(* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 9136 (* h1 h1) (* h2 h2) (* h3 
h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 11928 (* h1 h1) (* h2 h2) (* h3 h3) h4 
(* h5 h5 h5) (* j2 j2 j2)) (* 5664 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5 h5)
 (* j2 j2)) (* 504 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) j2) (* 8576 (* 
h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 30000 (* h1 h1
) (* h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 37332 (* h1 h1) (* h2 
h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 19112 (* h1 h1) (* h2 h2) (* h3 
h3) h4 (* h5 h5) h6 (* j2 j2)) (* 3252 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5
) h6 j2) (* 48 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) h6) (* 8576 (* h1 h1) 
(* h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 25808 (* h1 h1) (* h2
 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 29468 (* h1 h1) (* h2 h2) (* 
h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 15012 (* h1 h1) (* h2 h2) (* h3 h3) h4 
h5 (* h6 h6) (* j2 j2)) (* 2828 (* h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* h6 h6) j2
) (* 68 (* h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* h6 h6)) (* 2368 (* h1 h1) (* h2 
h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 5712 (* h1 h1) (* h2 h2) 
(* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 4816 (* h1 h1) (* h2 h2) (* h3 h3)
 h4 (* h6 h6 h6) (* j2 j2 j2)) (* 1664 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6
 h6) (* j2 j2)) (* 192 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6 h6) j2) (* 256 
(* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1280 (* 
h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 2368 (* h1 h1)
 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 1920 (* h1 h1) (* h2 h2
) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 576 (* h1 h1) (* h2 h2) (* h3 h3) 
(* h5 h5 h5 h5) (* j2 j2)) (* 2560 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) h6
 (* j2 j2 j2 j2 j2 j2)) (* 12288 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2)) (* 22224 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2
 j2 j2 j2)) (* 18328 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2))
 (* 6336 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2)) (* 504 (* h1 
h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) h6 j2) (* 4608 (* h1 h1) (* h2 h2) (* h3 h3
) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 20736 (* h1 h1) (* h2 h2) (* h3 
h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 36240 (* h1 h1) (* h2 h2) (* h3 
h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 30672 (* h1 h1) (* h2 h2) (* h3 h3) 
(* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 12584 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 
h5) (* h6 h6) (* j2 j2)) (* 2080 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* h6 
h6) j2) (* 56 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6)) (* 2560 (* h1 
h1) (* h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 11008 (* h1 h1
) (* h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 18624 (* h1 h1) (* 
h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 15656 (* h1 h1) (* h2 h2) 
(* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 6712 (* h1 h1) (* h2 h2) (* h3 h3) h5
 (* h6 h6 h6) (* j2 j2)) (* 1272 (* h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6 h6) 
j2) (* 40 (* h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6 h6)) (* 256 (* h1 h1) (* h2 
h2) (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1024 (* h1 h1) (* h2 h2)
 (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1616 (* h1 h1) (* h2 h2) (* h3
 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 1264 (* h1 h1) (* h2 h2) (* h3 h3) (* 
h6 h6 h6 h6) (* j2 j2 j2)) (* 496 (* h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6 h6) 
(* j2 j2)) (* 80 (* h1 h1) (* h2 h2) (* h3 h3) (* h6 h6 h6 h6) j2) (* 240 (* h1 
h1) (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 600 (* h1 h1) (* h2 h2)
 h3 (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 360 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4)
 (* h5 h5) j2) (* 480 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2)) 
(* 604 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2)) (* 132 (* h1 h1) (* 
h2 h2) h3 (* h4 h4 h4) h5 h6 j2) (* 8 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) h5 h6)
 (* 240 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) (* h6 h6) (* j2 j2 j2)) (* 64 (* h1 
h1) (* h2 h2) h3 (* h4 h4 h4) (* h6 h6) (* j2 j2)) (* 416 (* h1 h1) (* h2 h2) h3
 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 1456 (* h1 h1) (* h2 h2) h3 (* h4 h4
) (* h5 h5 h5) (* j2 j2 j2)) (* 1664 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5 
h5) (* j2 j2)) (* 624 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) j2) (* 1664 
(* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 4832 (* h1 h1)
 (* h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 4896 (* h1 h1) (* h2 h2) 
h3 (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 1784 (* h1 h1) (* h2 h2) h3 (* h4 h4) 
(* h5 h5) h6 j2) (* 56 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) h6) (* 1664 
(* h1 h1) (* h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 3664 (* h1 h1)
 (* h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 2508 (* h1 h1) (* h2 h2) 
h3 (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 544 (* h1 h1) (* h2 h2) h3 (* h4 h4) h5 
(* h6 h6) j2) (* 36 (* h1 h1) (* h2 h2) h3 (* h4 h4) h5 (* h6 h6)) (* 416 (* h1 
h1) (* h2 h2) h3 (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 592 (* h1 h1) (* h2 
h2) h3 (* h4 h4) (* h6 h6 h6) (* j2 j2 j2)) (* 176 (* h1 h1) (* h2 h2) h3 (* h4 
h4) (* h6 h6 h6) (* j2 j2)) (* 112 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* 
j2 j2 j2 j2 j2)) (* 504 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2
)) (* 840 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2)) (* 616 (* h1 
h1) (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2)) (* 168 (* h1 h1) (* h2 h2) h3 h4 
(* h5 h5 h5 h5) j2) (* 1184 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2)) (* 5060 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) 
(* 8156 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 5916 (* h1 h1
) (* h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2)) (* 1684 (* h1 h1) (* h2 h2) h3 h4 
(* h5 h5 h5) h6 j2) (* 48 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) h6) (* 2144 (* 
h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 8336 (* h1 h1)
 (* h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 12544 (* h1 h1) (* h2 
h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 8784 (* h1 h1) (* h2 h2) h3 h4 
(* h5 h5) (* h6 h6) (* j2 j2)) (* 2560 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* h6
 h6) j2) (* 128 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* h6 h6)) (* 1184 (* h1 h1)
 (* h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 3956 (* h1 h1) (* h2 h2)
 h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 4888 (* h1 h1) (* h2 h2) h3 h4 h5 (* 
h6 h6 h6) (* j2 j2 j2)) (* 2692 (* h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 
j2)) (* 624 (* h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6 h6) j2) (* 48 (* h1 h1) (* h2 
h2) h3 h4 h5 (* h6 h6 h6)) (* 112 (* h1 h1) (* h2 h2) h3 h4 (* h6 h6 h6 h6) (* 
j2 j2 j2 j2 j2)) (* 336 (* h1 h1) (* h2 h2) h3 h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2
)) (* 336 (* h1 h1) (* h2 h2) h3 h4 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 112 (* h1 
h1) (* h2 h2) h3 h4 (* h6 h6 h6 h6) (* j2 j2)) (* 128 (* h1 h1) (* h2 h2) h3 (* 
h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 704 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5
 h5) h6 (* j2 j2 j2 j2 j2)) (* 1536 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) h6 
(* j2 j2 j2 j2)) (* 1664 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2))
 (* 896 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 192 (* h1 h1) 
(* h2 h2) h3 (* h5 h5 h5 h5) h6 j2) (* 640 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3424 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2)) (* 7348 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* h6 h6)
 (* j2 j2 j2 j2)) (* 7952 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2
 j2)) (* 4408 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 1072 
(* h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* h6 h6) j2) (* 52 (* h1 h1) (* h2 h2) h3 
(* h5 h5 h5) (* h6 h6)) (* 640 (* h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 3360 (* h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2)) (* 7112 (* h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2)) (* 7648 (* h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 4272
 (* h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 1088 (* h1 h1) (* 
h2 h2) h3 (* h5 h5) (* h6 h6 h6) j2) (* 72 (* h1 h1) (* h2 h2) h3 (* h5 h5) (* 
h6 h6 h6)) (* 128 (* h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2
)) (* 640 (* h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1300 
(* h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 1360 (* h1 h1) (* 
h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 760 (* h1 h1) (* h2 h2) h3 h5 (* 
h6 h6 h6 h6) (* j2 j2)) (* 208 (* h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6 h6) j2) (* 
20 (* h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6 h6)) (* 60 (* h1 h1) (* h2 h2) (* h4 h4
 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 128 (* h1 h1) (* h2 h2) (* h4 h4 h4) (* h5 h5
) h6 (* j2 j2)) (* 76 (* h1 h1) (* h2 h2) (* h4 h4 h4) (* h5 h5) h6 j2) (* 8 (* 
h1 h1) (* h2 h2) (* h4 h4 h4) (* h5 h5) h6) (* 60 (* h1 h1) (* h2 h2) (* h4 h4 
h4) h5 (* h6 h6) (* j2 j2 j2)) (* 76 (* h1 h1) (* h2 h2) (* h4 h4 h4) h5 (* h6 
h6) (* j2 j2)) (* 16 (* h1 h1) (* h2 h2) (* h4 h4 h4) h5 (* h6 h6) j2) (* 104 
(* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 340 (* h1 h1) 
(* h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 396 (* h1 h1) (* h2 h2) (* 
h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 188 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5 
h5) h6 j2) (* 28 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5 h5) h6) (* 208 (* h1 h1)
 (* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 640 (* h1 h1) (* h2
 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 688 (* h1 h1) (* h2 h2) (* 
h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 288 (* h1 h1) (* h2 h2) (* h4 h4) (* h5
 h5) (* h6 h6) j2) (* 32 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6)) (* 
104 (* h1 h1) (* h2 h2) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 252 (* h1 
h1) (* h2 h2) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 192 (* h1 h1) (* h2 h2)
 (* h4 h4) h5 (* h6 h6 h6) (* j2 j2)) (* 44 (* h1 h1) (* h2 h2) (* h4 h4) h5 (* 
h6 h6 h6) j2) (* 28 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)
) (* 128 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 232 (* h1
 h1) (* h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 208 (* h1 h1) (* h2 h2) h4
 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 92 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5 h5) h6 
j2) (* 16 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5 h5) h6) (* 148 (* h1 h1) (* h2 h2) 
h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 652 (* h1 h1) (* h2 h2) h4 (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 1128 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5)
 (* h6 h6) (* j2 j2 j2)) (* 952 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5) (* h6 h6) 
(* j2 j2)) (* 388 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5) (* h6 h6) j2) (* 60 (* h1 
h1) (* h2 h2) h4 (* h5 h5 h5) (* h6 h6)) (* 148 (* h1 h1) (* h2 h2) h4 (* h5 h5)
 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 632 (* h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2)) (* 1048 (* h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2)) (* 832 (* h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2)) 
(* 308 (* h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6 h6) j2) (* 40 (* h1 h1) (* h2 
h2) h4 (* h5 h5) (* h6 h6 h6)) (* 28 (* h1 h1) (* h2 h2) h4 h5 (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2)) (* 112 (* h1 h1) (* h2 h2) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2
 j2)) (* 168 (* h1 h1) (* h2 h2) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 112 (* 
h1 h1) (* h2 h2) h4 h5 (* h6 h6 h6 h6) (* j2 j2)) (* 28 (* h1 h1) (* h2 h2) h4 
h5 (* h6 h6 h6 h6) j2) (* 16 (* h1 h1) (* h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* j2
 j2 j2 j2 j2 j2)) (* 96 (* h1 h1) (* h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2)) (* 240 (* h1 h1) (* h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2))
 (* 320 (* h1 h1) (* h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 240 (* h1
 h1) (* h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 96 (* h1 h1) (* h2 h2) 
(* h5 h5 h5 h5) (* h6 h6) j2) (* 16 (* h1 h1) (* h2 h2) (* h5 h5 h5 h5) (* h6 h6
)) (* 32 (* h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 192 (* h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 480 
(* h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 640 (* h1 h1) 
(* h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 480 (* h1 h1) (* h2 h2) (* 
h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 192 (* h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 
h6 h6) j2) (* 32 (* h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6 h6)) (* 16 (* h1 h1) 
(* h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 96 (* h1 h1) (* h2
 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 240 (* h1 h1) (* h2 h2) 
(* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 320 (* h1 h1) (* h2 h2) (* h5 h5) 
(* h6 h6 h6 h6) (* j2 j2 j2)) (* 240 (* h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6 
h6) (* j2 j2)) (* 96 (* h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6 h6) j2) (* 16 (* 
h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6 h6)) (* 7168 (* h1 h1) h2 (* h3 h3 h3 h3)
 (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 16128 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4
) h5 (* j2 j2 j2 j2)) (* 9408 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2
 j2)) (* 2128 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2)) (* 168 (* h1 
h1) h2 (* h3 h3 h3 h3) (* h4 h4) h5 j2) (* 7168 (* h1 h1) h2 (* h3 h3 h3 h3) (* 
h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 6400 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h6 
(* j2 j2 j2 j2)) (* 2112 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2))
 (* 304 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2)) (* 16 (* h1 h1) h2 
(* h3 h3 h3 h3) (* h4 h4) h6 j2) (* 12288 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h5 
h5) (* j2 j2 j2 j2 j2 j2)) (* 43008 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h5 h5) 
(* j2 j2 j2 j2 j2)) (* 46848 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 
j2 j2)) (* 16128 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 1728
 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2)) (* 24576 (* h1 h1) h2 (* 
h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 70656 (* h1 h1) h2 (* h3 h3 h3 
h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 67584 (* h1 h1) h2 (* h3 h3 h3 h3) h4 h5 h6 
(* j2 j2 j2 j2)) (* 28992 (* h1 h1) h2 (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2)) 
(* 5760 (* h1 h1) h2 (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2)) (* 432 (* h1 h1) h2 (* 
h3 h3 h3 h3) h4 h5 h6 j2) (* 12288 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 21504 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 
j2 j2 j2)) (* 14592 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) 
(* 4800 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2)) (* 768 (* h1 h1)
 h2 (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2)) (* 48 (* h1 h1) h2 (* h3 h3 h3 h3) 
h4 (* h6 h6) j2) (* 2048 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 
j2 j2 j2 j2)) (* 9728 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 
j2 j2)) (* 16128 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) 
(* 10368 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 1728 (* 
h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2)) (* 14336 (* h1 h1) h2 (* h3
 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 62976 (* h1 h1) h2 (* h3 h3
 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 99328 (* h1 h1) h2 (* h3 h3 h3 h3
) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 67200 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 
h5) h6 (* j2 j2 j2 j2)) (* 18432 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) h6 (* j2
 j2 j2)) (* 1728 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2)) (* 14336 
(* h1 h1) h2 (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 55808 (* 
h1 h1) h2 (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 82176 (* h1 h1)
 h2 (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 59136 (* h1 h1) h2 (* h3
 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 22176 (* h1 h1) h2 (* h3 h3 h3 h3) 
h5 (* h6 h6) (* j2 j2 j2)) (* 4080 (* h1 h1) h2 (* h3 h3 h3 h3) h5 (* h6 h6) (* 
j2 j2)) (* 288 (* h1 h1) h2 (* h3 h3 h3 h3) h5 (* h6 h6) j2) (* 2048 (* h1 h1) 
h2 (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 6656 (* h1 h1) h2 
(* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 8704 (* h1 h1) h2 (* h3 
h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 5888 (* h1 h1) h2 (* h3 h3 h3 h3) 
(* h6 h6 h6) (* j2 j2 j2 j2)) (* 2176 (* h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6 h6) 
(* j2 j2 j2)) (* 416 (* h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2)) (* 32 
(* h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6 h6) j2) (* 3072 (* h1 h1) h2 (* h3 h3 h3) 
(* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 6144 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) 
h5 (* j2 j2 j2)) (* 2496 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2)) 
(* 288 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h5 j2) (* 3072 (* h1 h1) h2 (* h3 
h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2)) (* 1792 (* h1 h1) h2 (* h3 h3 h3) (* h4 
h4 h4) h6 (* j2 j2 j2)) (* 320 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 
j2)) (* 16 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h6 j2) (* 9472 (* h1 h1) h2 
(* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 29440 (* h1 h1) h2 (* h3
 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 27408 (* h1 h1) h2 (* h3 h3 h3) 
(* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 7176 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) 
(* h5 h5) (* j2 j2)) (* 504 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) j2) 
(* 18944 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 45504 
(* h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 35712 (* h1 h1) h2
 (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 11052 (* h1 h1) h2 (* h3 h3 h3) 
(* h4 h4) h5 h6 (* j2 j2)) (* 1184 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 h6 j2)
 (* 4 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 h6) (* 9472 (* h1 h1) h2 (* h3 h3 
h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 13440 (* h1 h1) h2 (* h3 h3 h3) 
(* h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 6096 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4)
 (* h6 h6) (* j2 j2 j2)) (* 1088 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h6 h6) 
(* j2 j2)) (* 64 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h6 h6) j2) (* 6144 (* h1
 h1) h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 26112 (* h1 h1) 
h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 38400 (* h1 h1) h2 (* h3 
h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 21888 (* h1 h1) h2 (* h3 h3 h3) h4 
(* h5 h5 h5) (* j2 j2 j2)) (* 3456 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* 
j2 j2)) (* 24576 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)
) (* 94976 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
131456 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 77904 (* h1
 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 18120 (* h1 h1) h2 (* h3 
h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 1368 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5)
 h6 j2) (* 24576 (* h1 h1) h2 (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)
) (* 79872 (* h1 h1) h2 (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
99328 (* h1 h1) h2 (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 58432 (* h1 
h1) h2 (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 15936 (* h1 h1) h2 (* h3 h3
 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 1644 (* h1 h1) h2 (* h3 h3 h3) h4 h5 (* h6 h6
) j2) (* 12 (* h1 h1) h2 (* h3 h3 h3) h4 h5 (* h6 h6)) (* 6144 (* h1 h1) h2 (* 
h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 15104 (* h1 h1) h2 (* h3 h3 
h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 13632 (* h1 h1) h2 (* h3 h3 h3) h4 
(* h6 h6 h6) (* j2 j2 j2 j2)) (* 5696 (* h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6 h6) 
(* j2 j2 j2)) (* 1104 (* h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2)) (* 80
 (* h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6 h6) j2) (* 512 (* h1 h1) h2 (* h3 h3 h3) 
(* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 2816 (* h1 h1) h2 (* h3 h3 h3) (* 
h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 5760 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 
h5 h5) (* j2 j2 j2 j2 j2)) (* 5184 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* 
j2 j2 j2 j2)) (* 1728 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2)) 
(* 7168 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
37248 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 73600 
(* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 67808 (* h1 h1)
 h2 (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 28032 (* h1 h1) h2 (* h3 h3
 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 3744 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5
) h6 (* j2 j2)) (* 13312 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 64512 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2
 j2 j2 j2 j2)) (* 122112 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2)) (* 113792 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2)) (* 53664 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 
11696 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 912 (* h1 h1) 
h2 (* h3 h3 h3) (* h5 h5) (* h6 h6) j2) (* 7168 (* h1 h1) h2 (* h3 h3 h3) h5 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 32640 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 59264 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6 h6)
 (* j2 j2 j2 j2 j2)) (* 54912 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2
 j2 j2)) (* 27456 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 
7064 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 736 (* h1 h1) h2 
(* h3 h3 h3) h5 (* h6 h6 h6) j2) (* 8 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6 h6))
 (* 512 (* h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
2048 (* h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3328 
(* h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2816 (* h1 h1) 
h2 (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 1312 (* h1 h1) h2 (* h3 h3 
h3) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 320 (* h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6 
h6) (* j2 j2)) (* 32 (* h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6 h6) j2) (* 192 (* h1 
h1) h2 (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2)) (* 336 (* h1 h1) h2 (* h3 h3) 
(* h4 h4 h4 h4) h5 (* j2 j2)) (* 72 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4 h4) h5 j2
) (* 192 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4 h4) h6 (* j2 j2 j2)) (* 48 (* h1 h1)
 h2 (* h3 h3) (* h4 h4 h4 h4) h6 (* j2 j2)) (* 1536 (* h1 h1) h2 (* h3 h3) (* h4
 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 4224 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) 
(* h5 h5) (* j2 j2 j2)) (* 3264 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) 
(* j2 j2)) (* 576 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) j2) (* 3072 (* 
h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 5632 (* h1 h1) h2 (* 
h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 3168 (* h1 h1) h2 (* h3 h3) (* h4 h4 
h4) h5 h6 (* j2 j2)) (* 524 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 h6 j2) (* 4 
(* h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 h6) (* 1536 (* h1 h1) h2 (* h3 h3) (* h4 
h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 1344 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) 
(* h6 h6) (* j2 j2 j2)) (* 256 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) (* h6 h6) (* 
j2 j2)) (* 2368 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)
) (* 9136 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 
11928 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 5664 (* h1 
h1) h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 504 (* h1 h1) h2 (* h3 h3)
 (* h4 h4) (* h5 h5 h5) j2) (* 8576 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) 
h6 (* j2 j2 j2 j2 j2)) (* 28336 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) h6 
(* j2 j2 j2 j2)) (* 33092 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2
 j2)) (* 15732 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 2412 
(* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) h6 j2) (* 12 (* h1 h1) h2 (* h3 h3) 
(* h4 h4) (* h5 h5) h6) (* 8576 (* h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* 22160 (* h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2
 j2 j2 j2)) (* 20748 (* h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2))
 (* 8428 (* h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 1256 (* h1 
h1) h2 (* h3 h3) (* h4 h4) h5 (* h6 h6) j2) (* 16 (* h1 h1) h2 (* h3 h3) (* h4 
h4) h5 (* h6 h6)) (* 2368 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2
 j2 j2 j2)) (* 4240 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2
)) (* 2320 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2)) (* 400 
(* h1 h1) h2 (* h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2)) (* 768 (* h1 h1) h2 (* 
h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 3840 (* h1 h1) h2 (* h3 h3) 
h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 7104 (* h1 h1) h2 (* h3 h3) h4 (* h5 
h5 h5 h5) (* j2 j2 j2 j2)) (* 5760 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* 
j2 j2 j2)) (* 1728 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2)) (* 6144 
(* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 28736 (* h1 
h1) h2 (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 50912 (* h1 h1) h2 
(* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 41664 (* h1 h1) h2 (* h3 h3) h4
 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 14784 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) 
h6 (* j2 j2)) (* 1440 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) h6 j2) (* 10752 (* 
h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 45312 (* h1
 h1) h2 (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 74896 (* h1 h1) 
h2 (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 60076 (* h1 h1) h2 (* h3
 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 22956 (* h1 h1) h2 (* h3 h3) h4 (* 
h5 h5) (* h6 h6) (* j2 j2)) (* 3252 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* h6 h6
) j2) (* 36 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* h6 h6)) (* 6144 (* h1 h1) h2 
(* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 22592 (* h1 h1) h2 (* h3 
h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 32544 (* h1 h1) h2 (* h3 h3) h4 h5
 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 23120 (* h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6
) (* j2 j2 j2)) (* 8204 (* h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2)) (* 
1200 (* h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6) j2) (* 20 (* h1 h1) h2 (* h3 h3) 
h4 h5 (* h6 h6 h6)) (* 768 (* h1 h1) h2 (* h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2
 j2 j2 j2)) (* 2304 (* h1 h1) h2 (* h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)
) (* 2496 (* h1 h1) h2 (* h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 1152 (* 
h1 h1) h2 (* h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 192 (* h1 h1) h2 (* h3 
h3) h4 (* h6 h6 h6 h6) (* j2 j2)) (* 896 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 5376 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 12768 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* 15008 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)
) (* 8736 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 2016 (* h1 
h1) h2 (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 3328 (* h1 h1) h2 (* h3 h3) 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 18976 (* h1 h1) h2 (* h3 h3)
 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 43600 (* h1 h1) h2 (* h3 h3) 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 51184 (* h1 h1) h2 (* h3 h3) (* h5
 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 31792 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2)) (* 9520 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* h6 h6) 
(* j2 j2)) (* 960 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* h6 h6) j2) (* 3328 (* 
h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 18272 
(* h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 40896 
(* h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 47648 (* h1
 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 30392 (* h1 h1) h2 
(* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 10056 (* h1 h1) h2 (* h3 h3) 
(* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 1384 (* h1 h1) h2 (* h3 h3) (* h5 h5) (* h6
 h6 h6) j2) (* 24 (* h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6 h6)) (* 896 (* h1 h1
) h2 (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4736 (* h1 h1) h2
 (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 10272 (* h1 h1) h2 (* h3
 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 11728 (* h1 h1) h2 (* h3 h3) h5 
(* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 7480 (* h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6 
h6) (* j2 j2 j2)) (* 2568 (* h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2)) 
(* 392 (* h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6 h6) j2) (* 8 (* h1 h1) h2 (* h3 h3)
 h5 (* h6 h6 h6 h6)) (* 48 (* h1 h1) h2 h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2
)) (* 120 (* h1 h1) h2 h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2)) (* 72 (* h1 h1) 
h2 h3 (* h4 h4 h4 h4) (* h5 h5) j2) (* 96 (* h1 h1) h2 h3 (* h4 h4 h4 h4) h5 h6 
(* j2 j2 j2)) (* 108 (* h1 h1) h2 h3 (* h4 h4 h4 h4) h5 h6 (* j2 j2)) (* 12 (* 
h1 h1) h2 h3 (* h4 h4 h4 h4) h5 h6 j2) (* 48 (* h1 h1) h2 h3 (* h4 h4 h4 h4) (* 
h6 h6) (* j2 j2 j2)) (* 192 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 
j2 j2)) (* 672 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 768 
(* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2)) (* 288 (* h1 h1) h2 h3 (* 
h4 h4 h4) (* h5 h5 h5) j2) (* 768 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) h6 (* 
j2 j2 j2 j2)) (* 2032 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) 
(* 1800 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 544 (* h1 h1) h2
 h3 (* h4 h4 h4) (* h5 h5) h6 j2) (* 8 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) h6
) (* 768 (* h1 h1) h2 h3 (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 1344 (* 
h1 h1) h2 h3 (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 640 (* h1 h1) h2 h3 (* 
h4 h4 h4) h5 (* h6 h6) (* j2 j2)) (* 64 (* h1 h1) h2 h3 (* h4 h4 h4) h5 (* h6 h6
) j2) (* 192 (* h1 h1) h2 h3 (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 160 
(* h1 h1) h2 h3 (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2)) (* 112 (* h1 h1) h2 h3 
(* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 504 (* h1 h1) h2 h3 (* h4 h4) 
(* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 840 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5 h5
) (* j2 j2 j2)) (* 616 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 
168 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5 h5) j2) (* 1184 (* h1 h1) h2 h3 (* h4 
h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 4804 (* h1 h1) h2 h3 (* h4 h4) (* h5 
h5 h5) h6 (* j2 j2 j2 j2)) (* 7320 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) h6 (* 
j2 j2 j2)) (* 4976 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 1288 
(* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) h6 j2) (* 12 (* h1 h1) h2 h3 (* h4 h4) 
(* h5 h5 h5) h6) (* 2144 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2)) (* 7424 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)
) (* 9664 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 5648 
(* h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 1296 (* h1 h1) h2 h3
 (* h4 h4) (* h5 h5) (* h6 h6) j2) (* 32 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* 
h6 h6)) (* 1184 (* h1 h1) h2 h3 (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 3220 (* h1 h1) h2 h3 (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 3000 (* h1
 h1) h2 h3 (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 1064 (* h1 h1) h2 h3 (* h4
 h4) h5 (* h6 h6 h6) (* j2 j2)) (* 100 (* h1 h1) h2 h3 (* h4 h4) h5 (* h6 h6 h6)
 j2) (* 112 (* h1 h1) h2 h3 (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 224
 (* h1 h1) h2 h3 (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 112 (* h1 h1) h2 
h3 (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 384 (* h1 h1) h2 h3 h4 (* h5 h5 h5
 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 2064 (* h1 h1) h2 h3 h4 (* h5 h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2)) (* 4392 (* h1 h1) h2 h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) 
(* 4632 (* h1 h1) h2 h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 2424 (* h1 h1) h2
 h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 504 (* h1 h1) h2 h3 h4 (* h5 h5 h5 h5) 
h6 j2) (* 1536 (* h1 h1) h2 h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 7680 (* h1 h1) h2 h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 15480 
(* h1 h1) h2 h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 15756 (* h1 h1) h2
 h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 8148 (* h1 h1) h2 h3 h4 (* h5 h5 
h5) (* h6 h6) (* j2 j2)) (* 1764 (* h1 h1) h2 h3 h4 (* h5 h5 h5) (* h6 h6) j2) 
(* 36 (* h1 h1) h2 h3 h4 (* h5 h5 h5) (* h6 h6)) (* 1536 (* h1 h1) h2 h3 h4 (* 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 7088 (* h1 h1) h2 h3 h4 (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 13124 (* h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2)) (* 12244 (* h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2
 j2)) (* 5828 (* h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 1196 (* h1
 h1) h2 h3 h4 (* h5 h5) (* h6 h6 h6) j2) (* 40 (* h1 h1) h2 h3 h4 (* h5 h5) (* 
h6 h6 h6)) (* 384 (* h1 h1) h2 h3 h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 1536 (* h1 h1) h2 h3 h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2352 (* h1 
h1) h2 h3 h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 1680 (* h1 h1) h2 h3 h4 h5 
(* h6 h6 h6 h6) (* j2 j2 j2)) (* 528 (* h1 h1) h2 h3 h4 h5 (* h6 h6 h6 h6) (* j2
 j2)) (* 48 (* h1 h1) h2 h3 h4 h5 (* h6 h6 h6 h6) j2) (* 224 (* h1 h1) h2 h3 (* 
h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1456 (* h1 h1) h2 h3 (* h5 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3920 (* h1 h1) h2 h3 (* h5 h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 5600 (* h1 h1) h2 h3 (* h5 h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2)) (* 4480 (* h1 h1) h2 h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 
j2)) (* 1904 (* h1 h1) h2 h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 336 (* h1 
h1) h2 h3 (* h5 h5 h5 h5) (* h6 h6) j2) (* 448 (* h1 h1) h2 h3 (* h5 h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2856 (* h1 h1) h2 h3 (* h5 h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 7584 (* h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2)) (* 10760 (* h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2)) (* 8640 (* h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 3768 
(* h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 736 (* h1 h1) h2 h3 (* 
h5 h5 h5) (* h6 h6 h6) j2) (* 24 (* h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6 h6)) (* 
224 (* h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1408 
(* h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3696 (* h1 
h1) h2 h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 5200 (* h1 h1) h2 h3 
(* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 4160 (* h1 h1) h2 h3 (* h5 h5) (* 
h6 h6 h6 h6) (* j2 j2 j2)) (* 1824 (* h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6 h6) (* 
j2 j2)) (* 368 (* h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6 h6) j2) (* 16 (* h1 h1) h2 
h3 (* h5 h5) (* h6 h6 h6 h6)) (* 12 (* h1 h1) h2 (* h4 h4 h4 h4) (* h5 h5) h6 
(* j2 j2 j2)) (* 24 (* h1 h1) h2 (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 12 
(* h1 h1) h2 (* h4 h4 h4 h4) (* h5 h5) h6 j2) (* 12 (* h1 h1) h2 (* h4 h4 h4 h4)
 h5 (* h6 h6) (* j2 j2 j2)) (* 12 (* h1 h1) h2 (* h4 h4 h4 h4) h5 (* h6 h6) (* 
j2 j2)) (* 48 (* h1 h1) h2 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 148 
(* h1 h1) h2 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 156 (* h1 h1) h2 (* 
h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 60 (* h1 h1) h2 (* h4 h4 h4) (* h5 h5 h5
) h6 j2) (* 4 (* h1 h1) h2 (* h4 h4 h4) (* h5 h5 h5) h6) (* 96 (* h1 h1) h2 (* 
h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 252 (* h1 h1) h2 (* h4 h4 h4) 
(* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 216 (* h1 h1) h2 (* h4 h4 h4) (* h5 h5) (* 
h6 h6) (* j2 j2)) (* 60 (* h1 h1) h2 (* h4 h4 h4) (* h5 h5) (* h6 h6) j2) (* 48 
(* h1 h1) h2 (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 88 (* h1 h1) h2 
(* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 40 (* h1 h1) h2 (* h4 h4 h4) h5 
(* h6 h6 h6) (* j2 j2)) (* 28 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2
 j2 j2 j2)) (* 116 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) 
(* 184 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 136 (* h1 h1) 
h2 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 44 (* h1 h1) h2 (* h4 h4) (* h5 h5
 h5 h5) h6 j2) (* 4 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5 h5) h6) (* 148 (* h1 h1) 
h2 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 596 (* h1 h1) h2 (* 
h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 916 (* h1 h1) h2 (* h4 h4) (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 652 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5) (* 
h6 h6) (* j2 j2)) (* 200 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5) (* h6 h6) j2) (* 16
 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5) (* h6 h6)) (* 148 (* h1 h1) h2 (* h4 h4) 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 540 (* h1 h1) h2 (* h4 h4) (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 732 (* h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 
h6 h6) (* j2 j2 j2)) (* 436 (* h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 
j2)) (* 96 (* h1 h1) h2 (* h4 h4) (* h5 h5) (* h6 h6 h6) j2) (* 28 (* h1 h1) h2 
(* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 84 (* h1 h1) h2 (* h4 h4) h5
 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 84 (* h1 h1) h2 (* h4 h4) h5 (* h6 h6 h6 h6
) (* j2 j2 j2)) (* 28 (* h1 h1) h2 (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2)) (* 48
 (* h1 h1) h2 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 252 (* h1 
h1) h2 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 540 (* h1 h1) h2 h4 
(* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 600 (* h1 h1) h2 h4 (* h5 h5 h5 h5
) (* h6 h6) (* j2 j2 j2)) (* 360 (* h1 h1) h2 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2
 j2)) (* 108 (* h1 h1) h2 h4 (* h5 h5 h5 h5) (* h6 h6) j2) (* 12 (* h1 h1) h2 h4
 (* h5 h5 h5 h5) (* h6 h6)) (* 96 (* h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 500 (* h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2
 j2 j2)) (* 1060 (* h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 
1160 (* h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 680 (* h1 h1) h2
 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 196 (* h1 h1) h2 h4 (* h5 h5 h5) (* 
h6 h6 h6) j2) (* 20 (* h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6 h6)) (* 48 (* h1 h1) 
h2 h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 240 (* h1 h1) h2 h4 
(* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 480 (* h1 h1) h2 h4 (* h5 h5) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 480 (* h1 h1) h2 h4 (* h5 h5) (* h6 h6 h6 h6
) (* j2 j2 j2)) (* 240 (* h1 h1) h2 h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 
48 (* h1 h1) h2 h4 (* h5 h5) (* h6 h6 h6 h6) j2) (* 8 (* h1 h1) h2 (* h5 h5 h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 56 (* h1 h1) h2 (* h5 h5 h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 168 (* h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6
 h6) (* j2 j2 j2 j2 j2)) (* 280 (* h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2)) (* 280 (* h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 168
 (* h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 56 (* h1 h1) h2 (* h5 
h5 h5 h5) (* h6 h6 h6) j2) (* 8 (* h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6 h6)) (* 8 
(* h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 56 (* h1 
h1) h2 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 168 (* h1 h1) h2 
(* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 280 (* h1 h1) h2 (* h5 h5 h5
) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 280 (* h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6 
h6) (* j2 j2 j2)) (* 168 (* h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2)) 
(* 56 (* h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6 h6) j2) (* 8 (* h1 h1) h2 (* h5 h5 
h5) (* h6 h6 h6 h6)) (* 1024 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 
j2 j2 j2)) (* 2304 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) 
(* 1344 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 304 (* h1 h1)
 (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2)) (* 24 (* h1 h1) (* h3 h3 h3 h3) (* 
h4 h4 h4) h5 j2) (* 1024 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 
j2 j2)) (* 768 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2)) (* 192
 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2)) (* 16 (* h1 h1) (* h3 
h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2)) (* 4096 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4)
 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 14336 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) 
(* h5 h5) (* j2 j2 j2 j2 j2)) (* 15616 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) (* h5
 h5) (* j2 j2 j2 j2)) (* 5376 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* 
j2 j2 j2)) (* 576 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 
8192 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 21504 
(* h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 18176 (* h1 h1)
 (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 7488 (* h1 h1) (* h3 h3 h3 
h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 1520 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5
 h6 (* j2 j2)) (* 120 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 h6 j2) (* 4096 (* 
h1 h1) (* h3 h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 5120 (* h1 
h1) (* h3 h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2560 (* h1 h1) 
(* h3 h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 576 (* h1 h1) (* h3 h3 
h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 48 (* h1 h1) (* h3 h3 h3 h3) (* h4 
h4) (* h6 h6) (* j2 j2)) (* 2048 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2
 j2 j2 j2 j2 j2 j2)) (* 9728 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 
j2 j2 j2 j2)) (* 16128 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 
j2)) (* 10368 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 1728
 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2)) (* 14336 (* h1 h1) (* 
h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 60928 (* h1 h1) (* h3 
h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 92672 (* h1 h1) (* h3 h3 h3 
h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 61056 (* h1 h1) (* h3 h3 h3 h3) h4 
(* h5 h5) h6 (* j2 j2 j2 j2)) (* 17280 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) h6
 (* j2 j2 j2)) (* 1728 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 
14336 (* h1 h1) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
49664 (* h1 h1) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 63744 
(* h1 h1) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 40576 (* h1 h1)
 (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 14112 (* h1 h1) (* h3 h3 h3
 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 2576 (* h1 h1) (* h3 h3 h3 h3) h4 h5 (* h6
 h6) (* j2 j2)) (* 192 (* h1 h1) (* h3 h3 h3 h3) h4 h5 (* h6 h6) j2) (* 2048 (* 
h1 h1) (* h3 h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4608 (* h1 
h1) (* h3 h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4096 (* h1 h1) (* 
h3 h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1792 (* h1 h1) (* h3 h3 h3 
h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 384 (* h1 h1) (* h3 h3 h3 h3) h4 (* h6 
h6 h6) (* j2 j2 j2)) (* 32 (* h1 h1) (* h3 h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2)) 
(* 4096 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 23552 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
51712 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 52992 
(* h1 h1) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 24192 (* h1 h1)
 (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 3456 (* h1 h1) (* h3 h3 h3 
h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 8192 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 43008 (* h1 h1) (* h3 h3 h3 h3) (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 88064 (* h1 h1) (* h3 h3 h3 h3) (* h5
 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 89088 (* h1 h1) (* h3 h3 h3 h3) (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 46592 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2)) (* 11904 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6
) (* j2 j2 j2)) (* 1152 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2))
 (* 4096 (* h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 19456 (* h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
37376 (* h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 37888 
(* h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 22016 (* h1 h1)
 (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 7360 (* h1 h1) (* h3 h3 h3 
h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 1312 (* h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6 
h6) (* j2 j2)) (* 96 (* h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6 h6) j2) (* 256 (* h1 
h1) (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 512 (* h1 h1) (* h3 h3 
h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2)) (* 208 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4 
h4) h5 (* j2 j2)) (* 24 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4 h4) h5 j2) (* 256 (* 
h1 h1) (* h3 h3 h3) (* h4 h4 h4 h4) h6 (* j2 j2 j2 j2)) (* 128 (* h1 h1) (* h3 
h3 h3) (* h4 h4 h4 h4) h6 (* j2 j2 j2)) (* 16 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4
 h4) h6 (* j2 j2)) (* 1792 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 
j2 j2 j2 j2)) (* 5632 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 
j2)) (* 5232 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 1272
 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 72 (* h1 h1) (* h3 
h3 h3) (* h4 h4 h4) (* h5 h5) j2) (* 3584 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5
 h6 (* j2 j2 j2 j2 j2)) (* 7744 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 
j2 j2 j2)) (* 4928 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 
1396 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2)) (* 148 (* h1 h1) (* h3
 h3 h3) (* h4 h4 h4) h5 h6 j2) (* 1792 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h6
 h6) (* j2 j2 j2 j2 j2)) (* 1664 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h6 h6) 
(* j2 j2 j2 j2)) (* 560 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 
j2)) (* 64 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2)) (* 2048 (* 
h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 8704 (* h1 
h1) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 12800 (* h1 h1) 
(* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 7296 (* h1 h1) (* h3 h3 
h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 1152 (* h1 h1) (* h3 h3 h3) (* h4 h4
) (* h5 h5 h5) (* j2 j2)) (* 10240 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6
 (* j2 j2 j2 j2 j2 j2)) (* 38144 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 
(* j2 j2 j2 j2 j2)) (* 49920 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2
 j2 j2 j2)) (* 27248 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2))
 (* 5688 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 360 (* h1 
h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 j2) (* 10240 (* h1 h1) (* h3 h3 h3) (* 
h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 29184 (* h1 h1) (* h3 h3 h3) (* h4
 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 30208 (* h1 h1) (* h3 h3 h3) (* h4 h4) 
h5 (* h6 h6) (* j2 j2 j2 j2)) (* 14352 (* h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* h6
 h6) (* j2 j2 j2)) (* 3412 (* h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 
j2)) (* 324 (* h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) j2) (* 2048 (* h1 h1) 
(* h3 h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3840 (* h1 h1) (* 
h3 h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2496 (* h1 h1) (* h3 h3 
h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 736 (* h1 h1) (* h3 h3 h3) (* h4 
h4) (* h6 h6 h6) (* j2 j2 j2)) (* 80 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h6 h6 
h6) (* j2 j2)) (* 512 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 
j2 j2 j2)) (* 2816 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 
j2)) (* 5760 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 
5184 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 1728 (* h1 h1
) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2)) (* 7168 (* h1 h1) (* h3 h3 h3) 
h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 36224 (* h1 h1) (* h3 h3 h3) h4 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 69376 (* h1 h1) (* h3 h3 h3) h4 (* h5 
h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 61920 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) h6
 (* j2 j2 j2 j2)) (* 25056 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2
)) (* 3456 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2)) (* 13312 (* h1 
h1) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 60928 (* h1
 h1) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 108800 (* h1 
h1) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 95712 (* h1 h1) 
(* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 42352 (* h1 h1) (* h3 h3
 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 8400 (* h1 h1) (* h3 h3 h3) h4 (* 
h5 h5) (* h6 h6) (* j2 j2)) (* 576 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6)
 j2) (* 7168 (* h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2))
 (* 28544 (* h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
44672 (* h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 35136 (* 
h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 14816 (* h1 h1) (* h3
 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 3272 (* h1 h1) (* h3 h3 h3) h4 h5 
(* h6 h6 h6) (* j2 j2)) (* 296 (* h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6 h6) j2) (* 
512 (* h1 h1) (* h3 h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1536 
(* h1 h1) (* h3 h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1792 (* h1 
h1) (* h3 h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1024 (* h1 h1) (* h3 
h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 288 (* h1 h1) (* h3 h3 h3) h4 (* 
h6 h6 h6 h6) (* j2 j2 j2)) (* 32 (* h1 h1) (* h3 h3 h3) h4 (* h6 h6 h6 h6) (* j2
 j2)) (* 1024 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 6656 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2))
 (* 17152 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
21888 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 13824 (* 
h1 h1) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 3456 (* h1 h1) (* h3 
h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 4096 (* h1 h1) (* h3 h3 h3) (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 25088 (* h1 h1) (* h3 h3 h3) (* h5
 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 61952 (* h1 h1) (* h3 h3 h3) (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 78464 (* h1 h1) (* h3 h3 h3) (* h5
 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 53248 (* h1 h1) (* h3 h3 h3) (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2)) (* 18048 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5) (* 
h6 h6) (* j2 j2 j2)) (* 2304 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2
 j2)) (* 4096 (* h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 23552 (* h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 55552 (* h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2
 j2 j2)) (* 69248 (* h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2)) (* 48832 (* h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 
19232 (* h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 3840 (* h1 
h1) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 288 (* h1 h1) (* h3 h3 h3)
 (* h5 h5) (* h6 h6 h6) j2) (* 1024 (* h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 5632 (* h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 12800 (* h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 15616 (* h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 
j2 j2 j2)) (* 11072 (* h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) 
(* 4576 (* h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 1024 (* h1 h1
) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2)) (* 96 (* h1 h1) (* h3 h3 h3) h5 (* 
h6 h6 h6 h6) j2) (* 128 (* h1 h1) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 
j2 j2)) (* 352 (* h1 h1) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 
272 (* h1 h1) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2)) (* 48 (* h1 h1) (* 
h3 h3) (* h4 h4 h4 h4) (* h5 h5) j2) (* 256 (* h1 h1) (* h3 h3) (* h4 h4 h4 h4) 
h5 h6 (* j2 j2 j2 j2)) (* 368 (* h1 h1) (* h3 h3) (* h4 h4 h4 h4) h5 h6 (* j2 j2
 j2)) (* 92 (* h1 h1) (* h3 h3) (* h4 h4 h4 h4) h5 h6 (* j2 j2)) (* 4 (* h1 h1) 
(* h3 h3) (* h4 h4 h4 h4) h5 h6 j2) (* 128 (* h1 h1) (* h3 h3) (* h4 h4 h4 h4) 
(* h6 h6) (* j2 j2 j2 j2)) (* 32 (* h1 h1) (* h3 h3) (* h4 h4 h4 h4) (* h6 h6) 
(* j2 j2 j2)) (* 448 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 
j2 j2)) (* 1744 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) 
(* 2280 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 1056 (* 
h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2)) (* 72 (* h1 h1) (* h3 h3) 
(* h4 h4 h4) (* h5 h5 h5) j2) (* 1664 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5)
 h6 (* j2 j2 j2 j2 j2)) (* 5072 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 
(* j2 j2 j2 j2)) (* 5196 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 
j2)) (* 2088 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 300 (* 
h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 j2) (* 1664 (* h1 h1) (* h3 h3) (* h4
 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 3376 (* h1 h1) (* h3 h3) (* h4 h4 h4
) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 2148 (* h1 h1) (* h3 h3) (* h4 h4 h4) h5 (* 
h6 h6) (* j2 j2 j2)) (* 428 (* h1 h1) (* h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 
j2)) (* 16 (* h1 h1) (* h3 h3) (* h4 h4 h4) h5 (* h6 h6) j2) (* 448 (* h1 h1) 
(* h3 h3) (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 432 (* h1 h1) (* h3 
h3) (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 80 (* h1 h1) (* h3 h3) (* h4 
h4 h4) (* h6 h6 h6) (* j2 j2 j2)) (* 256 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 
h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1280 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5 
h5) (* j2 j2 j2 j2 j2)) (* 2368 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) 
(* j2 j2 j2 j2)) (* 1920 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 
j2)) (* 576 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 2560 (* 
h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 11584 (* h1
 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 19600 (* h1 h1) 
(* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 15016 (* h1 h1) (* h3 h3
) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 4800 (* h1 h1) (* h3 h3) (* h4 h4) 
(* h5 h5 h5) h6 (* j2 j2)) (* 360 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 
j2) (* 4608 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 17536 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 25328 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2))
 (* 17116 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 
5376 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 660 (* h1 
h1) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) j2) (* 2560 (* h1 h1) (* h3 h3) (* 
h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 7744 (* h1 h1) (* h3 h3) (* h4 
h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 8288 (* h1 h1) (* h3 h3) (* h4 h4) h5
 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 3720 (* h1 h1) (* h3 h3) (* h4 h4) h5 (* h6 h6
 h6) (* j2 j2 j2)) (* 628 (* h1 h1) (* h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2
)) (* 20 (* h1 h1) (* h3 h3) (* h4 h4) h5 (* h6 h6 h6) j2) (* 256 (* h1 h1) (* 
h3 h3) (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 512 (* h1 h1) (* h3 
h3) (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 304 (* h1 h1) (* h3 h3) (* 
h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 48 (* h1 h1) (* h3 h3) (* h4 h4) (* 
h6 h6 h6 h6) (* j2 j2 j2)) (* 896 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2)) (* 5248 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2)) (* 12128 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 
j2 j2)) (* 13824 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 
7776 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 1728 (* h1 h1) 
(* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 3328 (* h1 h1) (* h3 h3) h4 (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 18080 (* h1 h1) (* h3 h3) h4 (* h5
 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 39504 (* h1 h1) (* h3 h3) h4 (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 43984 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5
) (* h6 h6) (* j2 j2 j2 j2)) (* 25712 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* h6 
h6) (* j2 j2 j2)) (* 7056 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2
)) (* 576 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) j2) (* 3328 (* h1 h1) 
(* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 16480 (* h1 h1)
 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 32896 (* h1 h1) 
(* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 33712 (* h1 h1) (* h3
 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 18616 (* h1 h1) (* h3 h3) h4 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 5248 (* h1 h1) (* h3 h3) h4 (* h5 h5) 
(* h6 h6 h6) (* j2 j2)) (* 600 (* h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) j2)
 (* 896 (* h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
3840 (* h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6368 
(* h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 5072 (* h1 h1) 
(* h3 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 1928 (* h1 h1) (* h3 h3) h4 
h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 288 (* h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6 h6
) (* j2 j2)) (* 8 (* h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6 h6) j2) (* 512 (* h1 h1)
 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3584 (* h1 
h1) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 10368 (* h1
 h1) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 15872 (* h1 
h1) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 13568 (* h1 h1) 
(* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 6144 (* h1 h1) (* h3 h3)
 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 1152 (* h1 h1) (* h3 h3) (* h5 h5 h5
 h5) (* h6 h6) (* j2 j2)) (* 1024 (* h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6848 (* h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 19168 (* h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6
 h6) (* j2 j2 j2 j2 j2 j2)) (* 28960 (* h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2)) (* 25280 (* h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2)) (* 12544 (* h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2
 j2)) (* 3168 (* h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 288 
(* h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) j2) (* 512 (* h1 h1) (* h3 h3) (* 
h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3328 (* h1 h1) (* h3 h3) 
(* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 9088 (* h1 h1) (* h3 h3) 
(* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 13504 (* h1 h1) (* h3 h3) 
(* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 11776 (* h1 h1) (* h3 h3) (* h5
 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 6016 (* h1 h1) (* h3 h3) (* h5 h5) (* 
h6 h6 h6 h6) (* j2 j2 j2)) (* 1664 (* h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6)
 (* j2 j2)) (* 192 (* h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) j2) (* 16 (* h1
 h1) h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 56 (* h1 h1) h3 (* h4 
h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 64 (* h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5
 h5) (* j2 j2)) (* 24 (* h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5 h5) j2) (* 64 (* h1 
h1) h3 (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 144 (* h1 h1) h3 (* h4 
h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 88 (* h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5
) h6 (* j2 j2)) (* 8 (* h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5) h6 j2) (* 64 (* h1 
h1) h3 (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 72 (* h1 h1) h3 (* h4 h4
 h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 8 (* h1 h1) h3 (* h4 h4 h4 h4) h5 (* h6 h6
) (* j2 j2)) (* 16 (* h1 h1) h3 (* h4 h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2)) 
(* 16 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 72 (* h1 
h1) h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 120 (* h1 h1) h3 (* h4 
h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 88 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5
 h5) (* j2 j2)) (* 24 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5 h5) j2) (* 224 (* h1
 h1) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 860 (* h1 h1) h3 (* 
h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 1204 (* h1 h1) h3 (* h4 h4 h4) (* 
h5 h5 h5) h6 (* j2 j2 j2)) (* 724 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* 
j2 j2)) (* 156 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) h6 j2) (* 416 (* h1 h1) h3
 (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1216 (* h1 h1) h3 (* h4
 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 1232 (* h1 h1) h3 (* h4 h4 h4) 
(* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 464 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5) (* 
h6 h6) (* j2 j2)) (* 32 (* h1 h1) h3 (* h4 h4 h4) (* h5 h5) (* h6 h6) j2) (* 224
 (* h1 h1) h3 (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 428 (* h1 h1) 
h3 (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 224 (* h1 h1) h3 (* h4 h4 h4
) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 20 (* h1 h1) h3 (* h4 h4 h4) h5 (* h6 h6 h6) 
(* j2 j2)) (* 16 (* h1 h1) h3 (* h4 h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 16 (* h1 h1) h3 (* h4 h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 128 (* h1 h1
) h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 656 (* h1 h1) h3 (* 
h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 1320 (* h1 h1) h3 (* h4 h4) (* 
h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 1304 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) 
h6 (* j2 j2 j2)) (* 632 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 
120 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) h6 j2) (* 640 (* h1 h1) h3 (* h4 h4) 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2944 (* h1 h1) h3 (* h4 h4) (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 5348 (* h1 h1) h3 (* h4 h4) (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2)) (* 4772 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* h6
 h6) (* j2 j2 j2)) (* 2076 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 
j2)) (* 348 (* h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) j2) (* 640 (* h1 h1) 
h3 (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2544 (* h1 h1) h3 
(* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 3820 (* h1 h1) h3 (* h4 
h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 2608 (* h1 h1) h3 (* h4 h4) (* h5
 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 732 (* h1 h1) h3 (* h4 h4) (* h5 h5) (* h6 h6
 h6) (* j2 j2)) (* 40 (* h1 h1) h3 (* h4 h4) (* h5 h5) (* h6 h6 h6) j2) (* 128 
(* h1 h1) h3 (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 384 (* h1 h1
) h3 (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 396 (* h1 h1) h3 (* h4 
h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 152 (* h1 h1) h3 (* h4 h4) h5 (* h6 
h6 h6 h6) (* j2 j2 j2)) (* 12 (* h1 h1) h3 (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2
)) (* 224 (* h1 h1) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 1360 (* h1 h1) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3392
 (* h1 h1) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 4448 (* h1 h1)
 h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 3232 (* h1 h1) h3 h4 (* h5 
h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 1232 (* h1 h1) h3 h4 (* h5 h5 h5 h5) (* h6 
h6) (* j2 j2)) (* 192 (* h1 h1) h3 h4 (* h5 h5 h5 h5) (* h6 h6) j2) (* 448 (* h1
 h1) h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2600 (* h1 h1)
 h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6232 (* h1 h1) h3 h4 
(* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 7888 (* h1 h1) h3 h4 (* h5 h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 5552 (* h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6 
h6) (* j2 j2 j2)) (* 2056 (* h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) 
(* 312 (* h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6 h6) j2) (* 224 (* h1 h1) h3 h4 (* 
h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1184 (* h1 h1) h3 h4 (* h5 
h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2512 (* h1 h1) h3 h4 (* h5 h5) (* 
h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2688 (* h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6 
h6) (* j2 j2 j2 j2)) (* 1472 (* h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 
j2)) (* 352 (* h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 16 (* h1 h1)
 h3 h4 (* h5 h5) (* h6 h6 h6 h6) j2) (* 64 (* h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 480 (* h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1536 (* h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 2720 (* h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2)) (* 2880 (* h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2))
 (* 1824 (* h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 640 (* h1 h1
) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 96 (* h1 h1) h3 (* h5 h5 h5 h5) 
(* h6 h6 h6) j2) (* 64 (* h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 480 (* h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2
 j2 j2)) (* 1536 (* h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)
) (* 2720 (* h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2880 
(* h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 1824 (* h1 h1) h3 
(* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 640 (* h1 h1) h3 (* h5 h5 h5) (* 
h6 h6 h6 h6) (* j2 j2)) (* 96 (* h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6 h6) j2) (* 4
 (* h1 h1) (* h4 h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 12 (* h1 h1) (* 
h4 h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 12 (* h1 h1) (* h4 h4 h4 h4) (* h5
 h5 h5) h6 (* j2 j2)) (* 4 (* h1 h1) (* h4 h4 h4 h4) (* h5 h5 h5) h6 j2) (* 8 
(* h1 h1) (* h4 h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 16 (* h1 h1) 
(* h4 h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 8 (* h1 h1) (* h4 h4 h4 h4)
 (* h5 h5) (* h6 h6) (* j2 j2)) (* 4 (* h1 h1) (* h4 h4 h4 h4) h5 (* h6 h6 h6) 
(* j2 j2 j2 j2)) (* 4 (* h1 h1) (* h4 h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2)) 
(* 4 (* h1 h1) (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 16 (* h1 
h1) (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 24 (* h1 h1) (* h4 h4 h4
) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 16 (* h1 h1) (* h4 h4 h4) (* h5 h5 h5 h5) 
h6 (* j2 j2)) (* 4 (* h1 h1) (* h4 h4 h4) (* h5 h5 h5 h5) h6 j2) (* 28 (* h1 h1)
 (* h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 100 (* h1 h1) (* h4 
h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 132 (* h1 h1) (* h4 h4 h4) (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 76 (* h1 h1) (* h4 h4 h4) (* h5 h5 h5) (* 
h6 h6) (* j2 j2)) (* 16 (* h1 h1) (* h4 h4 h4) (* h5 h5 h5) (* h6 h6) j2) (* 28 
(* h1 h1) (* h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 80 (* h1 h1
) (* h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 76 (* h1 h1) (* h4 h4 
h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 24 (* h1 h1) (* h4 h4 h4) (* h5 h5) 
(* h6 h6 h6) (* j2 j2)) (* 4 (* h1 h1) (* h4 h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 
j2 j2 j2)) (* 8 (* h1 h1) (* h4 h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 4 
(* h1 h1) (* h4 h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 16 (* h1 h1) (* h4 h4
) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 76 (* h1 h1) (* h4 h4) (* 
h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 144 (* h1 h1) (* h4 h4) (* h5 h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 136 (* h1 h1) (* h4 h4) (* h5 h5 h5 h5) (* 
h6 h6) (* j2 j2 j2)) (* 64 (* h1 h1) (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 
j2)) (* 12 (* h1 h1) (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) j2) (* 32 (* h1 h1) (* 
h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 148 (* h1 h1) (* h4 
h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 272 (* h1 h1) (* h4 h4) (* 
h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 248 (* h1 h1) (* h4 h4) (* h5 h5 h5) 
(* h6 h6 h6) (* j2 j2 j2)) (* 112 (* h1 h1) (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) 
(* j2 j2)) (* 20 (* h1 h1) (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) j2) (* 16 (* h1 
h1) (* h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 64 (* h1 h1) 
(* h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 96 (* h1 h1) (* h4 h4
) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 64 (* h1 h1) (* h4 h4) (* h5 h5)
 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 16 (* h1 h1) (* h4 h4) (* h5 h5) (* h6 h6 h6 
h6) (* j2 j2)) (* 8 (* h1 h1) h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 48 (* h1 h1) h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 120 (* h1 h1) h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 160 (* 
h1 h1) h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 120 (* h1 h1) h4 (* 
h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 48 (* h1 h1) h4 (* h5 h5 h5 h5) (* h6
 h6 h6) (* j2 j2)) (* 8 (* h1 h1) h4 (* h5 h5 h5 h5) (* h6 h6 h6) j2) (* 8 (* h1
 h1) h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 48 (* h1 h1) 
h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 120 (* h1 h1) h4 (* h5
 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 160 (* h1 h1) h4 (* h5 h5 h5) (* 
h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 120 (* h1 h1) h4 (* h5 h5 h5) (* h6 h6 h6 h6) 
(* j2 j2 j2)) (* 48 (* h1 h1) h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 8 
(* h1 h1) h4 (* h5 h5 h5) (* h6 h6 h6 h6) j2) (* 256 h1 (* h2 h2 h2 h2) (* h3 h3
 h3) h4 h5 (* j2 j2 j2 j2)) (* 512 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 
j2 j2)) (* 208 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2)) (* 24 h1 (* h2 
h2 h2 h2) (* h3 h3 h3) h4 h5 j2) (* 256 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h6 
(* j2 j2 j2 j2)) (* 256 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2)) (* 
80 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2)) (* 8 h1 (* h2 h2 h2 h2) (* 
h3 h3 h3) h4 h6 j2) (* 128 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2
 j2 j2)) (* 416 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 
384 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2)) (* 72 h1 (* h2 h2 h2
 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2)) (* 256 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h5
 h6 (* j2 j2 j2 j2 j2)) (* 704 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2
 j2)) (* 576 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2)) (* 152 h1 (* h2
 h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2)) (* 12 h1 (* h2 h2 h2 h2) (* h3 h3 h3) 
h5 h6 j2) (* 128 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 288 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 224 h1 (* 
h2 h2 h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2)) (* 72 h1 (* h2 h2 h2 h2) (* h3
 h3 h3) (* h6 h6) (* j2 j2)) (* 8 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h6 h6) j2) 
(* 96 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 168 h1 (* h2 h2
 h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2)) (* 36 h1 (* h2 h2 h2 h2) (* h3 h3) (* 
h4 h4) h5 j2) (* 96 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2 j2)) (* 
56 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2)) (* 8 h1 (* h2 h2 h2 h2) 
(* h3 h3) (* h4 h4) h6 j2) (* 128 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* 
j2 j2 j2 j2)) (* 352 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 
272 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2)) (* 48 h1 (* h2 h2 h2 h2
) (* h3 h3) h4 (* h5 h5) j2) (* 256 h1 (* h2 h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 
j2 j2 j2)) (* 592 h1 (* h2 h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 452 h1 
(* h2 h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2)) (* 98 h1 (* h2 h2 h2 h2) (* h3 h3)
 h4 h5 h6 j2) (* 2 h1 (* h2 h2 h2 h2) (* h3 h3) h4 h5 h6) (* 128 h1 (* h2 h2 h2 
h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 224 h1 (* h2 h2 h2 h2) (* h3 h3) 
h4 (* h6 h6) (* j2 j2 j2)) (* 120 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h6 h6) (* 
j2 j2)) (* 16 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h6 h6) j2) (* 32 h1 (* h2 h2 h2
 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 128 h1 (* h2 h2 h2 h2) (* h3 
h3) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 168 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 
h5) (* j2 j2 j2)) (* 72 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2)) (* 
128 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 464 h1 (* 
h2 h2 h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 576 h1 (* h2 h2 h2 h2) 
(* h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 276 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 
h5) h6 (* j2 j2)) (* 36 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) h6 j2) (* 128 h1 
(* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 416 h1 (* h2 h2 h2
 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 496 h1 (* h2 h2 h2 h2) (* h3 h3)
 h5 (* h6 h6) (* j2 j2 j2)) (* 266 h1 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* 
j2 j2)) (* 60 h1 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6) j2) (* 2 h1 (* h2 h2 h2 
h2) (* h3 h3) h5 (* h6 h6)) (* 32 h1 (* h2 h2 h2 h2) (* h3 h3) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2)) (* 96 h1 (* h2 h2 h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2)
) (* 104 h1 (* h2 h2 h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2)) (* 48 h1 (* h2 
h2 h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2)) (* 8 h1 (* h2 h2 h2 h2) (* h3 h3) 
(* h6 h6 h6) j2) (* 24 h1 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2)) 
(* 60 h1 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2)) (* 36 h1 (* h2 h2 h2 
h2) h3 (* h4 h4) (* h5 h5) j2) (* 48 h1 (* h2 h2 h2 h2) h3 (* h4 h4) h5 h6 (* j2
 j2 j2)) (* 70 h1 (* h2 h2 h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2)) (* 24 h1 (* h2 
h2 h2 h2) h3 (* h4 h4) h5 h6 j2) (* 2 h1 (* h2 h2 h2 h2) h3 (* h4 h4) h5 h6) (* 
24 h1 (* h2 h2 h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 16 h1 (* h2 h2 h2 
h2) h3 (* h4 h4) (* h6 h6) (* j2 j2)) (* 16 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5
) (* j2 j2 j2 j2)) (* 56 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2)) (* 
64 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2)) (* 24 h1 (* h2 h2 h2 h2) h3 
h4 (* h5 h5 h5) j2) (* 64 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2))
 (* 200 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2)) (* 220 h1 (* h2 h2 
h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2)) (* 88 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5) h6
 j2) (* 4 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5) h6) (* 64 h1 (* h2 h2 h2 h2) h3 h4 
h5 (* h6 h6) (* j2 j2 j2 j2)) (* 168 h1 (* h2 h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2
 j2 j2)) (* 150 h1 (* h2 h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2)) (* 50 h1 (* h2 
h2 h2 h2) h3 h4 h5 (* h6 h6) j2) (* 4 h1 (* h2 h2 h2 h2) h3 h4 h5 (* h6 h6)) (* 
16 h1 (* h2 h2 h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 32 h1 (* h2 h2 h2 
h2) h3 h4 (* h6 h6 h6) (* j2 j2 j2)) (* 16 h1 (* h2 h2 h2 h2) h3 h4 (* h6 h6 h6)
 (* j2 j2)) (* 16 h1 (* h2 h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
72 h1 (* h2 h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 120 h1 (* h2 h2 h2 
h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 88 h1 (* h2 h2 h2 h2) h3 (* h5 h5 h5) h6
 (* j2 j2)) (* 24 h1 (* h2 h2 h2 h2) h3 (* h5 h5 h5) h6 j2) (* 32 h1 (* h2 h2 h2
 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 134 h1 (* h2 h2 h2 h2) h3 (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 214 h1 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 
h6) (* j2 j2 j2)) (* 158 h1 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2)) 
(* 50 h1 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6) j2) (* 4 h1 (* h2 h2 h2 h2) h3 
(* h5 h5) (* h6 h6)) (* 16 h1 (* h2 h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 
j2)) (* 64 h1 (* h2 h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 98 h1 (* h2
 h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 70 h1 (* h2 h2 h2 h2) h3 h5 (* h6
 h6 h6) (* j2 j2)) (* 22 h1 (* h2 h2 h2 h2) h3 h5 (* h6 h6 h6) j2) (* 2 h1 (* h2
 h2 h2 h2) h3 h5 (* h6 h6 h6)) (* 6 h1 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5) h6 
(* j2 j2 j2)) (* 14 h1 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 10 
h1 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5) h6 j2) (* 2 h1 (* h2 h2 h2 h2) (* h4 h4) 
(* h5 h5) h6) (* 6 h1 (* h2 h2 h2 h2) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 10
 h1 (* h2 h2 h2 h2) (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 4 h1 (* h2 h2 h2 h2) 
(* h4 h4) h5 (* h6 h6) j2) (* 4 h1 (* h2 h2 h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 
j2 j2)) (* 14 h1 (* h2 h2 h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 18 h1 (* h2
 h2 h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2)) (* 10 h1 (* h2 h2 h2 h2) h4 (* h5 h5 h5
) h6 j2) (* 2 h1 (* h2 h2 h2 h2) h4 (* h5 h5 h5) h6) (* 8 h1 (* h2 h2 h2 h2) h4 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 28 h1 (* h2 h2 h2 h2) h4 (* h5 h5) (* h6
 h6) (* j2 j2 j2)) (* 36 h1 (* h2 h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2)) 
(* 20 h1 (* h2 h2 h2 h2) h4 (* h5 h5) (* h6 h6) j2) (* 4 h1 (* h2 h2 h2 h2) h4 
(* h5 h5) (* h6 h6)) (* 4 h1 (* h2 h2 h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2))
 (* 12 h1 (* h2 h2 h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 12 h1 (* h2 h2 h2 
h2) h4 h5 (* h6 h6 h6) (* j2 j2)) (* 4 h1 (* h2 h2 h2 h2) h4 h5 (* h6 h6 h6) j2)
 (* 2 h1 (* h2 h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 10 h1 (* 
h2 h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 20 h1 (* h2 h2 h2 h2) 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 20 h1 (* h2 h2 h2 h2) (* h5 h5 h5) (* h6
 h6) (* j2 j2)) (* 10 h1 (* h2 h2 h2 h2) (* h5 h5 h5) (* h6 h6) j2) (* 2 h1 (* 
h2 h2 h2 h2) (* h5 h5 h5) (* h6 h6)) (* 2 h1 (* h2 h2 h2 h2) (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2)) (* 10 h1 (* h2 h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2
 j2 j2)) (* 20 h1 (* h2 h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 20 h1 
(* h2 h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 10 h1 (* h2 h2 h2 h2) (* h5
 h5) (* h6 h6 h6) j2) (* 2 h1 (* h2 h2 h2 h2) (* h5 h5) (* h6 h6 h6)) (* 1024 h1
 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 2304 h1 (* h2 h2 h2) 
(* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2)) (* 1344 h1 (* h2 h2 h2) (* h3 h3 h3 h3) 
h4 h5 (* j2 j2 j2)) (* 304 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2)) (* 
24 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 j2) (* 1024 h1 (* h2 h2 h2) (* h3 h3 h3
 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 1280 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h6 (* 
j2 j2 j2 j2)) (* 576 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2)) (* 112 
h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2)) (* 8 h1 (* h2 h2 h2) (* h3 h3 
h3 h3) h4 h6 j2) (* 512 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2
 j2 j2)) (* 1792 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) 
(* 1952 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 672 h1 (* 
h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2)) (* 72 h1 (* h2 h2 h2) (* h3 h3
 h3 h3) (* h5 h5) (* j2 j2)) (* 1024 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2
 j2 j2 j2 j2 j2)) (* 3072 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 
j2)) (* 3008 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 1184 h1 
(* h2 h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2)) (* 200 h1 (* h2 h2 h2) (* h3 h3
 h3 h3) h5 h6 (* j2 j2)) (* 12 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h5 h6 j2) (* 512 
h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1280 h1 (* 
h2 h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1184 h1 (* h2 h2 h2) 
(* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 512 h1 (* h2 h2 h2) (* h3 h3 h3 h3
) (* h6 h6) (* j2 j2 j2)) (* 104 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2
 j2)) (* 8 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h6 h6) j2) (* 1280 h1 (* h2 h2 h2)
 (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 2560 h1 (* h2 h2 h2) (* h3 h3 h3)
 (* h4 h4) h5 (* j2 j2 j2)) (* 1040 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 
(* j2 j2)) (* 120 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 j2) (* 1280 h1 (* h2
 h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2)) (* 896 h1 (* h2 h2 h2) (* h3 
h3 h3) (* h4 h4) h6 (* j2 j2 j2)) (* 208 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) 
h6 (* j2 j2)) (* 16 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h6 j2) (* 1536 h1 (* 
h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 4800 h1 (* h2 h2 h2) 
(* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 4464 h1 (* h2 h2 h2) (* h3 h3 h3) 
h4 (* h5 h5) (* j2 j2 j2)) (* 1128 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* 
j2 j2)) (* 72 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) j2) (* 3072 h1 (* h2 h2 
h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 8128 h1 (* h2 h2 h2) (* h3 h3 
h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 7104 h1 (* h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* 
j2 j2 j2)) (* 2412 h1 (* h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2)) (* 282 h1 
(* h2 h2 h2) (* h3 h3 h3) h4 h5 h6 j2) (* 2 h1 (* h2 h2 h2) (* h3 h3 h3) h4 h5 
h6) (* 1536 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
2624 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 1616 h1 (* h2
 h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2)) (* 392 h1 (* h2 h2 h2) (* h3 h3 
h3) h4 (* h6 h6) (* j2 j2)) (* 32 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6) j2) 
(* 256 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1088 
h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 1600 h1 (* h2 
h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 912 h1 (* h2 h2 h2) (* h3 
h3 h3) (* h5 h5 h5) (* j2 j2 j2)) (* 144 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 
h5) (* j2 j2)) (* 1536 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 
j2 j2)) (* 6208 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) 
(* 8848 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 5144 h1 
(* h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 1016 h1 (* h2 h2 h2) (* 
h3 h3 h3) (* h5 h5) h6 (* j2 j2)) (* 48 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) 
h6 j2) (* 1536 h1 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 5568 h1 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 7504 h1
 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 4712 h1 (* h2 h2 h2)
 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 1398 h1 (* h2 h2 h2) (* h3 h3 h3) h5
 (* h6 h6) (* j2 j2)) (* 160 h1 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) j2) (* 2 
h1 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6)) (* 256 h1 (* h2 h2 h2) (* h3 h3 h3) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 832 h1 (* h2 h2 h2) (* h3 h3 h3) (* h6 h6
 h6) (* j2 j2 j2 j2 j2)) (* 1024 h1 (* h2 h2 h2) (* h3 h3 h3) (* h6 h6 h6) (* j2
 j2 j2 j2)) (* 592 h1 (* h2 h2 h2) (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2)) (* 
160 h1 (* h2 h2 h2) (* h3 h3 h3) (* h6 h6 h6) (* j2 j2)) (* 16 h1 (* h2 h2 h2) 
(* h3 h3 h3) (* h6 h6 h6) j2) (* 256 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 
(* j2 j2 j2)) (* 448 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2)) (* 96 
h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 j2) (* 256 h1 (* h2 h2 h2) (* h3 h3) 
(* h4 h4 h4) h6 (* j2 j2 j2)) (* 96 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h6 
(* j2 j2)) (* 8 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h6 j2) (* 640 h1 (* h2 h2
 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 1760 h1 (* h2 h2 h2) (* 
h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 1360 h1 (* h2 h2 h2) (* h3 h3) (* h4
 h4) (* h5 h5) (* j2 j2)) (* 240 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) 
j2) (* 1280 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 2736 
h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 1964 h1 (* h2 h2 h2) 
(* h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 376 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) 
h5 h6 j2) (* 4 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6) (* 640 h1 (* h2 h2 h2)
 (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 864 h1 (* h2 h2 h2) (* h3 h3)
 (* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 288 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) 
(* h6 h6) (* j2 j2)) (* 24 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) j2) (* 
384 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 1488 h1 (* 
h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 1944 h1 (* h2 h2 h2) (* 
h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2)) (* 912 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 
h5 h5) (* j2 j2)) (* 72 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) j2) (* 1408 h1
 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 4976 h1 (* h2 h2 
h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 6252 h1 (* h2 h2 h2) (* h3 h3)
 h4 (* h5 h5) h6 (* j2 j2 j2)) (* 3218 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6
 (* j2 j2)) (* 540 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 j2) (* 6 h1 (* h2 
h2 h2) (* h3 h3) h4 (* h5 h5) h6) (* 1408 h1 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 
h6) (* j2 j2 j2 j2 j2)) (* 4272 h1 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 
j2 j2 j2)) (* 4964 h1 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 
2550 h1 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 458 h1 (* h2 h2 h2)
 (* h3 h3) h4 h5 (* h6 h6) j2) (* 8 h1 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6)) 
(* 384 h1 (* h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 912 h1 
(* h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 752 h1 (* h2 h2 h2) 
(* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2)) (* 248 h1 (* h2 h2 h2) (* h3 h3) h4 (* 
h6 h6 h6) (* j2 j2)) (* 24 h1 (* h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6) j2) (* 32 
h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 160 h1 (* h2
 h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 296 h1 (* h2 h2 h2) (* 
h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 240 h1 (* h2 h2 h2) (* h3 h3) (* h5 
h5 h5 h5) (* j2 j2 j2)) (* 72 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2
)) (* 384 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
1856 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 3368 h1 
(* h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 2764 h1 (* h2 h2 h2) 
(* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 928 h1 (* h2 h2 h2) (* h3 h3) (* h5 
h5 h5) h6 (* j2 j2)) (* 60 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 j2) (* 704 
h1 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3184 h1 
(* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 5570 h1 (* h2 
h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 4688 h1 (* h2 h2 h2) 
(* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 1888 h1 (* h2 h2 h2) (* h3 h3) 
(* h5 h5) (* h6 h6) (* j2 j2)) (* 296 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 
h6) j2) (* 6 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6)) (* 384 h1 (* h2 h2 
h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1664 h1 (* h2 h2 h2) (* 
h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2816 h1 (* h2 h2 h2) (* h3 h3) h5 
(* h6 h6 h6) (* j2 j2 j2 j2)) (* 2340 h1 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) 
(* j2 j2 j2)) (* 972 h1 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 172
 h1 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) j2) (* 4 h1 (* h2 h2 h2) (* h3 h3) h5
 (* h6 h6 h6)) (* 32 h1 (* h2 h2 h2) (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2
 j2)) (* 128 h1 (* h2 h2 h2) (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
200 h1 (* h2 h2 h2) (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 152 h1 (* h2 
h2 h2) (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 56 h1 (* h2 h2 h2) (* h3 h3) 
(* h6 h6 h6 h6) (* j2 j2)) (* 8 h1 (* h2 h2 h2) (* h3 h3) (* h6 h6 h6 h6) j2) 
(* 64 h1 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 160 h1 (* h2 h2
 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 96 h1 (* h2 h2 h2) h3 (* h4 h4 h4) 
(* h5 h5) j2) (* 128 h1 (* h2 h2 h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 160 
h1 (* h2 h2 h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2)) (* 34 h1 (* h2 h2 h2) h3 (* h4 
h4 h4) h5 h6 j2) (* 2 h1 (* h2 h2 h2) h3 (* h4 h4 h4) h5 h6) (* 64 h1 (* h2 h2 
h2) h3 (* h4 h4 h4) (* h6 h6) (* j2 j2 j2)) (* 16 h1 (* h2 h2 h2) h3 (* h4 h4 h4
) (* h6 h6) (* j2 j2)) (* 80 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 
j2 j2)) (* 280 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 320 h1
 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 120 h1 (* h2 h2 h2) h3 (* 
h4 h4) (* h5 h5 h5) j2) (* 320 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 
j2 j2 j2)) (* 944 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 984
 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 368 h1 (* h2 h2 h2) h3 
(* h4 h4) (* h5 h5) h6 j2) (* 8 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6) (* 
320 h1 (* h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 712 h1 (* h2 
h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 488 h1 (* h2 h2 h2) h3 (* h4 
h4) h5 (* h6 h6) (* j2 j2)) (* 102 h1 (* h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6) j2)
 (* 6 h1 (* h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6)) (* 80 h1 (* h2 h2 h2) h3 (* h4 
h4) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 112 h1 (* h2 h2 h2) h3 (* h4 h4) (* h6 h6 
h6) (* j2 j2 j2)) (* 32 h1 (* h2 h2 h2) h3 (* h4 h4) (* h6 h6 h6) (* j2 j2)) (* 
16 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 72 h1 (* h2 h2 
h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 120 h1 (* h2 h2 h2) h3 h4 (* h5 h5
 h5 h5) (* j2 j2 j2)) (* 88 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2)) (* 
24 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) j2) (* 192 h1 (* h2 h2 h2) h3 h4 (* h5 
h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 828 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2
 j2 j2 j2)) (* 1346 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 982 
h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2)) (* 278 h1 (* h2 h2 h2) h3 h4 
(* h5 h5 h5) h6 j2) (* 6 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5) h6) (* 352 h1 (* h2 
h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1380 h1 (* h2 h2 h2) h3 
h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 2106 h1 (* h2 h2 h2) h3 h4 (* h5 h5) 
(* h6 h6) (* j2 j2 j2)) (* 1496 h1 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 
j2)) (* 434 h1 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) j2) (* 16 h1 (* h2 h2 h2) 
h3 h4 (* h5 h5) (* h6 h6)) (* 192 h1 (* h2 h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2
 j2 j2 j2)) (* 636 h1 (* h2 h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 776
 h1 (* h2 h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 418 h1 (* h2 h2 h2) h3 
h4 h5 (* h6 h6 h6) (* j2 j2)) (* 92 h1 (* h2 h2 h2) h3 h4 h5 (* h6 h6 h6) j2) 
(* 6 h1 (* h2 h2 h2) h3 h4 h5 (* h6 h6 h6)) (* 16 h1 (* h2 h2 h2) h3 h4 (* h6 h6
 h6 h6) (* j2 j2 j2 j2 j2)) (* 48 h1 (* h2 h2 h2) h3 h4 (* h6 h6 h6 h6) (* j2 j2
 j2 j2)) (* 48 h1 (* h2 h2 h2) h3 h4 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 16 h1 (* 
h2 h2 h2) h3 h4 (* h6 h6 h6 h6) (* j2 j2)) (* 16 h1 (* h2 h2 h2) h3 (* h5 h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 88 h1 (* h2 h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* 192 h1 (* h2 h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 
208 h1 (* h2 h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 112 h1 (* h2 h2 h2) 
h3 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 24 h1 (* h2 h2 h2) h3 (* h5 h5 h5 h5) h6 j2)
 (* 96 h1 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 516 
h1 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1110 h1 (* h2 
h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 1200 h1 (* h2 h2 h2) h3 (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 660 h1 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 
h6) (* j2 j2)) (* 156 h1 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) j2) (* 6 h1 (* 
h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6)) (* 96 h1 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6
 h6) (* j2 j2 j2 j2 j2 j2)) (* 508 h1 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2)) (* 1080 h1 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2)) (* 1160 h1 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 640 h1 
(* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 156 h1 (* h2 h2 h2) h3 (* 
h5 h5) (* h6 h6 h6) j2) (* 8 h1 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6)) (* 16 h1
 (* h2 h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 80 h1 (* h2 h2 h2)
 h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 162 h1 (* h2 h2 h2) h3 h5 (* h6 h6
 h6 h6) (* j2 j2 j2 j2)) (* 168 h1 (* h2 h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 
j2)) (* 92 h1 (* h2 h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2)) (* 24 h1 (* h2 h2 h2
) h3 h5 (* h6 h6 h6 h6) j2) (* 2 h1 (* h2 h2 h2) h3 h5 (* h6 h6 h6 h6)) (* 16 h1
 (* h2 h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 34 h1 (* h2 h2 h2) (* 
h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 20 h1 (* h2 h2 h2) (* h4 h4 h4) (* h5 h5) 
h6 j2) (* 2 h1 (* h2 h2 h2) (* h4 h4 h4) (* h5 h5) h6) (* 16 h1 (* h2 h2 h2) (* 
h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 20 h1 (* h2 h2 h2) (* h4 h4 h4) h5 (* h6
 h6) (* j2 j2)) (* 4 h1 (* h2 h2 h2) (* h4 h4 h4) h5 (* h6 h6) j2) (* 20 h1 (* 
h2 h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 64 h1 (* h2 h2 h2) (* h4
 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 72 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5) 
h6 (* j2 j2)) (* 32 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5) h6 j2) (* 4 h1 (* h2 
h2 h2) (* h4 h4) (* h5 h5 h5) h6) (* 40 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2)) (* 124 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* 
j2 j2 j2)) (* 134 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 56
 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) j2) (* 6 h1 (* h2 h2 h2) (* h4 h4
) (* h5 h5) (* h6 h6)) (* 20 h1 (* h2 h2 h2) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 
j2 j2)) (* 48 h1 (* h2 h2 h2) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 36 h1 
(* h2 h2 h2) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2)) (* 8 h1 (* h2 h2 h2) (* h4 h4)
 h5 (* h6 h6 h6) j2) (* 4 h1 (* h2 h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 
j2)) (* 18 h1 (* h2 h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 32 h1 (* h2
 h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 28 h1 (* h2 h2 h2) h4 (* h5 h5 h5
 h5) h6 (* j2 j2)) (* 12 h1 (* h2 h2 h2) h4 (* h5 h5 h5 h5) h6 j2) (* 2 h1 (* h2
 h2 h2) h4 (* h5 h5 h5 h5) h6) (* 24 h1 (* h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* 104 h1 (* h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2
 j2)) (* 176 h1 (* h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 144 h1 
(* h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 56 h1 (* h2 h2 h2) h4 (* h5
 h5 h5) (* h6 h6) j2) (* 8 h1 (* h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6)) (* 24 h1 
(* h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 102 h1 (* h2 h2 h2
) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 168 h1 (* h2 h2 h2) h4 (* h5 h5)
 (* h6 h6 h6) (* j2 j2 j2)) (* 132 h1 (* h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* 
j2 j2)) (* 48 h1 (* h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6) j2) (* 6 h1 (* h2 h2 h2)
 h4 (* h5 h5) (* h6 h6 h6)) (* 4 h1 (* h2 h2 h2) h4 h5 (* h6 h6 h6 h6) (* j2 j2 
j2 j2 j2)) (* 16 h1 (* h2 h2 h2) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 24 h1
 (* h2 h2 h2) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 16 h1 (* h2 h2 h2) h4 h5 
(* h6 h6 h6 h6) (* j2 j2)) (* 4 h1 (* h2 h2 h2) h4 h5 (* h6 h6 h6 h6) j2) (* 2 
h1 (* h2 h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 12 h1 (* h2 
h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 30 h1 (* h2 h2 h2) (* h5
 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 40 h1 (* h2 h2 h2) (* h5 h5 h5 h5) (* 
h6 h6) (* j2 j2 j2)) (* 30 h1 (* h2 h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) 
(* 12 h1 (* h2 h2 h2) (* h5 h5 h5 h5) (* h6 h6) j2) (* 2 h1 (* h2 h2 h2) (* h5 
h5 h5 h5) (* h6 h6)) (* 4 h1 (* h2 h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 24 h1 (* h2 h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 60 h1 (* h2 h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 80 h1 (* h2 
h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 60 h1 (* h2 h2 h2) (* h5 h5 h5
) (* h6 h6 h6) (* j2 j2)) (* 24 h1 (* h2 h2 h2) (* h5 h5 h5) (* h6 h6 h6) j2) 
(* 4 h1 (* h2 h2 h2) (* h5 h5 h5) (* h6 h6 h6)) (* 2 h1 (* h2 h2 h2) (* h5 h5) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 12 h1 (* h2 h2 h2) (* h5 h5) (* h6 h6 
h6 h6) (* j2 j2 j2 j2 j2)) (* 30 h1 (* h2 h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2
 j2 j2 j2)) (* 40 h1 (* h2 h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 30 
h1 (* h2 h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 12 h1 (* h2 h2 h2) (* h5
 h5) (* h6 h6 h6 h6) j2) (* 2 h1 (* h2 h2 h2) (* h5 h5) (* h6 h6 h6 h6)) (* 3072
 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 6912 h1 (* h2 
h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 4032 h1 (* h2 h2) (* h3 h3 
h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 912 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) 
h5 (* j2 j2)) (* 72 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 j2) (* 3072 h1 (* 
h2 h2) (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 2816 h1 (* h2 h2) (* 
h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2)) (* 960 h1 (* h2 h2) (* h3 h3 h3 h3) 
(* h4 h4) h6 (* j2 j2 j2)) (* 144 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h6 (* 
j2 j2)) (* 8 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h6 j2) (* 3584 h1 (* h2 h2) 
(* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 12544 h1 (* h2 h2) (* h3 
h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 13664 h1 (* h2 h2) (* h3 h3 h3 h3)
 h4 (* h5 h5) (* j2 j2 j2 j2)) (* 4704 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5)
 (* j2 j2 j2)) (* 504 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2)) (* 
7168 h1 (* h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 20992 h1 
(* h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 20672 h1 (* h2 h2) (* 
h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 9152 h1 (* h2 h2) (* h3 h3 h3 h3) h4 
h5 h6 (* j2 j2 j2)) (* 1872 h1 (* h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2)) (* 
144 h1 (* h2 h2) (* h3 h3 h3 h3) h4 h5 h6 j2) (* 3584 h1 (* h2 h2) (* h3 h3 h3 
h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6400 h1 (* h2 h2) (* h3 h3 h3 h3) h4 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 4576 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6) 
(* j2 j2 j2 j2)) (* 1568 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2))
 (* 256 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2)) (* 16 h1 (* h2 h2) 
(* h3 h3 h3 h3) h4 (* h6 h6) j2) (* 512 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5
) (* j2 j2 j2 j2 j2 j2 j2)) (* 2432 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2)) (* 4032 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 
j2 j2 j2 j2)) (* 2592 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2))
 (* 432 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2)) (* 3584 h1 (* h2
 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 15744 h1 (* h2 h2
) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 24832 h1 (* h2 h2) (* 
h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 16800 h1 (* h2 h2) (* h3 h3 h3 
h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 4608 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5)
 h6 (* j2 j2 j2)) (* 432 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2)) 
(* 3584 h1 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
13952 h1 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 20544 
h1 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 14784 h1 (* h2 
h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 5544 h1 (* h2 h2) (* h3 h3 
h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 1020 h1 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 
h6) (* j2 j2)) (* 72 h1 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) j2) (* 512 h1 (* 
h2 h2) (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1664 h1 (* h2 
h2) (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2176 h1 (* h2 h2) (* 
h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1472 h1 (* h2 h2) (* h3 h3 h3 
h3) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 544 h1 (* h2 h2) (* h3 h3 h3 h3) (* h6 h6 
h6) (* j2 j2 j2)) (* 104 h1 (* h2 h2) (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2)) 
(* 8 h1 (* h2 h2) (* h3 h3 h3 h3) (* h6 h6 h6) j2) (* 1280 h1 (* h2 h2) (* h3 h3
 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 2560 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4
 h4) h5 (* j2 j2 j2)) (* 1040 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2
)) (* 120 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 j2) (* 1280 h1 (* h2 h2) (* 
h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2)) (* 768 h1 (* h2 h2) (* h3 h3 h3) (* 
h4 h4 h4) h6 (* j2 j2 j2)) (* 144 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h6 (* 
j2 j2)) (* 8 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h6 j2) (* 3072 h1 (* h2 h2) 
(* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 9408 h1 (* h2 h2) (* h3 
h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 8784 h1 (* h2 h2) (* h3 h3 h3) 
(* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 2520 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) 
(* h5 h5) (* j2 j2)) (* 216 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) j2) 
(* 6144 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 14912 
h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 12352 h1 (* h2 h2)
 (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 3956 h1 (* h2 h2) (* h3 h3 h3) 
(* h4 h4) h5 h6 (* j2 j2)) (* 434 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 j2) 
(* 2 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6) (* 3072 h1 (* h2 h2) (* h3 h3 h3
) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 4672 h1 (* h2 h2) (* h3 h3 h3) (* 
h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 2224 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) 
(* h6 h6) (* j2 j2 j2)) (* 408 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* 
j2 j2)) (* 24 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6) j2) (* 1792 h1 (* h2
 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 7616 h1 (* h2 h2) 
(* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 11200 h1 (* h2 h2) (* h3 h3 
h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 6384 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 
h5 h5) (* j2 j2 j2)) (* 1008 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2)
) (* 6656 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
25792 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 35984 h1 
(* h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 21776 h1 (* h2 h2) 
(* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 5348 h1 (* h2 h2) (* h3 h3 h3) h4 
(* h5 h5) h6 (* j2 j2)) (* 444 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 j2) (* 
6656 h1 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 21824 
h1 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 27728 h1 (* h2 
h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 16792 h1 (* h2 h2) (* h3 h3
 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 4716 h1 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6
 h6) (* j2 j2)) (* 500 h1 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) j2) (* 4 h1 (* 
h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6)) (* 1792 h1 (* h2 h2) (* h3 h3 h3) h4 (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4416 h1 (* h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2)) (* 4064 h1 (* h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 
j2 j2)) (* 1760 h1 (* h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2)) (* 344 
h1 (* h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2)) (* 24 h1 (* h2 h2) (* h3 h3
 h3) h4 (* h6 h6 h6) j2) (* 128 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 
j2 j2 j2 j2 j2 j2)) (* 704 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2
 j2 j2 j2)) (* 1440 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)
) (* 1296 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 432 h1 
(* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 1792 h1 (* h2 h2) (* h3 
h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 9312 h1 (* h2 h2) (* h3 h3 
h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 18400 h1 (* h2 h2) (* h3 h3 h3) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 16952 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 
h5) h6 (* j2 j2 j2 j2)) (* 7008 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 
j2 j2)) (* 936 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2)) (* 3328 h1 
(* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 16128 h1
 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 30528 h1 
(* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 28448 h1 (* h2
 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 13416 h1 (* h2 h2) (* 
h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 2924 h1 (* h2 h2) (* h3 h3 h3) 
(* h5 h5) (* h6 h6) (* j2 j2)) (* 228 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 
h6) j2) (* 1792 h1 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 8160 h1 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 14816 h1 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 13728 
h1 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 6864 h1 (* h2 h2) 
(* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 1766 h1 (* h2 h2) (* h3 h3 h3) h5 
(* h6 h6 h6) (* j2 j2)) (* 184 h1 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) j2) (* 
2 h1 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6)) (* 128 h1 (* h2 h2) (* h3 h3 h3) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 512 h1 (* h2 h2) (* h3 h3 h3) (* h6
 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 832 h1 (* h2 h2) (* h3 h3 h3) (* h6 h6 h6 
h6) (* j2 j2 j2 j2 j2)) (* 704 h1 (* h2 h2) (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 
j2 j2 j2)) (* 328 h1 (* h2 h2) (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 80 
h1 (* h2 h2) (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2)) (* 8 h1 (* h2 h2) (* h3 h3 
h3) (* h6 h6 h6 h6) j2) (* 96 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2
 j2)) (* 168 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2)) (* 36 h1 (* h2
 h2) (* h3 h3) (* h4 h4 h4 h4) h5 j2) (* 96 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4 
h4) h6 (* j2 j2 j2)) (* 24 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) h6 (* j2 j2)) 
(* 640 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 1760 h1
 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 1360 h1 (* h2 h2) 
(* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 240 h1 (* h2 h2) (* h3 h3) (* h4 
h4 h4) (* h5 h5) j2) (* 1280 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 
j2 j2)) (* 2352 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 1324 
h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2)) (* 222 h1 (* h2 h2) (* h3 
h3) (* h4 h4 h4) h5 h6 j2) (* 2 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6) (* 
640 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 576 h1 (* 
h2 h2) (* h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2)) (* 112 h1 (* h2 h2) (* h3 
h3) (* h4 h4 h4) (* h6 h6) (* j2 j2)) (* 768 h1 (* h2 h2) (* h3 h3) (* h4 h4) 
(* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 2928 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 
h5 h5) (* j2 j2 j2 j2)) (* 3816 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) 
(* j2 j2 j2)) (* 1872 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2)) 
(* 216 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) j2) (* 2688 h1 (* h2 h2) 
(* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 8976 h1 (* h2 h2) (* h3 
h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 10820 h1 (* h2 h2) (* h3 h3) (* 
h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 5378 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5
 h5) h6 (* j2 j2)) (* 852 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 j2) (* 6
 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6) (* 2688 h1 (* h2 h2) (* h3 h3) 
(* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 7184 h1 (* h2 h2) (* h3 h3) (* h4 
h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 6988 h1 (* h2 h2) (* h3 h3) (* h4 h4) h5 
(* h6 h6) (* j2 j2 j2)) (* 2930 h1 (* h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6) 
(* j2 j2)) (* 444 h1 (* h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6) j2) (* 6 h1 (* 
h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6)) (* 768 h1 (* h2 h2) (* h3 h3) (* h4 h4)
 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1456 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h6
 h6 h6) (* j2 j2 j2 j2)) (* 848 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h6 h6 h6) 
(* j2 j2 j2)) (* 152 h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2)) 
(* 224 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1120 
h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 2072 h1 (* h2 
h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 1680 h1 (* h2 h2) (* h3 h3)
 h4 (* h5 h5 h5 h5) (* j2 j2 j2)) (* 504 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 
h5) (* j2 j2)) (* 1664 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2)) (* 7808 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) 
(* 13920 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 11536 h1 
(* h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 4216 h1 (* h2 h2) (* h3 
h3) h4 (* h5 h5 h5) h6 (* j2 j2)) (* 456 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) 
h6 j2) (* 2880 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 12240 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 20534 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 16810
 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 6586 h1 (* h2 h2
) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 962 h1 (* h2 h2) (* h3 h3) h4 
(* h5 h5) (* h6 h6) j2) (* 12 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6)) (* 
1664 h1 (* h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6144 h1
 (* h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 9000 h1 (* h2 h2)
 (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 6580 h1 (* h2 h2) (* h3 h3) h4
 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 2410 h1 (* h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6)
 (* j2 j2)) (* 356 h1 (* h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) j2) (* 6 h1 (* h2 
h2) (* h3 h3) h4 h5 (* h6 h6 h6)) (* 224 h1 (* h2 h2) (* h3 h3) h4 (* h6 h6 h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 672 h1 (* h2 h2) (* h3 h3) h4 (* h6 h6 h6 h6) (* 
j2 j2 j2 j2 j2)) (* 736 h1 (* h2 h2) (* h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2
)) (* 352 h1 (* h2 h2) (* h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 64 h1 (* h2
 h2) (* h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2)) (* 224 h1 (* h2 h2) (* h3 h3) (* h5
 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1344 h1 (* h2 h2) (* h3 h3) (* h5 h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 3192 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2)) (* 3752 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 
j2 j2 j2)) (* 2184 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 
504 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 832 h1 (* h2 h2) (* 
h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4744 h1 (* h2 h2) (* 
h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 10900 h1 (* h2 h2) (* h3
 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 12796 h1 (* h2 h2) (* h3 h3) 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 7948 h1 (* h2 h2) (* h3 h3) (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2)) (* 2380 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6
) (* j2 j2)) (* 240 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) j2) (* 832 h1 
(* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4568 h1 
(* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 10224 h1 
(* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 11912 h1 (* h2
 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 7598 h1 (* h2 h2) (* 
h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 2514 h1 (* h2 h2) (* h3 h3) (* h5
 h5) (* h6 h6 h6) (* j2 j2)) (* 346 h1 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6
) j2) (* 6 h1 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6)) (* 224 h1 (* h2 h2) 
(* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1184 h1 (* h2 h2) (* 
h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2568 h1 (* h2 h2) (* h3 h3) 
h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2932 h1 (* h2 h2) (* h3 h3) h5 (* h6 
h6 h6 h6) (* j2 j2 j2 j2)) (* 1870 h1 (* h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* 
j2 j2 j2)) (* 642 h1 (* h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2)) (* 98 h1 
(* h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) j2) (* 2 h1 (* h2 h2) (* h3 h3) h5 (* h6 
h6 h6 h6)) (* 24 h1 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 60 
h1 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2)) (* 36 h1 (* h2 h2) h3 (* h4
 h4 h4 h4) (* h5 h5) j2) (* 48 h1 (* h2 h2) h3 (* h4 h4 h4 h4) h5 h6 (* j2 j2 j2
)) (* 54 h1 (* h2 h2) h3 (* h4 h4 h4 h4) h5 h6 (* j2 j2)) (* 6 h1 (* h2 h2) h3 
(* h4 h4 h4 h4) h5 h6 j2) (* 24 h1 (* h2 h2) h3 (* h4 h4 h4 h4) (* h6 h6) (* j2 
j2 j2)) (* 80 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 280 
h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 320 h1 (* h2 h2) h3 
(* h4 h4 h4) (* h5 h5 h5) (* j2 j2)) (* 120 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 
h5 h5) j2) (* 320 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 
848 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 752 h1 (* h2 h2) 
h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 228 h1 (* h2 h2) h3 (* h4 h4 h4) (* 
h5 h5) h6 j2) (* 4 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6) (* 320 h1 (* h2 h2
) h3 (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 568 h1 (* h2 h2) h3 (* h4 h4 
h4) h5 (* h6 h6) (* j2 j2 j2)) (* 276 h1 (* h2 h2) h3 (* h4 h4 h4) h5 (* h6 h6) 
(* j2 j2)) (* 28 h1 (* h2 h2) h3 (* h4 h4 h4) h5 (* h6 h6) j2) (* 80 h1 (* h2 h2
) h3 (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 72 h1 (* h2 h2) h3 (* h4 h4 
h4) (* h6 h6 h6) (* j2 j2 j2)) (* 48 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) 
(* j2 j2 j2 j2 j2)) (* 216 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2
 j2)) (* 360 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 264 h1 
(* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 72 h1 (* h2 h2) h3 (* h4 h4
) (* h5 h5 h5 h5) j2) (* 384 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2)) (* 1556 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) 
(* 2394 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 1662 h1 (* h2
 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 446 h1 (* h2 h2) h3 (* h4 h4) 
(* h5 h5 h5) h6 j2) (* 6 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6) (* 672 h1 
(* h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2372 h1 (* h2 
h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 3162 h1 (* h2 h2) h3 
(* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 1904 h1 (* h2 h2) h3 (* h4 h4) 
(* h5 h5) (* h6 h6) (* j2 j2)) (* 454 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 
h6) j2) (* 12 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6)) (* 384 h1 (* h2 h2)
 h3 (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1076 h1 (* h2 h2) h3 (* h4 
h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1040 h1 (* h2 h2) h3 (* h4 h4) h5 (* h6 
h6 h6) (* j2 j2 j2)) (* 386 h1 (* h2 h2) h3 (* h4 h4) h5 (* h6 h6 h6) (* j2 j2))
 (* 38 h1 (* h2 h2) h3 (* h4 h4) h5 (* h6 h6 h6) j2) (* 48 h1 (* h2 h2) h3 (* h4
 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 96 h1 (* h2 h2) h3 (* h4 h4) (* h6 
h6 h6 h6) (* j2 j2 j2 j2)) (* 48 h1 (* h2 h2) h3 (* h4 h4) (* h6 h6 h6 h6) (* j2
 j2 j2)) (* 112 h1 (* h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
608 h1 (* h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 1308 h1 (* h2 
h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 1396 h1 (* h2 h2) h3 h4 (* h5 
h5 h5 h5) h6 (* j2 j2 j2)) (* 740 h1 (* h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2
)) (* 156 h1 (* h2 h2) h3 h4 (* h5 h5 h5 h5) h6 j2) (* 416 h1 (* h2 h2) h3 h4 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2092 h1 (* h2 h2) h3 h4 (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 4256 h1 (* h2 h2) h3 h4 (* h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2)) (* 4388 h1 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 
j2 j2)) (* 2308 h1 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 512 h1 
(* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) j2) (* 12 h1 (* h2 h2) h3 h4 (* h5 h5 h5)
 (* h6 h6)) (* 416 h1 (* h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 1924 h1 (* h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
3594 h1 (* h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 3410 h1 (* h2
 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 1666 h1 (* h2 h2) h3 h4 (* h5
 h5) (* h6 h6 h6) (* j2 j2)) (* 354 h1 (* h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) j2
) (* 12 h1 (* h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6)) (* 112 h1 (* h2 h2) h3 h4 h5 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 448 h1 (* h2 h2) h3 h4 h5 (* h6 h6 h6 
h6) (* j2 j2 j2 j2 j2)) (* 688 h1 (* h2 h2) h3 h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2
 j2)) (* 496 h1 (* h2 h2) h3 h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 160 h1 (* h2
 h2) h3 h4 h5 (* h6 h6 h6 h6) (* j2 j2)) (* 16 h1 (* h2 h2) h3 h4 h5 (* h6 h6 h6
 h6) j2) (* 56 h1 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2
)) (* 364 h1 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
980 h1 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1400 h1 (* 
h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 1120 h1 (* h2 h2) h3 (* 
h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 476 h1 (* h2 h2) h3 (* h5 h5 h5 h5) (* 
h6 h6) (* j2 j2)) (* 84 h1 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) j2) (* 112 h1 
(* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 714 h1 (* h2
 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1896 h1 (* h2 h2) h3
 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2690 h1 (* h2 h2) h3 (* h5 h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 2160 h1 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 
h6) (* j2 j2 j2)) (* 942 h1 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) 
(* 184 h1 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) j2) (* 6 h1 (* h2 h2) h3 (* h5 
h5 h5) (* h6 h6 h6)) (* 56 h1 (* h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2
 j2 j2 j2 j2)) (* 352 h1 (* h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 924 h1 (* h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
1300 h1 (* h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 1040 h1 (* h2
 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 456 h1 (* h2 h2) h3 (* h5 h5)
 (* h6 h6 h6 h6) (* j2 j2)) (* 92 h1 (* h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) j2) 
(* 4 h1 (* h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6)) (* 6 h1 (* h2 h2) (* h4 h4 h4 h4
) (* h5 h5) h6 (* j2 j2 j2)) (* 12 h1 (* h2 h2) (* h4 h4 h4 h4) (* h5 h5) h6 (* 
j2 j2)) (* 6 h1 (* h2 h2) (* h4 h4 h4 h4) (* h5 h5) h6 j2) (* 6 h1 (* h2 h2) (* 
h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 6 h1 (* h2 h2) (* h4 h4 h4 h4) h5 (* 
h6 h6) (* j2 j2)) (* 20 h1 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2
)) (* 62 h1 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 66 h1 (* h2 
h2) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 26 h1 (* h2 h2) (* h4 h4 h4) (* 
h5 h5 h5) h6 j2) (* 2 h1 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5) h6) (* 40 h1 (* h2 
h2) (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 106 h1 (* h2 h2) (* h4 
h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 92 h1 (* h2 h2) (* h4 h4 h4) (* h5 
h5) (* h6 h6) (* j2 j2)) (* 26 h1 (* h2 h2) (* h4 h4 h4) (* h5 h5) (* h6 h6) j2)
 (* 20 h1 (* h2 h2) (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 38 h1 (* h2
 h2) (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 18 h1 (* h2 h2) (* h4 h4 h4) 
h5 (* h6 h6 h6) (* j2 j2)) (* 12 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2
 j2 j2 j2 j2)) (* 50 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) 
(* 80 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 60 h1 (* h2 h2)
 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 20 h1 (* h2 h2) (* h4 h4) (* h5 h5 
h5 h5) h6 j2) (* 2 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5 h5) h6) (* 48 h1 (* h2 h2)
 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 196 h1 (* h2 h2) (* h4 
h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 306 h1 (* h2 h2) (* h4 h4) (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2)) (* 222 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 
h6) (* j2 j2)) (* 70 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6) j2) (* 6 h1 
(* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6)) (* 48 h1 (* h2 h2) (* h4 h4) (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 178 h1 (* h2 h2) (* h4 h4) (* h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2)) (* 246 h1 (* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2)) (* 150 h1 (* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2)) 
(* 34 h1 (* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6 h6) j2) (* 12 h1 (* h2 h2) (* h4
 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 36 h1 (* h2 h2) (* h4 h4) h5 (* 
h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 36 h1 (* h2 h2) (* h4 h4) h5 (* h6 h6 h6 h6) 
(* j2 j2 j2)) (* 12 h1 (* h2 h2) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2)) (* 14 
h1 (* h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 74 h1 (* h2 
h2) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 160 h1 (* h2 h2) h4 (* 
h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 180 h1 (* h2 h2) h4 (* h5 h5 h5 h5) 
(* h6 h6) (* j2 j2 j2)) (* 110 h1 (* h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 
j2)) (* 34 h1 (* h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6) j2) (* 4 h1 (* h2 h2) h4 
(* h5 h5 h5 h5) (* h6 h6)) (* 28 h1 (* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2)) (* 146 h1 (* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2)) (* 310 h1 (* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 340
 h1 (* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 200 h1 (* h2 h2) h4 
(* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 58 h1 (* h2 h2) h4 (* h5 h5 h5) (* h6 h6
 h6) j2) (* 6 h1 (* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6)) (* 14 h1 (* h2 h2) h4 
(* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 70 h1 (* h2 h2) h4 (* h5 h5)
 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 140 h1 (* h2 h2) h4 (* h5 h5) (* h6 h6 
h6 h6) (* j2 j2 j2 j2)) (* 140 h1 (* h2 h2) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 
j2 j2)) (* 70 h1 (* h2 h2) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 14 h1 (* 
h2 h2) h4 (* h5 h5) (* h6 h6 h6 h6) j2) (* 2 h1 (* h2 h2) (* h5 h5 h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 14 h1 (* h2 h2) (* h5 h5 h5 h5) (* h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2)) (* 42 h1 (* h2 h2) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2
 j2 j2 j2)) (* 70 h1 (* h2 h2) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 
70 h1 (* h2 h2) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 42 h1 (* h2 h2) 
(* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 14 h1 (* h2 h2) (* h5 h5 h5 h5) (* h6
 h6 h6) j2) (* 2 h1 (* h2 h2) (* h5 h5 h5 h5) (* h6 h6 h6)) (* 2 h1 (* h2 h2) 
(* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 14 h1 (* h2 h2) (* h5 
h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 42 h1 (* h2 h2) (* h5 h5 h5) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 70 h1 (* h2 h2) (* h5 h5 h5) (* h6 h6 h6 
h6) (* j2 j2 j2 j2)) (* 70 h1 (* h2 h2) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2
)) (* 42 h1 (* h2 h2) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 14 h1 (* h2 h2)
 (* h5 h5 h5) (* h6 h6 h6 h6) j2) (* 2 h1 (* h2 h2) (* h5 h5 h5) (* h6 h6 h6 h6)
) (* 1024 h1 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 2304 h1 
h2 (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 1344 h1 h2 (* h3 h3 h3 h3
) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 304 h1 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* 
j2 j2)) (* 24 h1 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h5 j2) (* 1024 h1 h2 (* h3 h3 
h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 768 h1 h2 (* h3 h3 h3 h3) (* h4 h4
 h4) h6 (* j2 j2 j2 j2)) (* 192 h1 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 
j2)) (* 16 h1 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2)) (* 3584 h1 h2 (* h3 
h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 12544 h1 h2 (* h3 h3 h3 
h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 13664 h1 h2 (* h3 h3 h3 h3) (* h4
 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 4704 h1 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5
) (* j2 j2 j2)) (* 504 h1 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 
7168 h1 h2 (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 18432 h1 h2
 (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 14912 h1 h2 (* h3 h3 h3 
h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 5792 h1 h2 (* h3 h3 h3 h3) (* h4 h4) h5 
h6 (* j2 j2 j2)) (* 1112 h1 h2 (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 84 
h1 h2 (* h3 h3 h3 h3) (* h4 h4) h5 h6 j2) (* 3584 h1 h2 (* h3 h3 h3 h3) (* h4 h4
) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4864 h1 h2 (* h3 h3 h3 h3) (* h4 h4) (* h6
 h6) (* j2 j2 j2 j2 j2)) (* 2400 h1 h2 (* h3 h3 h3 h3) (* h4 h4) (* h6 h6) (* j2
 j2 j2 j2)) (* 512 h1 h2 (* h3 h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 40
 h1 h2 (* h3 h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2)) (* 2048 h1 h2 (* h3 h3 h3 
h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 9728 h1 h2 (* h3 h3 h3 h3) h4 
(* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 16128 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5 
h5) (* j2 j2 j2 j2 j2)) (* 10368 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 
j2 j2)) (* 1728 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2)) (* 8192 h1 
h2 (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 34816 h1 h2 (* 
h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 52992 h1 h2 (* h3 h3 h3 
h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 35008 h1 h2 (* h3 h3 h3 h3) h4 (* h5 
h5) h6 (* j2 j2 j2 j2)) (* 9984 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 
j2)) (* 1008 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 8192 h1 h2 (* 
h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 28160 h1 h2 (* h3 h3 
h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 35968 h1 h2 (* h3 h3 h3 h3) h4 
h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 22848 h1 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6) 
(* j2 j2 j2 j2)) (* 7776 h1 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 
1360 h1 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 96 h1 h2 (* h3 h3 h3 h3
) h4 h5 (* h6 h6) j2) (* 2048 h1 h2 (* h3 h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 4608 h1 h2 (* h3 h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2
)) (* 3968 h1 h2 (* h3 h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1632 h1 
h2 (* h3 h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 320 h1 h2 (* h3 h3 h3 h3)
 h4 (* h6 h6 h6) (* j2 j2 j2)) (* 24 h1 h2 (* h3 h3 h3 h3) h4 (* h6 h6 h6) (* j2
 j2)) (* 2048 h1 h2 (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2))
 (* 11776 h1 h2 (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
25856 h1 h2 (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 26496 h1 
h2 (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 12096 h1 h2 (* h3 h3 
h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 1728 h1 h2 (* h3 h3 h3 h3) (* h5 h5 
h5) h6 (* j2 j2 j2)) (* 4096 h1 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 21504 h1 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 43904 h1 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 44000 h1 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)
) (* 22496 h1 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 5496 h1
 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 504 h1 h2 (* h3 h3 h3 
h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 2048 h1 h2 (* h3 h3 h3 h3) h5 (* h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 9728 h1 h2 (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 18560 h1 h2 (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 18464 h1 h2 (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2))
 (* 10352 h1 h2 (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 3272 h1 h2 
(* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 540 h1 h2 (* h3 h3 h3 h3) h5 
(* h6 h6 h6) (* j2 j2)) (* 36 h1 h2 (* h3 h3 h3 h3) h5 (* h6 h6 h6) j2) (* 256 
h1 h2 (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 512 h1 h2 (* h3 h3 h3)
 (* h4 h4 h4 h4) h5 (* j2 j2 j2)) (* 208 h1 h2 (* h3 h3 h3) (* h4 h4 h4 h4) h5 
(* j2 j2)) (* 24 h1 h2 (* h3 h3 h3) (* h4 h4 h4 h4) h5 j2) (* 256 h1 h2 (* h3 h3
 h3) (* h4 h4 h4 h4) h6 (* j2 j2 j2 j2)) (* 128 h1 h2 (* h3 h3 h3) (* h4 h4 h4 
h4) h6 (* j2 j2 j2)) (* 16 h1 h2 (* h3 h3 h3) (* h4 h4 h4 h4) h6 (* j2 j2)) (* 
1536 h1 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 4800 h1 h2
 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 4464 h1 h2 (* h3 h3 h3)
 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 1128 h1 h2 (* h3 h3 h3) (* h4 h4 h4) 
(* h5 h5) (* j2 j2)) (* 72 h1 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) j2) (* 3072
 h1 h2 (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 6592 h1 h2 (* h3 
h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 4192 h1 h2 (* h3 h3 h3) (* h4 h4 
h4) h5 h6 (* j2 j2 j2)) (* 1132 h1 h2 (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2))
 (* 112 h1 h2 (* h3 h3 h3) (* h4 h4 h4) h5 h6 j2) (* 1536 h1 h2 (* h3 h3 h3) (* 
h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1600 h1 h2 (* h3 h3 h3) (* h4 h4 h4) 
(* h6 h6) (* j2 j2 j2 j2)) (* 528 h1 h2 (* h3 h3 h3) (* h4 h4 h4) (* h6 h6) (* 
j2 j2 j2)) (* 56 h1 h2 (* h3 h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2)) (* 1792 h1
 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 7616 h1 h2 (* 
h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 11200 h1 h2 (* h3 h3 h3)
 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 6384 h1 h2 (* h3 h3 h3) (* h4 h4) 
(* h5 h5 h5) (* j2 j2 j2)) (* 1008 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* 
j2 j2)) (* 6656 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2))
 (* 24512 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 32304
 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 18296 h1 h2 (* h3
 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 3968 h1 h2 (* h3 h3 h3) (* h4 h4
) (* h5 h5) h6 (* j2 j2)) (* 264 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 j2) 
(* 6656 h1 h2 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
19008 h1 h2 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 20016 h1 
h2 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 9576 h1 h2 (* h3 h3 
h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 2174 h1 h2 (* h3 h3 h3) (* h4 h4) h5
 (* h6 h6) (* j2 j2)) (* 190 h1 h2 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) j2) (* 
1792 h1 h2 (* h3 h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3520 h1
 h2 (* h3 h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2368 h1 h2 (* h3 
h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 656 h1 h2 (* h3 h3 h3) (* h4 
h4) (* h6 h6 h6) (* j2 j2 j2)) (* 64 h1 h2 (* h3 h3 h3) (* h4 h4) (* h6 h6 h6) 
(* j2 j2)) (* 512 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)
) (* 2816 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 5760 
h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 5184 h1 h2 (* h3 h3
 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 1728 h1 h2 (* h3 h3 h3) h4 (* h5 h5 
h5 h5) (* j2 j2 j2)) (* 4096 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2)) (* 20864 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2)) (* 40352 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 36448
 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 14952 h1 h2 (* h3 h3 
h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 2088 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5) 
h6 (* j2 j2)) (* 7168 h1 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 32640 h1 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 58208 h1 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
51440 h1 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 22992 h1 h2 
(* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 4600 h1 h2 (* h3 h3 h3) h4 
(* h5 h5) (* h6 h6) (* j2 j2)) (* 312 h1 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) 
j2) (* 4096 h1 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
15744 h1 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 24256 h1 
h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 19104 h1 h2 (* h3 h3 
h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 8040 h1 h2 (* h3 h3 h3) h4 h5 (* h6 
h6 h6) (* j2 j2 j2)) (* 1682 h1 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2)) 
(* 138 h1 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6) j2) (* 512 h1 h2 (* h3 h3 h3) h4 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1536 h1 h2 (* h3 h3 h3) h4 (* h6 h6
 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1760 h1 h2 (* h3 h3 h3) h4 (* h6 h6 h6 h6) (* 
j2 j2 j2 j2 j2)) (* 960 h1 h2 (* h3 h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) 
(* 248 h1 h2 (* h3 h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 24 h1 h2 (* h3 h3 
h3) h4 (* h6 h6 h6 h6) (* j2 j2)) (* 512 h1 h2 (* h3 h3 h3) (* h5 h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3328 h1 h2 (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2
 j2 j2 j2 j2 j2 j2)) (* 8576 h1 h2 (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2)) (* 10944 h1 h2 (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) 
(* 6912 h1 h2 (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 1728 h1 h2 (* 
h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 2048 h1 h2 (* h3 h3 h3) (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 12544 h1 h2 (* h3 h3 h3) (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 30944 h1 h2 (* h3 h3 h3) (* h5 h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 39072 h1 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6
 h6) (* j2 j2 j2 j2 j2)) (* 26328 h1 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2)) (* 8784 h1 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) 
(* 1080 h1 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 2048 h1 h2 (* h3
 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 11776 h1 h2 (* h3
 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 27712 h1 h2 (* h3 h3
 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 34328 h1 h2 (* h3 h3 h3) 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 23892 h1 h2 (* h3 h3 h3) (* h5 h5)
 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 9176 h1 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6)
 (* j2 j2 j2)) (* 1748 h1 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 
120 h1 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) j2) (* 512 h1 h2 (* h3 h3 h3) h5 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2816 h1 h2 (* h3 h3 h3) h5 (* h6
 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 6368 h1 h2 (* h3 h3 h3) h5 (* h6 h6 h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 7664 h1 h2 (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 
j2 j2 j2 j2)) (* 5288 h1 h2 (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 
2084 h1 h2 (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 432 h1 h2 (* h3 h3 
h3) h5 (* h6 h6 h6 h6) (* j2 j2)) (* 36 h1 h2 (* h3 h3 h3) h5 (* h6 h6 h6 h6) j2
) (* 128 h1 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 352 h1 h2
 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 272 h1 h2 (* h3 h3) (* h4 
h4 h4 h4) (* h5 h5) (* j2 j2)) (* 48 h1 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) 
j2) (* 256 h1 h2 (* h3 h3) (* h4 h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 368 h1 h2 
(* h3 h3) (* h4 h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 92 h1 h2 (* h3 h3) (* h4 h4 h4 
h4) h5 h6 (* j2 j2)) (* 4 h1 h2 (* h3 h3) (* h4 h4 h4 h4) h5 h6 j2) (* 128 h1 h2
 (* h3 h3) (* h4 h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 32 h1 h2 (* h3 h3) (* 
h4 h4 h4 h4) (* h6 h6) (* j2 j2 j2)) (* 384 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 
h5 h5) (* j2 j2 j2 j2 j2)) (* 1488 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* 
j2 j2 j2 j2)) (* 1944 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2)) 
(* 912 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2)) (* 72 h1 h2 (* h3 h3
) (* h4 h4 h4) (* h5 h5 h5) j2) (* 1408 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) 
h6 (* j2 j2 j2 j2 j2)) (* 4272 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 
j2 j2 j2)) (* 4372 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 
1748 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 240 h1 h2 (* h3 h3)
 (* h4 h4 h4) (* h5 h5) h6 j2) (* 1408 h1 h2 (* h3 h3) (* h4 h4 h4) h5 (* h6 h6)
 (* j2 j2 j2 j2 j2)) (* 2864 h1 h2 (* h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 
j2 j2)) (* 1780 h1 h2 (* h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 362 
h1 h2 (* h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2)) (* 14 h1 h2 (* h3 h3) (* h4
 h4 h4) h5 (* h6 h6) j2) (* 384 h1 h2 (* h3 h3) (* h4 h4 h4) (* h6 h6 h6) (* j2 
j2 j2 j2 j2)) (* 400 h1 h2 (* h3 h3) (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2)) 
(* 72 h1 h2 (* h3 h3) (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2)) (* 224 h1 h2 (* h3
 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1120 h1 h2 (* h3 h3) 
(* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 2072 h1 h2 (* h3 h3) (* h4 h4) 
(* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 1680 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 
h5) (* j2 j2 j2)) (* 504 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2)) 
(* 1664 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 7488
 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 12760 h1 h2 
(* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 10036 h1 h2 (* h3 h3) 
(* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 3376 h1 h2 (* h3 h3) (* h4 h4) (* h5 
h5 h5) h6 (* j2 j2)) (* 276 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 j2) (* 
2880 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
11024 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 16206
 h1 h2 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 11240 h1 h2 
(* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 3606 h1 h2 (* h3 h3) 
(* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 428 h1 h2 (* h3 h3) (* h4 h4) (* h5 
h5) (* h6 h6) j2) (* 1664 h1 h2 (* h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 4992 h1 h2 (* h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2))
 (* 5392 h1 h2 (* h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 2492 h1 
h2 (* h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 444 h1 h2 (* h3 h3) (* 
h4 h4) h5 (* h6 h6 h6) (* j2 j2)) (* 16 h1 h2 (* h3 h3) (* h4 h4) h5 (* h6 h6 h6
) j2) (* 224 h1 h2 (* h3 h3) (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 448 h1 h2 (* h3 h3) (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 264 h1 
h2 (* h3 h3) (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 40 h1 h2 (* h3 h3) 
(* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 512 h1 h2 (* h3 h3) h4 (* h5 h5 h5 h5
) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 3040 h1 h2 (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2)) (* 7136 h1 h2 (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2
 j2)) (* 8280 h1 h2 (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 4752 h1 
h2 (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 1080 h1 h2 (* h3 h3) h4 (* 
h5 h5 h5 h5) h6 (* j2 j2)) (* 1792 h1 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 9760 h1 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 21440 h1 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2)) (* 24088 h1 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 
14272 h1 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 3992 h1 h2 (* 
h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 336 h1 h2 (* h3 h3) h4 (* h5 h5 
h5) (* h6 h6) j2) (* 1792 h1 h2 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 8736 h1 h2 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 17392 h1 h2 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 18010 h1 h2 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 10148 h1 
h2 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 2906 h1 h2 (* h3 h3) h4 
(* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 320 h1 h2 (* h3 h3) h4 (* h5 h5) (* h6 h6 
h6) j2) (* 512 h1 h2 (* h3 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 2112 h1 h2 (* h3 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3408 h1 
h2 (* h3 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2688 h1 h2 (* h3 h3) 
h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 1046 h1 h2 (* h3 h3) h4 h5 (* h6 h6 h6
 h6) (* j2 j2 j2)) (* 172 h1 h2 (* h3 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2)) (* 6 
h1 h2 (* h3 h3) h4 h5 (* h6 h6 h6 h6) j2) (* 256 h1 h2 (* h3 h3) (* h5 h5 h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1792 h1 h2 (* h3 h3) (* h5 h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 5184 h1 h2 (* h3 h3) (* h5 h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 7936 h1 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* 6784 h1 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2)) (* 3072 h1 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 576 
h1 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 512 h1 h2 (* h3 h3) (* 
h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3424 h1 h2 (* h3 h3) (* 
h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 9576 h1 h2 (* h3 h3) (* h5 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 14436 h1 h2 (* h3 h3) (* h5 h5 h5)
 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 12544 h1 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6
 h6) (* j2 j2 j2 j2)) (* 6168 h1 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2
 j2)) (* 1528 h1 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 132 h1 h2 
(* h3 h3) (* h5 h5 h5) (* h6 h6 h6) j2) (* 256 h1 h2 (* h3 h3) (* h5 h5) (* h6 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1664 h1 h2 (* h3 h3) (* h5 h5) (* h6 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4536 h1 h2 (* h3 h3) (* h5 h5) (* h6 h6 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6708 h1 h2 (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2)) (* 5792 h1 h2 (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 
j2 j2)) (* 2904 h1 h2 (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 776 
h1 h2 (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 84 h1 h2 (* h3 h3) (* h5
 h5) (* h6 h6 h6 h6) j2) (* 16 h1 h2 h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2
 j2)) (* 56 h1 h2 h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 64 h1 h2 h3 
(* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2)) (* 24 h1 h2 h3 (* h4 h4 h4 h4) (* h5 h5 
h5) j2) (* 64 h1 h2 h3 (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 144 h1 
h2 h3 (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 88 h1 h2 h3 (* h4 h4 h4 h4) 
(* h5 h5) h6 (* j2 j2)) (* 8 h1 h2 h3 (* h4 h4 h4 h4) (* h5 h5) h6 j2) (* 64 h1 
h2 h3 (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 72 h1 h2 h3 (* h4 h4 h4 
h4) h5 (* h6 h6) (* j2 j2 j2)) (* 8 h1 h2 h3 (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 
j2)) (* 16 h1 h2 h3 (* h4 h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 16 h1 h2 h3
 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 72 h1 h2 h3 (* h4 h4 h4) 
(* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 120 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5 h5) 
(* j2 j2 j2)) (* 88 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 24 h1 h2
 h3 (* h4 h4 h4) (* h5 h5 h5 h5) j2) (* 192 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2)) (* 732 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 
j2)) (* 1020 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 612 h1 h2 h3
 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 132 h1 h2 h3 (* h4 h4 h4) (* h5 h5 
h5) h6 j2) (* 352 h1 h2 h3 (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 1028 h1 h2 h3 (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 1030 h1 h2
 h3 (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 384 h1 h2 h3 (* h4 h4 h4) 
(* h5 h5) (* h6 h6) (* j2 j2)) (* 30 h1 h2 h3 (* h4 h4 h4) (* h5 h5) (* h6 h6) 
j2) (* 192 h1 h2 h3 (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 380 h1 
h2 h3 (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 206 h1 h2 h3 (* h4 h4 h4)
 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 18 h1 h2 h3 (* h4 h4 h4) h5 (* h6 h6 h6) (* j2
 j2)) (* 16 h1 h2 h3 (* h4 h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 16 h1 
h2 h3 (* h4 h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 112 h1 h2 h3 (* h4 h4) 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 568 h1 h2 h3 (* h4 h4) (* h5 h5 h5 
h5) h6 (* j2 j2 j2 j2 j2)) (* 1128 h1 h2 h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 
j2 j2 j2)) (* 1096 h1 h2 h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 520 h1
 h2 h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 96 h1 h2 h3 (* h4 h4) (* h5 h5
 h5 h5) h6 j2) (* 416 h1 h2 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 1916 h1 h2 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 3510 h1 h2 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 3186 h1 h2
 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 1426 h1 h2 h3 (* h4 h4) 
(* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 250 h1 h2 h3 (* h4 h4) (* h5 h5 h5) (* h6 
h6) j2) (* 416 h1 h2 h3 (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 1636 h1 h2 h3 (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2452 h1
 h2 h3 (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1696 h1 h2 h3 (* h4 
h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 500 h1 h2 h3 (* h4 h4) (* h5 h5) (* 
h6 h6 h6) (* j2 j2)) (* 36 h1 h2 h3 (* h4 h4) (* h5 h5) (* h6 h6 h6) j2) (* 112 
h1 h2 h3 (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 336 h1 h2 h3 (* 
h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 346 h1 h2 h3 (* h4 h4) h5 (* h6
 h6 h6 h6) (* j2 j2 j2 j2)) (* 132 h1 h2 h3 (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 
j2 j2)) (* 10 h1 h2 h3 (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2)) (* 128 h1 h2 h3 
h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 784 h1 h2 h3 h4 (* h5 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1976 h1 h2 h3 h4 (* h5 h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 2624 h1 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2)) (* 1936 h1 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 752
 h1 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 120 h1 h2 h3 h4 (* h5 h5 h5
 h5) (* h6 h6) j2) (* 256 h1 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 1464 h1 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 3486 h1 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 4424 h1 h2 
h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 3156 h1 h2 h3 h4 (* h5 h5 h5
) (* h6 h6 h6) (* j2 j2 j2)) (* 1200 h1 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2
 j2)) (* 190 h1 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6) j2) (* 128 h1 h2 h3 h4 (* h5 
h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 656 h1 h2 h3 h4 (* h5 h5) (* h6
 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1358 h1 h2 h3 h4 (* h5 h5) (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2)) (* 1432 h1 h2 h3 h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2
)) (* 788 h1 h2 h3 h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 200 h1 h2 h3 h4
 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 14 h1 h2 h3 h4 (* h5 h5) (* h6 h6 h6 h6
) j2) (* 32 h1 h2 h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 240 h1 h2 h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 768 h1
 h2 h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1360 h1 h2 h3 (* 
h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1440 h1 h2 h3 (* h5 h5 h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2)) (* 912 h1 h2 h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2
 j2 j2)) (* 320 h1 h2 h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 48 h1 h2 h3 
(* h5 h5 h5 h5) (* h6 h6 h6) j2) (* 32 h1 h2 h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 240 h1 h2 h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 768 h1 h2 h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 1360 h1 h2 h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1440 
h1 h2 h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 912 h1 h2 h3 (* h5 h5 
h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 320 h1 h2 h3 (* h5 h5 h5) (* h6 h6 h6 h6) 
(* j2 j2)) (* 48 h1 h2 h3 (* h5 h5 h5) (* h6 h6 h6 h6) j2) (* 4 h1 h2 (* h4 h4 
h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 12 h1 h2 (* h4 h4 h4 h4) (* h5 h5 h5)
 h6 (* j2 j2 j2)) (* 12 h1 h2 (* h4 h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 4 h1
 h2 (* h4 h4 h4 h4) (* h5 h5 h5) h6 j2) (* 8 h1 h2 (* h4 h4 h4 h4) (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2)) (* 16 h1 h2 (* h4 h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2
 j2)) (* 8 h1 h2 (* h4 h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 4 h1 h2 (* h4
 h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 4 h1 h2 (* h4 h4 h4 h4) h5 (* h6 
h6 h6) (* j2 j2 j2)) (* 4 h1 h2 (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 
j2)) (* 16 h1 h2 (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 24 h1 h2 
(* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 16 h1 h2 (* h4 h4 h4) (* h5 h5 
h5 h5) h6 (* j2 j2)) (* 4 h1 h2 (* h4 h4 h4) (* h5 h5 h5 h5) h6 j2) (* 24 h1 h2 
(* h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 88 h1 h2 (* h4 h4 h4)
 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 120 h1 h2 (* h4 h4 h4) (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2)) (* 72 h1 h2 (* h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2
)) (* 16 h1 h2 (* h4 h4 h4) (* h5 h5 h5) (* h6 h6) j2) (* 24 h1 h2 (* h4 h4 h4) 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 70 h1 h2 (* h4 h4 h4) (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2)) (* 68 h1 h2 (* h4 h4 h4) (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2)) (* 22 h1 h2 (* h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 4 h1
 h2 (* h4 h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 8 h1 h2 (* h4 h4 h4) 
h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 4 h1 h2 (* h4 h4 h4) h5 (* h6 h6 h6 h6) 
(* j2 j2 j2)) (* 14 h1 h2 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 68 h1 h2 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 132 
h1 h2 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 128 h1 h2 (* h4 h4
) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 62 h1 h2 (* h4 h4) (* h5 h5 h5 h5) 
(* h6 h6) (* j2 j2)) (* 12 h1 h2 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) j2) (* 28 
h1 h2 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 132 h1 h2 
(* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 248 h1 h2 (* h4 h4) 
(* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 232 h1 h2 (* h4 h4) (* h5 h5 h5) 
(* h6 h6 h6) (* j2 j2 j2)) (* 108 h1 h2 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* 
j2 j2)) (* 20 h1 h2 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) j2) (* 14 h1 h2 (* h4 h4
) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 56 h1 h2 (* h4 h4) (* h5 
h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 84 h1 h2 (* h4 h4) (* h5 h5) (* h6 h6
 h6 h6) (* j2 j2 j2 j2)) (* 56 h1 h2 (* h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 
j2 j2)) (* 14 h1 h2 (* h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 8 h1 h2 h4
 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 48 h1 h2 h4 (* h5 h5 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 120 h1 h2 h4 (* h5 h5 h5 h5) (* h6
 h6 h6) (* j2 j2 j2 j2 j2)) (* 160 h1 h2 h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2)) (* 120 h1 h2 h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 48 h1 
h2 h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 8 h1 h2 h4 (* h5 h5 h5 h5) (* 
h6 h6 h6) j2) (* 8 h1 h2 h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2
)) (* 48 h1 h2 h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 120 h1 
h2 h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 160 h1 h2 h4 (* h5 h5 
h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 120 h1 h2 h4 (* h5 h5 h5) (* h6 h6 h6 h6
) (* j2 j2 j2)) (* 48 h1 h2 h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 8 h1 
h2 h4 (* h5 h5 h5) (* h6 h6 h6 h6) j2) (* 512 h1 (* h3 h3 h3 h3) (* h4 h4 h4) 
(* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1792 h1 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 
h5) (* j2 j2 j2 j2 j2)) (* 1952 h1 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 
j2 j2 j2)) (* 672 h1 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 72 
h1 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 1024 h1 (* h3 h3 h3 h3) 
(* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 2048 h1 (* h3 h3 h3 h3) (* h4 h4 h4
) h5 h6 (* j2 j2 j2 j2 j2)) (* 832 h1 (* h3 h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 
j2 j2 j2)) (* 96 h1 (* h3 h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 512 h1 
(* h3 h3 h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 256 h1 (* h3 h3
 h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 32 h1 (* h3 h3 h3 h3) (* 
h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 512 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 2432 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 
h5) (* j2 j2 j2 j2 j2 j2)) (* 4032 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* 
j2 j2 j2 j2 j2)) (* 2592 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 
j2)) (* 432 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 3584 h1 
(* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 14208 h1 (* 
h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 19584 h1 (* h3 h3 
h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 11360 h1 (* h3 h3 h3 h3) 
(* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 2976 h1 (* h3 h3 h3 h3) (* h4 h4) (* 
h5 h5) h6 (* j2 j2 j2)) (* 288 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 
j2)) (* 3584 h1 (* h3 h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2))
 (* 9856 h1 (* h3 h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
8512 h1 (* h3 h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2944 h1 
(* h3 h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 392 h1 (* h3 h3 h3 h3
) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 12 h1 (* h3 h3 h3 h3) (* h4 h4) h5 (* 
h6 h6) (* j2 j2)) (* 512 h1 (* h3 h3 h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 640 h1 (* h3 h3 h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2
 j2)) (* 256 h1 (* h3 h3 h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 32
 h1 (* h3 h3 h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 2048 h1 (* h3 h3 
h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 11264 h1 (* h3 h3 h3 
h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 23424 h1 (* h3 h3 h3 h3) h4 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 22464 h1 (* h3 h3 h3 h3) h4 (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2)) (* 9504 h1 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 
j2 j2 j2)) (* 1296 h1 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 4096 
h1 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 19968 
h1 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 37376 h1 
(* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 34144 h1 (* h3 
h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 16192 h1 (* h3 h3 h3 h3)
 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 3864 h1 (* h3 h3 h3 h3) h4 (* h5 h5)
 (* h6 h6) (* j2 j2 j2)) (* 360 h1 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 
j2)) (* 2048 h1 (* h3 h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 7680 h1 (* h3 h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 10624
 h1 (* h3 h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6880 h1 (* h3 
h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2160 h1 (* h3 h3 h3 h3) h4 
h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 296 h1 (* h3 h3 h3 h3) h4 h5 (* h6 h6 h6) 
(* j2 j2 j2)) (* 12 h1 (* h3 h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2)) (* 1024 h1 
(* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 6912 
h1 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 18816 
h1 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 26176 h1 
(* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 19296 h1 (* h3 
h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 6912 h1 (* h3 h3 h3 h3) 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 864 h1 (* h3 h3 h3 h3) (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2)) (* 1024 h1 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 6400 h1 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 16384 h1 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 22144 h1 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 16960 h1 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2)) (* 7312 h1 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 
1632 h1 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 144 h1 (* h3 h3 
h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 128 h1 (* h3 h3 h3) (* h4 h4 h4 h4) 
(* h5 h5) (* j2 j2 j2 j2 j2)) (* 416 h1 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) 
(* j2 j2 j2 j2)) (* 384 h1 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2)) 
(* 72 h1 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2)) (* 256 h1 (* h3 h3 h3
) (* h4 h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 448 h1 (* h3 h3 h3) (* h4 h4 h4 
h4) h5 h6 (* j2 j2 j2 j2)) (* 96 h1 (* h3 h3 h3) (* h4 h4 h4 h4) h5 h6 (* j2 j2 
j2)) (* 128 h1 (* h3 h3 h3) (* h4 h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 32 
h1 (* h3 h3 h3) (* h4 h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 256 h1 (* h3 h3 h3
) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1088 h1 (* h3 h3 h3) (* h4
 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 1600 h1 (* h3 h3 h3) (* h4 h4 h4) 
(* h5 h5 h5) (* j2 j2 j2 j2)) (* 912 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) 
(* j2 j2 j2)) (* 144 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2)) (* 
1536 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 5312 h1
 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 6192 h1 (* h3 h3 
h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 2776 h1 (* h3 h3 h3) (* h4 h4 
h4) (* h5 h5) h6 (* j2 j2 j2)) (* 384 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 
(* j2 j2)) (* 1536 h1 (* h3 h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 3520 h1 (* h3 h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
2416 h1 (* h3 h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 456 h1 (* h3 
h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 12 h1 (* h3 h3 h3) (* h4 h4 h4
) h5 (* h6 h6) (* j2 j2)) (* 256 h1 (* h3 h3 h3) (* h4 h4 h4) (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2)) (* 320 h1 (* h3 h3 h3) (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 
j2 j2)) (* 64 h1 (* h3 h3 h3) (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 128 
h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 704 h1 
(* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1440 h1 (* h3 
h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 1296 h1 (* h3 h3 h3) (* 
h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 432 h1 (* h3 h3 h3) (* h4 h4) (* h5 
h5 h5 h5) (* j2 j2 j2)) (* 1792 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2)) (* 8544 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2)) (* 15168 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2)) (* 12280 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 4440
 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 576 h1 (* h3 h3 h3) 
(* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 3328 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 13824 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5
) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 22016 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 16816 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6
 h6) (* j2 j2 j2 j2)) (* 5992 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* 
j2 j2 j2)) (* 744 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 
1792 h1 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 5856
 h1 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6944 h1 (* 
h3 h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 3488 h1 (* h3 h3 h3) 
(* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 632 h1 (* h3 h3 h3) (* h4 h4) h5 
(* h6 h6 h6) (* j2 j2 j2)) (* 24 h1 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2
 j2)) (* 128 h1 (* h3 h3 h3) (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2))
 (* 256 h1 (* h3 h3 h3) (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 160 
h1 (* h3 h3 h3) (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 32 h1 (* h3 h3 
h3) (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 512 h1 (* h3 h3 h3) h4 (* h5 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3200 h1 (* h3 h3 h3) h4 (* h5 h5 h5
 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 7872 h1 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 9504 h1 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2
 j2 j2)) (* 5616 h1 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 1296 
h1 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 2048 h1 (* h3 h3 h3) h4 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 11776 h1 (* h3 h3 h3) h4 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 27008 h1 (* h3 h3 h3) h4 (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 31424 h1 (* h3 h3 h3) h4 (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 19424 h1 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6
 h6) (* j2 j2 j2 j2)) (* 6000 h1 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2
 j2)) (* 720 h1 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 2048 h1 (* 
h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 10624 h1 (* 
h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 22464 h1 (* h3 
h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 24904 h1 (* h3 h3 h3)
 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 15252 h1 (* h3 h3 h3) h4 (* h5
 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 4812 h1 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6
 h6) (* j2 j2 j2)) (* 576 h1 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2)) 
(* 512 h1 (* h3 h3 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
2304 h1 (* h3 h3 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4000 h1 
(* h3 h3 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3376 h1 (* h3 h3 h3
) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1416 h1 (* h3 h3 h3) h4 h5 (* h6 
h6 h6 h6) (* j2 j2 j2 j2)) (* 260 h1 (* h3 h3 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2
 j2)) (* 12 h1 (* h3 h3 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2)) (* 256 h1 (* h3 h3 
h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1920 h1 (* h3 
h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 5952 h1 (* h3 
h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 9760 h1 (* h3 h3 
h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 8928 h1 (* h3 h3 h3) (* 
h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 4320 h1 (* h3 h3 h3) (* h5 h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2)) (* 864 h1 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) 
(* j2 j2 j2)) (* 512 h1 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2 j2)) (* 3648 h1 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 10880 h1 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 17552 h1 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 16464 h1 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
8912 h1 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 2544 h1 (* h3
 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 288 h1 (* h3 h3 h3) (* h5 h5 
h5) (* h6 h6 h6) (* j2 j2)) (* 256 h1 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1792 h1 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 5248 h1 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 8320 h1 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 7696 h1 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 
j2 j2 j2)) (* 4144 h1 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) 
(* 1200 h1 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 144 h1 (* h3 
h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 32 h1 (* h3 h3) (* h4 h4 h4 h4) 
(* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 128 h1 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5
) (* j2 j2 j2 j2)) (* 168 h1 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2)
) (* 72 h1 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2)) (* 128 h1 (* h3 h3)
 (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 336 h1 (* h3 h3) (* h4 h4 
h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 232 h1 (* h3 h3) (* h4 h4 h4 h4) (* h5 
h5) h6 (* j2 j2 j2)) (* 24 h1 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2)) 
(* 128 h1 (* h3 h3) (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 160 h1 
(* h3 h3) (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 16 h1 (* h3 h3) (* h4
 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 32 h1 (* h3 h3) (* h4 h4 h4 h4) (* h6 
h6 h6) (* j2 j2 j2 j2 j2)) (* 32 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2
 j2 j2 j2 j2 j2)) (* 160 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 
j2 j2)) (* 296 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 240
 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 72 h1 (* h3 h3) (* 
h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 384 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 1632 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2)) (* 2528 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 
j2 j2)) (* 1688 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 408 
h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 704 h1 (* h3 h3) (* h4 
h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2288 h1 (* h3 h3) (* h4 h4 
h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2570 h1 (* h3 h3) (* h4 h4 h4) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 1096 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5)
 (* h6 h6) (* j2 j2 j2)) (* 110 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5) (* h6 h6) 
(* j2 j2)) (* 384 h1 (* h3 h3) (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2
)) (* 864 h1 (* h3 h3) (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 504 
h1 (* h3 h3) (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 44 h1 (* h3 h3) 
(* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 32 h1 (* h3 h3) (* h4 h4 h4) (* h6
 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 32 h1 (* h3 h3) (* h4 h4 h4) (* h6 h6 h6 h6
) (* j2 j2 j2 j2 j2)) (* 224 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2)) (* 1248 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2)) (* 2712 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2))
 (* 2864 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 1464 h1 
(* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 288 h1 (* h3 h3) (* h4 
h4) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 832 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4168 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 8292 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2)) (* 8228 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2)) (* 4076 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 
j2)) (* 804 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 832 h1 
(* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3544 h1 
(* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 5792 h1 (* 
h3 h3) (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 4426 h1 (* h3 h3)
 (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1492 h1 (* h3 h3) (* h4 h4
) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 146 h1 (* h3 h3) (* h4 h4) (* h5 h5) 
(* h6 h6 h6) (* j2 j2)) (* 224 h1 (* h3 h3) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 736 h1 (* h3 h3) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2
 j2 j2 j2)) (* 824 h1 (* h3 h3) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2))
 (* 340 h1 (* h3 h3) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 28 h1 (* 
h3 h3) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 256 h1 (* h3 h3) h4 (* h5 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1696 h1 (* h3 h3) h4 (* h5 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4608 h1 (* h3 h3) h4 (* h5 h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6568 h1 (* h3 h3) h4 (* h5 h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 5176 h1 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2)) (* 2136 h1 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2))
 (* 360 h1 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 512 h1 (* h3 h3)
 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3136 h1 (* h3 h3) 
h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 7992 h1 (* h3 h3) h4 
(* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 10892 h1 (* h3 h3) h4 (* h5 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 8404 h1 (* h3 h3) h4 (* h5 h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2)) (* 3492 h1 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* 
j2 j2 j2)) (* 612 h1 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 256 h1
 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1408 h1 
(* h3 h3) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3112 h1 (* 
h3 h3) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3508 h1 (* h3 h3) 
h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2092 h1 (* h3 h3) h4 (* h5 
h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 604 h1 (* h3 h3) h4 (* h5 h5) (* h6 h6 
h6 h6) (* j2 j2 j2)) (* 60 h1 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) 
(* 64 h1 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 512 h1 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 1744 h1 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
3280 h1 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3680 h1
 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2464 h1 (* h3 h3)
 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 912 h1 (* h3 h3) (* h5 h5 h5 
h5) (* h6 h6 h6) (* j2 j2 j2)) (* 144 h1 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) 
(* j2 j2)) (* 64 h1 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 512 h1 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 1744 h1 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 3280 h1 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 3680 h1 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2464 h1
 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 912 h1 (* h3 h3) (* 
h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 144 h1 (* h3 h3) (* h5 h5 h5) (* h6 
h6 h6 h6) (* j2 j2)) (* 16 h1 h3 (* h4 h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2)) (* 56 h1 h3 (* h4 h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 64 h1 h3 
(* h4 h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 24 h1 h3 (* h4 h4 h4 h4) (* h5 
h5 h5) h6 (* j2 j2)) (* 32 h1 h3 (* h4 h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2
 j2 j2)) (* 70 h1 h3 (* h4 h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 40 
h1 h3 (* h4 h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 2 h1 h3 (* h4 h4 h4 
h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 16 h1 h3 (* h4 h4 h4 h4) h5 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2)) (* 16 h1 h3 (* h4 h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2))
 (* 16 h1 h3 (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 72 h1 h3 
(* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 120 h1 h3 (* h4 h4 h4) 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 88 h1 h3 (* h4 h4 h4) (* h5 h5 h5 h5) h6 
(* j2 j2 j2)) (* 24 h1 h3 (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 96 h1 h3
 (* h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 388 h1 h3 (* h4 
h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 588 h1 h3 (* h4 h4 h4) (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 396 h1 h3 (* h4 h4 h4) (* h5 h5 h5) (* 
h6 h6) (* j2 j2 j2)) (* 100 h1 h3 (* h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2))
 (* 96 h1 h3 (* h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 308 
h1 h3 (* h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 328 h1 h3 (* h4
 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 120 h1 h3 (* h4 h4 h4) (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2)) (* 4 h1 h3 (* h4 h4 h4) (* h5 h5) (* h6 h6 h6) 
(* j2 j2)) (* 16 h1 h3 (* h4 h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 32 h1 h3 (* h4 h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 16 h1 h3 (* 
h4 h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 56 h1 h3 (* h4 h4) (* h5 h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 300 h1 h3 (* h4 h4) (* h5 h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 636 h1 h3 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6
) (* j2 j2 j2 j2 j2)) (* 668 h1 h3 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2)) (* 348 h1 h3 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 72 h1 
h3 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 112 h1 h3 (* h4 h4) (* h5 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 570 h1 h3 (* h4 h4) (* h5 h5 h5
) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1162 h1 h3 (* h4 h4) (* h5 h5 h5) (* h6
 h6 h6) (* j2 j2 j2 j2 j2)) (* 1186 h1 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2)) (* 606 h1 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) 
(* 124 h1 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 56 h1 h3 (* h4 h4
) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 240 h1 h3 (* h4 h4) (* 
h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 386 h1 h3 (* h4 h4) (* h5 h5) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 278 h1 h3 (* h4 h4) (* h5 h5) (* h6 h6 h6
 h6) (* j2 j2 j2 j2)) (* 78 h1 h3 (* h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 
j2)) (* 2 h1 h3 (* h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 32 h1 h3 h4 
(* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 208 h1 h3 h4 (* h5 
h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 560 h1 h3 h4 (* h5 h5 h5 h5)
 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 800 h1 h3 h4 (* h5 h5 h5 h5) (* h6 h6 h6
) (* j2 j2 j2 j2 j2)) (* 640 h1 h3 h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2)) (* 272 h1 h3 h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 48 h1 h3 h4 
(* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 32 h1 h3 h4 (* h5 h5 h5) (* h6 h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 208 h1 h3 h4 (* h5 h5 h5) (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 560 h1 h3 h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 800 h1 h3 h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 640 h1 h3 h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 272 h1 h3 h4 
(* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 48 h1 h3 h4 (* h5 h5 h5) (* h6 h6 
h6 h6) (* j2 j2)) (* 2 h1 (* h4 h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 6 h1 (* h4 h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 6 h1 (* 
h4 h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 2 h1 (* h4 h4 h4 h4) (* h5 
h5 h5) (* h6 h6) (* j2 j2)) (* 2 h1 (* h4 h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2
 j2 j2 j2 j2)) (* 4 h1 (* h4 h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) 
(* 2 h1 (* h4 h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 2 h1 (* h4 h4 h4
) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 8 h1 (* h4 h4 h4) (* h5 h5
 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 12 h1 (* h4 h4 h4) (* h5 h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2)) (* 8 h1 (* h4 h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 
j2)) (* 2 h1 (* h4 h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 4 h1 (* h4 h4 
h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 16 h1 (* h4 h4 h4) (* h5
 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 24 h1 (* h4 h4 h4) (* h5 h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2)) (* 16 h1 (* h4 h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2
 j2 j2)) (* 4 h1 (* h4 h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 2 h1 (* h4
 h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6 h1 (* h4 h4 h4) 
(* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 6 h1 (* h4 h4 h4) (* h5 h5) (* 
h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 2 h1 (* h4 h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* 
j2 j2 j2)) (* 2 h1 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 10 h1 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
20 h1 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 20 h1 (* h4 
h4) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 10 h1 (* h4 h4) (* h5 h5 h5
 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 2 h1 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6 h6) 
(* j2 j2)) (* 2 h1 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 10 h1 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
20 h1 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 20 h1 (* h4 
h4) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 10 h1 (* h4 h4) (* h5 h5 h5
) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 2 h1 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6 h6) 
(* j2 j2)) (* 64 (* h2 h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 
128 (* h2 h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 52 (* h2 h2 h2 h2
) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2)) (* 6 (* h2 h2 h2 h2) (* h3 h3 h3) (* h4 
h4) h5 j2) (* 64 (* h2 h2 h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2)) (* 
32 (* h2 h2 h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2)) (* 4 (* h2 h2 h2 h2) 
(* h3 h3 h3) (* h4 h4) h6 (* j2 j2)) (* 64 (* h2 h2 h2 h2) (* h3 h3 h3) h4 (* h5
 h5) (* j2 j2 j2 j2 j2)) (* 208 (* h2 h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 
j2 j2 j2)) (* 192 (* h2 h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 36 
(* h2 h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2)) (* 128 (* h2 h2 h2 h2) (* 
h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 352 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5
 h6 (* j2 j2 j2 j2)) (* 304 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2)) 
(* 104 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2)) (* 12 (* h2 h2 h2 h2) 
(* h3 h3 h3) h4 h5 h6 j2) (* 64 (* h2 h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 
j2 j2 j2 j2)) (* 80 (* h2 h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) 
(* 32 (* h2 h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2)) (* 4 (* h2 h2 h2 
h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2)) (* 64 (* h2 h2 h2 h2) (* h3 h3 h3) (* 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 272 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) 
h6 (* j2 j2 j2 j2 j2)) (* 400 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2
 j2 j2)) (* 228 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 36 
(* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2)) (* 64 (* h2 h2 h2 h2) (* h3
 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 240 (* h2 h2 h2 h2) (* h3 h3 h3) 
h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 328 (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6
) (* j2 j2 j2 j2)) (* 204 (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2)
) (* 58 (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2)) (* 6 (* h2 h2 h2 h2
) (* h3 h3 h3) h5 (* h6 h6) j2) (* 16 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 
(* j2 j2 j2)) (* 28 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2)) (* 6 
(* h2 h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 j2) (* 16 (* h2 h2 h2 h2) (* h3 h3) 
(* h4 h4 h4) h6 (* j2 j2 j2)) (* 4 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4 h4) h6 (* 
j2 j2)) (* 32 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 
88 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 68 (* h2 h2 h2
 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 12 (* h2 h2 h2 h2) (* h3 h3) 
(* h4 h4) (* h5 h5) j2) (* 64 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2
 j2 j2)) (* 140 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 107 
(* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 19 (* h2 h2 h2 h2) (* h3
 h3) (* h4 h4) h5 h6 j2) (* 32 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* 
j2 j2 j2 j2)) (* 40 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2)) 
(* 8 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2)) (* 16 (* h2 h2 h2 
h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 64 (* h2 h2 h2 h2) (* h3 h3
) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 84 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5 
h5) (* j2 j2 j2)) (* 36 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2)) (* 
64 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 232 (* h2 h2
 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 292 (* h2 h2 h2 h2) (* h3 
h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 148 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) 
h6 (* j2 j2)) (* 24 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 j2) (* 64 (* h2 h2
 h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 192 (* h2 h2 h2 h2) (* 
h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 228 (* h2 h2 h2 h2) (* h3 h3) h4 h5 
(* h6 h6) (* j2 j2 j2)) (* 119 (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 
j2)) (* 19 (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) j2) (* 16 (* h2 h2 h2 h2) 
(* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 32 (* h2 h2 h2 h2) (* h3 h3) h4
 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 20 (* h2 h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6) 
(* j2 j2 j2)) (* 4 (* h2 h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2)) (* 16 
(* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 80 (* h2 h2 
h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 148 (* h2 h2 h2 h2) (* 
h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 120 (* h2 h2 h2 h2) (* h3 h3) (* h5 
h5 h5) h6 (* j2 j2 j2)) (* 36 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2
)) (* 32 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 148 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 262 
(* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 220 (* h2 h2 
h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 86 (* h2 h2 h2 h2) (* h3 
h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 12 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* 
h6 h6) j2) (* 16 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)
) (* 72 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 124 (* 
h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 102 (* h2 h2 h2 h2) 
(* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 40 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6
 h6 h6) (* j2 j2)) (* 6 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) j2) (* 4 (* h2
 h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 10 (* h2 h2 h2 h2) h3 (* 
h4 h4 h4) (* h5 h5) (* j2 j2)) (* 6 (* h2 h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) j2
) (* 8 (* h2 h2 h2 h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 9 (* h2 h2 h2 h2) 
h3 (* h4 h4 h4) h5 h6 (* j2 j2)) (* (* h2 h2 h2 h2) h3 (* h4 h4 h4) h5 h6 j2) 
(* 4 (* h2 h2 h2 h2) h3 (* h4 h4 h4) (* h6 h6) (* j2 j2 j2)) (* 4 (* h2 h2 h2 h2
) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 14 (* h2 h2 h2 h2) h3 (* h4 h4) 
(* h5 h5 h5) (* j2 j2 j2)) (* 16 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2
 j2)) (* 6 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) j2) (* 16 (* h2 h2 h2 h2) 
h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 48 (* h2 h2 h2 h2) h3 (* h4 h4) 
(* h5 h5) h6 (* j2 j2 j2)) (* 52 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2
 j2)) (* 20 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 j2) (* 16 (* h2 h2 h2 h2) 
h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 34 (* h2 h2 h2 h2) h3 (* h4 h4) h5
 (* h6 h6) (* j2 j2 j2)) (* 20 (* h2 h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 
j2)) (* 2 (* h2 h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6) j2) (* 4 (* h2 h2 h2 h2) h3 
(* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 4 (* h2 h2 h2 h2) h3 (* h4 h4) (* h6 
h6 h6) (* j2 j2 j2)) (* 8 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2)) (* 36 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 60 (* h2 h2
 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 44 (* h2 h2 h2 h2) h3 h4 (* h5 h5
 h5) h6 (* j2 j2)) (* 12 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) h6 j2) (* 16 (* h2 
h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 63 (* h2 h2 h2 h2) h3
 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 98 (* h2 h2 h2 h2) h3 h4 (* h5 h5) 
(* h6 h6) (* j2 j2 j2)) (* 71 (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2
)) (* 20 (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) j2) (* 8 (* h2 h2 h2 h2) h3 
h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 24 (* h2 h2 h2 h2) h3 h4 h5 (* h6 h6 
h6) (* j2 j2 j2 j2)) (* 25 (* h2 h2 h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2)) 
(* 10 (* h2 h2 h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2)) (* (* h2 h2 h2 h2) h3 h4 
h5 (* h6 h6 h6) j2) (* 4 (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 22 (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 48 (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 52 (* h2 h2 
h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 28 (* h2 h2 h2 h2) h3 (* h5 h5
 h5) (* h6 h6) (* j2 j2)) (* 6 (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) j2) (* 
4 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 22 (* h2 
h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 48 (* h2 h2 h2 h2) h3
 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 52 (* h2 h2 h2 h2) h3 (* h5 h5) (* 
h6 h6 h6) (* j2 j2 j2)) (* 28 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2
)) (* 6 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) j2) (* (* h2 h2 h2 h2) (* h4 
h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 2 (* h2 h2 h2 h2) (* h4 h4 h4) (* h5 h5) h6
 (* j2 j2)) (* (* h2 h2 h2 h2) (* h4 h4 h4) (* h5 h5) h6 j2) (* (* h2 h2 h2 h2) 
(* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* (* h2 h2 h2 h2) (* h4 h4 h4) h5 (* h6
 h6) (* j2 j2)) (* (* h2 h2 h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) 
(* 3 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 3 (* h2 h2 h2 h2
) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* (* h2 h2 h2 h2) (* h4 h4) (* h5 h5 h5)
 h6 j2) (* 2 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 6
 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 6 (* h2 h2 h2 h2
) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 2 (* h2 h2 h2 h2) (* h4 h4) (* h5 
h5) (* h6 h6) j2) (* (* h2 h2 h2 h2) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) 
(* 2 (* h2 h2 h2 h2) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2)) (* (* h2 h2 h2 h2) 
(* h4 h4) h5 (* h6 h6 h6) (* j2 j2)) (* (* h2 h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6
) (* j2 j2 j2 j2 j2)) (* 4 (* h2 h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2
 j2)) (* 6 (* h2 h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 4 (* h2 h2
 h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* (* h2 h2 h2 h2) h4 (* h5 h5 h5) 
(* h6 h6) j2) (* (* h2 h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 4 (* h2 h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 6 (* h2 h2 h2
 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 4 (* h2 h2 h2 h2) h4 (* h5 h5) 
(* h6 h6 h6) (* j2 j2)) (* (* h2 h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6) j2) (* 256 
(* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 576 (* h2 h2 h2
) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 336 (* h2 h2 h2) (* h3 h3 h3 
h3) (* h4 h4) h5 (* j2 j2 j2)) (* 76 (* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 
(* j2 j2)) (* 6 (* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 j2) (* 256 (* h2 h2 h2
) (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 192 (* h2 h2 h2) (* h3 h3 
h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2)) (* 48 (* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4
) h6 (* j2 j2 j2)) (* 4 (* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2)) (* 
256 (* h2 h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 896 (* 
h2 h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 976 (* h2 h2 h2) 
(* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 336 (* h2 h2 h2) (* h3 h3 h3 h3
) h4 (* h5 h5) (* j2 j2 j2)) (* 36 (* h2 h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* 
j2 j2)) (* 512 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 
1536 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 1568 (* h2 h2 
h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 720 (* h2 h2 h2) (* h3 h3 h3 h3
) h4 h5 h6 (* j2 j2 j2)) (* 152 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2))
 (* 12 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 h6 j2) (* 256 (* h2 h2 h2) (* h3 h3 h3
 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 384 (* h2 h2 h2) (* h3 h3 h3 h3) h4 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 208 (* h2 h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6) 
(* j2 j2 j2 j2)) (* 48 (* h2 h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2)) 
(* 4 (* h2 h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2)) (* 256 (* h2 h2 h2) 
(* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1152 (* h2 h2 h2) (* 
h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 1872 (* h2 h2 h2) (* h3 h3 
h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 1312 (* h2 h2 h2) (* h3 h3 h3 h3) (* 
h5 h5) h6 (* j2 j2 j2 j2)) (* 372 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* 
j2 j2 j2)) (* 36 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2)) (* 256 (* 
h2 h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1024 (* h2 
h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1552 (* h2 h2 h2) 
(* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1144 (* h2 h2 h2) (* h3 h3 
h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 436 (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* 
h6 h6) (* j2 j2 j2)) (* 82 (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2)) 
(* 6 (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) j2) (* 128 (* h2 h2 h2) (* h3 h3 
h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 256 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4 
h4) h5 (* j2 j2 j2)) (* 104 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2))
 (* 12 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 j2) (* 128 (* h2 h2 h2) (* h3 
h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2)) (* 64 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4
 h4) h6 (* j2 j2 j2)) (* 8 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2)) 
(* 256 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 784 
(* h2 h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 732 (* h2 h2 
h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 210 (* h2 h2 h2) (* h3 h3 
h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 18 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) (* 
h5 h5) j2) (* 512 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) 
(* 1264 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 1088 (* h2
 h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 349 (* h2 h2 h2) (* h3 h3 
h3) (* h4 h4) h5 h6 (* j2 j2)) (* 37 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 
j2) (* 256 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
368 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 140 (* h2 
h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 16 (* h2 h2 h2) (* h3 
h3 h3) (* h4 h4) (* h6 h6) (* j2 j2)) (* 128 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 
h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 544 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) 
(* j2 j2 j2 j2 j2)) (* 800 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2
 j2)) (* 456 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2)) (* 72 (* h2
 h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2)) (* 512 (* h2 h2 h2) (* h3 h3 h3)
 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 2016 (* h2 h2 h2) (* h3 h3 h3) h4 (* 
h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 2856 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 
(* j2 j2 j2 j2)) (* 1748 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2))
 (* 432 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 36 (* h2 h2 h2) 
(* h3 h3 h3) h4 (* h5 h5) h6 j2) (* 512 (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6
) (* j2 j2 j2 j2 j2 j2)) (* 1696 (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2
 j2 j2 j2 j2)) (* 2200 (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)
) (* 1352 (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 373 (* h2 
h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 37 (* h2 h2 h2) (* h3 h3 h3) 
h4 h5 (* h6 h6) j2) (* 128 (* h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2
 j2 j2 j2)) (* 288 (* h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2))
 (* 224 (* h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 72 (* h2 
h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2)) (* 8 (* h2 h2 h2) (* h3 h3 h3)
 h4 (* h6 h6 h6) (* j2 j2)) (* 128 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2)) (* 672 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2
 j2 j2 j2 j2)) (* 1344 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2)) (* 1256 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 528 
(* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 72 (* h2 h2 h2) (* h3
 h3 h3) (* h5 h5 h5) h6 (* j2 j2)) (* 256 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1264 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2436 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2)) (* 2302 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6)
 (* j2 j2 j2 j2)) (* 1090 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2
 j2)) (* 234 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 18 (* 
h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) j2) (* 128 (* h2 h2 h2) (* h3 h3 h3) 
h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 608 (* h2 h2 h2) (* h3 h3 h3) h5 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1136 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 
h6 h6) (* j2 j2 j2 j2 j2)) (* 1064 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* 
j2 j2 j2 j2)) (* 524 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 
128 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 12 (* h2 h2 h2) (* 
h3 h3 h3) h5 (* h6 h6 h6) j2) (* 16 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 
(* j2 j2 j2)) (* 28 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2)) (* 6 
(* h2 h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 j2) (* 16 (* h2 h2 h2) (* h3 h3) (* h4
 h4 h4 h4) h6 (* j2 j2 j2)) (* 4 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4 h4) h6 (* j2
 j2)) (* 64 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 
176 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 136 (* h2 h2 
h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 24 (* h2 h2 h2) (* h3 h3) (* 
h4 h4 h4) (* h5 h5) j2) (* 128 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 
j2 j2 j2)) (* 248 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 158
 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2)) (* 26 (* h2 h2 h2) (* h3 
h3) (* h4 h4 h4) h5 h6 j2) (* 64 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) (* h6 h6) 
(* j2 j2 j2 j2)) (* 64 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 j2
)) (* 12 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2)) (* 64 (* h2 h2
 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 244 (* h2 h2 h2) 
(* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 318 (* h2 h2 h2) (* h3 h3) 
(* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 156 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* 
h5 h5 h5) (* j2 j2)) (* 18 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) j2) (* 
224 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 764 (* 
h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 951 (* h2 h2 h2) 
(* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 486 (* h2 h2 h2) (* h3 h3) (* 
h4 h4) (* h5 h5) h6 (* j2 j2)) (* 75 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) 
h6 j2) (* 224 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 620 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 637 (* 
h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 281 (* h2 h2 h2) (* 
h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 40 (* h2 h2 h2) (* h3 h3) (* h4 h4) 
h5 (* h6 h6) j2) (* 64 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2
 j2 j2)) (* 124 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2)) 
(* 72 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2)) (* 12 (* h2 h2
 h2) (* h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2)) (* 16 (* h2 h2 h2) (* h3 h3) h4
 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 80 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5
 h5 h5) (* j2 j2 j2 j2 j2)) (* 148 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* 
j2 j2 j2 j2)) (* 120 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2)) (* 
36 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2)) (* 128 (* h2 h2 h2) (* 
h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 608 (* h2 h2 h2) (* h3 h3) 
h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 1096 (* h2 h2 h2) (* h3 h3) h4 (* h5 
h5 h5) h6 (* j2 j2 j2 j2)) (* 916 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* 
j2 j2 j2)) (* 336 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2)) (* 36 (* 
h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 j2) (* 224 (* h2 h2 h2) (* h3 h3) h4 (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 968 (* h2 h2 h2) (* h3 h3) h4 (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1661 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2)) (* 1389 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6)
 (* j2 j2 j2)) (* 547 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2)) 
(* 75 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) j2) (* 128 (* h2 h2 h2) (* 
h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 480 (* h2 h2 h2) (* h3 h3) 
h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 720 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6
 h6 h6) (* j2 j2 j2 j2)) (* 538 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 
j2 j2)) (* 196 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2)) (* 26 (* h2 
h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) j2) (* 16 (* h2 h2 h2) (* h3 h3) h4 (* h6 h6
 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 48 (* h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2)) (* 52 (* h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 
j2)) (* 24 (* h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 4 (* h2 h2
 h2) (* h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2)) (* 16 (* h2 h2 h2) (* h3 h3) (* h5 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 96 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 228 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 
(* j2 j2 j2 j2 j2)) (* 268 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2
 j2)) (* 156 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 36 (* h2
 h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2)) (* 64 (* h2 h2 h2) (* h3 h3) (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 368 (* h2 h2 h2) (* h3 h3) (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 852 (* h2 h2 h2) (* h3 h3) (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1006 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5)
 (* h6 h6) (* j2 j2 j2 j2)) (* 626 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6)
 (* j2 j2 j2)) (* 186 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2)) 
(* 18 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) j2) (* 64 (* h2 h2 h2) (* h3
 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 360 (* h2 h2 h2) (* h3 
h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 820 (* h2 h2 h2) (* h3 h3) 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 964 (* h2 h2 h2) (* h3 h3) (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 612 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 
h6 h6) (* j2 j2 j2)) (* 196 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 
j2)) (* 24 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) j2) (* 16 (* h2 h2 h2) 
(* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 88 (* h2 h2 h2) (* h3 
h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 196 (* h2 h2 h2) (* h3 h3) h5 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 226 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6
 h6) (* j2 j2 j2 j2)) (* 142 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 
j2)) (* 46 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2)) (* 6 (* h2 h2 h2
) (* h3 h3) h5 (* h6 h6 h6 h6) j2) (* 4 (* h2 h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5
) (* j2 j2 j2)) (* 10 (* h2 h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2)) (* 6 
(* h2 h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) j2) (* 8 (* h2 h2 h2) h3 (* h4 h4 h4 
h4) h5 h6 (* j2 j2 j2)) (* 9 (* h2 h2 h2) h3 (* h4 h4 h4 h4) h5 h6 (* j2 j2)) 
(* (* h2 h2 h2) h3 (* h4 h4 h4 h4) h5 h6 j2) (* 4 (* h2 h2 h2) h3 (* h4 h4 h4 h4
) (* h6 h6) (* j2 j2 j2)) (* 8 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 
j2 j2 j2)) (* 28 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 32 
(* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2)) (* 12 (* h2 h2 h2) h3 (* h4
 h4 h4) (* h5 h5 h5) j2) (* 32 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 
j2 j2 j2)) (* 88 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 84 
(* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 28 (* h2 h2 h2) h3 (* h4
 h4 h4) (* h5 h5) h6 j2) (* 32 (* h2 h2 h2) h3 (* h4 h4 h4) h5 (* h6 h6) (* j2 
j2 j2 j2)) (* 60 (* h2 h2 h2) h3 (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 31 
(* h2 h2 h2) h3 (* h4 h4 h4) h5 (* h6 h6) (* j2 j2)) (* 3 (* h2 h2 h2) h3 (* h4 
h4 h4) h5 (* h6 h6) j2) (* 8 (* h2 h2 h2) h3 (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 
j2 j2)) (* 8 (* h2 h2 h2) h3 (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2)) (* 4 (* h2 
h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 18 (* h2 h2 h2) h3 
(* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 30 (* h2 h2 h2) h3 (* h4 h4) (* h5
 h5 h5 h5) (* j2 j2 j2)) (* 22 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 
j2)) (* 6 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) j2) (* 32 (* h2 h2 h2) h3 
(* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 131 (* h2 h2 h2) h3 (* h4 h4) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 205 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) 
h6 (* j2 j2 j2)) (* 145 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 
39 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 j2) (* 56 (* h2 h2 h2) h3 (* h4 h4)
 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 203 (* h2 h2 h2) h3 (* h4 h4) (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2)) (* 282 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 
h6) (* j2 j2 j2)) (* 179 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)
) (* 44 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) j2) (* 32 (* h2 h2 h2) h3 
(* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 91 (* h2 h2 h2) h3 (* h4 h4) h5
 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 89 (* h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6 h6) 
(* j2 j2 j2)) (* 33 (* h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6 h6) (* j2 j2)) (* 3 
(* h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6 h6) j2) (* 4 (* h2 h2 h2) h3 (* h4 h4) (* 
h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 8 (* h2 h2 h2) h3 (* h4 h4) (* h6 h6 h6 h6) 
(* j2 j2 j2 j2)) (* 4 (* h2 h2 h2) h3 (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2)) 
(* 8 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 44 (* h2 h2
 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 96 (* h2 h2 h2) h3 h4 (* h5
 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 104 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* 
j2 j2 j2)) (* 56 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 12 (* h2 h2
 h2) h3 h4 (* h5 h5 h5 h5) h6 j2) (* 32 (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6
) (* j2 j2 j2 j2 j2 j2)) (* 162 (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2)) (* 333 (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) 
(* 347 (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 183 (* h2 h2 
h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 39 (* h2 h2 h2) h3 h4 (* h5 h5 h5
) (* h6 h6) j2) (* 32 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 150 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
286 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 278 (* h2 h2 
h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 138 (* h2 h2 h2) h3 h4 (* h5 
h5) (* h6 h6 h6) (* j2 j2)) (* 28 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) j2) 
(* 8 (* h2 h2 h2) h3 h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 32 (* h2 h2
 h2) h3 h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 49 (* h2 h2 h2) h3 h4 h5 
(* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 35 (* h2 h2 h2) h3 h4 h5 (* h6 h6 h6 h6) (* 
j2 j2 j2)) (* 11 (* h2 h2 h2) h3 h4 h5 (* h6 h6 h6 h6) (* j2 j2)) (* (* h2 h2 h2
) h3 h4 h5 (* h6 h6 h6 h6) j2) (* 4 (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 26 (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 70 (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 100 (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 80 (* 
h2 h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 34 (* h2 h2 h2) h3 (* h5
 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 6 (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) 
j2) (* 8 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
52 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 140 (* h2
 h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 200 (* h2 h2 h2) h3 
(* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 160 (* h2 h2 h2) h3 (* h5 h5 h5) 
(* h6 h6 h6) (* j2 j2 j2)) (* 68 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2
 j2)) (* 12 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) j2) (* 4 (* h2 h2 h2) h3 
(* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 26 (* h2 h2 h2) h3 (* h5 
h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 70 (* h2 h2 h2) h3 (* h5 h5) (* h6
 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 100 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) 
(* j2 j2 j2 j2)) (* 80 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) 
(* 34 (* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 6 (* h2 h2 h2) h3 
(* h5 h5) (* h6 h6 h6 h6) j2) (* (* h2 h2 h2) (* h4 h4 h4 h4) (* h5 h5) h6 (* j2
 j2 j2)) (* 2 (* h2 h2 h2) (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* (* h2 h2 
h2) (* h4 h4 h4 h4) (* h5 h5) h6 j2) (* (* h2 h2 h2) (* h4 h4 h4 h4) h5 (* h6 h6
) (* j2 j2 j2)) (* (* h2 h2 h2) (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2)) (* 2 (* 
h2 h2 h2) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 6 (* h2 h2 h2) (* h4 
h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 6 (* h2 h2 h2) (* h4 h4 h4) (* h5 h5 h5)
 h6 (* j2 j2)) (* 2 (* h2 h2 h2) (* h4 h4 h4) (* h5 h5 h5) h6 j2) (* 4 (* h2 h2 
h2) (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 11 (* h2 h2 h2) (* h4 
h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 10 (* h2 h2 h2) (* h4 h4 h4) (* h5 
h5) (* h6 h6) (* j2 j2)) (* 3 (* h2 h2 h2) (* h4 h4 h4) (* h5 h5) (* h6 h6) j2) 
(* 2 (* h2 h2 h2) (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 4 (* h2 h2 h2
) (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 2 (* h2 h2 h2) (* h4 h4 h4) h5 
(* h6 h6 h6) (* j2 j2)) (* (* h2 h2 h2) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2
 j2 j2)) (* 4 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 6 
(* h2 h2 h2) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 4 (* h2 h2 h2) (* h4 
h4) (* h5 h5 h5 h5) h6 (* j2 j2)) (* (* h2 h2 h2) (* h4 h4) (* h5 h5 h5 h5) h6 
j2) (* 4 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 16
 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 24 (* h2 h2 
h2) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 16 (* h2 h2 h2) (* h4 h4) 
(* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 4 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5) (* h6
 h6) j2) (* 4 (* h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 15 (* h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 21 (* h2
 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 13 (* h2 h2 h2) (* h4 
h4) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 3 (* h2 h2 h2) (* h4 h4) (* h5 h5) (* 
h6 h6 h6) j2) (* (* h2 h2 h2) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 3 (* h2 h2 h2) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 3 (* h2 h2 h2
) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* (* h2 h2 h2) (* h4 h4) h5 (* h6 
h6 h6 h6) (* j2 j2)) (* (* h2 h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2
 j2 j2)) (* 5 (* h2 h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
10 (* h2 h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 10 (* h2 h2 h2)
 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 5 (* h2 h2 h2) h4 (* h5 h5 h5 h5)
 (* h6 h6) (* j2 j2)) (* (* h2 h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6) j2) (* 2 (* 
h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 10 (* h2 h2 h2)
 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 20 (* h2 h2 h2) h4 (* h5 h5
 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 20 (* h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6 
h6) (* j2 j2 j2)) (* 10 (* h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 
2 (* h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6) j2) (* (* h2 h2 h2) h4 (* h5 h5) (* 
h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 5 (* h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6 
h6) (* j2 j2 j2 j2 j2)) (* 10 (* h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2
 j2 j2)) (* 10 (* h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 5 (* 
h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* (* h2 h2 h2) h4 (* h5 h5) 
(* h6 h6 h6 h6) j2) (* 256 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2
 j2 j2)) (* 576 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 
336 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 76 (* h2 h2) (* 
h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2)) (* 6 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4 
h4) h5 j2) (* 256 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2)) 
(* 192 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2)) (* 48 (* h2 h2
) (* h3 h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2)) (* 4 (* h2 h2) (* h3 h3 h3 h3) 
(* h4 h4 h4) h6 (* j2 j2)) (* 512 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) 
(* j2 j2 j2 j2 j2 j2)) (* 1792 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* 
j2 j2 j2 j2 j2)) (* 1952 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 
j2 j2)) (* 672 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 72
 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 1024 (* h2 h2) (* 
h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 2816 (* h2 h2) (* h3 h3 
h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 2560 (* h2 h2) (* h3 h3 h3 h3) (* 
h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 1104 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 h6 
(* j2 j2 j2)) (* 228 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 18 
(* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 h6 j2) (* 512 (* h2 h2) (* h3 h3 h3 h3) 
(* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 768 (* h2 h2) (* h3 h3 h3 h3) (* 
h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 416 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) 
(* h6 h6) (* j2 j2 j2 j2)) (* 96 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) (* h6 h6) 
(* j2 j2 j2)) (* 8 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2)) (* 
256 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1216 
(* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2016 (* h2 
h2) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 1296 (* h2 h2) (* h3 
h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 216 (* h2 h2) (* h3 h3 h3 h3) h4 
(* h5 h5 h5) (* j2 j2 j2)) (* 1024 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2)) (* 4416 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 
j2 j2 j2 j2 j2)) (* 6864 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 
j2 j2)) (* 4672 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 
1380 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 144 (* h2 h2) 
(* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 1024 (* h2 h2) (* h3 h3 h3 h3) h4 
h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3648 (* h2 h2) (* h3 h3 h3 h3) h4 h5 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4912 (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* h6 
h6) (* j2 j2 j2 j2 j2)) (* 3336 (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 
j2 j2 j2)) (* 1228 (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 
234 (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 18 (* h2 h2) (* h3 
h3 h3 h3) h4 h5 (* h6 h6) j2) (* 256 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 576 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2)) (* 512 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 
j2 j2)) (* 224 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 48 
(* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2)) (* 4 (* h2 h2) (* h3 h3 
h3 h3) h4 (* h6 h6 h6) (* j2 j2)) (* 256 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1472 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 3232 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 3312 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* 1512 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2))
 (* 216 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 512 (* h2 h2)
 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2688 (* h2 
h2) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 5504 (* h2 
h2) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 5568 (* h2 h2)
 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2912 (* h2 h2) (* h3
 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 744 (* h2 h2) (* h3 h3 h3 h3)
 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 72 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* 
h6 h6) (* j2 j2)) (* 256 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 1216 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 2336 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 2368 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 1376 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 460 (* h2 
h2) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 82 (* h2 h2) (* h3 h3 h3 h3
) h5 (* h6 h6 h6) (* j2 j2)) (* 6 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6 h6) j2) 
(* 64 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 128 (* h2 h2
) (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2)) (* 52 (* h2 h2) (* h3 h3 h3) (* 
h4 h4 h4 h4) h5 (* j2 j2)) (* 6 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4 h4) h5 j2) 
(* 64 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4 h4) h6 (* j2 j2 j2 j2)) (* 32 (* h2 h2)
 (* h3 h3 h3) (* h4 h4 h4 h4) h6 (* j2 j2 j2)) (* 4 (* h2 h2) (* h3 h3 h3) (* h4
 h4 h4 h4) h6 (* j2 j2)) (* 256 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) 
(* j2 j2 j2 j2 j2)) (* 784 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 
j2 j2 j2)) (* 732 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) 
(* 210 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 18 (* h2 h2) 
(* h3 h3 h3) (* h4 h4 h4) (* h5 h5) j2) (* 512 (* h2 h2) (* h3 h3 h3) (* h4 h4 
h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 1136 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 h6 
(* j2 j2 j2 j2)) (* 832 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2)) 
(* 245 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2)) (* 25 (* h2 h2) (* 
h3 h3 h3) (* h4 h4 h4) h5 h6 j2) (* 256 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* 
h6 h6) (* j2 j2 j2 j2 j2)) (* 304 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* h6 h6) 
(* j2 j2 j2 j2)) (* 108 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2 
j2)) (* 12 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* h6 h6) (* j2 j2)) (* 256 (* h2
 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1088 (* h2 h2
) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 1600 (* h2 h2) (* 
h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 912 (* h2 h2) (* h3 h3 h3) 
(* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 144 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* 
h5 h5 h5) (* j2 j2)) (* 896 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 
j2 j2 j2 j2 j2)) (* 3360 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 
j2 j2 j2)) (* 4544 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)
) (* 2692 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 654 (* 
h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 54 (* h2 h2) (* h3 h3 
h3) (* h4 h4) (* h5 h5) h6 j2) (* 896 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 2656 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6)
 (* j2 j2 j2 j2 j2)) (* 2976 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2
 j2 j2 j2)) (* 1576 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2)) 
(* 398 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 38 (* h2 h2) 
(* h3 h3 h3) (* h4 h4) h5 (* h6 h6) j2) (* 256 (* h2 h2) (* h3 h3 h3) (* h4 h4) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 512 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 368 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6 
h6) (* j2 j2 j2 j2)) (* 112 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 
j2 j2)) (* 12 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2)) (* 64 (* 
h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 352 (* h2 h2
) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 720 (* h2 h2) (* h3 
h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 648 (* h2 h2) (* h3 h3 h3) h4 
(* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 216 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5 h5
) (* j2 j2 j2)) (* 512 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2)) (* 2640 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2)) (* 5184 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
4772 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 2004 (* h2 h2
) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 288 (* h2 h2) (* h3 h3 h3) h4
 (* h5 h5 h5) h6 (* j2 j2)) (* 896 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2)) (* 4144 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6)
 (* j2 j2 j2 j2 j2 j2)) (* 7524 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* 6802 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 
j2 j2 j2)) (* 3156 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) 
(* 684 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 54 (* h2 h2) 
(* h3 h3 h3) h4 (* h5 h5) (* h6 h6) j2) (* 512 (* h2 h2) (* h3 h3 h3) h4 h5 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2000 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3168 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2)) (* 2600 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 
j2 j2)) (* 1164 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 269 
(* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2)) (* 25 (* h2 h2) (* h3 h3 h3
) h4 h5 (* h6 h6 h6) j2) (* 64 (* h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 192 (* h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2
 j2 j2 j2)) (* 224 (* h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2))
 (* 128 (* h2 h2) (* h3 h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 36 (* h2 
h2) (* h3 h3 h3) h4 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 4 (* h2 h2) (* h3 h3 h3) h4
 (* h6 h6 h6 h6) (* j2 j2)) (* 64 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 416 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2
 j2 j2 j2 j2 j2 j2)) (* 1072 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2)) (* 1368 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 
j2)) (* 864 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 216 
(* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 256 (* h2 h2) (* h3 
h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1568 (* h2 h2) (* 
h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3872 (* h2 h2) (* 
h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4904 (* h2 h2) (* h3 
h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 3328 (* h2 h2) (* h3 h3 h3)
 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 1128 (* h2 h2) (* h3 h3 h3) (* h5 h5
 h5) (* h6 h6) (* j2 j2 j2)) (* 144 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6
) (* j2 j2)) (* 256 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2
 j2 j2 j2 j2)) (* 1472 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2
 j2 j2 j2 j2)) (* 3472 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2
 j2 j2 j2)) (* 4328 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2
 j2)) (* 3052 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 
1202 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 240 (* h2 h2
) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 18 (* h2 h2) (* h3 h3 h3) 
(* h5 h5) (* h6 h6 h6) j2) (* 64 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 352 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 800 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2
 j2 j2 j2)) (* 976 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2))
 (* 692 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 286 (* h2 
h2) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 64 (* h2 h2) (* h3 h3 h3) 
h5 (* h6 h6 h6 h6) (* j2 j2)) (* 6 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6 h6) j2)
 (* 32 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 88 (* 
h2 h2) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 68 (* h2 h2) (* h3 
h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2)) (* 12 (* h2 h2) (* h3 h3) (* h4 h4 h4 
h4) (* h5 h5) j2) (* 64 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 h6 (* j2 j2 j2 j2
)) (* 92 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 23 (* h2 h2)
 (* h3 h3) (* h4 h4 h4 h4) h5 h6 (* j2 j2)) (* (* h2 h2) (* h3 h3) (* h4 h4 h4 
h4) h5 h6 j2) (* 32 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2
)) (* 8 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) (* h6 h6) (* j2 j2 j2)) (* 64 (* h2 
h2) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 244 (* h2 h2) (* 
h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 318 (* h2 h2) (* h3 h3) (* 
h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 156 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* 
h5 h5 h5) (* j2 j2)) (* 18 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) j2) (* 
224 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 700 (* 
h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 775 (* h2 h2) (* 
h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 350 (* h2 h2) (* h3 h3) (* h4 
h4 h4) (* h5 h5) h6 (* j2 j2)) (* 51 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) 
h6 j2) (* 224 (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 492 (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 341 (* 
h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 72 (* h2 h2) (* h3 
h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2)) (* 3 (* h2 h2) (* h3 h3) (* h4 h4 h4) 
h5 (* h6 h6) j2) (* 64 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2
 j2 j2)) (* 76 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2)) 
(* 16 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2)) (* 32 (* h2 h2
) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 160 (* h2 h2) 
(* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 296 (* h2 h2) (* h3 
h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 240 (* h2 h2) (* h3 h3) (* h4 
h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 72 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 
h5 h5) (* j2 j2)) (* 224 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2)) (* 1024 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2)) (* 1780 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) 
(* 1442 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 516 (* h2
 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 54 (* h2 h2) (* h3 h3) 
(* h4 h4) (* h5 h5 h5) h6 j2) (* 384 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1512 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 2318 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2)) (* 1714 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* h6
 h6) (* j2 j2 j2)) (* 602 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* 
j2 j2)) (* 78 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) j2) (* 224 (* h2
 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 688 (* h2 h2)
 (* h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 780 (* h2 h2) (* h3 
h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 386 (* h2 h2) (* h3 h3) (* h4 
h4) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 73 (* h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 
h6 h6) (* j2 j2)) (* 3 (* h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6 h6) j2) (* 32 
(* h2 h2) (* h3 h3) (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 64 (* h2
 h2) (* h3 h3) (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 40 (* h2 h2) (* 
h3 h3) (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 8 (* h2 h2) (* h3 h3) (* h4
 h4) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 64 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 384 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 912 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2
 j2 j2 j2)) (* 1072 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) 
(* 624 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 144 (* h2 h2) 
(* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2)) (* 224 (* h2 h2) (* h3 h3) h4 (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1236 (* h2 h2) (* h3 h3) h4 (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2754 (* h2 h2) (* h3 h3) h4 (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 3146 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2)) (* 1908 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6)
 (* j2 j2 j2)) (* 558 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) 
(* 54 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) j2) (* 224 (* h2 h2) (* h3 
h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1108 (* h2 h2) (* h3 
h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2252 (* h2 h2) (* h3 h3)
 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2398 (* h2 h2) (* h3 h3) h4 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1403 (* h2 h2) (* h3 h3) h4 (* h5 h5)
 (* h6 h6 h6) (* j2 j2 j2)) (* 424 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6)
 (* j2 j2)) (* 51 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) j2) (* 64 (* h2 
h2) (* h3 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 264 (* h2 h2) 
(* h3 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 428 (* h2 h2) (* h3 h3
) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 342 (* h2 h2) (* h3 h3) h4 h5 (* 
h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 137 (* h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6 h6) 
(* j2 j2 j2)) (* 24 (* h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2)) (* (* 
h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6 h6) j2) (* 32 (* h2 h2) (* h3 h3) (* h5 h5 h5
 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 224 (* h2 h2) (* h3 h3) (* h5 h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 648 (* h2 h2) (* h3 h3) (* h5 h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 992 (* h2 h2) (* h3 h3) (* h5 h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 848 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2)) (* 384 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* 
j2 j2 j2)) (* 72 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 64 
(* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
428 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
1198 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
1810 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1580 
(* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 784 (* h2 h2) 
(* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 198 (* h2 h2) (* h3 h3) (* 
h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 18 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 
h6 h6) j2) (* 32 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 208 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 568 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 844 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2))
 (* 736 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 376 
(* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 104 (* h2 h2) (* 
h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 12 (* h2 h2) (* h3 h3) (* h5 h5) 
(* h6 h6 h6 h6) j2) (* 4 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 
j2)) (* 14 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 16 (* h2 
h2) h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2)) (* 6 (* h2 h2) h3 (* h4 h4 h4 h4)
 (* h5 h5 h5) j2) (* 16 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2
)) (* 36 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 22 (* h2 h2)
 h3 (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2)) (* 2 (* h2 h2) h3 (* h4 h4 h4 h4) 
(* h5 h5) h6 j2) (* 16 (* h2 h2) h3 (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)
) (* 18 (* h2 h2) h3 (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 2 (* h2 h2) 
h3 (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2)) (* 4 (* h2 h2) h3 (* h4 h4 h4 h4) (* 
h6 h6 h6) (* j2 j2 j2 j2)) (* 4 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 
j2 j2 j2 j2)) (* 18 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) 
(* 30 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 22 (* h2 h2) h3
 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 6 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5
 h5 h5) j2) (* 32 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) 
(* 123 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 177 (* h2 
h2) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 113 (* h2 h2) h3 (* h4 h4 
h4) (* h5 h5 h5) h6 (* j2 j2)) (* 27 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) h6 
j2) (* 56 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
171 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 182 (* h2 
h2) h3 (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 73 (* h2 h2) h3 (* h4 
h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 6 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) 
(* h6 h6) j2) (* 32 (* h2 h2) h3 (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)
) (* 67 (* h2 h2) h3 (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 39 (* h2 
h2) h3 (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 4 (* h2 h2) h3 (* h4 h4 h4)
 h5 (* h6 h6 h6) (* j2 j2)) (* 4 (* h2 h2) h3 (* h4 h4 h4) (* h6 h6 h6 h6) (* j2
 j2 j2 j2 j2)) (* 4 (* h2 h2) h3 (* h4 h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) 
(* 16 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 84 (* 
h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 174 (* h2 h2) h3 
(* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 178 (* h2 h2) h3 (* h4 h4) (* 
h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 90 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) h6 
(* j2 j2)) (* 18 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) h6 j2) (* 56 (* h2 h2) 
h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 264 (* h2 h2) h3 
(* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 498 (* h2 h2) h3 (* h4 
h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 470 (* h2 h2) h3 (* h4 h4) (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2)) (* 222 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* h6 
h6) (* j2 j2)) (* 42 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) j2) (* 56 (* 
h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 224 (* h2 
h2) h3 (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 345 (* h2 h2) h3 
(* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 248 (* h2 h2) h3 (* h4 h4) 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 77 (* h2 h2) h3 (* h4 h4) (* h5 h5) (* 
h6 h6 h6) (* j2 j2)) (* 6 (* h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6 h6) j2) (* 
16 (* h2 h2) h3 (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 48 (* h2 
h2) h3 (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 50 (* h2 h2) h3 (* h4
 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 20 (* h2 h2) h3 (* h4 h4) h5 (* h6 
h6 h6 h6) (* j2 j2 j2)) (* 2 (* h2 h2) h3 (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2)
) (* 16 (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
100 (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 258 (* 
h2 h2) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 352 (* h2 h2) h3 
h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 268 (* h2 h2) h3 h4 (* h5 h5 h5
 h5) (* h6 h6) (* j2 j2 j2)) (* 108 (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* h6 h6) 
(* j2 j2)) (* 18 (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* h6 h6) j2) (* 32 (* h2 h2) 
h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 185 (* h2 h2) h3 h4
 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 447 (* h2 h2) h3 h4 (* h5 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 578 (* h2 h2) h3 h4 (* h5 h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2)) (* 422 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* 
j2 j2 j2)) (* 165 (* h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 27 (* 
h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6 h6) j2) (* 16 (* h2 h2) h3 h4 (* h5 h5) (* h6
 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 82 (* h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6
 h6) (* j2 j2 j2 j2 j2 j2)) (* 170 (* h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6 h6) (* 
j2 j2 j2 j2 j2)) (* 180 (* h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2
)) (* 100 (* h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 26 (* h2 h2
) h3 h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 2 (* h2 h2) h3 h4 (* h5 h5) (* 
h6 h6 h6 h6) j2) (* 4 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 30 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 96 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 170 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 180 (* 
h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 114 (* h2 h2) h3 (* 
h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 40 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6
 h6 h6) (* j2 j2)) (* 6 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6 h6) j2) (* 4 (* h2
 h2) h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 30 (* h2 h2
) h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 96 (* h2 h2) h3 
(* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 170 (* h2 h2) h3 (* h5 h5
 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 180 (* h2 h2) h3 (* h5 h5 h5) (* h6 
h6 h6 h6) (* j2 j2 j2 j2)) (* 114 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* 
j2 j2 j2)) (* 40 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 6 (* h2
 h2) h3 (* h5 h5 h5) (* h6 h6 h6 h6) j2) (* (* h2 h2) (* h4 h4 h4 h4) (* h5 h5 
h5) h6 (* j2 j2 j2 j2)) (* 3 (* h2 h2) (* h4 h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 
j2)) (* 3 (* h2 h2) (* h4 h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* (* h2 h2) (* 
h4 h4 h4 h4) (* h5 h5 h5) h6 j2) (* 2 (* h2 h2) (* h4 h4 h4 h4) (* h5 h5) (* h6 
h6) (* j2 j2 j2 j2)) (* 4 (* h2 h2) (* h4 h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2
 j2)) (* 2 (* h2 h2) (* h4 h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* (* h2 h2)
 (* h4 h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* (* h2 h2) (* h4 h4 h4 h4) 
h5 (* h6 h6 h6) (* j2 j2 j2)) (* (* h2 h2) (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2
 j2 j2 j2 j2)) (* 4 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) 
(* 6 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 4 (* h2 h2) (* 
h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2)) (* (* h2 h2) (* h4 h4 h4) (* h5 h5 h5 h5
) h6 j2) (* 4 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 15 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 21 (* h2
 h2) (* h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 13 (* h2 h2) (* h4 h4 
h4) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 3 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5) 
(* h6 h6) j2) (* 4 (* h2 h2) (* h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2)) (* 12 (* h2 h2) (* h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 12 
(* h2 h2) (* h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 4 (* h2 h2) (* h4
 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* (* h2 h2) (* h4 h4 h4) h5 (* h6 h6 
h6 h6) (* j2 j2 j2 j2 j2)) (* 2 (* h2 h2) (* h4 h4 h4) h5 (* h6 h6 h6 h6) (* j2 
j2 j2 j2)) (* (* h2 h2) (* h4 h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 2 (* h2
 h2) (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 10 (* h2 h2) 
(* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 20 (* h2 h2) (* h4 h4
) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 20 (* h2 h2) (* h4 h4) (* h5 h5 
h5 h5) (* h6 h6) (* j2 j2 j2)) (* 10 (* h2 h2) (* h4 h4) (* h5 h5 h5 h5) (* h6 
h6) (* j2 j2)) (* 2 (* h2 h2) (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) j2) (* 4 (* h2
 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 19 (* h2 h2) 
(* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 36 (* h2 h2) (* h4 h4
) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 34 (* h2 h2) (* h4 h4) (* h5 h5 
h5) (* h6 h6 h6) (* j2 j2 j2)) (* 16 (* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6 
h6) (* j2 j2)) (* 3 (* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) j2) (* 2 (* h2
 h2) (* h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 8 (* h2 h2) 
(* h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 12 (* h2 h2) (* h4 h4
) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 8 (* h2 h2) (* h4 h4) (* h5 h5) 
(* h6 h6 h6 h6) (* j2 j2 j2)) (* 2 (* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6 h6 h6)
 (* j2 j2)) (* (* h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2
)) (* 6 (* h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 15 
(* h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 20 (* h2 h2) h4
 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 15 (* h2 h2) h4 (* h5 h5 h5 h5
) (* h6 h6 h6) (* j2 j2 j2)) (* 6 (* h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* 
j2 j2)) (* (* h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6 h6) j2) (* (* h2 h2) h4 (* h5 
h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 6 (* h2 h2) h4 (* h5 h5 h5) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 15 (* h2 h2) h4 (* h5 h5 h5) (* h6 h6 
h6 h6) (* j2 j2 j2 j2 j2)) (* 20 (* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2
 j2 j2 j2)) (* 15 (* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 6 
(* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* (* h2 h2) h4 (* h5 h5 h5
) (* h6 h6 h6 h6) j2) (* 256 h2 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 
j2 j2 j2 j2)) (* 896 h2 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2
)) (* 976 h2 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 336 h2 
(* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 36 h2 (* h3 h3 h3 h3) 
(* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 512 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h5 h6 
(* j2 j2 j2 j2 j2 j2)) (* 1024 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2
 j2 j2)) (* 416 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 48 h2 
(* h3 h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 256 h2 (* h3 h3 h3 h3) (* h4
 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 128 h2 (* h3 h3 h3 h3) (* h4 h4 h4) 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 16 h2 (* h3 h3 h3 h3) (* h4 h4 h4) (* h6 h6) 
(* j2 j2 j2 j2)) (* 256 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2
 j2 j2 j2)) (* 1216 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 
j2)) (* 2016 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 
1296 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 216 h2 (* h3 
h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 1024 h2 (* h3 h3 h3 h3) (* h4 
h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 4160 h2 (* h3 h3 h3 h3) (* h4 h4) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 5968 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 
h5) h6 (* j2 j2 j2 j2 j2)) (* 3696 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* 
j2 j2 j2 j2)) (* 1044 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) 
(* 108 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 1024 h2 (* h3 h3 
h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2880 h2 (* h3 h3 h3 
h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2544 h2 (* h3 h3 h3 h3) (* 
h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 856 h2 (* h3 h3 h3 h3) (* h4 h4) h5 
(* h6 h6) (* j2 j2 j2 j2)) (* 96 h2 (* h3 h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2
 j2 j2)) (* 256 h2 (* h3 h3 h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 320 h2 (* h3 h3 h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
128 h2 (* h3 h3 h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 16 h2 (* h3
 h3 h3 h3) (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 512 h2 (* h3 h3 h3 h3) h4 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2944 h2 (* h3 h3 h3 h3) h4 (* h5
 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 6464 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2)) (* 6624 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2
 j2 j2 j2)) (* 3024 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 
432 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 1024 h2 (* h3 h3 h3 
h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 5120 h2 (* h3 h3 h3 
h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 9856 h2 (* h3 h3 h3 h3) 
h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 9264 h2 (* h3 h3 h3 h3) h4 (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 4512 h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2)) (* 1116 h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 
j2 j2)) (* 108 h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 512 h2 
(* h3 h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1920 h2 (* h3
 h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2624 h2 (* h3 h3 h3 
h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1632 h2 (* h3 h3 h3 h3) h4 h5 
(* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 464 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6 h6) 
(* j2 j2 j2 j2)) (* 48 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 
256 h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 1728 h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 4704 h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
6544 h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4824 h2
 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1728 h2 (* h3 h3 
h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 216 h2 (* h3 h3 h3 h3) (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2)) (* 256 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1600 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4096 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2)) (* 5536 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 4240 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2)) (* 1828 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) 
(* 408 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 36 h2 (* h3 h3
 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 64 h2 (* h3 h3 h3) (* h4 h4 h4 h4) 
(* h5 h5) (* j2 j2 j2 j2 j2)) (* 208 h2 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) 
(* j2 j2 j2 j2)) (* 192 h2 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2)) 
(* 36 h2 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2)) (* 128 h2 (* h3 h3 h3
) (* h4 h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 224 h2 (* h3 h3 h3) (* h4 h4 h4 
h4) h5 h6 (* j2 j2 j2 j2)) (* 48 h2 (* h3 h3 h3) (* h4 h4 h4 h4) h5 h6 (* j2 j2 
j2)) (* 64 h2 (* h3 h3 h3) (* h4 h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 16 
h2 (* h3 h3 h3) (* h4 h4 h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 128 h2 (* h3 h3 h3
) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 544 h2 (* h3 h3 h3) (* h4 
h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 800 h2 (* h3 h3 h3) (* h4 h4 h4) (* 
h5 h5 h5) (* j2 j2 j2 j2)) (* 456 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* 
j2 j2 j2)) (* 72 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2)) (* 512 h2 
(* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 1760 h2 (* h3 
h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 2120 h2 (* h3 h3 h3) (* 
h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 1052 h2 (* h3 h3 h3) (* h4 h4 h4) (* 
h5 h5) h6 (* j2 j2 j2)) (* 156 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 
j2)) (* 512 h2 (* h3 h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
1184 h2 (* h3 h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 872 h2 (* 
h3 h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 152 h2 (* h3 h3 h3) (* 
h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 128 h2 (* h3 h3 h3) (* h4 h4 h4) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 160 h2 (* h3 h3 h3) (* h4 h4 h4) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2)) (* 32 h2 (* h3 h3 h3) (* h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 
j2)) (* 64 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 352 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 720 
h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 648 h2 (* h3 h3
 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2)) (* 216 h2 (* h3 h3 h3) (* h4 h4)
 (* h5 h5 h5 h5) (* j2 j2 j2)) (* 512 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 2512 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2)) (* 4640 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2)) (* 3972 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) 
(* 1548 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 216 h2 (* h3 
h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 896 h2 (* h3 h3 h3) (* h4 h4) (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3760 h2 (* h3 h3 h3) (* h4 h4) (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6100 h2 (* h3 h3 h3) (* h4 h4) (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 4830 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2)) (* 1834 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6)
 (* j2 j2 j2)) (* 240 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) 
(* 512 h2 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
1616 h2 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1920 h2
 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 968 h2 (* h3 h3 
h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 152 h2 (* h3 h3 h3) (* h4 h4) 
h5 (* h6 h6 h6) (* j2 j2 j2)) (* 64 h2 (* h3 h3 h3) (* h4 h4) (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 128 h2 (* h3 h3 h3) (* h4 h4) (* h6 h6 h6 h6) (* j2
 j2 j2 j2 j2 j2)) (* 80 h2 (* h3 h3 h3) (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2
 j2)) (* 16 h2 (* h3 h3 h3) (* h4 h4) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 128 h2
 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 832 h2 (* h3
 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2144 h2 (* h3 h3 h3) 
h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 2736 h2 (* h3 h3 h3) h4 (* h5 h5
 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 1728 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* 
j2 j2 j2 j2)) (* 432 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 512 
h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3008 
h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 7072 h2 
(* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 8464 h2 (* h3 
h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 5400 h2 (* h3 h3 h3) h4 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 1728 h2 (* h3 h3 h3) h4 (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2)) (* 216 h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 
j2)) (* 512 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 2688 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 5760 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6472
 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 4012 h2 (* h3 
h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 1280 h2 (* h3 h3 h3) h4 (* 
h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 156 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 
h6) (* j2 j2)) (* 128 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 576 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 992 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 816 h2 
(* h3 h3 h3) h4 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 320 h2 (* h3 h3 h3) h4
 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 48 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6 h6)
 (* j2 j2 j2)) (* 64 h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2 j2)) (* 480 h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 1488 h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 2440 h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 2232 h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
1080 h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 216 h2 (* h3 
h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 128 h2 (* h3 h3 h3) (* h5 h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 912 h2 (* h3 h3 h3) (* h5 h5
 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2720 h2 (* h3 h3 h3) (* h5 h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4388 h2 (* h3 h3 h3) (* h5 h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4116 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2)) (* 2228 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2)) (* 636 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 
72 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 64 h2 (* h3 h3 h3) 
(* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 448 h2 (* h3 h3 h3)
 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1312 h2 (* h3 h3 h3) 
(* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2080 h2 (* h3 h3 h3) (* 
h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1924 h2 (* h3 h3 h3) (* h5 h5) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1036 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 
h6 h6) (* j2 j2 j2 j2)) (* 300 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 
j2 j2)) (* 36 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 16 h2 (* 
h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 64 h2 (* h3 h3) (* h4
 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 84 h2 (* h3 h3) (* h4 h4 h4 h4) (* 
h5 h5 h5) (* j2 j2 j2)) (* 36 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2
)) (* 64 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 168 h2
 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 116 h2 (* h3 h3) (* 
h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 12 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5
 h5) h6 (* j2 j2)) (* 64 h2 (* h3 h3) (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 
j2 j2)) (* 80 h2 (* h3 h3) (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 8 h2
 (* h3 h3) (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 16 h2 (* h3 h3) (* h4 
h4 h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 16 h2 (* h3 h3) (* h4 h4 h4) (* h5
 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 80 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5
) (* j2 j2 j2 j2 j2)) (* 148 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 
j2 j2)) (* 120 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2)) (* 36 h2 
(* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2)) (* 128 h2 (* h3 h3) (* h4 h4 
h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 544 h2 (* h3 h3) (* h4 h4 h4) (* 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 864 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) 
h6 (* j2 j2 j2 j2)) (* 616 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2
)) (* 168 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 224 h2 (* h3 
h3) (* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 744 h2 (* h3 h3) 
(* h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 881 h2 (* h3 h3) (* h4 
h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 398 h2 (* h3 h3) (* h4 h4 h4) (* 
h5 h5) (* h6 h6) (* j2 j2 j2)) (* 37 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) (* h6 
h6) (* j2 j2)) (* 128 h2 (* h3 h3) (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 288 h2 (* h3 h3) (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
176 h2 (* h3 h3) (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 16 h2 (* h3 h3
) (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 16 h2 (* h3 h3) (* h4 h4 h4) (* 
h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 16 h2 (* h3 h3) (* h4 h4 h4) (* h6 h6 h6 
h6) (* j2 j2 j2 j2 j2)) (* 64 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2
 j2 j2 j2 j2 j2)) (* 368 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2)) (* 832 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) 
(* 924 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 504 h2 (* 
h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 108 h2 (* h3 h3) (* h4 h4) 
(* h5 h5 h5 h5) h6 (* j2 j2)) (* 224 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1140 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 2318 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6)
 (* j2 j2 j2 j2 j2)) (* 2376 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2
 j2 j2 j2)) (* 1238 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) 
(* 264 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 224 h2 (* h3 
h3) (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 948 h2 (* h3 
h3) (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1572 h2 (* h3 h3)
 (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 1233 h2 (* h3 h3) (* h4
 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 422 h2 (* h3 h3) (* h4 h4) (* h5
 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 37 h2 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6 
h6) (* j2 j2)) (* 64 h2 (* h3 h3) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2
 j2 j2)) (* 200 h2 (* h3 h3) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2))
 (* 216 h2 (* h3 h3) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 88 h2 
(* h3 h3) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 8 h2 (* h3 h3) (* h4 
h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2)) (* 64 h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 432 h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1200 h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 1756 h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2)) (* 1428 h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2))
 (* 612 h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 108 h2 (* h3 
h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 128 h2 (* h3 h3) h4 (* h5 h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 792 h2 (* h3 h3) h4 (* h5 h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2044 h2 (* h3 h3) h4 (* h5 h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2828 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2)) (* 2220 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2)) (* 940 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 168
 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 64 h2 (* h3 h3) h4 (* 
h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 352 h2 (* h3 h3) h4 (* h5
 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 776 h2 (* h3 h3) h4 (* h5 h5) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 868 h2 (* h3 h3) h4 (* h5 h5) (* h6 h6
 h6 h6) (* j2 j2 j2 j2 j2)) (* 508 h2 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6 h6) (* 
j2 j2 j2 j2)) (* 140 h2 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 
12 h2 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 16 h2 (* h3 h3) (* h5
 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 128 h2 (* h3 h3) (* 
h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 436 h2 (* h3 h3) (* h5
 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 820 h2 (* h3 h3) (* h5 h5 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 920 h2 (* h3 h3) (* h5 h5 h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 616 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6
) (* j2 j2 j2 j2)) (* 228 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)
) (* 36 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 16 h2 (* h3 h3) 
(* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 128 h2 (* h3 h3)
 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 436 h2 (* h3 h3) 
(* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 820 h2 (* h3 h3) (* h5
 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 920 h2 (* h3 h3) (* h5 h5 h5) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 616 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6
 h6) (* j2 j2 j2 j2)) (* 228 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 
j2)) (* 36 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 8 h2 h3 (* h4
 h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 28 h2 h3 (* h4 h4 h4 h4) (* h5
 h5 h5) h6 (* j2 j2 j2 j2)) (* 32 h2 h3 (* h4 h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2
 j2)) (* 12 h2 h3 (* h4 h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* 16 h2 h3 (* h4 
h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 35 h2 h3 (* h4 h4 h4 h4) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 20 h2 h3 (* h4 h4 h4 h4) (* h5 h5) (* h6
 h6) (* j2 j2 j2)) (* h2 h3 (* h4 h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 8 
h2 h3 (* h4 h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 8 h2 h3 (* h4 h4 h4
 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 8 h2 h3 (* h4 h4 h4) (* h5 h5 h5 h5) h6
 (* j2 j2 j2 j2 j2 j2)) (* 36 h2 h3 (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 
j2 j2)) (* 60 h2 h3 (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 44 h2 h3
 (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2)) (* 12 h2 h3 (* h4 h4 h4) (* h5 h5
 h5 h5) h6 (* j2 j2)) (* 32 h2 h3 (* h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 130 h2 h3 (* h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2
)) (* 202 h2 h3 (* h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 142 h2 
h3 (* h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 38 h2 h3 (* h4 h4 h4) 
(* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 32 h2 h3 (* h4 h4 h4) (* h5 h5) (* h6 h6 h6
) (* j2 j2 j2 j2 j2 j2)) (* 102 h2 h3 (* h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2)) (* 110 h2 h3 (* h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) 
(* 42 h2 h3 (* h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 2 h2 h3 (* h4 
h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 8 h2 h3 (* h4 h4 h4) h5 (* h6 h6 h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 16 h2 h3 (* h4 h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 
j2 j2 j2)) (* 8 h2 h3 (* h4 h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 16 h2 
h3 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 88 h2 h3 (* 
h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 192 h2 h3 (* h4 h4) 
(* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 208 h2 h3 (* h4 h4) (* h5 h5 h5
 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 112 h2 h3 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6)
 (* j2 j2 j2)) (* 24 h2 h3 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 32 
h2 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 161 h2 h3
 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 329 h2 h3 (* h4 
h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 341 h2 h3 (* h4 h4) (* h5 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 179 h2 h3 (* h4 h4) (* h5 h5 h5) (* h6 
h6 h6) (* j2 j2 j2)) (* 38 h2 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) 
(* 16 h2 h3 (* h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 66 
h2 h3 (* h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 103 h2 h3 
(* h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 73 h2 h3 (* h4 h4) 
(* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 21 h2 h3 (* h4 h4) (* h5 h5) (* h6
 h6 h6 h6) (* j2 j2 j2)) (* h2 h3 (* h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2))
 (* 8 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 52 
h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 140 h2 h3 h4 
(* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 200 h2 h3 h4 (* h5 h5 h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 160 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6 h6
) (* j2 j2 j2 j2)) (* 68 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 
12 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* 8 h2 h3 h4 (* h5 h5 h5) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 52 h2 h3 h4 (* h5 h5 h5) (* h6 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 140 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2)) (* 200 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2
 j2 j2)) (* 160 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 68 h2 
h3 h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 12 h2 h3 h4 (* h5 h5 h5) (* 
h6 h6 h6 h6) (* j2 j2)) (* h2 (* h4 h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2
 j2 j2)) (* 3 h2 (* h4 h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 3 h2
 (* h4 h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* h2 (* h4 h4 h4 h4) (* 
h5 h5 h5) (* h6 h6) (* j2 j2)) (* h2 (* h4 h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2)) (* 2 h2 (* h4 h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2))
 (* h2 (* h4 h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* h2 (* h4 h4 h4) 
(* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4 h2 (* h4 h4 h4) (* h5 h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 6 h2 (* h4 h4 h4) (* h5 h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2)) (* 4 h2 (* h4 h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)
) (* h2 (* h4 h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2)) (* 2 h2 (* h4 h4 h4) 
(* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 8 h2 (* h4 h4 h4) (* h5 h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 12 h2 (* h4 h4 h4) (* h5 h5 h5) (* h6 h6
 h6) (* j2 j2 j2 j2)) (* 8 h2 (* h4 h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2
)) (* 2 h2 (* h4 h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* h2 (* h4 h4 h4) 
(* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3 h2 (* h4 h4 h4) (* h5 h5) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 3 h2 (* h4 h4 h4) (* h5 h5) (* h6 h6 h6 
h6) (* j2 j2 j2 j2)) (* h2 (* h4 h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) 
(* h2 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 5 h2 
(* h4 h4) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 10 h2 (* h4 h4)
 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 10 h2 (* h4 h4) (* h5 h5 h5
 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 5 h2 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6 h6
) (* j2 j2 j2)) (* h2 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2)) (* h2 
(* h4 h4) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 5 h2 (* h4 
h4) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 10 h2 (* h4 h4) (* h5
 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 10 h2 (* h4 h4) (* h5 h5 h5) (* 
h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 5 h2 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6 h6) (* 
j2 j2 j2)) (* h2 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2)) (* 256 (* h3 
h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 896 (* h3 h3 h3
 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 976 (* h3 h3 h3 h3) (* 
h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 336 (* h3 h3 h3 h3) (* h4 h4 h4) 
(* h5 h5) h6 (* j2 j2 j2 j2)) (* 36 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 
(* j2 j2 j2)) (* 256 (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2)) (* 512 (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2))
 (* 208 (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 24 (* 
h3 h3 h3 h3) (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 256 (* h3 h3 h3 h3) 
(* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1216 (* h3 h3 h3 h3) 
(* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2016 (* h3 h3 h3 h3) (* 
h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 1296 (* h3 h3 h3 h3) (* h4 h4) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 216 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5
) h6 (* j2 j2 j2 j2)) (* 512 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 2176 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 3328 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 2240 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2)) (* 672 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2)) (* 72 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 256
 (* h3 h3 h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 704 
(* h3 h3 h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 608 (* h3
 h3 h3 h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 208 (* h3 h3 h3 
h3) (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 24 (* h3 h3 h3 h3) (* h4 h4
) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 256 (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 1472 (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3232 (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3312 (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 1512 (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2)) (* 216 (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2
)) (* 256 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 1344 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 2752 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2))
 (* 2784 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
1456 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 372 (* h3 
h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 36 (* h3 h3 h3 h3) h4 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 64 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5
) h6 (* j2 j2 j2 j2 j2 j2)) (* 208 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) h6 (* 
j2 j2 j2 j2 j2)) (* 192 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2
)) (* 36 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 64 (* h3 h3 
h3) (* h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 112 (* h3 h3 h3) (* 
h4 h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 24 (* h3 h3 h3) (* h4 h4 h4 h4)
 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 128 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 544 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2
 j2 j2 j2 j2 j2)) (* 800 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2)) (* 456 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 72 
(* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 256 (* h3 h3 h3) (* 
h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 944 (* h3 h3 h3) (* 
h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1268 (* h3 h3 h3) (* h4 
h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 718 (* h3 h3 h3) (* h4 h4 h4) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 114 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) 
(* h6 h6) (* j2 j2 j2)) (* 128 (* h3 h3 h3) (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 352 (* h3 h3 h3) (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2
 j2 j2 j2)) (* 272 (* h3 h3 h3) (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2))
 (* 48 (* h3 h3 h3) (* h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 64 (* h3 h3
 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 352 (* h3 h3 
h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 720 (* h3 h3 h3) 
(* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 648 (* h3 h3 h3) (* h4 h4
) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 216 (* h3 h3 h3) (* h4 h4) (* h5 h5 
h5 h5) h6 (* j2 j2 j2 j2)) (* 256 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1312 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2560 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 2344 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6)
 (* j2 j2 j2 j2 j2)) (* 984 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2)) (* 144 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) 
(* 256 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 1152 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 2064 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 1844 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 790
 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 114 (* h3 h3 
h3) (* h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 64 (* h3 h3 h3) (* h4 h4) 
h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 224 (* h3 h3 h3) (* h4 h4) h5
 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 272 (* h3 h3 h3) (* h4 h4) h5 (* 
h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 136 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6 h6
 h6) (* j2 j2 j2 j2 j2)) (* 24 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6 h6 h6) (* j2 
j2 j2 j2)) (* 64 (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 416 (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 1072 (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 1368 (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 864 (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 216 (* 
h3 h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 128 (* h3 h3 h3) h4 
(* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 784 (* h3 h3 h3) h4
 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1936 (* h3 h3 h3) h4 
(* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2452 (* h3 h3 h3) h4 (* 
h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1664 (* h3 h3 h3) h4 (* h5 h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 564 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2)) (* 72 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2
 j2)) (* 64 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
 j2)) (* 384 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 928 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 1152 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 772 
(* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 264 (* h3 h3 h3
) h4 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 36 (* h3 h3 h3) h4 (* h5 h5) 
(* h6 h6 h6 h6) (* j2 j2 j2)) (* 16 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 64 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2)) (* 84 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 
36 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 32 (* h3 h3) (* h4
 h4 h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 84 (* h3 h3) (* h4 h4 
h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 58 (* h3 h3) (* h4 h4 h4 h4) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 6 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) 
(* h6 h6) (* j2 j2 j2)) (* 16 (* h3 h3) (* h4 h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2
 j2 j2 j2 j2)) (* 24 (* h3 h3) (* h4 h4 h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2
)) (* 16 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
80 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 148 (* h3
 h3) (* h4 h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 120 (* h3 h3) (* h4 
h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 36 (* h3 h3) (* h4 h4 h4) (* h5 h5
 h5 h5) h6 (* j2 j2 j2)) (* 64 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 288 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 496 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2)) (* 392 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2)) (* 120 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 64 
(* h3 h3) (* h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 232 
(* h3 h3) (* h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 284 (* 
h3 h3) (* h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 128 (* h3 h3) 
(* h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 12 (* h3 h3) (* h4 h4 h4
) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 16 (* h3 h3) (* h4 h4 h4) h5 (* h6 h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 40 (* h3 h3) (* h4 h4 h4) h5 (* h6 h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2)) (* 24 (* h3 h3) (* h4 h4 h4) h5 (* h6 h6 h6 h6) (* j2 j2
 j2 j2 j2)) (* 32 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 192 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 456 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 536 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 312 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 72
 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 64 (* h3 h3) (* 
h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 348 (* h3 h3) 
(* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 770 (* h3 h3) 
(* h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 872 (* h3 h3) (* 
h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 506 (* h3 h3) (* h4 h4) 
(* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 120 (* h3 h3) (* h4 h4) (* h5 h5 
h5) (* h6 h6 h6) (* j2 j2 j2)) (* 32 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 144 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 244 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 190 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6 h6 
h6) (* j2 j2 j2 j2 j2)) (* 64 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* 
j2 j2 j2 j2)) (* 6 (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) 
(* 16 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 112 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 324 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
496 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 424 (* 
h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 192 (* h3 h3) h4 
(* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 36 (* h3 h3) h4 (* h5 h5 h5 h5)
 (* h6 h6 h6) (* j2 j2 j2)) (* 16 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 112 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 324 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 496 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2
 j2 j2 j2 j2 j2)) (* 424 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 
j2 j2)) (* 192 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 36 
(* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2)) (* 4 h3 (* h4 h4 h4 h4) 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 14 h3 (* h4 h4 h4 h4) (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 16 h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* h6 h6
) (* j2 j2 j2 j2)) (* 6 h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) 
(* 4 h3 (* h4 h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 10 h3 
(* h4 h4 h4 h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 6 h3 (* h4 h4 h4 
h4) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 4 h3 (* h4 h4 h4) (* h5 h5 h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 18 h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* h6
 h6) (* j2 j2 j2 j2 j2 j2)) (* 30 h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2)) (* 22 h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)
) (* 6 h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 8 h3 (* h4 h4 
h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 36 h3 (* h4 h4 h4) 
(* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 60 h3 (* h4 h4 h4) (* h5 h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 44 h3 (* h4 h4 h4) (* h5 h5 h5) (* h6 h6
 h6) (* j2 j2 j2 j2)) (* 12 h3 (* h4 h4 h4) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 
j2)) (* 4 h3 (* h4 h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 14 h3 (* h4 h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 16 h3 
(* h4 h4 h4) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 6 h3 (* h4 h4 h4) 
(* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2)) (* 4 h3 (* h4 h4) (* h5 h5 h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 22 h3 (* h4 h4) (* h5 h5 h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 48 h3 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2)) (* 52 h3 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2
 j2 j2 j2)) (* 28 h3 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 
6 h3 (* h4 h4) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 4 h3 (* h4 h4) (* 
h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 22 h3 (* h4 h4) (* h5 
h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 48 h3 (* h4 h4) (* h5 h5 h5)
 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 52 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6
 h6 h6) (* j2 j2 j2 j2 j2)) (* 28 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6 h6) (* 
j2 j2 j2 j2)) (* 6 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2))) 0)))
(check-sat)
(exit)

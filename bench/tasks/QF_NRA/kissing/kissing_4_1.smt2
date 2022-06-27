(set-info :smt-lib-version 2.6)
(set-logic QF_NRA)
(set-info :source |
These benchmarks used in the paper:

  Dejan Jovanovic and Leonardo de Moura.  Solving Non-Linear Arithmetic.
  In IJCAR 2012, published as LNCS volume 7364, pp. 339--354.

The kissing family contains classic kissing number problems encoded in
SMT-LIB.

kissing problem: pack 1 spheres in 4 dimensions

Submitted to SMT-LIB by Dejan Jovanovic.
|)
(set-info :category "crafted")
(set-info :status sat)
(declare-fun x_0_0 () Real)
(declare-fun x_0_1 () Real)
(declare-fun x_0_2 () Real)
(declare-fun x_0_3 () Real)
(assert (= (+ (* x_0_0 x_0_0) (+ (* x_0_1 x_0_1) (+ (* x_0_2 x_0_2) (* x_0_3 x_0_3)))) 1))
(check-sat)
(exit)

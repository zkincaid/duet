(set-info :smt-lib-version 2.6)
(set-logic QF_NIA)
(set-info :source |
Problem: Semi-magic sqaure of cubes
Generate by: Fuqi Jia, Minghao Liu, Pei Huang, Feifei Ma, Jian Zhang
Generated on: 2022-02-28
Generator: https://github.com/MRVAPOR/math_puzzles_smtlib_generator
Application: Solving hard mathematical problems
Target solver: z3
|)
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "crafted")
(set-info :status unsat)
(declare-fun t () Int)
(declare-fun x_0_0 () Int)
(declare-fun x_0_1 () Int)
(declare-fun x_1_0 () Int)
(declare-fun x_1_1 () Int)
(assert (= (+ (* x_0_0 x_0_0 x_0_0) (* x_0_1 x_0_1 x_0_1) ) t))
(assert (= (+ (* x_1_0 x_1_0 x_1_0) (* x_1_1 x_1_1 x_1_1) ) t))
(assert (= (+ (* x_0_0 x_0_0 x_0_0) (* x_1_0 x_1_0 x_1_0) ) t))
(assert (= (+ (* x_0_1 x_0_1 x_0_1) (* x_1_1 x_1_1 x_1_1) ) t))
(assert (distinct x_0_0 x_0_1))
(assert (distinct x_0_0 x_1_0))
(assert (distinct x_0_0 x_1_1))
(assert (distinct x_0_1 x_1_0))
(assert (distinct x_0_1 x_1_1))
(assert (distinct x_1_0 x_1_1))
(assert (> x_0_0 0))
(assert (> x_0_1 0))
(assert (> x_1_0 0))
(assert (> x_1_1 0))
(check-sat)
;;(get-assignment)
;;(get-model)
(exit)

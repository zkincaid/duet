(set-logic LIA)


(synth-fun max10 ((x1 Int) (x2 Int) (x3 Int) (x4 Int) (x5 Int)
                 (x6 Int) (x7 Int) (x8 Int) (x9 Int) (x10 Int)) Int
)

(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)
(declare-var x4 Int)
(declare-var x5 Int)
(declare-var x6 Int)
(declare-var x7 Int)
(declare-var x8 Int)
(declare-var x9 Int)
(declare-var x10 Int)
(declare-var ub Int)


(constraint (>= (max10 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ) x1))
(constraint (>= (max10 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ) x2))
(constraint (>= (max10 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ) x3))
(constraint (>= (max10 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ) x4))
(constraint (>= (max10 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ) x5))
(constraint (>= (max10 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ) x6))
(constraint (>= (max10 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ) x7))
(constraint (>= (max10 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ) x8))
(constraint (>= (max10 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ) x9))
(constraint (>= (max10 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ) x10))

(constraint (or (not (and (<= x1 ub) (and (<= x2 ub) (and (<= x3 ub) (and (<= x4 ub) (and (<= x5 ub) (and (<= x6 ub) (and (<= x7 ub) (and (<= x8 ub) (and (<= x9 ub) (<= x10 ub)))))))))))
                (<= (max10 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) ub)))
(check-synth)


(assert (forall ((x Int) (y Int))
		(exists ((expr1 Int) (expr2 Int))
			(= (+ expr1 expr2) (+ (+ (+ x y) y) (+ x y))))))

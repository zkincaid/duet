(assert (forall ((totsec Int))
		(exists ((h Int) (m Int) (s Int))
			(or (< totsec 0)
			    (and
			     (= (+ (* 3600 h) (* 60 m) s) totsec)
			     (<= 0 m)
			     (< m 60)
			     (<= 0 s)
			     (< s 60))))))

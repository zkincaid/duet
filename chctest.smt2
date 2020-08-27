;;
;; i = 0;
;; L: while (i < 5) i=i+1;
;; assert(i<=4)
;;
;;

(declare-rel L (Int))
(declare-rel Error ())
(declare-var i Int)
(declare-var i_p Int)
(rule (L 0))
(rule (=> (and (L i) (< i 5) (= i_p (+ i 1))) (L i_p)))
(rule (=> (and (L i) (> i 4)) Error))
(query Error)

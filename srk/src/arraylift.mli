open Syntax


(** [array_exponentiate ctx exp_op] takes an exponentiation operation [exp_op]
  , and returns an exponentiation operator which numerically abstracts the array variables
  in the formula, applies exp_op, then reintroduces the array variables 
*)
val array_exponentiate :
  'a context ->
  'a Iteration.exp_op ->
  ('a TransitionFormula.t -> 'a arith_term -> 'a formula)


(** [map_elim ctx formula] computes an equisatisfiable formula to [formula]
  in which all array variables are replaced with numerical abstractions.
*)
val map_elim : 'a context -> 'a formula -> 'a formula
open Syntax


val array_exponentiate :
  'a context ->
  'a Iteration.exp_op ->
  ('a TransitionFormula.t -> 'a arith_term -> 'a formula)

val map_elim : 'a context -> 'a formula -> 'a formula
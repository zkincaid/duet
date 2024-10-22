open Syntax

type 'a t
val pp : 'a Iteration.Solver.t -> Format.formatter -> 'a t -> unit
val abstract : 'a Iteration.Solver.t -> 'a t
val exp_t : 'a Iteration.Solver.t -> 'a t -> 'a arith_term -> 'a formula
val exp : 'a Iteration.exp_op

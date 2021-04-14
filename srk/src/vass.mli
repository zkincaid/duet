(** Wedge abstract domain.  A wedge corresponds to a conjunction of equations
    and inequations over a vocabulary that includes addition, multiplication,
    exponentiation, logarithm, division, and modulo. *)
open Syntax

type 'a t
val pp : 'a context -> (symbol * symbol) list -> Format.formatter -> 'a t -> unit
val exp : 'a context -> (symbol * symbol) list -> 'a arith_term -> 'a t -> 'a formula
val abstract : 'a context -> 'a TransitionFormula.t -> 'a t

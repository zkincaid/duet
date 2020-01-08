(** Linear semiautomata *)

open Syntax

(** Linear semiautomaton abstraction, consisting of a linear automaton
    (i.e., a finite set of linear maps Q^n -> Q^n for some n) and an
    affine map from the space of symbols into Q^n *)
type t

val abstract : ?exists:(symbol -> bool) -> 'a context -> 'a formula -> (symbol * symbol) list -> t

val to_transition_formula : 'a context -> t -> (symbol * symbol) list -> 'a formula

val dimension : t -> int

val transitions : t -> Linear.QQMatrix.t list

val simulation : t -> Linear.QQMatrix.t

val join : t -> t -> t


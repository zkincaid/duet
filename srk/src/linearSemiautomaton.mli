(** Linear semiautomata *)

open Syntax
open Linear

(** Linear semiautomaton abstraction, consisting of a linear automaton
    (i.e., a finite set of linear maps Q^n -> Q^n for some n) and an
    affine map from the space of symbols into Q^n *)
type t

(** A linear transition system is a transition system over QQ^n where
   the set of transitions is a linear subspace of the transition space
   QQ^n x QQ^n; i.e., there are some matrices A and B such that the
   transitions are exactly the solutions to Ax' = Bx *)
type lts

(** TDLTS abstraction, consisting of a linear transition system that
   is total and deterministic (i.e., there is some matrix A such that
   the transitions are the solutions to x' = Ax) and an affine map
   from the space of symbols into Q^n *)
type tdlts_abstraction

val lts_of_tdlts : tdlts_abstraction -> lts
val tdlts_equiv : tdlts_abstraction -> tdlts_abstraction -> bool

val abstract : ?exists:(symbol -> bool) -> 'a context -> 'a formula -> (symbol * symbol) list -> t

(** [abstract_generalized_eigenspace lts eigenvalue rank] construct
   best TDLTS abstraction of an LTS, where the TDLTS has only
   [eigenvalue] as an eigenvalue, and the maximum rank of a
   generalized eigenvector is [rank]*)
val abstract_generalized_eigenspace : lts -> QQ.t -> int -> tdlts_abstraction

val lts_simulates : lts -> lts -> bool

val to_transition_formula : 'a context -> t -> (symbol * symbol) list -> 'a formula

val dimension : t -> int

val transitions : t -> QQMatrix.t list

val simulation : t -> QQMatrix.t

val join : t -> t -> t

val pp_tdlts : Format.formatter -> tdlts_abstraction -> unit
val pp_lts : Format.formatter -> lts -> unit

(** [mk_tdlts sim dyn] constructs a TDLTS with simulation [sim] and dynamics matrix [dyn] *)
val mk_tdlts : QQMatrix.t -> QQMatrix.t -> tdlts_abstraction

(** [mk_lts A B] constructs the LTS whose transitions are the
   solutions to (Ax' = Bx) *)
val mk_lts : QQMatrix.t -> QQMatrix.t -> lts

(** Approximate transitive closure computation. *)
open Syntax

module Solver : sig
  type 'a t

  (** Allocate a new solver. *)
  val make : 'a context -> ?theory:[`LIRR | `LIRA ] -> 'a TransitionFormula.t -> 'a t

  (** Symbolic abstraction as described in Reps, Sagiv, Yorsh---"Symbolic
     implementation of the best transformer", VMCAI 2004. *)
  val abstract : 'a t -> ('a, 'b) Abstract.domain -> 'b

  (** Retrieve the formula associated with a solver. *)
  val get_formula : 'a t -> 'a formula

  val get_symbols : 'a t -> (symbol * symbol) list
  val get_constants : 'a t -> Symbol.Set.t

  val get_transition_formula : 'a t -> 'a TransitionFormula.t

  (** Retrieve a model of the formula that not satisfy any blocking clause, if
     possible.  *)
  val get_model : 'a t -> [ `Sat of 'a Abstract.smt_model | `Unsat | `Unknown ]

  val check : 'a t -> [ `Sat | `Unsat | `Unknown ]

  val get_context : 'a t -> 'a context

  val get_theory : 'a t -> [ `LIRR | `LIRA ]

  (** [add s phis] conjoins each formula in [phis] to the formula associated
     with the solver. *)
  val add : 'a t -> ('a formula) list -> unit

  (** Push a fresh entry onto the solver's stack.  Assertions added to the
     formula with [add] are reverted after the entry is [pop]ed off the
     stack. *)
  val push : 'a t -> unit

  (** Pop last entry off of the solver's stack *)
  val pop : 'a t -> unit

  val get_abstract_solver : 'a t -> 'a Abstract.Solver.t

  val wedge_hull : 'a t -> 'a Wedge.t
end

type 'a exp_op = 'a Solver.t -> 'a arith_term -> 'a formula

type 'a wedge_exp_op =
  'a context ->
  (symbol * symbol) list ->
  'a Wedge.t ->
  'a arith_term ->
  'a formula

module Cartesian : sig
  type 'a t
  val pp : 'a Solver.t -> Format.formatter -> 'a t -> unit
  val precondition : 'a t -> 'a formula
  val postcondition : 'a t -> 'a formula
end

module type Exp = sig
  val exp : 'a exp_op
end

module type WedgeExp = sig
  val wedge_exp : 'a wedge_exp_op
end

module type Domain = sig
  type 'a t
  val pp : 'a Solver.t -> Format.formatter -> 'a t -> unit
  val abstract : 'a Solver.t -> 'a t
  val exp_t : 'a Solver.t -> 'a t -> 'a arith_term -> 'a formula
  val exp : 'a exp_op
end

module type WedgeDomain = sig
  type 'a t
  val pp : 'a Solver.t -> Format.formatter -> 'a t -> unit
  val wedge_abstract : 'a context ->
    (symbol * symbol) list ->
    'a Wedge.t ->
    'a t
  val exp_t : 'a context -> (symbol * symbol) list -> 'a t -> 'a arith_term -> 'a formula
  val wedge_exp : 'a wedge_exp_op
end

module LIRRGuard : Domain with type 'a t = 'a Cartesian.t

module WedgeGuard : WedgeDomain with type 'a t = 'a Cartesian.t

module PolyhedronGuard : Domain with type 'a t = 'a Cartesian.t

module LinearGuard : Domain with type 'a t = 'a Cartesian.t

(** Abstract a transition formula F(x,x') by a system of recurrences of the form
    a(x') >= a(x) + c
    where a is a linear map and c is a scalar. *)
module LossyTranslation : Domain

(** Abstract a transitiPon formula F(x,x') a translation
      a(x') = a(x) + c
    guarded by a LIA formula *)
module GuardedTranslation : Domain

(** Abstract a transition formula F(x,x',y) (where y denotes a set of
   symbolic constants) by a system of recurrences of the form
    [ax' >= ax + t(y)]
   where a is a linear map and t(y) is a (possibly non-linear)
   term over y. *)
module NonlinearRecurrenceInequation : WedgeDomain

(** Improve iteration operator using split invariants *)
val split : 'a exp_op -> 'a exp_op

(** Improve iteration operator using variable directions (increasing,
   decreasing, stable) to find phase splits. *)
val invariant_direction : 'a exp_op -> 'a exp_op

(** Given a transition formula T and a transition predicate p, we say
   that p is an invariant of T if T(x,x') /\ T(x',x'') is consistent and
     T(x,x') /\ T(x',x'') /\ p(x,x') => p(x',x'')
   A set of transition predicates defines a partition of T, which is acyclic
   in the sense that when a computation leaves a cell it may never return.
   This function takes a set of candidate transition predicates, a transition formula,
   and a mortal precondition operator and returns another mortal precondition
   via analyzing the phase transition structure of the transition formula. *)
val phase_mp : 'a context -> 
               ('a formula) list ->
               ('a Solver.t -> 'a TransitionFormula.t) ->
               ('a Solver.t -> 'a formula) ->
               'a Solver.t ->
               'a formula

val product : 'a exp_op list -> 'a exp_op

val closure : 'a exp_op -> 'a Solver.t -> 'a formula

val wedge_product : 'a wedge_exp_op list -> 'a wedge_exp_op

val wedge_lift : 'a wedge_exp_op -> 'a exp_op

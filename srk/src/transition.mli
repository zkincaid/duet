(** Transition formulas. *)
open Syntax

module type Var = sig
  type t
  val pp : Format.formatter -> t -> unit
  val show : t -> string
  val typ : t -> [ `TyInt | `TyReal ]
  val compare : t -> t -> int
  val symbol_of : t -> symbol
  val of_symbol : symbol -> t option
end

module Make
    (C : sig
       type t
       val context : t context
     end)
    (Var : Var) : sig

  (** There are two components in the representation of a transition: its {i
      transform}and its {i guard}.  The transform maps each variable that is
      {i written} during the transition to a term over its input variables.
      The guard is a formula that describes the condition under which the
      transition may be executed.  The set of variables that appear in the
      transform or the guard are called the {i footprint} of the
      transition. *)
  type t

  type var = Var.t

      (** Test whether two transitions are equal up to logical equivalence and
      renaming skolem constants.  The input transitions must be normal in the
      sense that (1) the transform only assigns skolem constants to terms
      (e.g., we may have [x := x'] with guard [x' = x + 1], but may not have
      [x := x + 1]) and (2) every skolem constant that appears in the guard
      also appears in the transform. *)
  val equal : t -> t -> bool

  (** Compare is a purely syntactic comparison.  Two transitions [tr] and
      [tr'] can be equivalent ([equal tr tr' = true]) but have [compare tr tr'
      != 0]. *)
  val compare : t -> t -> int

  val pp : Format.formatter -> t -> unit
  val show : t -> string

  (** Guarded parallel assignment *)
  val construct : C.t formula -> (var * C.t term) list -> t

  (** [assume phi] is a transition that doesn't modify any variables, but can
      only be executed when [phi] holds *)
  val assume : C.t formula -> t

  (** [assign v t] is a transition that assigns the term [t] to the variable
      [v]. *)
  val assign : var -> C.t term -> t

  (** Parallel assignment of a list of terms to a list of variables.
     If a variable appears multiple times as a target for an
     assignment, the rightmost assignment is taken. *)
  val parallel_assign : (var * C.t term) list -> t

  (** Assign a list of variables non-deterministic values. *)
  val havoc : var list -> t

  (** Sequentially compose two transitions. *)
  val mul : t -> t -> t

  (** Non-deterministically choose between two transitions *)
  val add : t -> t -> t

  (** Unexecutable transition (unit of [add]). *)
  val zero : t

  (** Skip (unit of [mul]). *)
  val one : t

  (** Widen abstracts both input transitions to the Cube abstract
     domain, performs the Cube widening operator, and then converts
     back to a transition.  The resulting transition is normal in the
     sense described in [equal]. *)
  val widen : t -> t -> t

  (** [exists ex tr] removes the variables that do not satisfy the predicate
      [ex] from the footprint of a transition.  For example, projecting a
      variable [x] out of a transition [tr] is logically equivalent to
      [(exists x. tr) && x' = x]. *)
  val exists : (var -> bool) -> t -> t

  val is_zero : t -> bool
  val is_one : t -> bool

  (** Is a variable written to in a transition? *)
  val mem_transform : var -> t -> bool

  (** Retrieve the value of a variable after a transition as a term over input
      variables (and Skolem constants) *)
  val get_transform : var -> t -> C.t term

  (** Enumerate the variables and values assigned in a transition. *)
  val transform : t -> (var * C.t term) BatEnum.t

  (** The condition under which a transition may be executed. *)
  val guard : t -> C.t formula

  (** Given a path (list of transitions [tr_1 ... tr_n]) and a post-condition
      formula, determine whether the path implies the post-condition.  If yes,
      return a sequence of intermediate assertions [phi_1 ... phi_n] that
      support the proof (for each [i], [{ phi_{i-1} } tr_i { phi_i }] holds,
      where [phi_0] is [true] and [phi_n] implies the post-condition). *)

  val interpolate : t list -> C.t formula -> [ `Valid of C.t formula list
                                             | `Invalid
                                             | `Unknown ]

  (** Given a pre-condition [P], a path [path], and a post-condition [Q],
      determine whether the Hoare triple [{P}path{Q}] is valid. *)
  val valid_triple : C.t formula -> t list -> C.t formula -> [ `Valid
                                                             | `Invalid
                                                             | `Unknown ]

  val defines : t -> var list
  val uses : t -> var list

  val abstract_post : (C.t,'abs) SrkApron.property -> t -> (C.t,'abs) SrkApron.property

  (** Compute a representation of a transition as a transition formula. *)
  val to_transition_formula : t -> C.t TransitionFormula.t

  val domain : (module Iteration.PreDomain) ref
  val star : t -> t
  val linearize : t -> t
end

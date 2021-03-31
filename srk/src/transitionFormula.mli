(** Transition formulas *)

open Syntax

(** A transition formula is a logical formula that describes a binary
   relation on a set of states.  Transition formulas are assumed to be
   quantifier-free, and are over four sets of symbols: pre-state
   symbols, post-state symbols, symbolic constants, and Skolem
   constants.  Pre-state and post-state symbols are in 1-1
   correspondence and define the space on which the transition formula
   acts.  Symbolic constants are parameters that do not change during
   a computation; wheras Skolem constants do (and should be thought of
   as existentially quantified variables). *)
type 'a t

(** Construct a transition formula.  The [exists] predicate identifies
   Skolem constants ([exists s] fails if [s] is a Skolem constant),
   with the default behavior that no symbols are Skolem consntas; the
   list of symbol pairs identifies the pre-state and post-state
   variables.  The remaining symbols are symbolic constants. *)

val make : ?exists:(symbol -> bool) -> 'a formula -> (symbol * symbol) list -> 'a t

(** Identity relation *)
val identity : 'a context -> (symbol * symbol) list -> 'a t

(** Zero *)
val zero : 'a context -> (symbol * symbol) list -> 'a t

(** Sequential composition *)
val mul : 'a context -> 'a t -> 'a t -> 'a t

(** Union *)
val add : 'a context -> 'a t -> 'a t -> 'a t

(** Retrieve the underlying formula *)
val formula : 'a t -> 'a formula

(** Retrieve the pre-state/post-state symbols of a transition formula *)
val symbols : 'a t -> (symbol * symbol) list

(** Retrieve the predicate that identifies skolem constants *)
val exists : 'a t -> (symbol -> bool)

(** Retrieve a predicate that identifies symbolic constants *)
val is_symbolic_constant : 'a t -> symbol -> bool

(** Retrieve the set of symbolic constants that appear in the underyling formula *)
val symbolic_constants : 'a t -> Symbol.Set.t

(** Find a wedge over the pre-state, post-state, and constant symbols
   that over-approximates the underlying formula of a transition
   formula *)
val wedge_hull : 'a context -> 'a t -> 'a Wedge.t

(** Overapproxmate a transition formula by a linear arithmetic
   transition formula *)
val linearize : 'a context -> 'a t -> 'a t

(** Map pre-state symbols to their post-state counterparts *)
val pre_map : 'a context -> (symbol * symbol) list -> ('a term) Symbol.Map.t

(** Map post-state symbols to their pre-state counterparts *)
val post_map : 'a context -> (symbol * symbol) list -> ('a term) Symbol.Map.t

(** Retrieve the set of pre-state symbols *)
val pre_symbols : (symbol * symbol) list -> Symbol.Set.t

(** Retrieve the set of post-state symbols *)
val post_symbols : (symbol * symbol) list -> Symbol.Set.t

(** Apply a transformation to the formula, leaving existentially
   quantified variables and transition symbols fixed. *)
val map_formula : ('a Formula.t -> 'a Formula.t) -> 'a t -> 'a t

val preimage : 'a context -> 'a t -> 'a Formula.t -> 'a Formula.t

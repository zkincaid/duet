(** Formula and term simplification. *)
open Syntax

module RationalTerm : sig
  type 'a rt_context
  type 'a t
  val mk_context : 'a context -> 'a rt_context
  val of_term : 'a rt_context -> 'a arith_term -> 'a t
  val term_of : 'a rt_context -> 'a t -> 'a arith_term
end

val simplify_terms_rewriter : 'a context -> 'a rewriter

val simplify_terms : 'a context -> 'a formula -> 'a formula

val simplify_term : 'a context -> 'a arith_term -> 'a arith_term

(** Purify function applications in a ground formula: replace each function
    application within a formula with a fresh symbol, and return both the
    resulting formula and a mapping from the fresh symbols to the terms they
    define. *)
val purify : 'a context -> ('a,'b) expr -> (('a,'b) expr * (('a,typ_fo) expr) Symbol.Map.t)

val partition_implicant : ('a formula) list -> ('a formula) list list

(** Given a list of formulas [xs], find a sublist [xs'] such that the
   conjunction of all [xs] is equivalent to conjunction of all [xs'].
   The sublist [xs'] is not guaranteed to be minimal. *)
val simplify_conjunction : 'a context -> 'a formula list -> 'a formula list

(** Given a term [t] and a constant symbol [x], find a coefficient [a]
   and a term [s] such that [t] is equal to [a*x + s] ([a] may be 0).
   Return [None] if this is not possible (e.g., the term [x*x]). *)
val isolate_linear : 'a context -> symbol -> 'a arith_term -> (QQ.t * 'a arith_term) option

(** Formula simplification given in Isil Dillig, Thomas Dillig, Alex
   Aiken: "Small formulas for large programs: on-line constraint
   simplification in scalable static analysis", SAS 2010. *)
val simplify_dda : 'a context -> 'a formula -> 'a formula

(** Find an equivalent formula that does not use integer division by
   integer constants.  If [max] is provided, only eliminate integer
   division with a dominator less than [max]. *)
val eliminate_idiv : ?max:int -> 'a context -> 'a formula -> 'a formula

(** Purify floor functions in an expression: replace each function
   application within a formula with a fresh symbol, and return both
   the resulting formula [phi] and a mapping [f] from the fresh
   symbols to terms, so that if we substitute each symbol [s] in the
   domain of [f] with [floor (f s)], we get the original formula *)
val purify_floor : 'a context ->
                   ('a,'b) expr ->
                   (('a,'b) expr * (('a,typ_arith) expr) Symbol.Map.t)

(** Eliminate floor functions in a formula.  The formula is equivalent
   to the original, modulo the fresh symbols introduced in floor
   purification. *)
val eliminate_floor : 'a context -> 'a formula -> 'a formula

(** Simplify an atomic formula that consists of a binary operation of integers. *)
val simplify_integer_atom : 'a context -> [`Eq | `Leq | `Lt ] -> 'a arith_term -> 'a arith_term ->
   [ `CompareZero of [ `Eq | `Leq | `Lt ] * Linear.QQVector.t
      | `Divides of ZZ.t * Linear.QQVector.t
      | `NotDivides of ZZ.t * Linear.QQVector.t ]

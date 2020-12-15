(** Formula and term simplification. *)
open Syntax

module RationalTerm : sig
  type 'a rt_context
  type 'a t
  val mk_context : 'a context -> 'a rt_context
  val of_term : 'a rt_context -> 'a term -> 'a t
  val term_of : 'a rt_context -> 'a t -> 'a term
end

val simplify_terms_rewriter : 'a context -> 'a rewriter

val simplify_terms : 'a context -> 'a formula -> 'a formula

val simplify_term : 'a context -> 'a term -> 'a term

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
val isolate_linear : 'a context -> symbol -> 'a term -> (QQ.t * 'a term) option

(** Formula simplification given in Isil Dillig, Thomas Dillig, Alex
   Aiken: "Small formulas for large programs: on-line constraint
   simplification in scalable static analysis", SAS 2010. *)
val simplify_dda : 'a context -> 'a formula -> 'a formula

(** Purify floors in a formula by converting them to ite expressions then 
   eliminating the ite expressions. *)
val purify_floor : 'a context -> 'a formula -> 'a formula

(** Simplify an atomic formula that consists of a binary operation of integers. *)
val simplify_integer_atom : 'a context -> [`Eq | `Leq | `Lt ] -> 'a term -> 'a term ->
   [ `CompareZero of [ `Eq | `Leq | `Lt ] * Linear.QQVector.t
      | `Divides of ZZ.t * Linear.QQVector.t
      | `NotDivides of ZZ.t * Linear.QQVector.t ]
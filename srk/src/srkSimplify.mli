(** Formula and term simplification. *)
open Syntax

module TermPolynomial : sig
  type 'a polynomial_context
  type 'a t
  val mk_context : 'a context -> 'a polynomial_context
  val of_term : 'a polynomial_context -> 'a term -> 'a t
  val term_of : 'a polynomial_context -> 'a t -> 'a term
end

val simplify_terms_rewriter : 'a context -> 'a rewriter

val simplify_terms : 'a context -> 'a formula -> 'a formula

val simplify_term : 'a context -> 'a term -> 'a term

(** Purify function applications in a ground formula: replace each function
    application within a formula with a fresh symbol, and return both the
    resulting formula and a mapping from the fresh symbols to the terms they
    define. *)
val purify : 'a context -> 'a formula -> ('a formula * (('a,typ_fo) expr) Symbol.Map.t)

val partition_implicant : ('a formula) list -> ('a formula) list list

(** Given a list of formulas [xs], find a sublist [xs'] such that the
   conjunction of all [xs] is equivalent to conjunction of all [xs'].
   The sublist [xs'] is not guaranteed to be minimal. *)
val simplify_conjunction : 'a context -> 'a formula list -> 'a formula list

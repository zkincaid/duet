open Syntax

module TermPolynomial : sig
  type 'a polynomial_context
  type 'a t
  val mk_context : 'a context -> 'a polynomial_context
  val of_term : 'a polynomial_context -> 'a term -> 'a t
  val term_of : 'a polynomial_context -> 'a t -> 'a term
end

val simplify_terms_rewriter : 'a context -> 'a rewriter
val simplify_terms : 'a context -> ('a,'b) expr -> ('a,'b) expr

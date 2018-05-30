(** Operations on exponential polynomials. Exponential-polynomials are
   expressions of the form [E ::= x | lambda | lambda^x | E*E | E+E]
   where [lambda] is a rational *)
open Syntax

type t

val pp : Format.formatter -> t -> unit
val show : t -> string

val equal : t -> t -> bool

val add : t -> t -> t
val mul : t -> t -> t

val negate : t -> t

val zero : t
val one : t

val of_polynomial : Polynomial.QQX.t -> t

val of_exponential : QQ.t -> t

val scalar : QQ.t -> t

val scalar_mul : QQ.t -> t -> t

(** [compose_left_affine f a b] computes the function [lambda x. f (ax + b)] *)
val compose_left_affine : t -> int -> int -> t

(** [summation f] computes an exponential-polynomial [g] such that [g(n) = sum_{i=0}^n f(i)]. *)
val summation : t -> t

(** [solve_rec lambda g] computes an exponential-polynomial [g] such that
    {ul
      {- g(0) = f(0) }
      {- g(n) = lambda*g(n-1) + f(n) }} *)
val solve_rec : QQ.t -> t -> t

(** [term_of srk t f] computes a term representing [f(t)]. *)
val term_of : ('a context) -> 'a term -> t -> 'a term

val eval : t -> int -> QQ.t

val enum : t -> (Polynomial.QQX.t * QQ.t) BatEnum.t
val add_term : Polynomial.QQX.t -> QQ.t -> t -> t
val of_term : Polynomial.QQX.t -> QQ.t -> t

module UltPeriodic : sig
  type elt = t
  type t
  val equal : t -> t -> bool
  val add : t -> t -> t
  val negate : t -> t
  val zero : t
  val mul : t -> t -> t
  val one : t

  val pp : Format.formatter -> t -> unit
  val show : t -> string

  (** [make t p] constructs an ultimately periodic sequence *)
  val make : elt list -> elt list -> t

  (** Retrieve the transient part of a sequence *)
  val transient : t -> elt list

  (** Retrieve the periodic part of a sequence *)
  val periodic : t -> elt list

  (** Enumerate the sequence. *)
  val enum : t -> elt BatEnum.t

  val period_len : t -> int
  val transient_len : t -> int

  (** Given an ultimately periodic sequence [f1 f2 f3 ...] compute the
      sequence [lambda n. sum_{i=1}^n fi(i)]. *)
  val summation : t -> t

  val solve_rec : QQ.t -> t -> t
end

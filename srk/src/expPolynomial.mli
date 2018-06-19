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

(** [solve_rec ?initial lambda g] computes an exponential-polynomial [g] such that
    {ul
      {- g(0) = initial }
      {- g(n+1) = lambda*g(n) + f(n) }}.
    If the initial value is omitted, it is taken to be 0. *)
val solve_rec : ?initial:QQ.t -> QQ.t -> t -> t

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
  val make : QQ.t list -> elt list -> t

  (** Retrieve the transient part of a sequence *)
  val transient : t -> QQ.t list

  (** Retrieve the periodic part of a sequence *)
  val periodic : t -> elt list

  (** Enumerate the sequence. *)
  val enum : t -> QQ.t BatEnum.t

  val eval : t -> int -> QQ.t
  val period_len : t -> int
  val transient_len : t -> int

  (** Given a function f, compute the function [lambda n. sum_{i=0}^n f(i) *)
  val summation : t -> t

  (** [solve_rec ?initial coeff f] computes the function [g] that satisfies
        g(0) = initial
        g(n+1) = coeff*g_{n}(n) + f_n(n)
      If initial is omitted, it is taken to be 0.
  *)
  val solve_rec : ?initial:QQ.t -> QQ.t -> t -> t

  (** [term_of srk q r f] computes a term representing [f(qp + r)],
      where [p] is the period of [f]. *)
  val term_of : 'a context -> 'a term -> 'a term -> t -> 'a term

  val scalar : QQ.t -> t
  val of_polynomial : Polynomial.QQX.t -> t
  val of_exponential : QQ.t -> t
  val of_exp_polynomial : elt -> t

  (** [compose_left_affine f a b] computes an ultimately periodic function g such that for all k
       [g_i(i) = f_{ai+b}(ai+b)] *)
  val compose_left_affine : t -> int -> int -> t

  (** [flatten f_0 ... f_{p-1}] computes a function [g] such that [g(qp + r) = f_r(q)] *)
  val flatten : t list -> t

  (** [flatten [t_0, ..., t_{n-1}] f] computes a function [g] such
     that [g(i) = t_i] for i < n and [g(i) = f(i-n)] otherwise.  If we
     imagine f as an infinite sequenc [f_0 f_1 f_2 ...], then [g] is
     the sequence [t_0, ..., t_{n-1}, f_0, f_1, f_2, ...]. *)
  val shift : QQ.t list -> t -> t
end

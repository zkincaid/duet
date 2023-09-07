(** Operations on exponential polynomials. Exponential-polynomials are
   expressions of the form [E ::= x | lambda | lambda^x | E*E | E+E]
   where [lambda] is a rational *)
open Syntax

module MakeEP
  (B : sig 
    include Algebra.Ring 
    val compare : t -> t -> int 
    val exp : t -> int -> t 
    val pp : Format.formatter -> t -> unit
  end)
  (C : sig
    include Algebra.Ring
    val lift : B.t -> t
    val int_mul : int -> t -> t
  end)
  (CX : sig
    include Polynomial.Univariate with type scalar = C.t
    val pp : Format.formatter -> t -> unit
  end) : sig
  type t

  val pp : Format.formatter -> t -> unit
  val show : t -> string

  val equal : t -> t -> bool

  val add : t -> t -> t
  val mul : t -> t -> t

  val negate : t -> t

  val zero : t
  val one : t

  val of_polynomial : CX.t -> t

  val of_exponential : B.t -> t

  val scalar : C.t -> t

  val scalar_mul : C.t -> t -> t

  val eval : t -> int -> C.t

  val enum : t -> (CX.t * B.t) BatEnum.t

end

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

val eval : t -> int -> QQ.t

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
val term_of : ('a context) -> 'a arith_term -> t -> 'a arith_term



val enum : t -> (Polynomial.QQX.t * QQ.t) BatEnum.t
val add_term : Polynomial.QQX.t -> QQ.t -> t -> t
val of_term : Polynomial.QQX.t -> QQ.t -> t

(** Vectors with exponential-polynomial entries *)
module Vector : sig
  include Ring.Vector with type scalar = t
                       and type dim = int
  val of_qqvector : Linear.QQVector.t -> t
end

(** Matrices with exponential-polynomial entries *)
module Matrix : sig
  include Ring.Matrix with type scalar = t
                       and type vector = Vector.t
                       and type dim = int
  val pp : Format.formatter -> t -> unit
  val of_qqmatrix : Linear.QQMatrix.t -> t
end

(** Symbolically exponentiate a matrix with rational eigenvalues.
   None indicates the matrix has irrational eigenvalues.  *)
val exponentiate_rational : Linear.QQMatrix.t -> Matrix.t option

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

  (** Given a function f, compute the function [lambda n. sum_{i=0}^n f(i)] *)
  val summation : t -> t

  (** [solve_rec ?initial coeff f] computes the function [g] that satisfies
      {ul
       {- [g(0) = initial] }
       {- [g(n+1) = coeff*g(n) + f_n(n)] }}.

      If initial is omitted, it is taken to be 0.
  *)
  val solve_rec : ?initial:QQ.t -> QQ.t -> t -> t

  (** [term_of srk q r f] computes a term representing [f(qp + r)],
      where [p] is the period of [f]. *)
  val term_of : 'a context -> 'a arith_term -> 'a arith_term -> t -> 'a arith_term

  val scalar : QQ.t -> t
  val of_polynomial : Polynomial.QQX.t -> t
  val of_exponential : QQ.t -> t
  val of_exp_polynomial : elt -> t

  (** [compose_left_affine f a b] computes an ultimately periodic function g such that for all k
       [g_i(i) = f_{ai+b}(ai+b)] *)
  val compose_left_affine : t -> int -> int -> t

  (** [flatten f_0 ... f_{p-1}] computes a function [g] such that [g(qp + r) = f_r(q)] *)
  val flatten : t list -> t

  (** [shift [t_0, ..., t_{n-1}] f] computes a function [g] such
     that [g(i) = t_i] for i < n and [g(i) = f(i-n)] otherwise.  If we
     imagine f as an infinite sequence [f_0 f_1 f_2 ...], then [g] is
     the sequence [t_0, ..., t_{n-1}, f_0, f_1, f_2, ...]. *)
  val shift : QQ.t list -> t -> t
end

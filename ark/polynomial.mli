module type Univariate = sig
  include Linear.Vector with type dim = int
  val order : t -> int
  val mul : t -> t -> t
  val one : t
  val scalar : scalar -> t
  val compose : t -> t -> t

  (** The polynomial [p(x) = x] *)
  val identity : t

  val eval : t -> scalar -> scalar

  (** Exponentiation *)
  val exp : t -> int -> t
end

module Uvp (R : Linear.Ring) : Univariate with type scalar = R.t

(** Univariate polynomials with rational coefficients *)
module QQUvp : sig
  include Univariate with type scalar = QQ.t

  val pp : Format.formatter -> t -> unit
  val show : t -> string

  (** Given a polynomial [p(x)], compute a polynomial [q(x)] such that that
      for every integer [x >= 0], we have [q(x) = sum_{i=0}^x p(i)]. *)
  val summation : t -> t
end

module Monomial : sig
  type t
  type dim = int

  val mul : t -> t -> t
  val one : t
  val mul_term : dim -> int -> t -> t
  val singleton : dim -> int -> t
  val power : dim -> t -> int
  val enum : t -> (dim * int) BatEnum.t
  val of_enum : (dim * int) BatEnum.t -> t
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val pivot : dim -> t -> (int * t)
end

(** Multi-variate polynomial *)
module Mvp : sig
  include Linear.Vector with type dim = Monomial.t
                         and type scalar = QQ.t
  val mul : t -> t -> t
  val one : t
  val scalar : QQ.t -> t
  val of_dim : Monomial.dim -> t
end

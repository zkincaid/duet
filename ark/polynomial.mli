module type Univariate = sig
  include Linear.Vector with type dim = int
  val order : t -> int
  val mul : t -> t -> t
  val one : t
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

type t

val pp : Format.formatter -> t -> unit
val show : t -> string

val equal : t -> t -> bool

val add : t -> t -> t
val mul : t -> t -> t

val negate : t -> t

val zero : t
val one : t

val summation : t -> t

val of_polynomial : Polynomial.QQX.t -> t
val of_exponential : QQ.t -> t
val scalar : QQ.t -> t

(** [compose_left_affine f a b] computes the function [lambda x. f (ax + b)] *)
val compose_left_affine : t -> int -> int -> t

(** [solve_rec lambda g] computes an exponential-polynomial g(n) such that
    g(0) = f(0)
    g(n) = lambda*g(n-1) + f(n)
*)
val solve_rec : QQ.t -> t -> t

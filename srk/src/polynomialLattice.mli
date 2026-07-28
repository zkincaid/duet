open Polynomial

(** A polynomial lattice L is of the form QQ[X] Z + ZZ B,
    where Z is an ideal and B is a basis (i.e., linearly independent set).
    When B is the empty set, ZZ B = {0}, and similarly for QQ[X] Z.
*)
type t

val make_lattice : Rewrite.t -> QQXs.t list -> t

val member : QQXs.t -> t -> bool

val change_monomial_ordering :
  t -> (Monomial.t -> Monomial.t -> [ `Eq | `Lt | `Gt  ]) -> t

(** Compute the sum of two polynomial lattices. Monomial order may change. *)
val sum : t -> t -> t

(** Compute the intersection of two polynomial lattices. Monomial order may change. *)
val intersect : t -> t -> t

val subset : t -> t -> bool

val equal : t -> t -> bool

(** Intersect the lattice with the space of polynomials over monomials satisfying
    the given predicate.  Assumes that the set of monomials satisfying the given
    predicate is downwards-closed w.r.t. the monomial ordering of the lattice. *)
val restrict : (Monomial.t -> bool) -> t -> t

val pp : (Format.formatter -> int -> unit)
  -> Format.formatter -> t -> unit

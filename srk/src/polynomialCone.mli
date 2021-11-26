open Polynomial
open Syntax

type t

val pp :  (Format.formatter -> int -> unit) -> Format.formatter -> t -> unit

val intersection : t -> t -> t

(* int refers to dimensions
   already implemented polyhedron of a cone (wrt to the monomials as dimensions),
   project out the dimensions that correspond to
   monomials with variables we don't want, and take the generators of the
   resulting cone is the projection.
 *)
val project : t -> (int -> bool) -> t

val get_ideal : t -> Rewrite.t

val get_cone_generators : t -> (QQXs.t BatList.t)

val change_monomial_ordering: t ->
  (Monomial.t -> Monomial.t -> [ `Eq | `Lt | `Gt  ]) -> t

(* Making a minimal salient polynomial cone. *)
val trivial : t

(* Compute the smallest cone that contains the ideal and a given set of nonnegative polynomials. *)
val make_enclosing_cone : Polynomial.Rewrite.t -> QQXs.t BatList.t -> t

(* Adding a list of zero polynomials and a list of nonnegative polynomials to an existing cone. *)
val add_polys_to_cone : t -> QQXs.t BatList.t -> QQXs.t BatList.t -> t

(* This does not belong here in this interface *)
(* val mk_nonnegative_cone_of_tf : ('a TransitionFormula.t -> t) *)

(* Test if a polynomial is contained in the cone. *)
val mem : QQXs.t -> t -> bool

(* Does -1 belong to this cone? If yes then all polynomials belong to the cone thus
   it will no longer be consistent. *)
val is_proper: t -> bool

(* ideals must be the same, rewrite to the same monomial ordering and test
   if cone are the same
   or use the membership testing on the generators
 *)
val equal: t -> t -> bool

val to_formula : 'a context -> (int -> 'a arith_term) -> t -> 'a formula

(* To get a fresh symbol for elimination https://github.com/zkincaid/duet/blob/modern/srk/src/polynomial.ml#L989 *)
(* Consider using the dual space, polyhedron.ml to do the Farkas lemma stuff *)

(* another module that takes in CoordinateSystem and compute polynomial cones for formulas *)

(** Cutting plane closure of polynomial cones, defined per the weak theory
    of arithmetic.
*)

(** [regular_cutting_plane_closure lattice cone]
    computes the smallest regular polynomial cone that contains [cone] and
    is closed under CP-INEQ with respect to the lattice L spanned by
    [lattice] AND (the polynomial) 1.

    A polynomial cone C is closed under CP-INEQ if for all f in L,
    integers n, m with n > 0,
    whenever nf + m is in C, f + floor(m/n) is in C.
    It is regular if C \cap (-C) is an ideal.

    Models of the theory are polynomial cones C that are consistent
    (the ideal is proper), regular,
    closed under CP-INEQ, and closed under CP-EQ (not done here).
 *)
val regular_cutting_plane_closure :
  Polynomial.QQXs.t list -> PolynomialCone.t -> PolynomialCone.t

(** Raised if there is a non-integral rational in the lattice.
    E.g., If 1/2 is in the lattice, 2 (1/2) + (-1) >= 0
    implies 1/2 + floor(-1/2) >= 0, which implies -1/2 >= 0.
 *)
exception Invalid_lattice

(* Export temporarily for testing *)

open Polynomial
open PolynomialUtil

(** Denominator, and the basis polynomials not equal to 1 (1 is implicit) *)
type polylattice = ZZ.t * QQXs.t * QQXs.t list

val polylattice_spanned_by : QQXs.t list -> polylattice

type transformation_data =
  { codomain_dims: Monomial.dim * Monomial.dim list
  ; substitutions: (Monomial.dim -> QQXs.t) * (Monomial.dim -> QQXs.t)
  ; rewrite_polys: QQXs.t * QQXs.t list
  }

val pp_transformation_data : (Format.formatter -> int -> unit)
                             -> Format.formatter -> transformation_data -> unit

val compute_transformation : polylattice -> PolyVectorContext.t -> transformation_data

val compute_cut : transformation_data -> PolynomialCone.t -> (QQXs.t list * QQXs.t list)

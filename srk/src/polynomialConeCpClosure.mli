open Polynomial

(** Cutting plane closure of polynomial cones, defined per the weak theory
    of arithmetic.
*)

type polylattice

(** [polylattice_spanned_by polys] is the lattice spanned by [polys]
    AND the polynomial 1.
 *)
val polylattice_spanned_by : QQXs.t list -> polylattice

(** [regular_cutting_plane_closure lattice cone]
    computes the smallest regular polynomial cone that contains [cone] and
    is closed under CP-INEQ with respect to [lattice].

    A polynomial cone C is closed under CP-INEQ w.r.t. L
    if for all f in L, integers n, m with n > 0,
    whenever nf + m is in C, f + floor(m/n) is in C.
    It is regular if C \cap (-C) is an ideal.

    Models of the theory are polynomial cones C that are consistent
    (the ideal is proper), regular,
    closed under CP-INEQ, and closed under CP-EQ (not done here).
 *)
val regular_cutting_plane_closure :
  polylattice -> PolynomialCone.t -> PolynomialCone.t

(** Raised if there is a non-integral rational in the lattice.
    E.g., If 1/2 is in the lattice, 2 (1/2) + (-1) >= 0
    implies 1/2 + floor(-1/2) >= 0, which implies -1/2 >= 0.
 *)
exception Invalid_lattice

(* Export temporarily for testing *)

open Polynomial
open PolynomialUtil

type transformation_data =
  { codomain_dims: Monomial.dim * Monomial.dim list
  ; substitutions: (Monomial.dim -> QQXs.t) * (Monomial.dim -> QQXs.t)
  ; rewrite_polys: QQXs.t * QQXs.t list
  }

val pp_transformation_data : (Format.formatter -> int -> unit)
                             -> Format.formatter -> transformation_data -> unit

val compute_transformation : polylattice -> PolyVectorContext.t -> transformation_data

val compute_cut : transformation_data -> PolynomialCone.t -> (QQXs.t list * QQXs.t list)

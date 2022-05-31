open Polynomial

(** Cutting plane closure of polynomial cones, defined per the weak theory
    of arithmetic.
*)

(** A polynomial lattice L is of the form I + ZZ B,
    where I is an ideal and B is a finite set of polynomials that include 1
    and are reduced with respect to I.
*)
type polylattice

val affine_generators : polylattice -> QQXs.t list

val ideal_of : polylattice -> Rewrite.t

val in_polylattice : QQXs.t -> polylattice -> bool

val pp_polylattice : (Format.formatter -> int -> unit)
                     -> Format.formatter -> polylattice -> unit

(** [regular_cutting_plane_closure cone lattice]
    computes a coherent (C, L) such that C is the smallest
    regular polynomial cone that contains [cone] and is
    closed under CP-INEQ with respect to [lattice].
    L is (C \cap -C) + [lattice].
 *)
val regular_cutting_plane_closure :
  PolynomialCone.t -> QQXs.t list -> PolynomialCone.t * polylattice

(* Export temporarily for testing *)

(*
open Polynomial
open PolynomialUtil

type transformation_data =
  { codomain_dims: Monomial.dim * Monomial.dim list
  ; substitutions: (Monomial.dim -> QQXs.t) * (Monomial.dim -> QQXs.t)
  ; rewrite_polys: QQXs.t * QQXs.t list
  }

val pp_transformation_data : (Format.formatter -> int -> unit)
                             -> Format.formatter -> transformation_data -> unit

val compute_transformation : QQXs.t list -> PolyVectorContext.t -> transformation_data

val compute_cut : transformation_data -> PolynomialCone.t -> (QQXs.t list * QQXs.t list)
 *)

(** Cutting plane closure of polynomial cones, defined per the weak theory
    of arithmetic.
*)

(** [cutting_plane_closure lattice cone]
    computes the cutting plane closure of the polynomial cone [cone] with
    respect to the lattice spanned by [lattice] AND (the polynomial) 1.
 *)
val cutting_plane_closure :
  Polynomial.QQXs.t list -> PolynomialCone.t -> PolynomialCone.t

(* Export temporarily for testing *)

open Polynomial
open PolynomialUtil

(** Denominator, and the basis polynomials not equal to 1 (1 is implicit) *)
type polylattice = ZZ.t * QQXs.t * QQXs.t list
  
val lattice_spanned_by : QQXs.t list -> polylattice

type transformation_data

val pp_transformation_data : (Format.formatter -> int -> unit)
                             -> Format.formatter -> transformation_data -> unit

val compute_transformation : polylattice -> PolyVectorContext.t -> transformation_data

val compute_cut : PolyVectorContext.t -> transformation_data ->
                  QQXs.t list -> QQXs.t list -> (QQXs.t list * QQXs.t list)

                                          

                                 
                                   

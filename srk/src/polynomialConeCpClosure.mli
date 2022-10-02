open Polynomial

(** Cutting plane closure of polynomial cones, defined per the weak theory
    of arithmetic.
*)

val set_cutting_plane_method : [`GomoryChvatal | `Normaliz] -> unit

(** [regular_cutting_plane_closure cone affine_lattice]
    computes a coherent (C, L) such that C is the smallest
    regular polynomial cone that contains [cone] and is
    closed under CP-INEQ with respect to L or [affine_lattice \cup {1}],
    where L is (C \cap -C) + [affine_lattice \cup {1}].
    (The closures w.r.t. L or (affine_lattice \cup {1}) are equal.)
 *)
val regular_cutting_plane_closure :
  PolynomialCone.t -> QQXs.t list -> PolynomialCone.t * PolynomialLattice.t

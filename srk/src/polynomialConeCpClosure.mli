(** Cutting plane closure of polynomial cones, defined per the weak theory
    of arithmetic.
*)

(** [cutting_plane_closure lattice cone]
    computes the cutting plane closure of the polynomial cone [cone] with
    respect to the lattice spanned by [lattice] AND (the polynomial) 1.
 *)
val cutting_plane_closure :
  Polynomial.QQXs.t list -> PolynomialCone.t -> PolynomialCone.t

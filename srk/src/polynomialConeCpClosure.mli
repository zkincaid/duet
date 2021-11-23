(** Cutting plane closure of polynomial cones, defined per the weak theory
    of arithmetic.
*)

type lattice

(** Compute lattice spanned by given polynomials AND the constant polynomial 1. *)
val lattice_spanned_by : Polynomial.QQXs.t list -> lattice

val cutting_plane_closure : ?verbose:bool -> lattice -> PolynomialCone.t -> PolynomialCone.t

val pp : (Format.formatter -> int -> unit) -> Format.formatter -> lattice -> unit


(** Temporarily export for testing *)

type transformation_data

val compute_transformation : ?verbose:bool -> lattice
  -> Polynomial.Monomial.t list -> transformation_data

val pp_transformation_data : (Format.formatter -> int -> unit)
  -> Format.formatter -> transformation_data -> unit

val rewrite_with_linear_map : ?verbose:bool -> lattice -> PolynomialCone.t
  -> transformation_data * Polynomial.QQXs.t list * Polynomial.QQXs.t list

(** Temporarily export for testing purposes *)
module PolyhedralCone : sig
  type polycone
  type lattice

  val empty_polycone : polycone

  val add_conic_gens : polycone -> Mpzf.t list list -> polycone

  (** Add QQ-linear generators (two-sided generators) to the cone *)
  val add_linear_gens : polycone -> Mpzf.t list list -> polycone

  val empty_lattice : lattice

  val add_lattice_gens : lattice -> Mpzf.t list list -> lattice

  val get_conic_gens : polycone -> Mpzf.t list list

  val get_linear_gens : polycone -> Mpzf.t list list

  (** Row-hermite normal form *)
  val get_hermitized_lattice_basis : lattice -> Mpzf.t list list

  val get_lattice_dim : lattice -> int

  val intersect_cones : polycone -> polycone -> polycone

  (** Given
      (1) generators C for a polyhedral cone containing some rational r in QQ, and
      (2) a basis B consisting of vectors of the form r e_i for some r in QQ
          and standard vector e_i (a monomial), for a lattice containing 1,
      such that both sets reside within some R^d,
      compute cl_{ZZ B'} (QQ C \cap QQ B),
      where B' = {e_i : r e_i in B for some r in QQ}.

      See Corollary 4.2 (or thereabouts).
      Conditions 1 and 2 are needed for integer hull computation to coincide with
      the CP-closure.
  *)
  val standard_cutting_plane: ?verbose:bool -> ?asserts:bool
    -> polycone -> lattice -> polycone

  (** Given polyhedral cone generators C and a lattice basis B,
      both containing 1 in QQ, compute cl_{ZZ B}(QQ C).
  *)
  val cutting_plane_closure : ?verbose:bool -> ?asserts:bool
    -> polycone -> lattice -> polycone

  val pp_polycone : Format.formatter -> polycone -> unit

  val pp_lattice : Format.formatter -> lattice -> unit

end

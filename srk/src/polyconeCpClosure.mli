(** Cutting plane closure of polynomial cones, defined per the weak theory
    of arithmetic.

    A polynomial cone C is represented by its set of (QQ-conic + QQ-linear) 
    generators, given in the form of vectors of type Mpz list list.
    The components of these vectors correspond to some fixed monomial order,
    and are such that the constant term must be in the first position.

    A lattice L is likewise represented by its set of ZZ-linear generators
    given in vector form, presented according to the same monomial order
    as that for the cone, with constant terms appearing in the first position.

    Given (C, L), [cutting_plane_closure C L] computes the cutting plane closure
    of C with respect to L.
*)

type polycone
type lattice

(** Create an empty polynomial cone *)
val empty_polycone : polycone

(** Add QQ-conic generators to the cone *)
val add_conic_gens : polycone -> Mpzf.t list list -> (polycone, string) result

(** Add QQ-linear generators (two-sided generators) to the cone *)
val add_linear_gens : polycone -> Mpzf.t list list -> (polycone, string) result

(** Create an empty lattice *)
val empty_lattice : lattice

(** Add ZZ-linear generators to a lattice *)
val add_lattice_gens : lattice -> Mpzf.t list list -> (lattice, string) result

(** Get the conic generators of a cone *)
val get_conic_gens : polycone -> Mpzf.t list list

(** Get the conic generators of a cone *)
val get_linear_gens : polycone -> Mpzf.t list list

val get_lattice_gens : lattice -> Mpzf.t list list

val pp_polycone : Format.formatter -> polycone -> unit

val pp_lattice : Format.formatter -> lattice -> unit

(** Given
    (1) generators C for a cone containing some rational r in QQ, and
    (2) a basis B consisting of vectors of the form r e_i for some r in QQ
        and standard vector e_i (a monomial), for a lattice containing 1,
    such that both sets reside within some R^d,
    compute cl_{ZZ B'} (QQ C \cap QQ B),
    where B' = {e_i : r e_i in B for some r in QQ}.

    This is only in the interface for testing purposes.
*)
val standard_cutting_plane : ?verbose:bool -> ?asserts:bool
  -> polycone -> lattice -> (polycone, string) result

(** Given cone generators C and a lattice basis B, both containing 1 in QQ,
    compute cl_{ZZ B}(QQ C).
*)
val cutting_plane_closure : ?verbose:bool -> ?asserts:bool ->
  polycone -> lattice -> (polycone, string) result

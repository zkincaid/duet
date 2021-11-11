(** Some utility functions for polynomials *)

open Polynomial

(** A polynomial-vector context is a bijective map between a set of monomials
    and the dimensions of the vector space spanned by that set of monomials.
*)
module PolyVectorContext : sig

  type t

  (** Raised when a monomial-dimension association cannot be found *)
  exception Not_in_context

  (** Monomials are assigned dimensions (integer indices) according to the
      monomial order given, with smallest dimension given to the smallest monomial
      if [increasing] is true, and smallest dimension given to the largest monomial
      if [increasing] is false. Monomials in the list do not have to be unique.
  *)
  val context: ?increasing:bool
    -> (Monomial.t -> Monomial.t -> [`Eq | `Lt | `Gt ])
    -> Monomial.t list -> t

  val dim_of : Monomial.t -> t -> Monomial.dim

  val monomial_of : Monomial.dim -> t -> Monomial.t

  val num_dimensions : t -> int

  val max_dimension : t -> int

  (** Fold over context in increasing order of dimension *)
  val fold_over_dimensions: (Monomial.dim -> Monomial.t -> 'a -> 'a) -> t -> 'a -> 'a

  val pp : (Format.formatter -> int -> unit) -> Format.formatter -> t -> unit

  (*
  val reorder : t
    -> ?increasing: bool
    -> (Monomial.t -> Monomial.t -> [`Eq | `Lt | `Gt ])
    -> t
  *)

end

module PolyVectorConversion : sig

  (** Project polynomial into the vector space spanned by monomials in the context *)
  val rational_poly_to_vector : PolyVectorContext.t -> QQXs.t -> Linear.QQVector.t

  (** Project polynomial into the vector space spanned by monomials in the context *)
  val rational_poly_to_scalars : PolyVectorContext.t -> QQXs.t -> Mpqf.t list

  (** Recover polynomial from its representation as a vector in the context *)
  val scalars_to_rational_poly : PolyVectorContext.t -> Mpqf.t list -> QQXs.t

end

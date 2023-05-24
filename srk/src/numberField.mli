open Polynomial

(** Given a univariate polynomial, and a variable dimension, create an
    equivalent multivariate polynomial using the given dimension.*)
val make_multivariate : Monomial.dim -> QQX.t -> QQXs.t

(** Given a multivariate polynomial over a single dimension, create an
    equivalent univariate polynomial.
    @raise Failure if input is not a univariate polynomial.*)
val make_univariate : QQXs.t -> QQX.t

(** Let K1 = Q[v0,v1]/p and K2=Q[v0,v1]/q be number fields. 
    [prim, v0_in_prim, v1_in_prim] = [primitive_elem p q v0 v1] 
    is such that the number field K3 = Q[x]/prim such that K3 is the smallest
    field that contains K1 and K2. [v0_in_prim] and [v1_in_prim] give the 
    representations of v0 and v1 in K3 respectively.*)
val primitive_elem : QQXs.t -> QQXs.t -> Monomial.dim -> Monomial.dim -> QQX.t * QQX.t * QQX.t

(** Given a minimal polynomial, construct a number field. Giving a
    polynomial that is not irreducible in Q[x] gives undefined behavior.*)
module MakeNF (A : sig val min_poly : QQX.t end) : sig
  
  (** The type of elements of the number field. *)
  type elem

  (** The degree of the extension.*)
  val deg : int

  (** Converts a univariate polynomial to an element of the number field.*)
  val make_elem : QQX.t -> elem

  val mul : elem -> elem -> elem

  val add : elem -> elem -> elem

  val sub : elem -> elem -> elem

  val inverse : elem -> elem

  val exp : elem -> int -> elem

  val equal : elem -> elem -> bool

  val is_zero : elem -> bool

  val one : elem

  val zero : elem

  val negate : elem -> elem

  val pp : Format.formatter -> elem -> unit

  (** Univariate polynomials over the number field*)
  module X : 
    sig
      include Euclidean with type scalar = elem
  
      (** Pretty printer. The field variable is z and the polynomial variable is x.*)
      val pp : Format.formatter -> t -> unit

      (** Convert a rational polynomial to a polynomial in the number field*)
      val lift : QQX.t -> t

      (** Convert a polynomial in the number field to a multivariate polynomial.
          The field variable is 0, and the polynomial variable is 1.*)
      val de_lift : t -> QQXs.t

      (** Factors a square free polynomial in the number field.*)
      val factor_square_free_poly : t -> (scalar * ((t * int) list))

      (** Factors an arbitrary polynomial in the number field.*)
      val factor : t -> (scalar * ((t * int) list))

      (** Extract the root of a linear polynomial
          @raise Failure if the input is not linear*)
      val extract_root_from_linear : t -> elem
    end

  module O : Order.Order

end

(** [min_poly, roots] = [splitting_field p] is such that Q[x]/min_poly is the
    splitting field of [p]. [roots] give the representation of the roots along with
    their multiplicity of [p] in the splitting field.*)
val splitting_field : QQX.t -> QQX.t * ((QQX.t * int) list)

  



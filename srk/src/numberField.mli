open Polynomial

(** Given a univariate polynomial, and a variable dimension, create an
    equivalent multivariate polynomial using the given dimension.*)
val make_multivariate : Monomial.dim -> QQX.t -> QQXs.t

(** Given a multivariate polynomial over a single dimension, create an
    equivalent univariate polynomial.
    @raise Failure if input is not a univariate polynomial.*)
val make_univariate : QQXs.t -> QQX.t

(** Let K1 = Q\[v0\]/p(v0) and K2=K1\[v1\]/q(v1) with p in Q\[v0\] and q in Q\[v0, v1\]. K2 can be 
    represented by Q\[v0, v1\]/<p, q>. Let K1 have degree d1 over Q and K2 have degree d2 over K1.
    [prim, v0_in_prim, v1_in_prim] = [primitive_elem (d1*d2) p q v0 v1] is such that K2 is isomporphic
    to Q\[x\]/<prim>. v0_in_prim and v1_in_prim give the images of the elements v0 + <p, q> and
    v1 + <p, q> under the isomorphism from K2 = Q\[v0, v1\]/<p, q> to Q\[x\]/<prim>.*)
val primitive_elem : int -> QQXs.t -> QQXs.t -> Monomial.dim -> Monomial.dim -> QQX.t * QQX.t * QQX.t

(** [m = compute_min_poly_p q p] computes the minimal polynomial [m] of [q] within the field
    Q[z]/p(z). That is with q(z) an element of Q[z]/p(z).*)
val compute_min_poly_p : QQX.t -> QQX.t -> QQX.t

module type NF = sig  

  (** The degree of the extension.*)
  val deg : int

  (** int_poly is a monic integer polynomial that defines the same field as A.min_poly. *)
  val int_poly : QQX.t

  (** The type of elements of the number field. *)
  type t

  (** Converts a univariate polynomial to an element of the number field.*)
  val make_elem : QQX.t -> t

  (** Get the polynomial representation of an elem modulo int_poly*)
  val get_poly : t -> QQX.t
  
  val of_rat : QQ.t -> t

  (** Computes the monic minimal polynomial of a given element. *)
  val compute_min_poly : t -> QQX.t

  val mul : t -> t -> t

  val int_mul : int -> t -> t

  val add : t -> t -> t

  val sub : t -> t -> t

  val inverse : t -> t

  val exp : t -> int -> t

  val equal : t -> t -> bool

  val compare : t -> t -> int

  val is_zero : t -> bool

  val one : t

  val zero : t

  val negate : t -> t

  val pp : Format.formatter -> t -> unit

  (** Univariate polynomials over the number field*)
  module X : 
    sig
      include Euclidean with type scalar = t
  
      (** Pretty printer. The field variable is z and the polynomial variable is x.*)
      val pp : Format.formatter -> t -> unit

      (** Convert a rational polynomial to a polynomial in the number field*)
      val lift : QQX.t -> t

      (** Convert a polynomial in the number field to a multivariate polynomial.
          The field variable is 0, and the polynomial variable is 1.*)
      val de_lift : t -> QQXs.t

      (** Factors a square free polynomial in the number field.*)
      val factor_square_free_poly : t -> (scalar * (t list))

      (** Factors an arbitrary polynomial in the number field.*)
      val factor : t -> (scalar * ((t * int) list))

      (** Extract the root of a linear polynomial
          @raise Failure if the input is not linear*)
      val extract_root_from_linear : t -> scalar
    end

  (** An order of the number field. An order in a number field is a finite 
    dimensional Z module with compatible multiplication to make an order a ring. Let 1,e_1,...,e_{n-1}
    be a basis for the order as a Z module. Then the rank of the order is n. Elements of the
    order are integer combinations of 1,e_2,...,e_n. Therfore, elements of the order are
    represented by integer arrays of size n. For implementation reasons we assume the constant
    dimension 1 is the rightmost dimension. That is, if e_1,...,e_{n-1}, 1 is a basis for an 
    order the element a + be_{n-1} could be represented by \[|0, 0, ..., b, a|\]. The order of
    the other dimensions doesn't matter.*)
  module O : sig
    (** Type for ideals of orders.*)
    type ideal

    (** Elements of the order. *)
    type o

    val pp_o : Format.formatter -> o -> unit

    (** Every element of the number field a can be uniquely written as a = 1/d * o, where
       d is an integer and o is an element of O. [make_o_el a = (d, o)]*)
    val make_o_el : t -> ZZ.t * o

    (** [order_el_to_f_elem (d, o) = a], where a = 1/d * o. *)
    val order_el_to_f_elem : ZZ.t * o -> t

    (** This is really just used for testing. An arbitrary integer matrix may not be an ideal.*)
    val idealify : ZZ.t array array -> ideal

    (** Pretty printer for ideals*)
    val pp_i : Format.formatter -> ideal -> unit
    
    (** Tests if two ideals are the same.*)
    val equal_i : ideal -> ideal -> bool

    val sum_i : ideal -> ideal -> ideal
    
    val mul_i : ideal -> ideal -> ideal

    (** Get the ideal generated by an elem.*)
    val ideal_generated_by : o -> ideal

    (** The ideal generated by 1.*)
    val one_i : ideal

    val intersect_i : ideal -> ideal -> ideal

    (** I : J = {x \in O : xJ \subseteq I }. *)
    val quotient_i : ideal -> ideal -> ideal

    (** Given an ideal, get the smallest positive integer that is a member of that ideal.*)
    val get_smallest_int : ideal -> ZZ.t

    (** Fractional ideals of the order. A fractional ideal consists of an integer d and and ideal
        i. The elements of the fractional ideal are the elements of i divided by d.*)
    type frac_ideal

    (** The fractional ideal generated by 1.*)
    val one : frac_ideal
    
    val sum : frac_ideal -> frac_ideal -> frac_ideal
    
    val intersect : frac_ideal -> frac_ideal -> frac_ideal

    val mul : frac_ideal -> frac_ideal -> frac_ideal

    val exp : frac_ideal -> int -> frac_ideal

    (** I :_K J = {x \in K : xJ \subseteq I } where K is the respective number field. *)
    val quotient : frac_ideal -> frac_ideal -> frac_ideal

    val pp : Format.formatter -> frac_ideal -> unit

    val equal : frac_ideal -> frac_ideal -> bool
    
    val subset : frac_ideal -> frac_ideal -> bool

    val make_frac_ideal : ZZ.t -> ideal -> frac_ideal

    (** Given an overorder o, represented as a fractional ideal, and a fractional ideal
        compute an overorder C and fractional ideal J such that J is invertible in C.*)
    val compute_overorder : frac_ideal -> frac_ideal -> frac_ideal * frac_ideal

    (** The algorithm of Ge (1993). Given ideals I_1, ..., I_k of the order
        computes an overorder C, proper invertible ideals J_1, ..., J_l of C, and
        integers e_1, ..., e_l, such that J_i + J_j = C for i <> j, and 
        (I_1C)...(I_kC) = J_1^e_1...J_l^e_l*)
    val factor_refinement : frac_ideal list -> frac_ideal * (frac_ideal * int) list

    (** Given ideals I_1, ..., I_k of the order. Computes \[\[f_11; ...; f_1l\];
                                                            \[f_21; ...; f_2l\];
                                                            \[...\]
                                                            \[f_k1; ...; f_kl\]\], 
        ideals J_1, ..., J_l of overorder C, such that I_iC = J_1^f_i1...J_l^f_il.*)
    val compute_factorization : frac_ideal list -> int list list * frac_ideal list * frac_ideal
    
    (** Given elements gamma_1, ..., gamma_k of the order, computes a basis
                                                            \[\[f_11; ...; f_1k\];
                                                            \[f_21; ...; f_2k\];
                                                            \[...\]
                                                            \[f_l1; ...; f_lk\]\]
        for the set {n_1, ..., n_k : gamma_1^n_1...gamma_k^n_k is a unit of O.} *)
    val find_unit_basis : o list -> int list list
  end

  (** Given elements gamma_1, ..., gamma_k of the number field, computes a basis
                                                            \[\[f_11; ...; f_1k\];
                                                            \[f_21; ...; f_2k\];
                                                            \[...\]
                                                            \[f_l1; ...; f_lk\]\]
        for the set {n_1, ..., n_k : gamma_1^n_1...gamma_k^n_k = 1.} *)
  val find_relations : t list -> int list list

end

(** Given an irreducible polynomial, construct a number field. Giving a
    polynomial that is not irreducible in Q[x] gives undefined behavior.*)
module MakeNF (A : sig val min_poly : QQX.t end) : NF

type sf = Sf : (module NF with type t = 'a) * (('a * int) list) -> sf

(** [min_poly, roots] = [splitting_field p] is such that Q[x]/min_poly is the
    splitting field of [p]. [roots] give the representation of the roots along with
    their multiplicity of [p] in the splitting field.*)
val splitting_field : QQX.t -> sf
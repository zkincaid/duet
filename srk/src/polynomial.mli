(** Polynomials and Grobner bases. *)

open Syntax

(** Signature of univariate polynmials *)
module type Univariate = sig
  include Ring.Vector with type dim = int
  val order : t -> int
  val mul : t -> t -> t
  val one : t
  val scalar : scalar -> t
  val compose : t -> t -> t

  (** The polynomial [p(x) = x] *)
  val identity : t

  val eval : t -> scalar -> scalar

  (** Exponentiation *)
  val exp : t -> int -> t

  (** [mul_monomial k d p] multiplies the polynomial p by k * x^d *)
  val mul_monomial : scalar -> int -> t -> t
end

(** Univariate polynomials over a given ring *)
module MakeUnivariate (R : Algebra.Ring) : Univariate with type scalar = R.t

module type Euclidean = sig
  include Univariate

  (** Given polynomials a and b with b not 0, compute q, r such that
    a = bq + r with deg(r) < deg (b).*)
  val qr : t -> t -> t * t

  (** Given two non-zero polynomials a and b, computes u, v, g such that 
    gcd(a, b) = g, g is monic, and au + bv = g via the extended euclidean algorithm.*)
  val ex_euc : t -> t -> t * t * t

  (** Given a polynomial p, computes (a1, i1), ..., (ak, ik) such that a1^i1...ak^ik = p
      and each ai is square free.*)
  val square_free_factor : t -> (t * int) list
end

(** Univariate polynomials over a field give a Euclidean domain. *)
module MakeEuclidean (
  F : sig
    include Algebra.Field
    val int_mul : int -> t -> t (*Mathematically this isn't needed ix = x + x + ... + x. But there could be faster implementations.*)
  end
  ) : Euclidean with type scalar = F.t

(** Univariate polynomials with rational coefficients *)
module QQX : sig
  include Euclidean with type scalar = QQ.t

  val pp : Format.formatter -> t -> unit
  val show : t -> string

  (** Given a polynomial [p(x)], compute a polynomial [q(x)] such that that
      for every integer [x >= 0], we have [q(x) = sum_{i=0}^x p(i)]. *)
  val summation : t -> t

  (** Given a polynomial [p(x)], compute a factorization [p(x) = c*q1(x)^d1 *
      ... qn(x)^dn] such that each qi is an irreducible polynomial with
      integer coefficients. *)
  val factor : t -> QQ.t * ((t * int) list)

  (** Greatest common divisor of all coefficients. *)
  val content : t -> QQ.t

  (** [choose k] is the polynomial [x*(x-1)*...*(x-k+1)/k!].  For any
     natural n, p(n) evaluates to (n choose k). *)
  val choose : int -> t

  (** [term_of srk t p] computes a term representing [p(t)]. *)
  val term_of : ('a context) -> 'a arith_term -> t -> 'a arith_term

end

(** Monomials *)
module Monomial : sig
  type t
  type dim = int

  val pp : (Format.formatter -> int -> unit) -> Format.formatter -> t -> unit

  val mul : t -> t -> t
  val one : t
  val mul_term : dim -> int -> t -> t
  val singleton : dim -> int -> t
  val power : dim -> t -> int
  val enum : t -> (dim * int) BatEnum.t
  val of_enum : (dim * int) BatEnum.t -> t
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val pivot : dim -> t -> (int * t)
  val div : t -> t -> t option

  (** Least common multiple *)
  val lcm : t -> t -> t

  (** Greatest common divisor *)
  val gcd : t -> t -> t

  (** {2 Monomial orderings} *)

  (** Lexicographic order *)
  val lex : t -> t -> [ `Eq | `Lt | `Gt ]

  (** Compare by total degree, then lexicographic order *)
  val deglex : t -> t -> [ `Eq | `Lt | `Gt ]

  (** Compare by total degree, then reverse lexicographic order *)
  val degrevlex : t -> t -> [ `Eq | `Lt | `Gt ]

  (** Given a list of *subsets* of dimensions [p1, ..., pn], a monomial [m]
      can be considered as a list of monomials ("blocks") [m1, ..., mn, m0],
      where each [mi] contains the dimensions that belong to [pi] (and not to
      any lower [i]), and m0 contains the dimensions not belonging to any pi.
      Given a monomial ordering for comparing blocks, the block ordering is
      the lexicographic ordering on monomials viewed as lists of blocks. *)
  val block :
    ((dim -> bool) list) ->
    (t -> t -> [ `Eq | `Lt | `Gt ]) ->
    (t -> t -> [ `Eq | `Lt | `Gt ])

  val term_of : ('a context) -> (dim -> 'a arith_term) -> t -> 'a arith_term

  (** Determine whether a monomial is a variable *)
  val destruct_var : t -> dim option

  (** Sum of powers of all variables. *)
  val total_degree : t -> int
end

(** Signature of multivariate polynmials *)
module type Multivariate = sig
  type t
  type scalar
  type dim = Monomial.t

  val equal : t -> t -> bool
  val add : t -> t -> t
  val negate : t -> t
  val mul : t -> t -> t
  val zero : t
  val one : t

  val sub : t -> t -> t

  val pp : (Format.formatter -> scalar -> unit) ->
           (Format.formatter -> int -> unit) ->
           Format.formatter ->
           t ->
           unit

  (** [add_term k m p] is the polynomial k*m + p *)
  val add_term : scalar -> Monomial.t -> t -> t

  (** Constant polynomial *)
  val scalar : scalar -> t

  (** Polynomial consisting of a single variable *)
  val of_dim : int -> t

  val scalar_mul : scalar -> t -> t

  val coeff : Monomial.t -> t -> scalar
  val pivot : Monomial.t -> t -> scalar * t
  val enum : t -> (scalar * Monomial.t) BatEnum.t
  val of_enum : (scalar * Monomial.t) BatEnum.t -> t
  val of_list : (scalar * Monomial.t) list -> t

  (** Exponentiation by a positive integer *)
  val exp : t -> int -> t

  (** Generalization of polynomial composition -- substitute each
     dimension for a multivariate polynomial *)
  val substitute : (int -> t) -> t -> t

  (** Multiply a polynomial by a monomial *)
  val mul_monomial : Monomial.t -> t -> t

  (** Divide a polynomial by a monomial *)
  val div_monomial : t -> Monomial.t -> t option

  (** Given polynomial p and monomial m, compute polynomials q and r
     such that p = q*m + r, and such that m does not divide any term
     in r. *)
  val qr_monomial : t -> Monomial.t -> t * t

  (** The set of dimensions that appear in a polynomial *)
  val dimensions : t -> SrkUtil.Int.Set.t

  (** Maximum total degree of a monomial term *)
  val degree : t -> int

  val fold : (dim -> scalar -> 'a -> 'a) -> t -> 'a -> 'a
end
                    
(** Multi-variate polynomials over a ring *)
module MakeMultivariate (R : Algebra.Ring) : Multivariate with type scalar = R.t

(** Multi-variate polynomials with rational coefficients *)
module QQXs : sig
  include Multivariate with type scalar = QQ.t

  val pp : (Format.formatter -> int -> unit) -> Format.formatter -> t -> unit
  val compare : t -> t -> int

  (** Convert a rational vector to a linear polynomial, where each dimension
      corresponds to a variable except the designated [const] dimension, which
      is treated at a constant 1. *)
  val of_vec : ?const:int -> Linear.QQVector.t -> t

  (** Write a polynomial as a sum [t + p], where [t] is a linear term and [p]
      is a polynomial in which every monomial has degree >= 2 *)
  val split_linear : ?const:int -> t -> (Linear.QQVector.t * t)

  (** Convert a linear polynomial to a vector, where each dimension
      corresponds to a variable except the designated [const] dimension, which
      is treated at a constant 1.  Return [None] if the polynomial is
      not linear. *)
  val vec_of : ?const:int -> t -> Linear.QQVector.t option

  val term_of : ('a context) -> (Monomial.dim -> 'a arith_term) -> t -> 'a arith_term

  val of_term : ('a context) -> 'a arith_term -> t

  (** Greatest common divisor of all coefficients. *)
  val content : t -> QQ.t

  (** Write a polynomial p(x) as c*m(x)*q(x), where c is the content
     of p, m is the greatest common divisors of all monomials in p,
     and q is the remainder. *)
  val factor_gcd : t -> (QQ.t * Monomial.t * t)

  (** Write a polynomial p(x) as c*m(x) + q(x), where c is the leading
     coefficient and q is the leading monomial of p (w.r.t. the given
      monomial order *)
  val split_leading :
    (Monomial.t -> Monomial.t -> [ `Eq | `Lt | `Gt ]) ->
    t ->
    (QQ.t * Monomial.t * t)

  val degree : t -> int
end

(** Conversion between multivariate polynomials with rational coefficients and
   rational vectors. *)
module LinearQQXs : sig
  include Linear.DenseConversion
    with type vec = QQXs.t
     and type dim = Monomial.t

  (** Densify, associating [Linear.const_dim] with [Monomial.one]. *)
  val densify_affine : context -> QQXs.t -> Linear.QQVector.t
  (** Sparsify, associating [Linear.const_dim] with [Monomial.one]. *)
  val sparsify_affine : context -> Linear.QQVector.t -> QQXs.t
end

(** Rewrite systems for multi-variate polynomials. A polynomial rewrite system
    consists of a set of polynomial rewrite rules [m1 -> p1, ..., mn -> pn]
    where each [mi] is a monomial, each [pi] is a polynomial, and such that
    [mi] is greater than any monomial in [pi] in some admissible order.  An
    admissible order is a total order on monomial such that for all [m], [n],
    [p], we have:
    1. [m <= n] implies [mp <= np]
    2. [m <= mp]
 *)
module Rewrite : sig
  type t

  val pp : (Format.formatter -> int -> unit) -> Format.formatter -> t -> unit

  (** Given an admissible order and a list of zero polynomials, orient the
      polynomials into a rewrite system.  This generalizes Gauss-Jordan
      elimination, but (unlike Groebner basis computation) does not saturate
      the rewrite system with implied equations.  Thus, it can only be used as
      a semi-test for membership in the ideal generated by the input
      polynomials.  *)
  val mk_rewrite : (Monomial.t -> Monomial.t -> [ `Eq | `Lt | `Gt ]) ->
    QQXs.t list ->
    t

  val reduce_rewrite : t -> t

  (** Saturate a polynomial rewrite system with implied equalities  *)
  val grobner_basis : t -> t

  (** Reduce a multi-variate polynomial using the given rewrite rules until
      no more rewrite rules apply *)
  val reduce : t -> QQXs.t -> QQXs.t

  (** Reduce a multi-variate polynomial using the given rewrite rules until no
      more rewrite rules apply.  Return both the reduced polynomial and the
      polynomials used during reduction. *)
  val preduce : t -> QQXs.t -> (QQXs.t * QQXs.t list)

  (** Add a new zero-polynomial to a rewrite system and saturate *)
  val add_saturate : t -> QQXs.t -> t

  val generators : t -> QQXs.t list

  val get_monomial_ordering : t -> 
    (Monomial.t -> Monomial.t -> [`Eq | `Lt | `Gt])

  (** Given a Groebner basis for an ideal (under some monomial
     ordering), compute a Groebner basis for the same ideal under the
     given ordering. *)
  val reorder_groebner : (Monomial.t -> Monomial.t -> [`Eq | `Lt | `Gt]) -> t -> t

  (** Is one rewrite contained inside another? *)
  val subset : t -> t -> bool

  (** Is one rewrite equal to another? *)
  val equal : t -> t -> bool

  (** Find the subset of rewrites that only refer to monomials satisfying the
     given predicate.  Assuming that the rewrite is a grobner basis and the set of
     monomials satisfying the predicate is downwards-closed w.r.t. the
     monomial ordering, this is a grobner basis for the intersection of the ideal
      and the space of polynomials over the given set of monomials *)
  val restrict : (Monomial.t -> bool) -> t -> t
end

(** A polynomial ideal is a set of polynomials that is closed under
   addition, and is closed under multiplication by any polynomial. *)
module Ideal : sig
  type t

  (** Pretty print *)
  val pp : (Format.formatter -> int -> unit) -> Format.formatter -> t -> unit

  (** Compute the smallest ideal that contains a given set of polynomials *)
  val make : QQXs.t list -> t

  val add_saturate : t -> QQXs.t -> t

  val reduce : t -> QQXs.t -> QQXs.t

  (** Compute a finite set of polynomials that generates the given
     ideal.  Note [make (generators i) = i], but [generators (make g)]
     is not necessarily equal to [g]. *)
  val generators : t -> QQXs.t list

  (** Is one ideal contained inside another? *)
  val subset : t -> t -> bool

  (** Is one ideal equal to another? *)
  val equal : t -> t -> bool

  (** Does an ideal contain a given polynomial? *)
  val mem : QQXs.t -> t -> bool

  (** Intersect two ideals. *)
  val intersect : t -> t -> t

  (** Compute the ideal consisting of all products of polynomials
     belonging to the two given ideals *)
  val product : t -> t -> t

  (** Compute the ideal consisting of all sums of polynomials beloning
     to the two given ideals *)
  val sum : t -> t -> t

  (** Compute the ideal consisting of all polynomials in the given
     ideal that are defined only over dimensions satisfying the given
     predicate. *)
  val project : (int -> bool) -> t -> t
end

(**Grobner basis computation using the FGb library.*)
module FGb : sig
  (**[grobner_basis block1 block2 polys] computes a Grobner basis of the polynomials in [polys] within the ring Q\[block1, block2\]. 
  The monomial order used in the computation is a block ordering defined by the variables in [block1] and [block2] with [block1] >> [block2]. That is,
  for any monomials m1 and m2 where, m1 contains variables in [block1] but m2 does not, m1>m2. The monomial order within each block is degree reverse
  lexicographic defined by the order of the variables in the given list. That is [grobner_basis \["x"; "y"; "z"\] \[\] polys] defines a drl order with [x] > [y] > [z].
  As in the previous example [block2] can be empty, indicated a normal drl order. However, [block1] must be non-empty. For the input polynomials to be 
  well formed the variables in [polys] need to be in the set [block1 @ block2]. *)
  val grobner_basis : Monomial.dim list -> Monomial.dim list -> QQXs.t list -> QQXs.t list

  (**[get_mon_order block1 block2] should return the monomial ordering used in the Grobner basis computation [grobner_basis block1 block2 polys]. 
      TODO: Actually, this isn't quite right. The degrevlex of fgb uses the order of the variables in the block, whereas the monomial degrevlex uses the 
      lex ordering of the variables regardless of the order they appear in the list.*)
  val get_mon_order : Monomial.dim list -> Monomial.dim list -> Monomial.t -> Monomial.t -> [`Eq | `Lt | `Gt]

end


(** A witness is a representation of a polynomial combination of a set of
   generator polynomials, where each generator polynomial is represente by an
   integer identifier.  *)
module Witness : sig
  include Ring.Vector with type dim = int
                       and type scalar = QQXs.t
end

(** Polynomial rewrite systems tagged with witnesses.  Reducing a polynomial
   [p] yields both a residue polynomial [r] and a polynomial combination of
   generators [w], so that [p = r + w]. *)
module RewriteWitness : sig
  type t
  val mk_rewrite : (Monomial.t -> Monomial.t -> [ `Eq | `Lt | `Gt ]) ->
    (QQXs.t * Witness.t) list ->
    t
  val grobner_basis : t -> t
  val add_saturate : t -> QQXs.t -> Witness.t -> t
  val reduce : t -> QQXs.t -> (QQXs.t * Witness.t)

  (** Check if a given polynomial reduces to zero.  If so, return the witness
     of membership. *)
  val zero_witness : t -> QQXs.t -> Witness.t option
  val reducew : t -> (QQXs.t * Witness.t) -> (QQXs.t * Witness.t)
  val generators : t -> (QQXs.t * Witness.t) list
  val forget : t -> Rewrite.t
end

val pp_ascii_dim : Format.formatter -> int -> unit
val pp_numeric_dim : string -> Format.formatter -> int -> unit

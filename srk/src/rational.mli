exception Divide_by_zero

module type RationalFunc = sig

  type num

  type den

  (** Technically the elements are equivalence classes where (a, b)~(c, d) if ad = cb.
  But this module uses the gcd of D to mostly normalize elements. They could be 
  off by a constant.*)
  type t

  val zero : t

  val one : t

  val of_n_d : num * den -> t

  (**This is equiv, not structural equal*)
  val equal : t -> t -> bool

  (**(a, b) = (c, d) if a = c and b = d*)
  val equal_syn : t -> t -> bool

  val add : t -> t -> t

  val negate : t -> t

  val lift : num -> t
    
  val mul : t -> t -> t

  val int_mul : int -> t -> t

  val pp : Format.formatter -> t -> unit

  (**Computes partial fractional decomposition. Let [den_pow] = (g_1, e_1), ..., (g_k, e_k).
  [partial_fraction num den_pow] computes (n_1, (g_1, e_1)), ..., (n_k, (g_k, e_k))
  such that num/((g_1, e_1)...(g_k, e_k)) = (n_1/(g_1, e_1)) + ... + (n_k/(g_k, e_k))*)
  val partial_fraction : num -> (den * int) list -> (num * (den * int)) list
end



(** Makes a field of rational functions. The given polynomial ring should be an integral domain. There is no way to enforce this in code.*)
module MakeRat (D : sig 
    include Polynomial.Euclidean
    val pp : Format.formatter -> t -> unit
    val scalar_inv : scalar -> scalar
  end) : sig
   
  include RationalFunc with type num = D.t and type den = D.t

  (**@raise Divide_by_zero if the input is 0.*)
  val inverse : t -> t

end


(** Makes rational function, but where the numerator type is a superset of the denominator type. *)
module MakeRatDiff
  (N : sig 
    include Polynomial.Univariate
    val pp : Format.formatter -> t -> unit
    val int_mul : int -> t -> t
  end)
  (D : sig
    include Polynomial.Euclidean
    val pp: Format.formatter -> t -> unit
  end)
  (I : sig
    val lift : D.t -> N.t
    val qr : N.t -> D.t -> N.t * N.t
  end) : RationalFunc with type num = N.t and type den = D.t


(**Exponential polynomials with heavyside terms over a number field as solutions to a solvable polynomial.*)
module type ExpPolyNF = sig
  (**The number field from which elements are drawn from*)
  module NF : NumberField.NF

  (**A constant is a multivariate polynomial with number field coefficients. The variable
      represent the initial values of the sequence*)
  module ConstRing : Polynomial.Multivariate with type scalar = NF.t

  (**The polynomial part of an exponential polynomial*)
  module ConstRingX : Polynomial.Univariate with type scalar = ConstRing.t

  type t 
  val zero : t
  val one : t
  val scalar : ConstRing.t -> t
  val of_polynomial : ConstRingX.t -> t

  (**Exponential bases are number field elements*)
  val of_exponential : NF.t -> t

  val of_exponential_poly : NF.t -> ConstRingX.t -> t

  (**One way to handle 0 eigenvalues is to use heavyside functions. Essentially iverson brackets multiplied by constants
      of_heavy i c represents the term \[n>=i\] * c.*)
  val of_heavy : int -> ConstRing.t -> t

  val scalar_mul : ConstRing.t -> t -> t
  val add : t -> t -> t
  val negate : t -> t
  val equal : t -> t -> bool
  val eval : t -> int -> ConstRing.t
  
  (** Enumerate the exponential part.*)
  val enum_ep : t -> (ConstRingX.t * NF.t) BatEnum.t

  (** Enumerate the heavysides*)
  val enum_heavy : t -> (int * ConstRing.t) BatEnum.t

  val pp : Format.formatter -> t -> unit
  
  (** This module contains recurrence solutions.*)
  val get_rec_sols : unit -> t array

  (** Get the algebraic relations of the bases of the exponentials in [get_rec_sols ()].
      The second returned element gives the mapping from bases to variable dimensions.*)
  val base_relations : unit -> Polynomial.QQXs.t list * (NF.t * int) BatEnum.t

  (** Get the algebraic relations of [get_rec_sols ()]. Let d be [(Array.length (get_rec_sols ()))].
      The result contains polynomials over the dimensions 0, ..., d-1, d, ..., 2d - 1, 2d. The
      first 0, ..., d-1 variable are the pre-state. The d, ..., 2d-1 variables are the post-state
      and the 2d'th variable is the iteration variable K.*)
  val algebraic_relations : unit -> Polynomial.QQXs.t list

  val shift_remove_heavys : unit -> Polynomial.QQXs.t array list * int * t array

  val long_run_algebraic_relations : unit -> Polynomial.QQXs.t array list * int * Polynomial.QQXs.t list

end

module ConstRingX : Polynomial.Univariate with type scalar = Polynomial.QQXs.t

(** Rational exponential polynomials with heavyside and IIFS.*)
module RatEP : sig
  
  type t

  val equal : t -> t -> bool

  val pp : Format.formatter -> t -> unit

  val zero : t

  val one : t

  (** Currently this function will fail if the input contains an iif*)
  val eval : t -> int -> Polynomial.QQXs.t

  val scalar : Polynomial.QQXs.t -> t

  val of_polynomial : ConstRingX.t -> t

  val of_exponential : QQ.t -> t
    
  val scalar_mul : Polynomial.QQXs.t -> t -> t

  (** Enumerate the exponential part.*)
  val enum_ep : t -> (ConstRingX.t * QQ.t) BatEnum.t

  (** Enumerate the heavysides*)
  val enum_heavy : t -> (int * Polynomial.QQXs.t) BatEnum.t

  val enum_iif : t -> ((Polynomial.QQX.t * int) * Polynomial.QQXs.t) BatEnum.t
      
  val add : t -> t -> t
    
  val negate : t -> t
    
  val mul : t -> t -> t

  val solve_rec : ?initial:Q.t option array option -> TransitionIdeal.block list -> t array

  val to_nf : t array -> (module ExpPolyNF)

end
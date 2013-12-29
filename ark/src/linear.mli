open Apak
open ArkPervasives
open Hashcons

(** Variable (dimension) signature *)
module type Var = sig
  include Putil.Ordered
  val to_smt : t -> Z3.ast
end

(** Hashed variable (dimension) signature *)
module type HVar = Putil.Hashed.S

(** Augment a variable type with a new dimension for constants.  Linear
    expressions over Affine(V) are equivalent to affine expressions over V. *)
module Affine (V : Var) : Var with type t = V.t affine

module Expr : sig
  module type S = sig
    include Putil.S

    type dim
    type base
    val scalar_mul : base -> t -> t
    val add : t -> t -> t
    val sub : t -> t -> t
    val negate : t -> t
    val equal : t -> t -> bool
    val zero : t
    val find : dim -> t -> base
    val enum : t -> (dim * base) BatEnum.t
    val of_enum : (dim * base) BatEnum.t -> t
    val add_term : dim -> base -> t -> t
    val min_binding : t -> (dim * base)
    val max_binding : t -> (dim * base)
    val enum_ordered : t -> (dim * base) BatEnum.t
    val var : dim -> t
    val to_smt : (dim -> Smt.ast) -> (base -> Smt.ast) -> t -> Smt.ast

    (** Transpose a system of linear equations.  The length of [rows] should
	match length of [equations], and the variables each equation should be
	all belong to the list [columns].  The result is a system of linear
	equations over the row variables. *)
    val transpose : t list -> dim list -> dim list -> t list
  end

  (** Linear expressions implemented with standard maps *)
  module Make (V : Var) (R : Ring.S) : S with type dim = V.t
					 and type base = R.t

  (** Linear expressions implemented with Patricia trees.  This should support
      faster addition than the [Make] functor. *)
  module HMake (V : HVar) (R : Ring.S) : S with type dim = V.t hash_consed
					   and type base = R.t
					   and type t = (V.t, R.t) Hmap.t

  (** Univariate polynomials with coefficients in R *)
  module MakePolynomial (R : Ring.S) : sig
    include S with type dim = int
	      and type base = R.t

    (** Multiplicative unit *)
    val one : t

    (** Multiple a polynomial by a monomial *)
    val mul_term : int -> R.t -> t -> t

    (** Multiply two polynomials *)
    val mul : t -> t -> t

    (** Constant exponentiation of a polynomial *)
    val exp : t -> int -> t

    (** Functional composition of two polynomials *)
    val compose : t -> t -> t

    (** Given a polynomial [p] and a ring element [x], compute [p(x)]. *)
    val eval : t -> R.t -> R.t

    (** Highest degree of the terms of a polynomial *)
    val order : t -> int
  end
end

exception No_solution
exception Many_solutions

module GaussElim (F : Field.S) (E : Expr.S with type base = F.t) : sig
  val solve : (E.t * F.t) list -> (E.dim -> F.t)
end

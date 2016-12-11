(** Linear terms and various linear algebra operations. *)

open Apak
open ArkPervasives
open Hashcons

(** Variable (dimension) signature *)
module type Var = sig
  include Putil.Ordered
end

(** Hashed variable (dimension) signature *)
module type HVar = Putil.Hashed.S

(** Augment a variable type with a new dimension for constants.  Linear
    expressions over Affine(V) are equivalent to affine expressions over V. *)
module AffineVar (V : Var) : sig
  include Var with type t = V.t affine
  val to_smt : (V.t -> Smt.ast) -> t -> Smt.ast
end

module Expr : sig
  module type S = sig
    include Putil.S

    type dim
    type base
    val scalar_mul : base -> t -> t
    val add : t -> t -> t
    val negate : t -> t
    val equal : t -> t -> bool
    val zero : t
    val find : dim -> t -> base
    val enum : t -> (dim * base) BatEnum.t
    val add_term : dim -> base -> t -> t
    val min_binding : t -> (dim * base)
    val max_binding : t -> (dim * base)
    val enum_ordered : t -> (dim * base) BatEnum.t
    val var : dim -> t
    val sub : t -> t -> t
    val of_enum : (dim * base) BatEnum.t -> t
    val pivot : dim -> t -> (base * t)
    val to_smt : (dim -> Smt.ast) -> (base -> Smt.ast) -> t -> Smt.ast

    (** Transpose a system of linear equations.  The length of [rows] should
        match length of [equations], and the variables each equation
        should be all belong to the list [columns].  The result is a
        system of linear equations over the row variables. *)
    val transpose : t list -> dim list -> dim list -> t list
    val sum : t BatEnum.t -> t
    val term : dim -> base -> t
  end

  (** Linear expressions implemented with standard maps *)
  module Make (V : Var) (R : Ring.S) : S with type dim = V.t
                                          and type base = R.t

  (** Linear expressions implemented with Patricia trees.  This should support
      faster addition than the [Make] functor. *)
  module HMake (V : HVar) (R : Ring.S) : S with type dim = V.t hash_consed
                                            and type base = R.t
                                            and type t = (V.t, R.t) Hmap.t

  module LiftMap
      (V : Var)
      (M : Putil.Map.S with type key = V.t)
      (R : Ring.S)
    : S with type dim = V.t
         and type base = R.t
         and type t = R.t M.t

  (** Univariate polynomials with coefficients in R *)
  module MakePolynomial (R : Ring.S) : sig
    include S with type dim = int
               and type base = R.t

    (** Multiplicative unit *)
    val one : t

    (** Constant polynomial *)
    val const : R.t -> t

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

  module Hashed : sig
    module type S = sig
      include S
      val hash : t -> int
      val equal : t -> t -> bool
    end
    module HMake (V : HVar) (R : Ring.Hashed.S) : S
      with type dim = V.t Hashcons.hash_consed
       and type base = R.t
  end
end

module Affine : sig
  module type S = sig
    type var
    include Expr.S with type dim = var affine
    val const : base -> t
    val const_of : t -> base option
    val const_coeff : t -> base
    val var_bindings : t -> (var * base) BatEnum.t
    val var_bindings_ordered : t -> (var * base) BatEnum.t
    val var_coeff : var -> t -> base
  end
  module LiftMap
      (V : Var)
      (M : Putil.Map.S with type key = V.t)
      (R : Ring.S) : S with type var = V.t
                        and type base = R.t

end

exception No_solution
exception Many_solutions

module GaussElim (F : Field.S) (E : Expr.S with type base = F.t) : sig
  val solve : (E.t * F.t) list -> (E.dim -> F.t)

  (** Given a predicate on dimensions and a list of terms (all implicitly
      equal to zero), orient the equations as rewrite rules that eliminate
      dimensions that don't satisfy the predicate. *)
  val orient : (E.dim -> bool) -> E.t list -> (E.dim * E.t) list
end

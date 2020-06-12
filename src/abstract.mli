(** Symbolic abstraction routines. *)
open Syntax

(** [affine_hull srk phi symbols] computes a basis for the affine hull of phi,
    projected onto the given set of symbols.  The basis is represented as a
    list of terms, with the interpretation that a point [p] belongs to the
    affine hull if every term in the list evaluates to 0 at [p]. *)
val affine_hull : 'a context -> 'a formula -> symbol list -> 'a term list

(** Let [cs = t1, ..., tn] be a list of terms. [t1, ..., tn] generates
   a linear space of functions from interpretations to rationals;
   [vanishing_space srk phi cs] computes a basis for the subspace of
   functions from interpretations to rationals that evaluate to zero
   on all models of [phi]. *)
val vanishing_space : 'a context -> 'a formula -> 'a term array -> Linear.QQVectorSpace.t

(** [boxify srk phi terms] computes the strongest formula of the form
    [/\ { lo <= t <= hi : t in terms }]
    that is implied by [phi]. *)
val boxify : 'a context -> 'a formula -> 'a term list -> 'a formula

(** [abstract ?exists srk man phi] computes the strongest property that is
    implied by [phi] which is expressible within a given abstract domain.  The
    property is restricted to use only the symbols that satisfy the [?exists]
    predicate (which defaults to the constant [true] predicate). *)
val abstract : ?exists:(symbol -> bool) ->
               'a context ->
               'abs Apron.Manager.t ->
               'a formula ->
               ('a,'abs) SrkApron.property

module Sign : sig
  type 'a t
  val abstract : 'a context -> 'a formula -> 'a term list -> 'a t
  val formula_of : 'a context -> 'a t -> 'a formula
  val join : 'a t -> 'a t -> 'a t
  val equal : 'a t -> 'a t -> bool
  val bottom : 'a t
  val top : 'a t
  val exists : (symbol -> bool) -> 'a t -> 'a t
end

(** Symbolic abstraction as described in Reps, Sagiv,
   Yorsh---"Symbolic implementation of the best transformer", VMCAI
   2004. *)
module MakeAbstractRSY
    (C : sig
       type t
       val context : t context
     end) : sig

  (** Domains must satisfy the ascending chain condition, and are
     equipped with a function [of_model] that computes the best
     abstraction of a single model. *)
  module type Domain = sig
    type t
    val top : t
    val bottom : t

    (** Project property onto the symbols that satisfy the given
       predicate *)
    val exists : (symbol -> bool) -> t -> t

    val join : t -> t -> t
    val equal : t -> t -> bool

    (** Best abstraction of a model, restricted to the symbols in the
       given list.  *)
    val of_model : C.t Interpretation.interpretation -> symbol list -> t

    val formula_of : t -> C.t formula
  end

  (** Sign analysis determines whether each variables is positive,
     nonnegative, zero, nonpositive, negative, or unknown. *)
  module Sign : Domain

  (** Domain of affine equalities *)
  module AffineRelation : Domain
    with type t = (C.t, Polka.equalities Polka.t) SrkApron.property

  (** Predicate abstraction *)
  module PredicateAbs (U : sig val universe : C.t formula list end) : Domain

  (** Reduced product of abstract domains *)
  module Product (A : Domain) (B : Domain) : Domain with type  t = A.t * B.t

  (** Compute the best abstraction of a formula within a given domain.
     For a formula [phi], this is an element of the abstract domain
     [elt] such that: (1) [phi |= formula_of elt], (2) [elt] is
     expressed only over the symbols that satisy the [exists]
     predicate, and (3) for any [elt'] satisfying (1) and (2), we have
     [elt <= elt'].  *)
  val abstract : ?exists:(symbol -> bool) -> (module Domain with type t = 'a) -> C.t formula -> 'a
end

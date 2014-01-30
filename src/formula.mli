(** Arithmetic formulas *)

open Apak
open ArkPervasives

exception Nonlinear
exception Timeout

module type S = sig
  type t
  include Putil.Hashed.S with type t := t
  include Putil.OrderedMix with type t := t

  module T : Term.S

  (** {2 Formula constructors} *)

  (** True *)
  val top : t

  (** False *)
  val bottom : t

  val conj : t -> t -> t
  val disj : t -> t -> t

  (** [leqz t] is a formula representing [t <= 0]. *)
  val leqz : T.t -> t

  (** [eqz t] is a formula representing [t = 0]. *)
  val eqz : T.t -> t

  (** [ltz t] is a formula representing [t < 0]. *)
  val ltz : T.t -> t
  val atom : T.t atom -> t
  val eq : T.t -> T.t -> t
  val leq : T.t -> T.t -> t
  val geq : T.t -> T.t -> t
  val lt : T.t -> T.t -> t
  val gt : T.t -> T.t -> t
  val negate : t -> t

  val big_conj : t BatEnum.t -> t
  val big_disj : t BatEnum.t -> t

  (** {2 Formula deconstructors} *)

  (** [eval] is a fold for formulas.  More precisely, formulas are initial
      objects in the category of formula-algebras, and [eval alg] gives the
      (unique) morphism from the initial algebra to [alg] *)
  val eval : ('a, T.t atom) formula_algebra -> t -> 'a

  (** One-step unfolding of a formula *)
  val view : t -> (t, T.t atom) open_formula

  (** {2 Abstract domain operations} *)

  (** Covert an abstract value to a formula *)
  val of_abstract : 'a T.D.t -> t

  (** Convert a formula to a (possibly weaker) abstract value.  Optionally
      project the resulting abstract value onto a subset of the free variables
      in the formula (this is faster than abstracting and then projecting. *)
  val abstract : ?exists:(T.V.t -> bool) option ->
                 'a Apron.Manager.t ->
                 t ->
                 'a T.D.t

  (** Abstract post-condition of an assigment *)
  val abstract_assign : 'a Apron.Manager.t ->
                        'a T.D.t ->
                        T.V.t ->
                        T.t ->
                        'a T.D.t

  (** Abstract post-condition of an assumption *)
  val abstract_assume : 'a Apron.Manager.t -> 'a T.D.t -> t -> 'a T.D.t

  (** {2 Quantification} *)

  (** [exists p phi] existentially quantifies each variable in [phi] which
      does not satisfy the predicate [p]. The strategy used to eliminate
      quantifers is the one specified by [opt_qe_strategy]. *)
  val exists : (T.V.t -> bool) -> t -> t

  (** [exists vars phi] existentially quantifies each variable in [phi] which
      appears in the list [vars].  The strategy used to eliminate
      quantifiers is the one specified by [opt_qe_strategy] *)
  val exists_list : T.V.t list -> t -> t

  (** Default quantifier elimination strategy.  If not set, defaults to
      [qe_lme]. *)
  val opt_qe_strategy : ((T.V.t -> bool) -> t -> t) ref

  (** {3 Quantifier elimination strategies} *)

  (** Quantifier elimination algorithm based on lazy model enumeration, as
      described in David Monniaux: "Quantifier elimination by lazy model
      enumeration", CAV2010. *)
  val qe_lme : (T.V.t -> bool) -> t -> t

  (** Use Z3's built-in quantifier elimination algorithm *)
  val qe_z3 : (T.V.t -> bool) -> t -> t

  (** Over-approximate quantifier elimination.  Computes intervals for each
      variable to be quantified, and replaces occurrences of the variable
      with the appropriate bound.  *)
  val qe_cover : (T.V.t -> bool) -> t -> t

  val qe_partial : (T.V.t -> bool) -> t -> t

  (** {2 Simplification} *)

  (** [simplify p phi] simplifies the formula [phi], treating the variables
      which do not satisfy the predicate [p] as existentially quantified
      ([simplify] may, but is not obligated to, eliminate these variables).
      [simplify] may overapproximate [phi] (i.e., [simplify p phi] is implied
      by [phi], but [phi] does not necessarily implify [simplify p phi]).  The
      strategy used by [simplify] is the sequence of strategies given in
      [opt_simplification_strategy].  *)
  val simplify : (T.V.t -> bool) -> t -> t

  (** Simplify using Z3's built-in simplification routines *)
  val simplify_z3 : (T.V.t -> bool) -> t -> t

  (** Simplify using the algorithm described in Isil Dillig, Thomas Dillig,
      Alex Aiken: "Small Formulas for Large Programs: On-Line Constraint
      Simplification in Scalable Static Analysis", SAS 2010. *)
  val simplify_dillig : (T.V.t -> bool) -> t -> t

  (** Default simplification strategy.  If not set, defaults to
      [qe_cover; simplify_dillig]. *)
  val opt_simplify_strategy : ((T.V.t -> bool) -> t -> t) list ref

  (** {2 Formula linearization} *)

  (** Over-approximate an arbitrary formula by a linear arithmetic formula.
      This process requires introduction of new (existentially quantified)
      variables: the first argument to [linearize] is a function which
      generates new rational-typed variables.  The strategy used by
      [linearize] is the one specified by [opt_linearize_strategy]. *)
  val linearize : (unit -> T.V.t) -> t -> t


  (** Linearize using APRON's linearization strategy.  Should be faster (but
      less accurate) than [linearize_apron_dnf].  *)
  val linearize_apron : (unit -> T.V.t) -> t -> t

  (** Linearize using APRON's linearization strategy.  This forces a (lazy)
      conversion to DNF.  Should be more accurate (but slower) than
      [linearize_apron]. *)
  val linearize_apron_dnf : (unit -> T.V.t) -> t -> t

  (** Linearize using symbolic optimization and a combination of constant &
      symbolic intervals for nonlinear terms.  *)
  val linearize_opt : (unit -> T.V.t) -> t -> t

  (** Linearize by dropping nonlinear terms.  *)
  val linearize_trivial : (unit -> T.V.t) -> t -> t

  (** Default linearization strategy.  If not set, defaults to
      [linearize_opt]. *)
  val opt_linearize_strategy : ((unit -> T.V.t) -> t -> t) ref

  (** {2 Misc operations} *)

  val of_smt : Smt.ast -> t
  val to_smt : t -> Smt.ast

  val implies : t -> t -> bool
  val equiv : t -> t -> bool

  (** Substitute every atom in a formula with another formula. *)
  val map : (T.t atom -> t) -> t -> t

  (** Apply a substitution *)
  val subst : (T.V.t -> T.t) -> t -> t

  (** Given an interpretation [m] and a formula [phi], [select_disjunct m phi]
      finds a clause in the DNF of [phi] such that [m] is a model of that
      clause (or return [None] if no such clause exists). *)
  val select_disjunct : (T.V.t -> QQ.t) -> t -> t option

  val symbolic_bounds : (T.V.t -> bool) -> t -> T.t -> (pred * T.t) list

  val symbolic_abstract : (T.t list) -> t -> (QQ.t option * QQ.t option) list
  val disj_optimize : (T.t list) -> t -> (QQ.t option * QQ.t option) list list

  val dnf_size : t -> int
  val nb_atoms : t -> int
  val size : t -> int

  val log_stats : unit -> unit

  module Syntax : sig
    val ( && ) : t -> t -> t
    val ( || ) : t -> t -> t
    val ( == ) : T.t -> T.t -> t
    val ( < ) : T.t -> T.t -> t
    val ( > ) : T.t -> T.t -> t
    val ( <= ) : T.t -> T.t -> t
    val ( >= ) : T.t -> T.t -> t
  end
end

module Make (T : Term.S) : S with module T = T
module MakeEq (F : S) : sig
  module AMap : BatMap.S with type key = F.T.V.t affine
  (** [extract_equalities phi vars] computes a basis for the smallest linear
      manifold which contains [phi] and is defined over the variables
      [vars]. *)
  val extract_equalities : F.t -> F.T.V.t list -> F.T.Linterm.t list
end

(** Symbolic abstraction routines. *)
open Syntax

(** [affine_hull srk phi symbols] computes a basis for the affine hull of phi,
    projected onto the given set of symbols.  The basis is represented as a
    list of terms, with the interpretation that a point [p] belongs to the
    affine hull if every term in the list evaluates to 0 at [p]. *)
val affine_hull : 'a context -> 'a formula -> symbol list -> 'a arith_term list

(** Let [cs = t1, ..., tn] be a list of terms. [t1, ..., tn] generates
   a linear space of functions from interpretations to rationals;
   [vanishing_space srk phi cs] computes a basis for the subspace of
   functions from interpretations to rationals that evaluate to zero
   on all models of [phi]. *)
val vanishing_space : 'a context -> 'a formula -> 'a arith_term array -> Linear.QQVectorSpace.t

(** Given a formula [F] and terms [t_0,...,t_n], compute the convex hull all
   points [ { (t_0(x),...,t_n(x)) : x |= F } ]. *)
val conv_hull : ?man:(DD.closed Apron.Manager.t) ->
  'a context ->
  'a formula ->
  ('a arith_term) array ->
  DD.closed DD.t

(** [boxify srk phi terms] computes the strongest formula of the form
    [/\ { lo <= t <= hi : t in terms }]
    that is implied by [phi]. *)
val boxify : 'a context -> 'a formula -> 'a arith_term list -> 'a formula

(** [abstract ?exists srk man phi] computes the strongest property that is
    implied by [phi] which is expressible within a given abstract domain.  The
    property is restricted to use only the symbols that satisfy the [?exists]
    predicate (which defaults to the constant [true] predicate). *)
val abstract : ?exists:(symbol -> bool) ->
               'a context ->
               'abs Apron.Manager.t ->
               'a formula ->
               ('a,'abs) SrkApron.property


type 'a smt_model =
  [ `LIRA of 'a Interpretation.interpretation
  | `LIRR of LirrSolver.Model.t ]

type ('a, 'b) domain =
  { join : 'b -> 'b -> 'b
  ; of_model : 'a smt_model -> 'b
  ; formula_of : 'b -> 'a formula
  ; top : 'b
  ; bottom : 'b }
  
(** An solver contains a single formula that can be abstracted in various ways
   (convex hull, affine hull, sign analysis, ...); the solver allows different
   abstraction routines to share the work of computing a diverse set of models
    of the formula *)
module Solver : sig
  type 'a t

  (** Allocate a new solver. *)
  val make : 'a context -> ?theory:[`LIRR | `LIRA ] -> 'a formula -> 'a t

  (** Symbolic abstraction as described in Reps, Sagiv, Yorsh---"Symbolic
     implementation of the best transformer", VMCAI 2004. *)
  val abstract : 'a t -> ('a, 'b) domain -> 'b

  (** Retrieve the formula associated with a solver. *)
  val get_formula : 'a t -> 'a formula

  (** Retrieve a model of the formula that not satisfy any blocking clause, if
     possible.  *)
  val get_model : 'a t -> [ `Sat of 'a smt_model | `Unsat | `Unknown ]

  val get_context : 'a t -> 'a context

  (** [with_blocking s f x] executed [f x] under a new blocking level.  All
     formulas added to the solver using [block s phi] are forgotten. *)
  val with_blocking : 'a t -> ('c -> 'b) -> 'c -> 'b

  (** [block s phi] adds [phi] as a blocking clause (i.e., [get_model s] may
     no longer return a model that satisfies [phi]).  [block] should only be
     called within a procedure that passed to [with_blocking], to ensure that
     blocking clauses are removed.  *)
  val block : 'a t -> 'a formula -> unit
end

(** The sign domain represents formulas of the form (/\ t <> 0), where t
   belongs to some fixed set of terms and [<>] is one of [{<,>,=,<=,>=}].  *)
module Sign : sig
  type 'a t
  val formula_of : 'a context -> 'a t -> 'a formula
  val join : 'a t -> 'a t -> 'a t
  val equal : 'a t -> 'a t -> bool
  val bottom : 'a t
  val top : 'a t
  val exists : (symbol -> bool) -> 'a t -> 'a t
  val abstract : 'a Solver.t -> ?bottom:('a t) -> 'a arith_term list -> 'a t
end

(** Finite conjunctions of predicates drawn from some fixed set *)
module PredicateAbs : sig
  type 'a t = ('a, typ_bool) Expr.Set.t
  val formula_of : 'a context -> 'a t -> 'a formula
  val join : 'a t -> 'a t -> 'a t
  val equal : 'a t -> 'a t -> bool
  val top : 'a t
  val exists : (symbol -> bool) -> 'a t -> 'a t

  (** Given a set of predicates, find the subset that is entailed by the
     formula associated with the given solver. *)
  val abstract : 'a Solver.t -> 'a t -> 'a t
end

(** Domain of linear equations over a fixed set of terms *)
module LinearSpan : sig
  type t = Linear.QQVectorSpace.t
  val abstract : 'a Solver.t -> ?bottom:(t option) -> 'a arith_term array -> t

  (** [affine_hull solver symbols] computes a basis for the space of all
     implied affine equations a*symbols = b entailed by the formula associated
     with [solver].  The affine equations are represented w.r.t. the basis
     defined by [Syntax.symbol_of_int / Syntax.int_of_symbol].  *)
  val affine_hull : 'a Solver.t -> ?bottom:t -> symbol list -> t
end

(** Domain of affine inequations over a fixed set of terms *)
module ConvexHull : sig
  type t = DD.closed DD.t
  val abstract : 'a Solver.t ->
    ?man:(DD.closed Apron.Manager.t) ->
    ?bottom:(t option) ->
    'a arith_term array ->
    t
end

module PolynomialCone : sig
  type t = PolynomialCone.t
  val abstract : 'a Solver.t -> ?bottom:t -> 'a arith_term array -> t
end

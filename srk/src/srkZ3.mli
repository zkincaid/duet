(** Interface to {{:https://github.com/Z3Prover/z3} Z3} SMT solver *)
open Syntax
open Interpretation

type z3_context = Z3.context
type z3_expr = Z3.Expr.expr
type z3_func_decl = Z3.FuncDecl.func_decl

(** The process-global Z3 context.  Every [?context] argument in this module
    defaults to it.  Z3 ASTs are tied to their context; mixing ASTs from
    different contexts is an error, so new code should use this context
    rather than calling [Z3.mk_context]. *)
val get_default_context : unit -> z3_context

type 'a open_expr = [
  | `Real of QQ.t
  | `App of z3_func_decl * 'a list
  | `Var of int * typ_fo
  | `Add of 'a list
  | `Mul of 'a list
  | `Binop of [ `Div | `Mod | `Select ] * 'a * 'a
  | `Unop of [ `Floor | `Neg ] * 'a
  | `Store of 'a * 'a * 'a
  | `Tru
  | `Fls
  | `And of 'a list
  | `Or of 'a list
  | `Not of 'a
  | `Ite of 'a * 'a * 'a
  | `Quantify of [`Exists | `Forall] * string * typ_fo * 'a
  | `Atom of [`Eq | `Leq | `Lt] * 'a * 'a
  | `IsInt of 'a list
]

val z3_of_term : 'a context -> z3_context -> 'a term -> z3_expr
val z3_of_arith_term : 'a context -> z3_context -> 'a arith_term -> z3_expr
val z3_of_arr_term : 'a context -> z3_context -> 'a arr_term -> z3_expr
val z3_of_formula : 'a context -> z3_context -> 'a formula -> z3_expr
val z3_of_expr : 'a context -> z3_context -> ('a,typ_fo) expr -> z3_expr

(** Convert a Z3 expression into a term.  Raises [Invalid_argument] on
    failure. *)
val term_of_z3 : 'a context -> z3_expr -> 'a term

(** Convert a Z3 expression into a formula.  Raises [Invalid_argument] on
    failure. *)
val formula_of_z3 : 'a context -> z3_expr -> 'a formula

(** Convert a Z3 expression into an expression.  Raises [Invalid_argument] on
    failure. *)
val expr_of_z3 : 'a context -> z3_expr -> ('a,typ_fo) expr

module Solver : sig
  type 'a t

  val make : ?context:z3_context -> ?theory:string -> 'a context -> 'a t

  val add : 'a t -> ('a formula) list -> unit
  val push : 'a t -> unit
  val pop : 'a t -> int -> unit
  val reset : 'a t -> unit
  val check : ?assumptions:('a formula list) -> 'a t -> [ `Sat | `Unsat | `Unknown ]
  val to_string : 'a t -> string
    
  (** Compute a model of a solver's context.  The model is abstract -- it can
      be used to evaluate terms, but its bindings may not be enumerated (see
      [Interpretation] for more detail). *)
  val get_model : ?symbols:(symbol list) ->
    ?assumptions:('a formula list) ->
    'a t ->
    [ `Sat of 'a interpretation
    | `Unsat
    | `Unknown ]

  (** Compute a model of the a solver's context, and return an intepretation
      that binds the specified subset of symbols.  If the symbol list contains
      all symbols of the formula, then the interpretation is a model of the
      solver's context. *)
  val get_concrete_model : 'a t ->
    symbol list ->
    [ `Sat of 'a interpretation
    | `Unsat
    | `Unknown ]

  val get_unsat_core : 'a t ->
    ('a formula) list ->
    [ `Sat | `Unsat of ('a formula) list | `Unknown ]

  val get_reason_unknown : 'a t -> string
end

(** Given a formula phi and a list of objectives [o1,...,on], find the least
    bounding interval for each objective within the feasible region defined by
    the formula. *)
val optimize_box : ?context:z3_context ->
  'a context ->
  'a formula ->
  ('a arith_term) list ->
  [ `Sat of Interval.t list | `Unsat | `Unknown ]

(** Quantifier elimination *)
val qe : ?context:z3_context -> 'a context -> 'a formula -> 'a formula

(** Simplify a formula using Z3's routines.  The resulting formula is
    equisatisfiable, but not necessarily equivalent, to the original. *)
val simplify : ?context:z3_context -> 'a context -> 'a formula -> 'a formula

(** Parse a SMTLIB2-formatted string *)
val load_smtlib2 : ?context:z3_context -> 'a context -> string -> 'a formula

(** Sequence interpolation.  Returns either a model of the formula or a
    sequence of interpolants if there is no model.  *)
val interpolate_seq : ?context:z3_context ->
  'a context ->
  'a formula list ->
  [ `Sat of 'a interpretation | `Unsat of 'a formula list | `Unknown ]

(** Constrained Horn Clauses *)
module CHC : sig

  (** CHC solver *)
  type 'a solver

  val mk_solver : ?context:z3_context -> 'a context -> 'a solver

  (** Register a symbol as a relation in a system of constrained Horn clauses.
      Each relation should be registered before calling [check]. *)
  val register_relation : 'a solver -> symbol -> unit

  (** [add_rule solver hypothesis conclusion] adds the rule [hypothesis =>
      conclusion] to [solver]. *)
  val add_rule : 'a solver -> 'a formula -> 'a formula -> unit

  (** [add solver formulas] asserts that each formula in [formulas] holds.
      These formulas should not be CHCs. *)
  val add : 'a solver -> ('a formula) list -> unit

  val check : 'a solver -> [ `Sat | `Unsat | `Unknown ]
  val get_solution : 'a solver -> symbol -> 'a formula

  val to_string : 'a solver -> string
end

(** Constrained Horn clause solving via Z3's Fixedpoint interface (the
    Spacer engine), with refutation-witness extraction.

    This module is separate from (and unrelated to) the older {!CHC} module
    above.  A system of CHCs is built from {i relations} and {i rules}:

    - A relation of arity [n] is an srk symbol of type
      [`TyFun (arg_types, `TyBool)]; an {i atom} is a Bool-typed application
      [mk_app rel args] (which is an srk formula).  Relations must be
      registered ({!FixedpointChc.register_relation} /
      {!FixedpointChc.mk_relation}) before appearing in rules.
    - A rule [forall vars. body => head] is given as two srk formulas over
      ordinary {i constant symbols}; the engine quantifies the rule-local
      symbols itself.  The body must be {i positive}: registered relations
      may occur only as top-level conjunct atoms.

    Reachability of a relation is decided with {!FixedpointChc.query_relation};
    on [`Reachable] the answer carries a best-effort typed derivation
    (see {!FixedpointChc.step}); on [`Unreachable],
    {!FixedpointChc.get_solution} yields the inductive invariant certificate
    for each relation. *)
module FixedpointChc : sig

  (** CHC solver over Z3's Fixedpoint engine. *)
  type 'a t

  (** Result of a reachability query.  Note the vocabulary: [`Reachable]
      means the queried relation is non-empty (for an error relation: the
      program is {i unsafe}); [`Unreachable] means the CHC system has a
      solution in which the queried relation is empty (the program is
      {i safe}). *)
  type query_status = [ `Reachable | `Unreachable | `Unknown of string ]

  (** A ground relation fact appearing in a derivation, e.g. [R(0, 5)].
      [relation = None] means the fact's declaration is foreign (e.g. a
      Z3-generated auxiliary relation) and could not be mapped back to a
      registered srk relation; [fact_raw] is always the original Z3
      expression. *)
  type 'a relation_fact = {
    relation : symbol option;
    fact_args : (('a, typ_fo) expr) list;  (** [[]] if conversion failed *)
    fact_raw : z3_expr;
  }

  (** One hyper-resolution step of a refutation, i.e. one rule application
      in the derivation of the queried relation.  Steps are listed in
      derivation order: premises of a step are concluded by earlier steps.

      [conclusion] and [premises] are the reliable payload: they are ground
      facts whose relation declarations are ours.  [rule_name]/[valuation]
      are best-effort: they are populated when the step could be matched
      against a stored rule ([step_status = `Ok]), in which case [valuation]
      assigns a ground value to each of the rule's quantified symbols
      (array-typed symbols omitted).  When no stored rule matches,
      [step_status] is [`Failed reason] and the facts are still usable. *)
  type 'a step = {
    step_index : int;
    rule_name : string option;
    conclusion : 'a relation_fact;
    premises : 'a relation_fact list;
    valuation : (symbol * ('a, typ_fo) expr) list;
    step_raw_rule : z3_expr;
    step_status : [ `Ok | `Failed of string ];
  }

  type 'a query_answer = {
    status : query_status;
    raw_answer : z3_expr option;
    (** [Z3.Fixedpoint.get_answer], captured immediately after the query
        (Z3 keeps only the most recent answer). *)
    steps : 'a step list;
    (** Nonempty only for [`Reachable]; best effort, [[]] if the proof
        could not be walked. *)
  }

  (** Create a CHC solver.  Configures the Spacer engine and disables the
      slicing/inlining preprocessing passes (so refutation proofs cite
      rules recognizably close to the ones added). *)
  val mk_solver : ?context:z3_context -> 'a context -> 'a t

  (** [mk_relation solver ~name dom] creates a fresh symbol of type
      [`TyFun (dom, `TyBool)] and registers it as a relation. *)
  val mk_relation : 'a t -> ?name:string -> typ_fo list -> symbol

  (** Register an existing symbol of type [`TyFun (_, `TyBool)] as a
      relation.  Raises [Invalid_argument] on any other type. *)
  val register_relation : 'a t -> symbol -> unit

  (** [add_rule solver ~name ~vars ~body ~head ()] adds the rule
      [forall vars. body => head].

      [head] must be an application of a registered relation; any other
      head [h] (e.g. [mk_false srk]) is routed to the internal error
      relation, turning the rule into
      [body /\ not h => error_relation solver ()].

      [vars] lists the rule-local (universally quantified) symbols --
      typically pre-state, post-state and havoc symbols.  It is sanitized
      (deduplicated; restricted to first-order non-relation symbols that
      occur in the rule).  If omitted, it is inferred as {i all} such
      symbols, in symbol-id order; callers that know the intended variable
      set should pass it explicitly.

      Raises [Invalid_argument] if the body is not a positive Horn body
      (a registered relation occurring under negation/disjunction/ite or
      inside an atom argument), if an atom is ill-sorted w.r.t. its
      relation's declared domain, or if a query has already been issued. *)
  val add_rule : 'a t -> ?name:string -> ?vars:symbol list ->
    body:'a formula -> head:'a formula -> unit -> unit

  (** Assert background (non-CHC) facts. *)
  val add : 'a t -> 'a formula list -> unit

  (** The internal nullary relation concluded by rules whose head is not a
      registered relation atom (see {!add_rule}).  Query this symbol to
      check [body => false]-style rules. *)
  val error_relation : 'a t -> symbol

  (** Decide reachability of a registered relation.  Rules are frozen after
      the first query; multiple relations may be queried in sequence. *)
  val query_relation : 'a t -> symbol -> 'a query_answer

  (** After an [`Unreachable] query: the inductive-invariant certificate
      that Spacer computed for [rel], as a formula in which de Bruijn
      variable [i] refers to [rel]'s [i]-th argument.  Returns [mk_false]
      for relations that head no rule. *)
  val get_solution : 'a t -> symbol -> 'a formula

  (** Print the registered CHC system in srk syntax (one rule per line,
      with the caller's symbol names).  More readable than {!to_string},
      which shows Z3's internal rendering. *)
  val pp_rules : Format.formatter -> 'a t -> unit

  (** Print a ground relation fact, e.g. [p(101, 91)]; foreign facts are
      shown as their raw Z3 expression. *)
  val pp_fact : 'a t -> Format.formatter -> 'a relation_fact -> unit

  (** Print one derivation step: index, rule name (if identified),
      conclusion, premises, and valuation (or failure reason). *)
  val pp_step : 'a t -> Format.formatter -> 'a step -> unit

  (** Print a derivation, one step per line, in derivation order. *)
  val pp_derivation : 'a t -> Format.formatter -> 'a step list -> unit

  val to_string : 'a t -> string
end

(** Interface to {{:https://github.com/Z3Prover/z3} Z3} SMT solver *)
open Syntax
open Interpretation

type z3_context = Z3.context
type z3_expr = Z3.Expr.expr
type z3_func_decl = Z3.FuncDecl.func_decl

type 'a open_expr = [
  | `Real of QQ.t
  | `App of z3_func_decl * 'a list
  | `Var of int * typ_fo
  | `Add of 'a list
  | `Mul of 'a list
  | `Binop of [ `Div | `Mod ] * 'a * 'a
  | `Unop of [ `Floor | `Neg ] * 'a
  | `Tru
  | `Fls
  | `And of 'a list
  | `Or of 'a list
  | `Not of 'a
  | `Ite of 'a * 'a * 'a
  | `Quantify of [`Exists | `Forall] * string * typ_fo * 'a
  | `Atom of [`Eq | `Leq | `Lt] * 'a * 'a
]

val z3_of_term : 'a context -> z3_context -> 'a term -> z3_expr
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
  val add : 'a t -> ('a formula) list -> unit
  val push : 'a t -> unit
  val pop : 'a t -> int -> unit
  val reset : 'a t -> unit
  val check : 'a t -> ('a formula) list -> [ `Sat | `Unsat | `Unknown ]
  val to_string : 'a t -> string
    
  (** Compute a model of a solver's context.  The model is abstract -- it can
      be used to evaluate terms, but its bindings may not be enumerated (see
      [Interpretation] for more detail). *)
  val get_model : ?symbols:(symbol list) ->
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

val mk_solver : ?context:z3_context -> ?theory:string -> 'a context -> 'a Solver.t

(** Given a formula phi and a list of objectives [o1,...,on], find the least
    bounding interval for each objective within the feasible region defined by
    the formula. *)
val optimize_box : ?context:z3_context ->
  'a context ->
  'a formula ->
  ('a term) list ->
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

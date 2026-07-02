(** Common interface for SMT solvers *)
open Syntax
open Interpretation

module StdSolver : sig
  type 'a t
  val make : ?context:SrkZ3.z3_context -> ?theory:string -> 'a context -> 'a t
  val add : 'a t -> ('a formula) list -> unit
  val push : 'a t -> unit
  val pop : 'a t -> int -> unit
  val reset : 'a t -> unit
  val check : ?assumptions:('a formula list) -> 'a t -> [ `Sat | `Unsat | `Unknown ]
  val to_string : 'a t -> string
  val get_model : ?symbols:(symbol list) ->
    ?assumptions:('a formula list) ->
    'a t ->
    [ `Sat of 'a interpretation
    | `Unsat
    | `Unknown ]
  val get_concrete_model : 'a t ->
    symbol list ->
    [ `Sat of 'a interpretation
    | `Unsat
    | `Unknown ]
  val get_unsat_core : 'a t ->
    ('a formula) list ->
    [ `Sat | `Unsat of ('a formula) list | `Unknown ]
end

module Model : sig
  type 'a t
  val sat : 'a t -> 'a formula -> bool
  val sign : 'a t -> 'a arith_term -> [ `Zero | `Pos | `Neg | `Unknown ]
end

module Solver : sig
  type 'a t
  val make : 'a context -> 'a t
  val add : 'a t -> 'a formula list -> unit
  val check : ?assumptions:('a formula list) -> 'a t -> [ `Sat | `Unsat | `Unknown ]
  val get_model : 'a t -> [ `Sat of 'a Model.t | `Unsat | `Unknown ]
  val push : 'a t -> unit
  val pop : 'a t -> int -> unit
end

(** Constrained Horn clause solving via Z3's Fixedpoint interface (Spacer),
    with refutation-witness extraction.  This is a thin wrapper around
    {!SrkZ3.FixedpointChc} -- see that module's documentation for the CHC
    conventions (relations are [`TyFun (_, `TyBool)] symbols; rules are
    formulas over constants; bodies must be positive) and for the record
    fields of {!SrkZ3.FixedpointChc.query_answer} /
    {!SrkZ3.FixedpointChc.step}.

    Note: CHC solving is Z3-backed regardless of the context's theory
    (unlike {!Solver.make}, there is no LIRR backend). *)
module ChcSolver : sig
  type 'a t
  type query_status = SrkZ3.FixedpointChc.query_status
  type 'a relation_fact = 'a SrkZ3.FixedpointChc.relation_fact
  type 'a step = 'a SrkZ3.FixedpointChc.step
  type 'a query_answer = 'a SrkZ3.FixedpointChc.query_answer

  val make : ?context:SrkZ3.z3_context -> 'a context -> 'a t
  val mk_relation : 'a t -> ?name:string -> typ_fo list -> symbol
  val register_relation : 'a t -> symbol -> unit
  val add_rule : 'a t -> ?name:string -> ?vars:symbol list ->
    body:'a formula -> head:'a formula -> unit -> unit
  val add : 'a t -> 'a formula list -> unit
  val error_relation : 'a t -> symbol
  val query_relation : 'a t -> symbol -> 'a query_answer
  val get_solution : 'a t -> symbol -> 'a formula
  val pp_rules : Format.formatter -> 'a t -> unit
  val pp_fact : 'a t -> Format.formatter -> 'a relation_fact -> unit
  val pp_step : 'a t -> Format.formatter -> 'a step -> unit
  val pp_derivation : 'a t -> Format.formatter -> 'a step list -> unit
  val to_string : 'a t -> string
end

(** Compute a model of a formula.  The model is abstract -- it can be used to
    evaluate terms, but its bindings may not be enumerated (see
    [Interpretation] for more detail). *)
val get_model : ?symbols:(symbol list) ->
  'a context ->
  'a formula ->
  [ `Sat of 'a interpretation
  | `Unsat
  | `Unknown ]

(** Compute a model of a formula, and return an intepretation that binds the
    specified subset of symbols.  If the symbol list contains all symbols of
    the formula, then the interpretation is a model of the formula. *)
val get_concrete_model : 'a context ->
  symbol list ->
  'a formula ->
  [ `Sat of 'a interpretation
  | `Unsat
  | `Unknown ]

val is_sat : 'a context -> 'a formula -> [ `Sat | `Unsat | `Unknown ]

val entails : 'a context -> 'a formula -> 'a formula -> [`Yes | `No | `Unknown]

val equiv : 'a context -> 'a formula -> 'a formula -> [`Yes | `No | `Unknown]

(** Given an a model [m] and a formula [phi] such that [m |= phi], attempt to
    compute a new interpretation [m'] such that [m' |= phi], [m(x) = m'(x)]
    for all constant symbols and non-real functions, and for all real
    functions [f], [m'(f)] is affine.  Return [`Unsat] if there is no such
    [m'], or [`Unknown] if the status of the associated SMT query could not be
    determined. *)
val affine_interpretation : 'a context ->
  'a interpretation ->
  'a formula ->
  [ `Sat of 'a interpretation | `Unsat | `Unknown ]

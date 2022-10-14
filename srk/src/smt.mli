(** Common interface for SMT solvers *)
open Syntax
open Interpretation

module Solver : sig
  type 'a t
  val add : 'a t -> ('a formula) list -> unit
  val push : 'a t -> unit
  val pop : 'a t -> int -> unit
  val reset : 'a t -> unit
  val check : 'a t -> ('a formula) list -> [ `Sat | `Unsat | `Unknown ]
  val to_string : 'a t -> string
  val get_model : ?symbols:(symbol list) ->
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
  val get_unsat_core_or_concrete_model : 'a t -> ('a formula) list -> symbol list -> 
    [ `Sat of 'a interpretation 
      | `Unsat of ('a formula) list 
      | `Unknown ]
end

val mk_solver : ?theory:string -> 'a context -> 'a Solver.t

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
val get_concrete_model : 'a context -> ?solver:'a Solver.t -> symbol list -> 'a formula -> 
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

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
end

val mk_solver : ?theory:string -> 'a context -> 'a Solver.t

val get_model : ?symbols:(symbol list) ->
  'a context ->
  'a formula ->
  [ `Sat of 'a interpretation
  | `Unsat
  | `Unknown ]

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

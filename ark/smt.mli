(** Common interface for SMT solvers *)
open Syntax

val mk_solver : ?theory:string -> 'a context -> 'a smt_solver

val get_model : 'a context -> 'a formula -> [ `Sat of 'a smt_model
                                            | `Unsat
                                            | `Unknown ]

val is_sat : 'a context -> 'a formula -> [ `Sat | `Unsat | `Unknown ]

val entails : 'a context -> ?theory:string -> 'a formula -> 'a formula -> [`Yes | `No | `Unknown]

(** Set the default solver to be used by [mk_solver] (and thus the rest of the
    functions in this module. *)
val set_default_solver : [ `Z3 | `Mathsat ] -> unit

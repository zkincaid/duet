(** Common interface for SMT solvers *)
open Syntax

val mk_solver : ?theory:string -> 'a context -> 'a smt_solver

val get_model : 'a context -> 'a formula -> [ `Sat of 'a smt_model
                                            | `Unsat
                                            | `Unknown ]

val is_sat : 'a context -> 'a formula -> [ `Sat | `Unsat | `Unknown ]

val entails : 'a context -> 'a formula -> 'a formula -> [`Yes | `No | `Unknown]

val equiv : 'a context -> 'a formula -> 'a formula -> [`Yes | `No | `Unknown]

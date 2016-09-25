open Syntax

val mk_solver : 'a context -> 'a smt_solver

val get_model : 'a context -> 'a formula -> [ `Sat of 'a smt_model
                                            | `Unsat
                                            | `Unknown ]

val is_sat : 'a context -> 'a formula -> [ `Sat | `Unsat | `Unknown ]

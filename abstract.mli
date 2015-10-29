open Syntax
open Smt

exception Nonlinear

val affine_hull : 'a smt_context -> 'a formula -> const_sym list -> 'a term list

val boxify : 'a smt_context -> 'a formula -> 'a term list -> 'a formula

(** Alternating quantifier satisfiability *)
val aqsat : 'a smt_context -> 'a formula -> [ `Sat | `Unsat | `Unknown ]

(** Alternating quantifier optimization *)
val aqopt : 'a smt_context -> 'a formula -> 'a term -> [ `Sat of Interval.t
                                                       | `Unsat
                                                       | `Unknown ]

(** Quantifier eliminiation via model-based projection *)
val qe_mbp : 'a smt_context -> 'a formula -> 'a formula

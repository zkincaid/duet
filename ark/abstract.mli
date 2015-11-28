open Syntax
open Smt

exception Nonlinear

val affine_hull : 'a smt_context -> 'a formula -> symbol list -> 'a term list

val boxify : 'a smt_context -> 'a formula -> 'a term list -> 'a formula

(** Alternating quantifier satisfiability *)
val aqsat : 'a smt_context -> 'a formula -> [ `Sat | `Unsat | `Unknown ]

(** Alternating quantifier satisfiability *)
val aqsat_forward : 'a smt_context -> 'a formula -> [ `Sat | `Unsat | `Unknown ]

(** Alternating quantifier optimization *)
val maximize : 'a smt_context -> 'a formula -> 'a term -> [ `Bounded of QQ.t
                                                          | `Infinity
                                                          | `MinusInfinity
                                                          | `Unknown ]

(** Quantifier eliminiation via model-based projection *)
val qe_mbp : 'a smt_context -> 'a formula -> 'a formula

(** Alternating quantifier satisfiability *)
val easy_sat : 'a smt_context -> 'a formula -> [ `Sat | `Unsat | `Unknown ]

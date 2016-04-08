open Syntax
open Smt

(** Satisfiability via strategy improvement *)
val simsat : 'a smt_context -> 'a formula -> [ `Sat | `Unsat | `Unknown ]

(** Satisfiability via strategy improvement, forwards version *)
val simsat_forward : 'a smt_context -> 'a formula -> [ `Sat
                                                     | `Unsat
                                                     | `Unknown ]

(** Alternating quantifier optimization *)
val maximize : 'a smt_context -> 'a formula -> 'a term -> [ `Bounded of QQ.t
                                                          | `Infinity
                                                          | `MinusInfinity
                                                          | `Unknown ]

(** Quantifier eliminiation via model-based projection *)
val qe_mbp : 'a smt_context -> 'a formula -> 'a formula

(** Alternating quantifier satisfiability *)
val easy_sat : 'a smt_context -> 'a formula -> [ `Sat | `Unsat | `Unknown ]

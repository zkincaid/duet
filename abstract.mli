open Syntax
open Smt

module Interpretation : sig
  type 'a interpretation
  val pp : Format.formatter -> 'a interpretation -> unit
  val empty : 'a context -> 'a interpretation
  val add_real : symbol -> QQ.t -> 'a interpretation -> 'a interpretation
  val add_bool : symbol -> bool -> 'a interpretation -> 'a interpretation
  val real : 'a interpretation -> symbol -> QQ.t
  val bool : 'a interpretation -> symbol -> bool
  val value : 'a interpretation -> symbol -> [`Real of QQ.t | `Bool of bool]
  val of_model : 'a context -> 'a smt_model -> symbol list -> 'a interpretation
  val enum : 'a interpretation ->
    (symbol * [`Real of QQ.t | `Bool of bool]) BatEnum.t
  val substitute : 'a interpretation -> ('a,'typ) expr -> ('a,'typ) expr
end

val affine_hull : 'a smt_context -> 'a formula -> symbol list -> 'a term list

val boxify : 'a smt_context -> 'a formula -> 'a term list -> 'a formula

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

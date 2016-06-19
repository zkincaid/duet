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

type 'a strategy =
    Strategy of ('a formula * ('a,typ_fo) expr * 'a strategy) list

type quantifier_prefix = ([`Forall | `Exists] * symbol) list

val pp_strategy : 'a context -> Format.formatter -> 'a strategy -> unit

val show_strategy : 'a context -> 'a strategy -> string

(** Compute a winning SAT/UNSAT strategy for a formula.  The formula is
    represented in prenex form (quantifier prefix + matrix). *)
val winning_strategy : 'a smt_context -> quantifier_prefix -> 'a formula ->
  [ `Sat of 'a strategy
  | `Unsat of 'a strategy
  | `Unknown ]

(** Verify that a SAT strategy is in fact a winning strategy.  (To verify an
    UNSAT strategy, just negate the formula & quantifier prefix) *)
val check_strategy : 'a smt_context -> quantifier_prefix -> 'a formula ->
  'a strategy -> bool

val normalize : 'a context -> 'a formula -> quantifier_prefix * 'a formula

type skeleton

val pp_skeleton : 'a context -> Format.formatter -> skeleton -> unit

val destruct_skeleton : 'a context -> skeleton ->
  [ `Forall of symbol * symbol * skeleton
  | `Exists of symbol * (('a,typ_fo) expr * skeleton) list
  | `Empty ]

(** Desruct a skeleton by extracting the first *block* of quantifiers (maximal
    contiguous sequence of existential or universal quantifiers *)
val destruct_skeleton_block : 'a context -> skeleton ->
  [ `Forall of (symbol * symbol) list * skeleton
  | `Exists of ((symbol * ('a,typ_fo) expr) list * skeleton) list
  | `Empty ]

(** Compute a winning strategy for either the SAT player or the UNSAT
    player *)
val winning_skeleton : 'a smt_context -> quantifier_prefix -> 'a formula ->
  [ `Sat of skeleton
  | `Unsat of skeleton
  | `Unknown ]

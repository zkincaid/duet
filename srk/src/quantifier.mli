open Syntax
open Interpretation

(** Satisfiability via strategy improvement *)
val simsat : 'a context -> 'a formula -> [ `Sat | `Unsat | `Unknown ]

(** Satisfiability via strategy improvement, forwards version *)
val simsat_forward : 'a context -> 'a formula -> [ `Sat
                                                 | `Unsat
                                                 | `Unknown ]

(** Alternating quantifier optimization *)
val maximize : 'a context -> 'a formula -> 'a arith_term -> [ `Bounded of QQ.t
                                                            | `Infinity
                                                            | `MinusInfinity
                                                            | `Unknown ]

(** Quantifier eliminiation via model-based projection *)
val qe_mbp : 'a context -> 'a formula -> 'a formula

(** Model-based projection.  If [dnf] option is set, convert to
   disjunctive normal form. *)
val mbp : ?dnf:bool -> 'a context -> (symbol -> bool) -> 'a formula -> 'a formula

(** Over-approximtate model-based projection.  If [dnf] option is set,
   convert to disjunctive normal form. *)
val mbp_cover : ?dnf:bool -> 'a context -> (symbol -> bool) -> 'a formula -> 'a formula

(** Alternating quantifier satisfiability *)
val easy_sat : 'a context -> 'a formula -> [ `Sat | `Unsat | `Unknown ]

type 'a strategy

type quantifier_prefix = ([`Forall | `Exists] * symbol) list

val pp_strategy : 'a context -> Format.formatter -> 'a strategy -> unit

val show_strategy : 'a context -> 'a strategy -> string

(** Pushes quantifiers further into expression tree. Does not preserve 
 * quantifier ordering. May eliminate unused quantifiers.*)
val miniscope : 'a context -> 'a formula -> 'a formula

(** Compute a winning SAT/UNSAT strategy for a formula.  The formula is
    represented in prenex form (quantifier prefix + matrix). *)
val winning_strategy : 'a context -> quantifier_prefix -> 'a formula ->
  [ `Sat of 'a strategy
  | `Unsat of 'a strategy
  | `Unknown ]

(** Verify that a SAT strategy is in fact a winning strategy.  (To verify an
    UNSAT strategy, just negate the formula & quantifier prefix) *)
val check_strategy : 'a context -> quantifier_prefix -> 'a formula ->
  'a strategy -> bool

(** Write a formula in prenex normal form, using constant symbols instead of
    variables. *)
val normalize : 'a context -> 'a formula -> quantifier_prefix * 'a formula

val is_presburger_atom : 'a context -> 'a formula -> bool

(** Given an interpretation [M], a conjunctive formula [cube] such
   that [M |= cube], and a predicate [p], find a cube [cube']
   expressed over symbols that satisfy [p] such that [M |= cube' |=
   cube].  [local_project_cube] has a finite image in the sense that
   for any cube [c], the set [{ local_project_cube srk p m c : m |= c
   }] is finite.  [local_project_cube] assumes a formula in [QF_LRA];
   if not, then [cube'] may not entail [cube], but it is guaranteed to
   be satisfied by [M]. *)
val local_project_cube : 'a context ->
  (symbol -> bool) ->
  'a interpretation ->
  'a formula list ->
  'a formula list

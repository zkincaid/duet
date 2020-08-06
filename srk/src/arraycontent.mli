open Syntax
open Iteration
module V = Linear.QQVector
module M = Linear.QQMatrix
module Z = Linear.ZZVector

(* converts a positive monic flat array formula to an
 * equivalent monic flat array formula as a quantifier prefix list
 * together with a matrix *)

(* takes in quantifier prefix and formula; attaches prefix.
 * Does not do any renaming/attempts to avoid capture *)

(* converts monic flat array to equiv lia formula; 
 * TODO check for types for arr;, make sure quants have right type; fix
 * types in general *)

val to_mfa : 'a context -> 'a formula -> 'a formula
 
val mfa_to_lia : 'a context -> 'a formula -> 'a formula

(*val projection : 'a context ->'a formula -> Symbol.Set.t -> 'a t*)

val mbp_qe : 'a context -> 'a formula -> 'a formula


(** Projects array trans. formula to lia trans formula at symbolic dimension.
    Return is tuple containing:
      projection index sym, primed and unprimed version,
      mapping from array symbol to its lia symbol
      lia trans. symbols and formula *)
val projection :  'a context ->
           'a formula ->
           (symbol * symbol) list ->
           (symbol * symbol) *
           (symbol, symbol) Hashtbl.t *
           ((symbol * symbol) list * 'a formula)

val is_eq_projs : 
  'a Syntax.context -> 
  'a Syntax.formula -> 
  'a Syntax.formula ->
  (Syntax.symbol * Syntax.symbol) list -> 
  [ `No | `Unknown | `Yes ]

module Array_analysis (Iter : PreDomain) : PreDomain
 

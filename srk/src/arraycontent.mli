open Syntax
open Iteration
module V = Linear.QQVector
module M = Linear.QQMatrix
module Z = Linear.ZZVector

type 'a t = 'a formula

type qfp =  [ `Exists of string * Syntax.typ_fo
            | `Forall of string * Syntax.typ_fo] list

(* converts a positive monic flat array formula to an
 * equivalent monic flat array formula as a quantifier prefix list
 * together with a matrix *)
val to_mfa : 'a context -> 'a formula -> qfp * 'a t

(* takes in quantifier prefix and formula; attaches prefix.
 * Does not do any renaming/attempts to avoid capture *)
val add_prefix : 'a context -> qfp * 'a t -> 'a t

(* converts monic flat array to equiv lia formula; 
 * TODO check for types for arr;, make sure quants have right type; fix
 * types in general *)
val mfa_to_lia : 'a context -> (qfp * 'a formula) -> Symbol.Set.t -> 'a t

(*val projection : 'a context ->'a formula -> Symbol.Set.t -> 'a t*)


module Array_analysis (Iter : PreDomain) : PreDomain
  with type 'a t = 'a formula

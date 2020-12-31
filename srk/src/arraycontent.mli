open Syntax
open Iteration
module V = Linear.QQVector
module M = Linear.QQMatrix
module Z = Linear.ZZVector
module T = TransitionFormula

(* converts a positive monic flat array formula to an
 * equivalent monic flat array formula as a quantifier prefix list
 * together with a matrix *)

(* takes in quantifier prefix and formula; attaches prefix.
 * Does not do any renaming/attempts to avoid capture *)

(* converts monic flat array to equiv lia formula; 
 * TODO check for types for arr;, make sure quants have right type; fix
 * types in general *)


val pmfa_to_lia : 'a context -> 'a T.t -> 'a T.t

val eliminate_stores : 'a context -> 'a formula -> 'a formula

(*val projection : 'a context ->'a formula -> Symbol.Set.t -> 'a t*)

(** Projects array trans. formula to lia trans formula at symbolic dimension.
    Return is tuple containing:
      projection index sym, primed and unprimed version,
      mapping from array symbol to its lia symbol
      lia trans. symbols and formula *)
val projection :  
  'a context -> 'a T.t -> symbol * (symbol, symbol) Hashtbl.t * 'a T.t

module Array_analysis (Iter : PreDomain) : sig
  include PreDomain
end

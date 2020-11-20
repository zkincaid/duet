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

(* Bidirectional Hashtbl *)
module Bitbl : sig
  type ('a, 'b) t
  val create : int -> ('a, 'b) t
  val mem : ('a, 'b) t -> 'a -> bool
  val rev_mem : ('a, 'b) t -> 'b -> bool
  val add : ('a, 'b) t -> 'a -> 'b -> unit
  val find : ('a, 'b) t -> 'a -> 'b
  val rev_find : ('a, 'b) t -> 'b -> 'a
end



val to_mfa : 'a context -> 'a T.t -> 'a formula
 
val mfa_to_lia : 'a context -> 'a formula -> (Syntax.symbol * Syntax.symbol) list -> 'a formula




(*val projection : 'a context ->'a formula -> Symbol.Set.t -> 'a t*)

val mbp_qe : ?flag:bool -> 'a context -> 'a formula -> bool -> 'a formula * symbol list


(** Projects array trans. formula to lia trans formula at symbolic dimension.
    Return is tuple containing:
      projection index sym, primed and unprimed version,
      mapping from array symbol to its lia symbol
      lia trans. symbols and formula *)
val projection :  
  'a context -> 'a T.t -> symbol * (symbol, symbol) Hashtbl.t * 'a T.t

val lift : 'a context -> (symbol * symbol) -> (symbol, symbol) Hashtbl.t -> 
  'a formula -> 'a formula

module Array_analysis (Iter : PreDomain) : sig
  include PreDomain
end

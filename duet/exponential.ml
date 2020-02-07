(** Implements the exponential domain where the base (codomain) is some APRON
    numerical domain, and the exponent (domain) is some predicate abstraction
    domain. *)

open Core
open Srk
open Apak

(* Set of predicates *)
module Pred = struct
  type t = bexpr [@@deriving show,ord]
end
module PSet = Putil.Set.Make(Pred)

module Make
    (Man : sig
       val predicates : AP.Set.t -> PSet.t
     end) =
struct
  module AI = Ai.ApronInterpretation

  include Lattice.FunctionSpace.Total.Make(PSet)(AI)

  let add k v f = update k (AI.join v (eval f k)) f

  let add_val preds v f =
    if AI.is_bottom v then f else begin
      let add_true p st =
        if AI.assert_true p v then PSet.add p st else st
      in
      let st = PSet.fold add_true preds PSet.empty in
      add st v f
    end

  let project func aps =
    let preds = Man.predicates aps in
    let f map (st, av) = add (PSet.inter st preds) (AI.project av aps) map in
    BatEnum.fold f (const (AI.project (default func) aps)) (enum func)

  let top aps =
    let preds = Man.predicates aps in
    add_val preds (AI.top aps) (const (AI.bottom aps))

  let bottom aps = const (AI.bottom aps)

  let widen = merge AI.widen

  let is_bottom func =
    BatEnum.is_empty (enum func) && AI.is_bottom (default func)

  let name = "Power APRON"

  let transfer def func =
    let default = AI.inject (default func) (Def.get_defs def) in
    let aps = AI.get_domain default in
    let preds = Man.predicates aps in
    let f func (_, av) = add_val preds (AI.transfer def av) func in
    BatEnum.fold f (const default) (enum func)

  let assert_true bexpr func =
    let p (_, av) = AI.assert_true bexpr av in
    BatEnum.for_all p (enum func)

  let assert_memsafe expr func =
    let p (_, av) = AI.assert_memsafe expr av in
    BatEnum.for_all p (enum func)

  let cyl func _aps =
    let aps = AI.get_domain (default func) in
    let preds = Man.predicates aps in
    let f func (_, av) = add_val preds (AI.cyl av aps) func in
    BatEnum.fold f (const (AI.cyl (default func) aps)) (enum func)

  let inject func aps =
    let default = AI.inject (default func) aps in
    let aps = AI.get_domain default in
    let preds = Man.predicates aps in
    let f func (_, av) = add_val preds (AI.inject av aps) func in
    BatEnum.fold f (const default) (enum func)

  let rename func rename =
    let map =
      List.fold_left (fun m (k,v) -> AP.Map.add k v m) AP.Map.empty rename
    in
    let rnm x =
      try AP.Map.find x map
      with Not_found -> x
    in
    let rename_st = PSet.map (Bexpr.subst_ap rnm) in
    let f func (st, av) = add (rename_st st) (AI.rename av rename) func in
    BatEnum.fold f (const (AI.rename (default func) rename)) (enum func)

  let meet f g =
    let add func ((st1, v1), (st2, v2)) =
      add (PSet.union st1 st2) (AI.meet v1 v2) func
    in
    let default = AI.meet (default f) (default g) in
    (SrkUtil.cartesian_product (enum f) (enum g))
    |> BatEnum.fold add (const default)
end




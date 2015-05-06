open Core
open Apak

module type FlowGraph = sig
  include Graph.Sig.I
  val is_initial : V.t -> t -> bool
  val is_terminal : V.t -> t -> bool
  val enum_initial : t -> V.t BatEnum.t
  val enum_terminal : t -> V.t BatEnum.t
  val clone : (V.t -> V.t) -> t -> t
end

module MakeFG (G : Graph.Sig.I) : FlowGraph with type t = G.t
                                             and module V = G.V
                                             and module E = G.E

module Pack : sig
  type pair
  module SetMap : (Map.S with type key = AP.Set.t)
  module PowerSet : Putil.Set.S with type elt = AP.Set.t
  module PairSet : Putil.Set.S with type elt = pair
  val fst : pair -> AP.t
  val snd : pair -> AP.t
  val project_fst : PairSet.t -> AP.Set.t
  val project_snd : PairSet.t -> AP.Set.t
  val mk_pair : AP.t -> AP.t -> pair
end

module G : sig
  include FlowGraph with type V.t = Def.t
                     and type E.label = Pack.PairSet.t
  val group_pred : V.t -> t -> (V.t -> 'a) -> 'a ->
    (AP.Set.t -> 'a -> 'a -> 'a) ->
    'a Pack.SetMap.t
  val edge_label : E.t -> Pack.PairSet.t
  val inputs : t -> V.t -> Pack.PowerSet.t
  val outputs : t -> V.t -> Pack.PowerSet.t
  val domain : t -> V.t -> AP.Set.t
  val codomain : t -> V.t -> AP.Set.t
  val sanity_check : t -> unit
  val minimize : t -> t
  val display_labelled : t -> unit (** Display with edge labels *)
end

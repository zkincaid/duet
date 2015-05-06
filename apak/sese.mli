(** Compute single-entry single-exit regions of a control flow graph. *)
module type G = sig
  type t
  module V : Graph.Sig.VERTEX
  module E : Graph.Sig.EDGE with type vertex = V.t
  val fold_vertex : (V.t -> 'a -> 'a) -> t  -> 'a -> 'a
  val fold_edges_e : (E.t -> 'a -> 'a) -> t -> 'a -> 'a
  val fold_edges : (V.t -> V.t -> 'a -> 'a) -> t -> 'a -> 'a
  val fold_succ : (V.t -> 'a -> 'a) -> t -> V.t -> 'a -> 'a
  val fold_pred : (V.t -> 'a -> 'a) -> t -> V.t -> 'a -> 'a
  val nb_vertex : t -> int
  val mem_vertex : t -> V.t -> bool
end

module Make(H : G) : sig
  include RecGraph.S with type atom = H.V.t
                      and type Block.t = int
                      and type ('a, 'b) typ = ('a, 'b) RecGraph.seq_typ
                      and type G.V.t = (H.V.t, int) RecGraph.seq_typ

  (** [construct g en ex] constructs a recursive graph structurally identical
      to [g] and where the blocks are the single-entry single-exit regions of
      [g].  This procedure assumes that [en] is the initial vertex of [g], and
      every vertex in [g] is reachable from [en].  The top-level graph is at
      block 0. *)
  val construct : H.t -> entry:(H.V.t) -> exit:H.V.t -> t

  (** Augment an SESE graph with linear regions (maximal straight-line SESE
      regions).  Linear regions are a generalization of basic blocks, where
      canonical SESE regions are treated like atomic instructions. *)
  val mk_linear_regions : t -> t

  (** Fold over the vertices of a graph, where the order is an "inside-out"
      ordering: for any SESE region with entry [n] and exit [x], the vertices
      internal to the region are traversed before [n] and [x]. *)
  val fold_sese : (H.V.t -> 'a -> 'a) -> H.t -> H.V.t -> 'a -> 'a

  (** Compute a map from vertices to their closest enclosing SESE region
      ([None] if the given vertex isn't inside any SESE region). *)
  val block : t -> H.V.t -> Block.t option

  (** Display the structure of a SESE graph.  Should only be used for
      debugging. *)
  val display : t -> unit
end

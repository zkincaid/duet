(** Useful operations on graphs *)

val display_dot : (out_channel -> 'a -> unit) -> 'a -> unit

module type G = sig
  include Graph.Sig.G
  val vertices : t -> V.t BatEnum.t
  val edges : t -> (V.t * V.t) BatEnum.t
  val edges_e : t -> E.t BatEnum.t
  val enum_succ : t -> V.t -> V.t BatEnum.t
  val enum_succ_e : t -> V.t -> E.t BatEnum.t
  val enum_pred : t -> V.t -> V.t BatEnum.t
  val enum_pred_e : t -> V.t -> E.t BatEnum.t
end

module type P = sig
  include G
  val empty : t
  val add_vertex : t -> vertex -> t
  val remove_vertex : t -> vertex -> t
  val add_edge : t -> vertex -> vertex -> t
  val add_edge_e : t -> edge -> t
  val remove_edge : t -> vertex -> vertex -> t
  val remove_edge_e : t -> edge -> t
  val union : t -> t -> t
  val intersect : t -> t -> t
end

module type I = sig
  include G
  val create : ?size:int -> unit -> t
  val clear : t -> unit
  val copy : t -> t
  val add_vertex : t -> vertex -> unit
  val remove_vertex : t -> vertex -> unit
  val add_edge : t -> vertex -> vertex -> unit
  val add_edge_e : t -> edge -> unit
  val remove_edge : t -> vertex -> vertex -> unit
  val remove_edge_e : t -> edge -> unit
end

module type Vertex = sig
  type t
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val hash : t -> int
  module HT : BatHashtbl.S with type key = t
  module Map : Putil.Map.S with type key = t
  module Set : Putil.Hashed.Set.S with type elt = t
end

module Persistent : sig
  module Digraph : sig
    module Make
      (V : Vertex) :
      P with type V.t = V.t
	and type V.label = V.t
	and type E.t = V.t * V.t
	and type E.label = unit
    module MakeLabeled
      (V : Vertex)
      (E : Graph.Sig.ORDERED_TYPE_DFT) :
      P with type V.t = V.t
	and type V.label = V.t
	and type E.t = V.t * E.t * V.t
	and type E.label = E.t
    module MakeBidirectional
      (V : Vertex) :
      P with type V.t = V.t
	and type V.label = V.t
	and type E.t = V.t * V.t
	and type E.label = unit
    module MakeBidirectionalLabeled
      (V : Vertex)
      (E : Graph.Sig.ORDERED_TYPE_DFT) :
      P with type V.t = V.t
	and type V.label = V.t
	and type E.t = V.t * E.t * V.t
	and type E.label = E.t
  end
end

module Imperative : sig
  module Digraph : sig
    module Make
      (V : Vertex) :
      I with type V.t = V.t
	and type V.label = V.t
	and type E.t = V.t * V.t
	and type E.label = unit
    module MakeLabeled
      (V : Vertex)
      (E : Graph.Sig.ORDERED_TYPE_DFT) :
      I with type V.t = V.t
	and type V.label = V.t
	and type E.t = V.t * E.t * V.t
	and type E.label = E.t
    module MakeBidirectional
      (V : Vertex) :
      I with type V.t = V.t
	and type V.label = V.t
	and type E.t = V.t * V.t
	and type E.label = unit
    module MakeBidirectionalLabeled
      (V : Vertex)
      (E : Graph.Sig.ORDERED_TYPE_DFT) :
      I with type V.t = V.t
	and type V.label = V.t
	and type E.t = V.t * E.t * V.t
	and type E.label = E.t
  end
end

module ForgetDirection(G : Graph.Sig.G) :
  (Graph.Sig.G with type t = G.t
	       and type V.t = G.V.t
	       and type E.t = G.E.t)

module Reverse(G : Graph.Sig.G) :
  (Graph.Sig.G with type t = G.t
	       and type V.t = G.V.t
	       and type E.t = G.E.t)

module Subgraph(G : Graph.Sig.G) :
  (Graph.Sig.G with type t = G.t * (G.V.t -> bool)
	       and type V.t = G.V.t
	       and type E.t = G.E.t)


type edge_type = TreeEdge | BackEdge | CrossEdge | ForwardEdge

module DfsTree : sig
  module type G = sig
    type t
    module V : Graph.Sig.VERTEX
    module E : Graph.Sig.EDGE with type vertex = V.t
    val iter_succ : (V.t -> unit) -> t -> V.t -> unit
    val fold_succ : (V.t -> 'a -> 'a) -> t -> V.t -> 'a -> 'a
    val nb_vertex : t -> int
    val find_edge : t -> V.t -> V.t -> E.t
    val is_directed : bool
    val iter_edges_e : (E.t -> unit) -> t -> unit
    val iter_vertex : (V.t -> unit) -> t -> unit
  end
  module Make (G : G) : sig
    type t
    val compute : G.t -> G.V.t -> t

    val size : t -> int
    val get_dfs_num : G.V.t -> t -> int
    val fold_dfs_tree : (G.V.t -> 'a list -> 'a) -> t -> 'a
    val is_ancestor : G.V.t -> G.V.t -> t -> bool
    val is_root : G.V.t -> t -> bool
    val parent : G.V.t -> t -> G.V.t option
    val classify : G.V.t -> G.V.t -> t -> edge_type
    val iter_dfs_order :
      ?pre:(G.V.t -> unit) -> ?post:(G.V.t -> unit) -> t -> unit
    val fold_tree_succ :
      (G.V.t -> 'a -> 'a) -> G.t -> t -> G.V.t -> 'a -> 'a
    val fold_nontree_succ :
      (G.V.t -> 'a -> 'a) -> G.t -> t -> G.V.t -> 'a -> 'a
    val fold_backedges :
      (G.V.t -> 'a -> 'a) -> G.t -> t -> G.V.t -> 'a -> 'a
    val fold_forward_edges :
      (G.V.t -> 'a -> 'a) -> G.t -> t -> G.V.t -> 'a -> 'a
    val fold_crossedges :
      (G.V.t -> 'a -> 'a) -> G.t -> t -> G.V.t -> 'a -> 'a
    val fold_edges_dfs_order :
      ('a -> G.V.t -> G.V.t -> 'a) -> 'a -> G.t -> t -> 'a
    val vertices : t -> G.V.t BatEnum.t
    val leaves : t -> G.V.t BatEnum.t
    val display : (G.V.t -> string) -> t -> G.t -> unit
  end
end

(** Create a persistent copy of a graph. *)
module PersistentCopy : sig
  module type G = sig
    type t
    module V : Graph.Sig.VERTEX
    val fold_vertex : (V.t -> 'a -> 'a) -> t -> 'a -> 'a
    val fold_edges : (V.t -> V.t -> 'a -> 'a) -> t -> 'a -> 'a
    val fold_succ : (V.t -> 'a -> 'a) -> t -> V.t -> 'a -> 'a
    val mem_vertex : t -> V.t -> bool
  end
  module Digraph (G : G) : sig
    include Graph.Sig.P with type V.t = G.V.t
			and type E.label = unit
    val copy : G.t -> t
    val copy_reachable : G.V.t -> G.t -> t
  end
end

module Display : sig
  module type G = sig
    type t
    module V : Graph.Sig.VERTEX
    module E : Graph.Sig.EDGE with type vertex = V.t
    val iter_vertex : (V.t -> unit) -> t -> unit
    val iter_edges_e : (E.t -> unit) -> t -> unit
  end

  module Make
    (G : G)
    (S : Putil.S with type t = G.V.t)
    (D : sig
      val graph_attributes : G.t -> Graph.Graphviz.DotAttributes.graph list
      val vertex_attributes : G.V.t -> Graph.Graphviz.DotAttributes.vertex list
      val edge_attributes : G.E.t -> Graph.Graphviz.DotAttributes.edge list
    end) :
  sig
    val output_graph : out_channel -> G.t -> unit
    val display : G.t -> unit
  end

  module MakeSimple (G : G) (S : Putil.S with type t = G.V.t) :
  sig
    val output_graph : out_channel -> G.t -> unit
    val display : G.t -> unit
  end

  module MakeLabeled
    (G : G)
    (Show_vertex : Putil.S with type t = G.V.t)
    (Show_edge : Putil.S with type t = G.E.label) :
  sig
    val output_graph : out_channel -> G.t -> unit
    val display : G.t -> unit
  end

  module MakeStructural
    (G : G) :
  sig
    val output_graph : out_channel -> G.t -> unit
    val display : G.t -> unit
  end
end

module Unfold : sig
  module type G = sig
    type t
    module V : Graph.Sig.VERTEX
    val empty : t
    val add_vertex : t -> V.t -> t
    val add_edge : t -> V.t -> V.t -> t
    val mem_vertex : t -> V.t -> bool
    val fold_succ : (V.t -> 'a -> 'a) -> t -> V.t -> 'a -> 'a
  end
  module Make (G : G) : sig
    val unfold : G.V.t -> (G.V.t -> G.V.t BatEnum.t) -> G.t
    val forward_reachable : G.t -> G.V.t -> G.t
  end
end

module Slice : sig
  module type G = sig
    type t
    module V : Graph.Sig.VERTEX
    module E : Graph.Sig.EDGE with type vertex = V.t
    val fold_succ : (V.t -> 'a -> 'a) -> t -> V.t -> 'a -> 'a
    val fold_pred : (V.t -> 'a -> 'a) -> t -> V.t -> 'a -> 'a
  end
  module Make (G : G) : sig
    val neighborhood : G.t -> G.V.t -> int -> (G.V.t -> bool)
    val forward_reachable : G.t -> G.V.t -> G.V.t BatEnum.t
    val backward_reachable : G.t -> G.V.t -> G.V.t BatEnum.t
    val chop : G.t -> G.V.t -> G.V.t -> G.V.t BatEnum.t
    val forward_reachable_set : G.t -> G.V.t list -> G.V.t BatEnum.t
    val backward_reachable_set : G.t -> G.V.t list -> G.V.t BatEnum.t
    val chop_set : G.t -> G.V.t list -> G.V.t list -> G.V.t BatEnum.t
  end
end

module Traverse : sig
  module type G = sig
    val is_directed : bool
    type t
    module V: Graph.Sig.COMPARABLE
    val iter_vertex : (V.t -> unit) -> t -> unit
    val fold_vertex : (V.t -> 'a -> 'a) -> t -> 'a -> 'a
    val iter_succ : (V.t -> unit) -> t -> V.t -> unit
    val fold_succ : (V.t -> 'a -> 'a) -> t -> V.t -> 'a -> 'a
  end
  module Make (G : G) : sig
    val reverse_postorder : G.V.t -> G.t -> G.V.t BatEnum.t
  end
end

module Build : sig
  module type G = sig
    type t
    type vertex
    val remove_vertex : t -> vertex -> t
    val enum_pred : t -> vertex -> vertex BatEnum.t
    val enum_succ : t -> vertex -> vertex BatEnum.t
    val add_edge : t -> vertex -> vertex -> t
  end
  module Make(G : G) : sig
    val split : G.t -> G.vertex -> pred:G.vertex -> succ:G.vertex -> G.t
    val eliminate_vertex : G.t -> G.vertex -> G.t
  end
end

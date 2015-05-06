(** Strongly connected components *)

type ('a, 'b) scc =
  { graph : 'b;
    mutable entries : 'a list;
    mutable exits : 'a list;
    mutable backedges : 'a list }

type ('a, 'b) scc_type =
  | Simple of 'a
  | Scc of ('a, 'b) scc

type ('a, 'b) scc_vertex =
  { scc_id : int;
    mutable vtype : ('a, 'b) scc_type }

module type G = sig
  type t
  module V : Graph.Sig.VERTEX
  val iter_vertex : (V.t -> unit) -> t -> unit
  val iter_succ : (V.t -> unit) -> t -> V.t -> unit
  val fold_vertex : (V.t -> 'a -> 'a) -> t -> 'a -> 'a
  val fold_edges : (V.t -> V.t -> 'a -> 'a) -> t -> 'a -> 'a
  val fold_succ : (V.t -> 'a -> 'a) -> t -> V.t -> 'a -> 'a
  val mem_vertex : t -> V.t -> bool
end

module SccGraph (G : G) : sig
  type t
  include Graph.Sig.P with type t := t
                       and type V.t = (G.V.t, t) scc_vertex

  val construct : G.t -> t
  val enum_headers : t -> G.V.t BatEnum.t
  val is_header : t -> G.V.t -> bool

  val output_scc_graph : (G.V.t -> string) -> out_channel -> t -> unit

  (** Display an SCC graph with boxes around each SCC *)
  val display_scc : t -> (G.V.t -> string) -> unit

  val fold_inside_out : (G.V.t -> 'a -> 'a) -> G.t -> 'a -> 'a
end

module SccInfo : sig
  module type G = sig
    type t
    module V : Graph.Sig.VERTEX

    val iter_vertex : (V.t -> unit) -> t -> unit
    val iter_succ : (V.t -> unit) -> t -> V.t -> unit
    val iter_pred : (V.t -> unit) -> t -> V.t -> unit
  end
  module Make (G : G) : sig
    include Putil.OrderedMix

    val mem : G.V.t -> t -> bool
    val enum : t -> G.V.t BatEnum.t
    val equal : t -> t -> bool
    val hash : t -> int

    val scc : G.t -> t BatEnum.t
    val scc_map : G.t -> (int * (G.V.t -> t))

    val is_sink : G.t -> t -> bool
    val is_source : G.t -> t -> bool
    val sinks : G.t -> t BatEnum.t
    val sources : G.t -> t BatEnum.t

    val in_degree : G.t -> t -> int
    val out_degree : G.t -> t -> int
    val degree : G.t -> t -> int

    val component_entries : G.t -> t -> G.V.t list
    val component_exits : G.t -> t -> G.V.t list
    val entries : G.t -> (G.V.t list * t) BatEnum.t
    val exits : G.t -> (G.V.t list * t) BatEnum.t
  end
end

type 'a loop_nest =
  { body : 'a;
    headers : 'a;
    children : 'a loop_nest list }

(** Weak topological order element *)
type 'a wto_elt =
  | WSimple of 'a
  | WLoop of ('a wto_elt) list

(** Weak topological order *)
type 'a wto = ('a wto_elt) list

(** Compute weak topological orders *)
module Wto (G : G) : sig
  val create : G.t -> G.V.t wto
  val create_widening : G.t -> G.V.t wto * (G.V.t -> bool)
end

val format_wto :
  (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a wto -> unit

(** Fixpoint computation *)

module type G = sig
  include Loop.G
  module E : Graph.Sig.EDGE with type vertex = V.t
  val iter_edges_e : (E.t -> unit) -> t -> unit
end

(** High-level interface for fixpoint computations. *)
module MakeAnalysis (G : G) (D : Sig.AbstractDomain.S) : sig
  (** Internal state of the analysis, used for querying the properties
      associated with each vertex in the fixpoint. *)
  type result

  (** Compute a fixpoint result.  This result is accessed using the query
      functions below. *)
  val analyze :
    (G.V.t -> D.t -> D.t) ->
    ?edge_transfer:(G.E.t -> D.t -> D.t) ->
    G.t ->
    result

  (** Property associated with the pre-state of a vertex. *)
  val input : result -> G.V.t -> D.t

  (** Property associated with the post-state of a vertex. *)
  val output : result -> G.V.t -> D.t

  (** Enumerate over the pre-state properties of each vertex. *)
  val enum_input : result -> (G.V.t * D.t) BatEnum.t

  (** Enumerate over the post-state properties of each vertex. *)
  val enum_output : result -> (G.V.t * D.t) BatEnum.t
end

(** {2 Low-level fixpoint inferface} *)

(** Worklist *)
type 'a worklist =
  { pick : unit -> ('a * 'a worklist) option;
    add_succs : 'a -> 'a worklist }

(** Fixpoint computation using a weak topological iteration order.  The first
    argument is the WTO defining iteration order; the second is an update
    function which is repeatedly applied until each component of the WTO
    converges (for every [v], we have [update v = false]). *)
val fix_wto : 'a Loop.wto -> ('a -> bool) -> unit

(** Fixpoint computation using a worklist.  This is typically slower than
    WTO-based iteration schemes. *)
val fix_worklist : 'a worklist -> ('a -> bool) -> unit

(** Module implementing fixpoint computation using a weak topological
    iteration order.  This is typically faster and more general than
    [fix_wto]. *)
module Wto (G : G) : sig
  module VSet : Set.S with type elt = G.V.t

  (** Fixpoint computation over a graph using weak topological iteration order
      (which is either provided by the [wto] argument, or computed).  A
      marking scheme is used to avoid unnecessary vertex evaluations.  The
      {!init} parameter gives the set of vertices that are initially marked
      (which defaults to the set of all vertices).

      This function may take two update functions, [update] and [wide_update].
      If [wide_update] is not [None], it is applied at the feedback vertices
      instead of [update]. *)
  val fix : G.t ->
    ?wto:(G.V.t Loop.wto option) ->
    ?init:(VSet.t) ->
    (G.V.t -> bool) ->
    (G.V.t -> bool) option ->
    unit
end

(** Module implementing fixpoint computation using a priority worklist.
    Priorities comparison is implemented by the [C] module argument. *)
module GraphWorklist
  (G : Graph.Sig.G)
  (C : sig val compare : G.V.t -> G.V.t -> int end) :
sig
  module VSet : Set.S with type elt = G.V.t
  val fix : G.t -> ?init:(VSet.t) -> (G.V.t -> bool) -> unit
end

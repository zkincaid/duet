(** Path expression algorithms *)

module type G = sig
  type t
  module V : Graph.Sig.VERTEX
  module E : Graph.Sig.EDGE with type vertex = V.t
  val fold_vertex : (V.t -> 'a -> 'a) -> t  -> 'a -> 'a
  val fold_edges_e : (E.t -> 'a -> 'a) -> t -> 'a -> 'a
  val fold_succ : (V.t -> 'a -> 'a) -> t -> V.t -> 'a -> 'a
  val fold_pred : (V.t -> 'a -> 'a) -> t -> V.t -> 'a -> 'a
  val nb_vertex : t -> int
end

(** Compute path expressions for all pairs of vertices on dense graphs *)
module Make(G : G)(K : Sig.KA.Ordered.S) :
sig

  (** Get a path expression for all pairs of vertices. *)
  val all_paths : G.t -> (G.E.t -> K.t) -> (G.V.t -> G.V.t -> K.t)

  val all_paths_v : G.t -> (G.V.t -> K.t) -> (G.V.t -> G.V.t -> K.t)
end

(** Path expression algorithms for sparse graphs *)
module MakeElim (G : G)(K : Sig.KA.Ordered.S) :
sig
  (** Get a path expression for a single source and single target *)
  val path_expr : G.t -> (G.E.t -> K.t) -> G.V.t -> G.V.t -> K.t

  val path_expr_v : G.t -> (G.V.t -> K.t) -> G.V.t -> G.V.t -> K.t

  (** Get a path expression for a single source and a set of targets
      (specified by a predicate) by taking the sum the path expressions to
      each individual target. *)
  val path_expr_multiple_tgt : G.t -> (G.E.t -> K.t) -> G.V.t -> (G.V.t -> bool) -> K.t
  val path_expr_multiple_tgt_v : G.t -> (G.V.t -> K.t) -> G.V.t -> (G.V.t -> bool) -> K.t

  (** Compute a path expression from a single source to every other vertex.
      This function has the same signature as [path_expr] and [allpaths], but
      is more efficient if path expressions are required for multiple
      targets, but only a single source. *)
  val single_src : G.t -> (G.E.t -> K.t) -> G.V.t -> (G.V.t -> K.t)

  (** Similar to [single_src], except path expressions are only computed for
      target vertices that satisfy the given predicate. *)
  val single_src_restrict :
    G.t -> (G.E.t -> K.t) -> G.V.t -> (G.V.t -> bool) -> (G.V.t -> K.t)

  val single_src_v : G.t -> (G.V.t -> K.t) -> G.V.t -> (G.V.t -> K.t)
  val single_src_restrict_v :
    G.t -> (G.V.t -> K.t) -> G.V.t -> (G.V.t -> bool) -> (G.V.t -> K.t)


  (** For each vertex [v], compute the sum over all [u] of [path_expr v u].
      That is, [paths_from] computes, for each vertex [v], a path expression
      that represents all paths emanating from [v].  This is equivalent to
      (but more efficent than) calling [path_expr_multiple_tgt v (fun _ ->
      true)] for every vertex v. *)
  val paths_from : G.t -> (G.E.t -> K.t) -> G.V.t -> (G.V.t -> K.t)
end

open RecGraph
module MakeRG
  (R : RecGraph.S)
  (Block : BLOCK with type t = R.block)
  (K : Sig.KA.Quantified.Ordered.S) :
sig
  module HT : BatHashtbl.S with type key = Block.t
  type query
  val mk_query : R.t ->
    (R.atom -> K.t) ->
    (R.block -> (K.var -> bool)) ->
    R.block ->
    query
  val compute_summaries : query -> unit
  val add_callgraph_edge : query -> Block.t -> Block.t -> unit
  val get_summaries : query -> K.t HT.t
  val get_summary : query -> Block.t -> K.t
  val single_src_blocks : query -> Block.t -> K.t
  val single_src_restrict :
    query -> (R.G.V.t -> bool) -> (R.G.V.t -> K.t -> unit) -> unit
  val single_src : query -> Block.t -> R.G.V.t -> K.t
  val enum_single_src : query -> (Block.t * R.G.V.t * K.t) BatEnum.t
  val enum_single_src_tmp : (R.G.V.t -> (R.atom, R.block) typ) -> query -> (Block.t * R.G.V.t * K.t) BatEnum.t
end

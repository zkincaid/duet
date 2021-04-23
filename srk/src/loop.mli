(** Loops *)

module type G = sig
  type t
  module V : sig
    type t
    val compare : t -> t -> int
    val hash : t -> int
    val equal : t -> t -> bool
  end
  val iter_vertex : (V.t -> unit) -> t -> unit
  val iter_succ : (V.t -> unit) -> t -> V.t -> unit
end

(** Ordered loop nesting forests *)
module Make(G : G) : sig

  (** A loop of a graph [G] is a pair [(h,B)] consisting of a set of
     vertices [B], and a header vertex [h] that belongs to [B] such
     that subgraph of [G] induced by [B] is strongly connected. *)
  type loop
     
  (** An ordered loop nesting forest of a graph [G] consists of a
     sequence of the strongly connected components of [G] in
     topological order, and such that each non-trival SCC [C] is
     associated with (1) a header vertex [v], and (2) an ordered loop
     nesting forest for the subgraph of [G] induced by [C \ H].  (Note
     that an SCC consisting of a single vertex with a self-loop is
     considered a non-trival SCC).  An ordered loop nesting forest is
     simultaneously a loop nesting forest (Ramalingam: On loops,
     dominators, and dominance frontiers) and a weak topological order
     (Bourdoncle: Efficient chaotic iteration strategies with
     widenings).  *)
  type forest = [ `Vertex of G.V.t | `Loop of loop ] list

  module VertexSet : BatSet.S

  (** Construct an ordered loop nesting forest, and return the list of
     roots. *)
  val loop_nest : G.t -> forest

  (** Header vertex of a loop.  If any vertex in the loop has an
     incoming edge from outside the loop, so does the header. *)
  val header : loop -> G.V.t

  (** Set of vertices belonging to a loop. *)
  val body : loop -> VertexSet.t

  (** [children loop] produces a list of the vertices and loops for
     which [loop] is the least (most deeply nested) that contains it,
     ordered topologically.  Note that children does not contain the
     loop header.  *)
  val children : loop -> forest

  (** Compute a list of all headers of all loops in a loop nesting
     forest for a graph [G].  The subgraph obtained by removing the
     incoming edges to each header vertex is acyclic.  *)
  val cutpoints : forest -> VertexSet.t

  (** Compute a list of all loops in a loop nesting forest.  Every
     pair of loops is either disjoint or one is a proper subloop of
     the other (a loop [(h,B)] is a subloop of [(h',B')] if [B] is a
     subset of [B' - {h}]. *)
  val all_loops : forest -> loop list

  (** Pretty-print. *)
  val pp : (Format.formatter -> G.V.t -> unit) ->
           Format.formatter -> forest -> unit
end with module VertexSet = BatSet.Make(G.V)

(** Operations for manipulating weighted graphs.

   A weighted graph is a graph where edges are labeled by elements of
   a regular algebra. *)

type 'a weighted_graph

type 'a t = 'a weighted_graph

(** Regular algebra signature *)
type 'a algebra =
  { mul : 'a -> 'a -> 'a;
    add : 'a -> 'a -> 'a;
    star : 'a -> 'a;
    zero : 'a;
    one : 'a }

(** Unweighted graphs *)
module U : Graph.Sig.G with type V.t = int

type vertex = int

(** Create an empty weighted graph over the given algebra of weights. *)
val empty : ('a algebra) -> 'a t

(** Add a vertex to a graph. *)
val add_vertex : 'a t -> vertex -> 'a t

(** [add_edge g u w v] adds an edge [u -w-> v] to [g].  If there is already an
    edge from [u] to [v], then [w] is added to the weight of the edge. *)
val add_edge : 'a t -> vertex -> 'a -> vertex -> 'a t

(** Find the weight associated with a single edge. *)
val edge_weight : 'a t -> vertex -> vertex -> 'a

(** [path_weight g u v] computes the sum of all weighted paths from [u] to [v]
    in [g]. *)
val path_weight : 'a t -> vertex -> vertex -> 'a

(** [cut_graph g c] computes the cut graph g'
    g' = <c, {(u, w, v) : (u, v) in c x c,
                          w is the sum of all paths from u to v in g not going
                          through any node in c}> **)
val cut_graph : 'a t -> vertex list -> 'a t

(** Remove a vertex from a graph. *)
val remove_vertex : 'a t -> vertex -> 'a t

(** [contract g v] removes vertex [v] from [g] while preserving all weighted
    paths among remaining vertices.  That is, for each pair of edges [p -pw->
    v] and [v -sw-> s], adds the edge [p -> s] with weight [pw.vw*.sw], where
    [vw] is the weight of the self-loop at [v]. *)
val contract_vertex : 'a t -> vertex -> 'a t

val split_vertex : 'a t -> vertex -> 'a -> vertex -> 'a t

val forget_weights : 'a t -> U.t

val map_weights : (vertex -> 'a -> vertex -> 'a) -> 'a t -> 'a t

val fold_edges : ((vertex * 'a * vertex) -> 'b -> 'b) -> 'a t -> 'b -> 'b
val iter_edges : ((vertex * 'a * vertex) -> unit) -> 'a t -> unit
val fold_succ_e :  ((vertex * 'a * vertex) -> 'b -> 'b) ->
  'a t ->
  vertex ->
  'b ->
  'b
val fold_pred_e :  ((vertex * 'a * vertex) -> 'b -> 'b) ->
  'a t ->
  vertex ->
  'b ->
  'b
val iter_succ_e :  ((vertex * 'a * vertex) -> unit) -> 'a t -> vertex -> unit
val iter_pred_e :  ((vertex * 'a * vertex) -> unit) -> 'a t -> vertex -> unit

val fold_vertex : (vertex -> 'b -> 'b) -> 'a t -> 'b -> 'b
val iter_vertex : (vertex -> unit) -> 'a t -> unit
val mem_edge : 'a t -> vertex -> vertex -> bool

(** Find the largest integer identifier for a vertex in a graph *)
val max_vertex : 'a t -> int

(** Compute least fixpoint solution to a system of constraints defined
   over a weighted graph.  The type ['v] represents values in poset.
   We compute the least annotation [inv] of the graph such that
    {ul
      {- [inv(v) >= init(v)] for all vertices [v] }
      {- [update (inv src) weight (inv dst) = None] for each edge (src, weight, dst) } }
   The update function associates each edge with a constraint.  The
   constraint is satisfied when the update function returns [None];
   otherwise [update pre weight post] should return the least value [post'] such that
    {ul
      {- [post' >= post] }
      {- [update pre weight post' = None] (i.e., [post'] satisfies the associated constraint) }}

    The poset ['v] is expected to satisfy the ascending chain condition, and
    [update] is expected to be monotone in the sense that if [pre >= pre'] and
    [update pre weight post = None], then [update pre' weight post = None]. *)
val forward_analysis :
  'a t ->
  entry:int ->
  update:(pre:'v -> 'a -> post:'v -> 'v option) ->
  init:(int -> 'v) ->
  (int -> 'v)

(** Weight algebras, equipped with additional operations for interpreting
    recursive graphs *)
module type Weight = sig
  type t
  val mul : t -> t -> t
  val add : t -> t -> t
  val zero : t
  val one : t
  val star : t -> t
  val equal : t -> t -> bool
  val project : t -> t
  val widen : t -> t -> t
end

type 'a label =
  | Weight of 'a
  | Call of int * int

(** A weighted recursive graph is a graph with two types of edges: weighted
    edges and call edges.  Each call edges designates an entry vertex and exit
    vertex, and weight queries treat the edge as having a weight that
    over-approximates the weights of paths from entry to exit.  Since a call
    edge [(s,t)] may appear between [s] and [t], recursive graphs can model
    (mutually) recursive procedures.  *)
module MakeRecGraph (W : Weight) : sig
  (** A recursive graph is a weighted graph with edges are either weighted by
      [W] or by calls.  Algebraic operations for call edges are undefined, and
      weighted graph operations that would invoke an algebraic operation
      (e.g., [contract_vertex], [path_weight]) on a call weight raise
      [Invalid_arg]. *)
  type t = (W.t label) weighted_graph

  (** A query is an intermediate structure for perfoming path weight queries.
      After creating a recursive graph, a query can be constructed using
      [mk_query] and accessed using [path_weight]. *)
  type query

  (** Create an empty recursive graph. *)
  val empty : t

  (** Create a query structure.  The optional [delay] parameter specifies the
      widening delay to use during summary computation. *)
  val mk_query : ?delay:int -> t -> query

  (** Over-approximate the sum of the weights of all paths between two given
      vertices.  *)
  val path_weight : query -> vertex -> vertex -> W.t
end

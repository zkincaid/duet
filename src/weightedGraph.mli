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

(** Omega algebra signature *)
type ('a,'b) omega_algebra =
  { omega : 'a -> 'b;
    omega_add : 'b -> 'b -> 'b;
    omega_mul : 'a -> 'b -> 'b }

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

(** Multiple-source all-target path expressions. [msat_path_weight g
   srcs] computes a function [f] which maps a vertex [u] belonging to
   [src] and any other vertex [v] to to the sum of all weighted paths
   from [u] to [v].  *)
val msat_path_weight : 'a t -> vertex list -> 'a t

(** [omega_path_weight g alg v] computes the sum of all weighted omega
   paths starting at [v] in [g]. *)
val omega_path_weight : 'a t -> ('a,'b) omega_algebra -> vertex -> 'b

(** [cut_graph g c] computes the cut graph g'
    g' = <c, \{ (u, w, v) : (u, v) in c x c,
                          w is the sum of all paths from u to v in g not going
                          through any node in c \}> **)
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

module type AbstractWeight = sig
  type weight
  type abstract_weight
  val abstract : weight -> abstract_weight
  val concretize : abstract_weight -> weight
  val equal : abstract_weight -> abstract_weight -> bool
  val widen : abstract_weight -> abstract_weight -> abstract_weight
end

(** A recursive graph is a graph with two types of edges: simple edges
   and call edges.  Each call edge designates an entry vertex and exit
   vertex, and can be interpreted a set of paths that begin and entry
   and end at exit. *)
module RecGraph : sig
  type t
  type call = vertex * vertex

  (** A query is an intermediate structure for perfoming path
     expression queries.  After creating a recursive graph, a query
     can be constructed using [mk_query] and accessed using
     [pathexpr]. *)
  type query

  (** A weight query is an intermediate structure for perfoming path
     weight queries. *)
  type 'a weight_query

  exception No_summary of call

  (** The callgraph of a recursive graph has calls as vertices, and an
     edge c1 to c2 iff a call to c2 appears on a path in c1.  A
     callgraph can be constructed using [mk_callgraph]. *)
  module CallGraph : sig
    type t
    module V : sig
      type t = call
    end
    val iter_vertex : (call -> unit) -> t -> unit
    val iter_succ  : (call -> unit) -> t -> call -> unit
  end

  val empty : unit -> t
  val add_vertex : t -> vertex -> t
  val add_edge : t -> vertex -> vertex -> t
  val add_call_edge : t -> vertex -> call -> vertex -> t

  (** Create a query for computing path expressions beginning at the
     designated source vertex. *)
  val mk_query : t -> vertex -> query

  (** Find a nested path expression recognizing every interprocedural
     path from the query's source vertex to the given target vertex.
     Every complete entry-to-call edge path is enclosed in a
     segment. *)
  val pathexpr : query -> vertex -> Pathexpr.nested Pathexpr.t

  (** Find a simple path expression recognizing every intraprocedural
     path through a given call.  The call must appear on at least one
     of the call edges of the recursive graph of the query. *)
  val call_pathexpr : query -> call -> Pathexpr.simple Pathexpr.t

  (** Find an omega regular expression recognizing every infinite
     interprocedural path beginning at the query's source vertex. *)
  val omega_pathexpr : query -> Pathexpr.nested Pathexpr.omega

  val mk_callgraph : query -> CallGraph.t

  (** Create a weighted query for computing path weights.  The
     supplied algebra is used to assign weights to simple edges; the
     query maintains summaries for each call that are used to assign
     weights to call edges. *)
  val mk_weight_query : query -> 'a Pathexpr.nested_algebra -> 'a weight_query

  (** Build call summaries via successive approximation. *)
  val summarize_iterative : query ->
                            'a Pathexpr.nested_algebra ->
                            ?delay:int ->
                            (module AbstractWeight
                                    with type weight = 'a) ->
                            'a weight_query
  (** Find the sum of weights of all interprocedural paths beginning
     at the query's source vertex and ending at a given target. *)
  val path_weight : 'a weight_query -> vertex -> 'a

  (** Find the sum of weights of all intraprocedural paths through a
     given call. *)
  val call_weight : 'a weight_query -> call -> 'a

  val get_summary : 'a weight_query -> call -> 'a
  val set_summary : 'a weight_query -> call -> 'a -> unit

  (** Find the sum of weights of all infinite interprocedural paths
     beginning at the query's source vertex. *)
  val omega_path_weight : 'a weight_query -> ('a,'b) Pathexpr.omega_algebra -> 'b
end

open Syntax

type 'a label =
  | Weight of 'a
  | Call of int * int

module Make
    (C : sig
       type t
       val context : t Syntax.context
     end)
    (Var : sig
       type t
       val pp : Format.formatter -> t -> unit
       val typ : t -> [ `TyInt | `TyReal ]
       val compare : t -> t -> int
       val symbol_of : t -> symbol
       val of_symbol : symbol -> t option
       val is_global : t -> bool
       val hash : t -> int
       val equal : t -> t -> bool
     end)
    (T : sig
       type t
       type var = Var.t
       val pp : Format.formatter -> t -> unit
       val guard : t -> C.t formula
       val transform : t -> (var * C.t term) BatEnum.t
       val mem_transform : var -> t -> bool
       val get_transform : var -> t -> C.t term
       val assume : C.t formula -> t
       val mul : t -> t -> t
       val add : t -> t -> t
       val zero : t
       val one : t
       val star : t -> t
       val exists : (var -> bool) -> t -> t
     end) : sig

  type vertex = int
  type transition = T.t
  type t = (transition label) WeightedGraph.t
  type query = T.t WeightedGraph.RecGraph.weight_query

  module VarSet : BatSet.S with type elt = Var.t

  (** Create an empty transition system. *)
  val empty : t

  (** Create a query structure.  The optional [delay] parameter specifies the
      widening delay to use during summary computation. *)
  val mk_query : ?delay:int ->
                 t ->
                 vertex ->
                 (module WeightedGraph.AbstractWeight
                         with type weight = transition) ->
                 query

  (** Over-approximate the sum of the weights of all paths from the
     query's source vertex to the given target vertex. *)
  val path_weight : query -> vertex -> transition

  (** Over-approximate the sum of the weights of all paths between two given
      vertices.  *)
  val call_weight : query -> (vertex * vertex) -> transition

  (** Over-approximate the sum of the weights of all infinite paths
     starting at a given vertex. *)
  val omega_path_weight : query -> (transition,'b) Pathexpr.omega_algebra -> 'b

  (** Project out local variables from each transition that are referenced
      only by that transition. *)
  val remove_temporaries : t -> t

  (** Compute interval invariants for each loop header of a transition system.
      The invariant computed for a loop is defined only over the variables
      read or written to by the loop. *)
  val forward_invariants_ivl : t -> vertex -> (vertex * C.t formula) list

  (** Compute interval-and-predicate invariants for each loop header
     of a transition system.  The invariant computed for a loop is
     defined only over the variables read or written to by the
     loop. *)
  val forward_invariants_ivl_pa : C.t formula list ->
                                  t ->
                                  vertex ->
                                  (vertex * C.t formula) list

  (** Simplify a transition system by contracting vertices that do not satisfy
      the given predicate.  Simplification does not guarantee that all such
      vertices are contracted.  In particular, simplification will not
      contract vertices with loops or vertices adjacent to call edges. *)
  val simplify : (vertex -> bool) -> t -> t

  (** Given a transition system and entry, compute a set of loop
     headers along with the set of variables that are read within the
     body of the associated loop *)
  val loop_headers_live : t -> (int * VarSet.t) list

  module type AbstractDomain = Abstract.MakeAbstractRSY(C).Domain

  module type IncrAbstractDomain = sig
    include AbstractDomain
    val incr_abstract : C.t Interpretation.interpretation list ->
                        symbol list ->
                        C.t Smt.Solver.t
                        ->
                        t ->
                        (t * C.t Interpretation.interpretation list)
  end

  module LiftIncr (A : AbstractDomain) : IncrAbstractDomain with type t = A.t

  module ProductIncr
           (A : IncrAbstractDomain)
           (B : IncrAbstractDomain) : IncrAbstractDomain with type t = A.t * B.t

  (** [forward_invariants d ts entry] computes invariants for [ts]
     starting from the node [entry] using the abstract domain [d] *)
  val forward_invariants : (module IncrAbstractDomain with type t = 'a) ->
                           t ->
                           vertex ->
                           (vertex -> 'a)
end

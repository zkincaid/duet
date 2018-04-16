open Syntax

type 'a label = 'a WeightedGraph.label =
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
       val compare : t -> t -> int
       val equal : t -> t -> bool
       val mul : t -> t -> t
       val add : t -> t -> t
       val zero : t
       val one : t
       val star : t -> t
       val widen : t -> t -> t
       val exists : (var -> bool) -> t -> t
     end) : sig

  type vertex = int
  type transition = T.t
  type t = (transition label) WeightedGraph.t
  type query

  (** Crate an empty transition system. *)
  val empty : t

  (** Create a query structure.  The optional [delay] parameter specifies the
      widening delay to use during summary computation. *)
  val mk_query : ?delay:int -> t -> query

  (** Over-approximate the sum of the weights of all paths between two given
      vertices.  *)
  val path_weight : query -> vertex -> vertex -> transition

  (** Project out local variables from each transition that are referenced
      only by that transition. *)
  val remove_temporaries : t -> t

  (** Compute interval invariants for each loop header of a transition system.
      The invariant computed for a loop is defined only over the variables
      read or written to by the loop. *)
  val forward_invariants : t -> vertex -> (vertex * C.t formula) list

  val forward_invariants_pa : C.t formula list -> t -> vertex -> (vertex * C.t formula) list
  (** Simplify a transition system by contracting vertices that do not satisfy
      the given predicate.  Simplification does not guarantee that all such
      vertices are contracted.  In particular, simplification will not
      contract vertices with loops or vertices adjacent to call edges. *)
  val simplify : (vertex -> bool) -> t -> t
end

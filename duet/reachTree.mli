module TransitionSystem = Srk.TransitionSystem
module Syntax = Srk.Syntax 
module Interpretation = Srk.Interpretation 

type equery = OverApprox | UnderApprox
module ART
    (G : sig
       type t
       type vertex
       type weight
       val fold_succ :  (vertex -> 'a -> 'a) -> t -> vertex -> 'a -> 'a
       val weight : t -> vertex -> vertex -> weight
       val summary : t -> vertex -> weight
       val compare_vertex : vertex -> vertex -> int
       val pp_vertex : Format.formatter -> vertex -> unit
     end)
    (L : sig
       type t
       val top : t
       val bottom : t
       val meet : t -> t -> t
       val leq : t -> t -> bool
       val negate : t -> t
       val pp : Format.formatter -> t -> unit
     end)
    (T : sig
       type t
       type label
       type state
       val check : label -> t list -> label -> [ `Valid of label list
                                               | `Invalid of state
                                               | `Unknown ]
       val post_model : state -> t -> state option
       val is_deterministic : t -> bool
       val mul : t -> t -> t
       val assume : label -> t
       val guard : t -> label
       val pp_state : Format.formatter -> state -> unit
     end with type t = G.weight
          and type label = L.t) : sig
  type node
  type t
  type state = T.state
  type weight = T.t
  val make : G.t -> L.t -> src:G.vertex -> dst:G.vertex -> t
  val get_entry : t -> G.vertex 
  val get_err_loc : t -> G.vertex
  val get_precondition : t -> L.t
  val print_tree : t -> string -> node -> unit
  val parent : t -> node -> node
  val parent_weight : t -> node -> (node * weight) option
  val maps_to : t -> node -> G.vertex
  val add_frontier : t -> node -> unit
  val deque_frontier : t -> node option
  val tree_path : t -> ?src:node -> node -> node list
  val is_leaf : t -> node -> bool
  val label : t -> node -> L.t
  val expand : t -> node -> unit
  val close : t -> node -> (bool * node list)
  val force_cover : t -> node -> node -> bool
  val lclose : t -> node -> bool
  val is_covered : t -> node -> bool 
  val refine: t -> node list -> L.t list -> unit
  val log_art : t -> unit 
  val log_node :  node -> unit 
  val of_node : node -> int
  val root : node
  val pp_node : Format.formatter -> node -> unit
  val execute : t -> node -> T.state -> [ `Safe | `Unsafe of node ]
  val gps : t -> [ `Safe | `Unsafe of node ]
  val path_to_error : t -> node -> weight
  val generate_test : t -> node -> [ `Test of state | `Pruned ]
end

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
       val iter_succ_e :  (vertex * weight * vertex -> unit) -> t -> vertex -> unit
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
     end with type t = G.weight
          and type label = L.t) : sig
  type node
  type t
  type state = T.state
  type weight = T.t
  exception Mexception of string
  val make : G.t -> G.vertex -> G.vertex -> t
  val get_entry : t -> G.vertex 
  val get_err_loc : t -> G.vertex
  val print_tree : t -> string -> node -> unit
  val parent : t -> node -> node
  val parent_weight : t -> node -> (node * weight) option
  val maps_to : t -> node -> G.vertex
  val tree_path : t -> ?src:node -> node -> node list
  val children : t -> node -> node list
  val descendants : t -> node -> node list
  val leaves : t -> node list
  val is_leaf : t -> node -> bool
  val label : t -> node -> L.t
  val set_label : t -> node -> L.t -> unit
  val get_precedent_nodes : t -> node -> node list
  val get_id : t -> node
  val add_tree_vertex :
    t -> ?label:L.t -> G.vertex -> int -> node
  val expand :
    t -> node -> T.state -> (node * T.state) list * node list
  val cover : t -> node -> node -> bool
  val close : t -> node -> (bool * node list)
  val force_cover : t -> node -> node -> (bool * node list) 
  val lclose : t -> node -> (bool * node list)
  val is_covered : t -> node -> bool 
  val refine: t -> node list -> L.t list -> node list  
  val log_art : t -> unit 
  val log_node :  node -> unit 
  val of_node : node -> int
  val root : node
  val pp_node : Format.formatter -> node -> unit
end

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
  val make : G.t -> G.vertex -> G.vertex -> t ref
  val get_entry : t ref -> G.vertex 
  val get_err_loc : t ref -> G.vertex
  val print_tree : t ref -> string -> node -> unit
  val parent : t ref -> node -> node
  val parent_weight : t ref -> node -> (node * weight) option
  val maps_to : t ref -> node -> G.vertex
  val tree_path : t ref -> ?src:node -> node -> node list
  val children : t ref -> node -> node list
  val descendants : t ref -> node -> node list
  val leaves : t ref -> node list
  val is_leaf : t ref -> node -> bool
  val label : t ref -> node -> L.t
  val set_label : t ref -> node -> L.t -> unit
  val get_precedent_nodes : t ref -> node -> node list
  val get_id : t ref -> node
  val add_tree_vertex :
    t ref -> ?label:L.t -> G.vertex -> int -> node
  val expand :
    t ref -> node -> T.state -> (node * T.state) list * node list
  val cover : t ref -> node -> node -> bool
  val close : t ref -> node -> (bool * node list)
  val force_cover : t ref -> node -> node -> (bool * node list) 
  val lclose : t ref -> node -> (bool * node list)
  val is_covered : t ref -> node -> bool 
  val refine: t ref -> node list -> L.t list -> node list  
  val log_art : t ref -> unit 
  val log_node :  node -> unit 
  val of_node : node -> int
  val root : node
  val pp_node : Format.formatter -> node -> unit
end

module TransitionSystem = Srk.TransitionSystem
module Syntax = Srk.Syntax 
module Interpretation = Srk.Interpretation 

type equery = OverApprox | UnderApprox
module ART :
  functor
    (Ctx: Srk.Syntax.Context)
    (** transition formula algebra *)
    (K : sig
           type t
           type var
           val pp : Format.formatter -> t -> unit
           val guard : t -> Ctx.t Srk.Syntax.formula
           val transform : t -> (var * Ctx.t Srk.Syntax.arith_term) BatEnum.t
           val mem_transform : var -> t -> bool
           val get_transform : var -> t -> Ctx.t Srk.Syntax.arith_term
           val assume : Ctx.t Srk.Syntax.formula -> t
           val mul : t -> t -> t
           val add : t -> t -> t
           val conjunct : t -> t -> t 
           val zero : t
           val one : t
           val star : t -> t
           val exists : (var -> bool) -> t -> t
           val contains_havoc : t -> bool
           val contextualize :  t -> t -> t  -> [ `Sat of t | `Unsat ]
           val interpolate_or_concrete_model : t list -> Ctx.t Syntax.formula 
                 -> [`Valid of Ctx.t Syntax.formula list 
                      | `Invalid of Ctx.t Interpretation.interpretation | `Unknown ]
         
           val get_post_model :
             Ctx.t Srk.Interpretation.interpretation ->
             t -> Ctx.t Srk.Interpretation.interpretation option
           val is_deterministic : t -> bool
         end)
    (** transition system with edge weights from K *)
    (TS : sig
            type vertex
            type transition = K.t
            type t 
            type query
            type reverse_query
            val empty : t
            val path_weight : query -> vertex -> transition
            val call_weight : query -> vertex * vertex -> transition
            val mk_reverse_query : query -> vertex -> reverse_query
            val exit_summary : reverse_query -> vertex -> vertex -> K.t
            val target_summary : reverse_query -> vertex -> K.t

            val set_summary : query -> vertex * vertex -> transition -> unit
            val get_summary : query -> vertex * vertex -> transition
            val omega_path_weight :
              query -> (transition, 'b) Srk.Pathexpr.omega_algebra -> 'b
            val forward_invariants_ivl :
              t -> vertex -> (vertex * Ctx.t Srk.Syntax.formula) list
            val forward_invariants_ivl_pa :
              Ctx.t Srk.Syntax.formula list ->
              t -> vertex -> (vertex * Ctx.t Srk.Syntax.formula) list
            val simplify : (vertex -> bool) -> t -> t
            val iter_succ_e :
              ((vertex * (transition TransitionSystem.label) * vertex) -> unit) -> t -> vertex -> unit
            val edge_weight :
              t -> vertex -> vertex -> K.t Srk.TransitionSystem.label
            
            val fold_succ_e : (vertex * (K.t Srk.TransitionSystem.label) * vertex -> 'b -> 'b) -> t -> vertex -> 'b -> 'b
            end)
    (** a module giving a procedure name type. Procedures are implicitly represented by pairs of CFG vertices in Duet.
        Here we give them a type. *)
    (PN : sig
            type t
            val make : TS.vertex * TS.vertex -> t
            val string_of : t -> string
            val of_string : string -> t
            val compare : t -> t -> int
          end)
    (** a module giving a vertex name type. Vertices are integers in Duet, here we give them a type. *)
    (VN : sig
            val to_vertex : int -> TS.vertex
            val of_vertex : TS.vertex -> int
          end)
    (** a module giving an interface for accessing over/under-approximate procedure summaries. *)
    (Summarizer : sig
                    type t
                    (** [init g s] returns a Summarizer.t type for a given transition system, source vertex pair (g, s). *)
                    val init : TS.t -> TS.vertex -> TS.vertex -> bool -> t
                    (** [over_proc_summary s n] returns the over-approximate procedure summary for procedure `n`. *)
                    val over_proc_summary : t -> PN.t -> K.t
                    (** [under_proc_summary s n] returns the under-approximate procedure summary (initially `false`) for procedure `n`. *)
                    val under_proc_summary : t -> PN.t -> K.t
                    (** [set_over_proc_summary s n w] sets the over-approximate procedure summary to be `w` at procedure `n`. *)
                    val set_over_proc_summary : t -> PN.t -> K.t -> unit
                    (** [set_under_proc_summary s n w] sets the under-approximate procedure summary to be `w` at procedure `n`. *)
                    val set_under_proc_summary : t -> PN.t -> K.t -> unit
                    (** [refine s n pre post] refines the over-approximate procedure summary at `n` by conjuncting on (pre) /\ (post') *)
                    val refine_over_summary : t -> PN.t -> K.t -> unit
                    (** [refine_under s n tr] refines the under-approximate procedure summary at `n` by adding `tr` as a disjunct. *)
                    val refine_under_summary : t -> PN.t -> K.t -> unit
                    (** [path_weight_intra s u v] gives the weighted path summary between (u, v) on an intraprocedural CFG *)
                    val path_weight_intra : t -> TS.vertex -> TS.vertex -> K.t
                    (** [path_weight_inter s u v] gives the inter-procedural path weight between (u, v) *)
                    val path_weight_inter : t -> TS.vertex -> K.t
                  end)
    ->
    sig
      type node
      type t
      type state_formula = Ctx.t Srk.Syntax.formula
      exception Mexception of string
      val make : TS.t -> TS.vertex -> TS.vertex -> state_formula -> Summarizer.t -> t ref
      val get_entry : t ref -> TS.vertex 
      val get_err_loc : t ref -> TS.vertex
      val get_summarizer : t ref -> Summarizer.t 
      val print_tree : t ref -> string -> node -> unit
      val parent : t ref -> node -> node
      val maps_to : t ref -> node -> TS.vertex
      val tree_path : t ref -> ?src:node -> node -> node list
      val children : t ref -> node -> node list
      val descendants : t ref -> node -> node list
      val leaves : t ref -> node -> node list
      val is_leaf : t ref -> node -> bool
      val label : t ref -> node -> state_formula
      val set_label : t ref -> node -> state_formula -> unit
      val get_precedent_nodes : t ref -> node -> node list
      val get_id : t ref -> node
      val add_tree_vertex :
        t ref -> ?label:Ctx.t Srk.Syntax.formula -> TS.vertex -> int -> node
      val expand :
        int -> t ref -> node -> Ctx.t Interpretation.interpretation -> (node * Ctx.t Interpretation.interpretation) list * node list
      val cover : t ref -> node -> node -> bool
      val close : t ref -> node -> (bool * node list)
      val force_cover : t ref -> node -> node -> (bool * node list) 
      val lclose : t ref -> node -> (bool * node list)
      val is_covered : t ref -> node -> bool 
      val refine: t ref -> node list -> Ctx.t Syntax.formula list -> node list  
      val log_art : t ref -> unit 
      val log_node :  node -> unit 
      val of_node : node -> int
      val root : node
    end

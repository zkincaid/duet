(*
module TransitionSystem = Srk.TransitionSystem
module Syntax = Srk.Syntax 
module Interpretation = Srk.Interpretation 
*)
(*
module LeftRegularSummaryProvider :
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
        val simplify : ?try_rtc:bool -> (vertex -> bool) -> t -> t
        val iter_succ_e :
            ((vertex * (transition TransitionSystem.label) * vertex) -> unit) -> t -> vertex -> unit
        val edge_weight :
            t -> vertex -> vertex -> K.t Srk.TransitionSystem.label    
        val fold_succ_e : (vertex * (K.t Srk.TransitionSystem.label) * vertex -> 'b -> 'b) -> t -> vertex -> 'b -> 'b
        end)
    -> sig 
    type t
    val init : TS.t -> int -> int -> bool -> t
    val path_weight_intra : t -> int -> int -> TS.transition
    val path_weight_inter : t -> int -> TS.transition
  end

module InterproceduralSummaryProvider :
(Ctx: Srk.Syntax.Context)
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
    val simplify : ?try_rtc:bool -> (vertex -> bool) -> t -> t
    val iter_succ_e :
      ((vertex * (transition TransitionSystem.label) * vertex) -> unit) -> t -> vertex -> unit
    val edge_weight :
      t -> vertex -> vertex -> K.t Srk.TransitionSystem.label    
    val fold_succ_e : (vertex * (K.t Srk.TransitionSystem.label) * vertex -> 'b -> 'b) -> t -> vertex -> 'b -> 'b
    end)
  (ProcName : sig
                type t = int * int
                val make : int * int -> t
                val string_of : t -> string
                val of_string : string -> t
                val compare : t -> t -> int
              end)
    ->
    sig
      type t 
      val init : TS.t -> int -> int -> t
      val over_proc_summary : t -> ProcName.t -> TS.transition
      val set_over_proc_summary : t -> ProcName.t -> TS.transition -> unit
      val under_proc_summary : t -> ProcName.t -> TS.transition
      val set_under_proc_summary : t -> ProcName.t -> TS.transition -> unit
      val refine_over_summary : t -> ProcName.t -> TS.transition -> unit
      val refine_under_summary : t -> ProcName.t -> TS.transition -> unit
    end

module SilentSummaryProvider :
functor 
    (TS : sig 
        type t
        type transition
    end)
    (ProcName : sig
                type t = int * int
                val make : int * int -> t
                val string_of : t -> string
                val of_string : string -> t
                val compare : t -> t -> int
              end)
    ->
    sig
      type t 
      val init : TS.t -> int -> int -> t
      val over_proc_summary : t -> ProcName.t -> TS.transition
      val set_over_proc_summary : t -> ProcName.t -> TS.transition -> unit
      val under_proc_summary : t -> ProcName.t -> TS.transition
      val set_under_proc_summary : t -> ProcName.t -> TS.transition -> unit
      val refine_over_summary : t -> ProcName.t -> TS.transition -> unit
      val refine_under_summary : t -> ProcName.t -> TS.transition -> unit
    end
*)
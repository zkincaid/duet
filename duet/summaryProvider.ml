open Core
open Srk
open CfgIr
open BatPervasives
open Cra 

(*

include Log.Make(struct let name = "sgt" end)

module IntMap = BatMap.Make(Int)
module StringMap = BatMap.Make(String)
module DQ = BatDeque
module ARR = Batteries.DynArray 
type idq_t = int BatDeque.t 
type state_formula = Ctx.t Syntax.formula 
exception Mexception of string 




let log_formulas prefix formulas = 
  List.iteri (fun i f -> logf "[formula] %s(%i): %a\n" prefix i (Syntax.pp_expr srk) f) formulas 

let log_weights prefix weights = 
  List.iteri (fun i f -> logf "[weight] %s(%i): %a\n" prefix i K.pp f) weights


let log_model prefix model = 
  logf "[model] %s: %a\n" prefix Interpretation.pp model

module LeftRegularSummaryProvider  (Ctx: Srk.Syntax.Context)
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
= 
struct
  type t = {
    graph: TS.t;
    src: int;
    query: TS.query;
    rev_query: TS.reverse_query;
    silent: bool;
    monotone: bool;
  }
  let mk_query ts entry = TS.mk_query ts entry (if !monotone then (module MonotoneDom) else (module TransitionDom))

  let init (graph: TS.t) (src: int) (tgt: int) (enable_summary: bool) : t =
    let q = mk_query graph src in
    let rq = TS.mk_reverse_query q tgt in
    { graph = graph
    ; src = src
    ; query = q
    ; rev_query = rq
    ; silent = not enable_summary }
  

  let path_weight_intra (ctx: t) (src: int) (dst: int) =
      TS.exit_summary ctx.rev_query src dst
  
  let path_weight_inter (ctx: t) (src: int) =
      TS.target_summary ctx.rev_query src
  
end

module InterproceduralSummaryProvider(ProcName : sig
  type t = int * int 
  val make : TS.vertex * TS.vertex -> t
  val string_of : t -> string
  val of_string : string -> t
  val compare : t -> t -> int
end)
= 
  struct 
      module SMap = BatMap.Make(ProcName)
      type t = {
        graph: cfg_t;
        src: int;
        query: TS.query;
        rev_query: TS.reverse_query;
        mutable underapprox: K.t SMap.t;
        mutable overapprox: K.t SMap.t; (* Caution: used only for silent mode where no CRA-generated summaries are used. *)
      }

      let init (graph: cfg_t) (src: int) (tgt: int) : t =
        let q = mk_query graph src in
        let rq = TS.mk_reverse_query q tgt in
        { graph = graph
        ; src = src
        ; query = q
        ; rev_query = rq
        ; underapprox = SMap.empty
        ; overapprox = SMap.empty  }

      (** retrieve over-approximate procedure summary *)
      let over_proc_summary (ctx: t) ((u, v) : ProcName.t) =
          TS.get_summary ctx.query (u, v) 
          |> K.exists (V.is_global)
        
      (** set over-approximate procedure summary *)
      let set_over_proc_summary (ctx: t) ((u, v): ProcName.t) (w: K.t) =
            TS.set_summary ctx.query (u, v) w

      (** retrieve under-approximate procedure summary *)
      let under_proc_summary (ctx: t) ((u, v): ProcName.t) : K.t = 
        match SMap.find_default K.zero (u, v) ctx.underapprox
          |> K.project_mbp (V.is_global) 
        with
        | `Sat tr -> tr  
        |  _ -> 
          log_weights "under_proc_summary: this weight is unsat: " [SMap.find_default K.zero (u, v) ctx.underapprox];
          K.zero 
          (*failwith "under_proc_summary: cannot model-based project"*)
        
      (** set under-approximate procedure summary *)
      let set_under_proc_summary (ctx: t) ((u, v): ProcName.t) (w: K.t) : unit = 
        ctx.underapprox <- SMap.add (u, v) w ctx.underapprox

      (** refinement of procedure summaries using a two-voc transition formula *)
      let refine_over_summary (ctx: t) ((u, v): ProcName.t) (rfn: K.t) =
          over_proc_summary ctx (u, v) 
          |> K.conjunct rfn 
          |> set_over_proc_summary ctx (u, v)
        
      let refine_under_summary (ctx: t) ((u, v): ProcName.t) (w:K.t) : unit = 
        let summary = under_proc_summary ctx (u, v) in 
        let summary' = K.add summary w in 
        log_weights "under-approx summary refined to " [summary'];
        set_under_proc_summary ctx (u, v) summary'
      
  end

module SilentSummaryProvider(ProcName : sig
  type t = int * int 
  val make : TS.vertex * TS.vertex -> t
  val string_of : t -> string
  val of_string : string -> t
  val compare : t -> t -> int
end) = 
struct
    module SMap = BatMap.Make(ProcName)
    type t = {
      graph: cfg_t;
      src: int;
      mutable underapprox: K.t SMap.t;
      mutable overapprox: K.t SMap.t; (* Caution: used only for silent mode where no CRA-generated summaries are used. *)
    }

    let init (graph: cfg_t) (src: int) (tgt: int) : t =
      { graph = graph
      ; src = src
      ; underapprox = SMap.empty
      ; overapprox = SMap.empty  }

    (** retrieve over-approximate procedure summary *)
    let over_proc_summary (ctx: t) ((u, v) : ProcName.t) =
        match SMap.find_opt (u, v) ctx.overapprox with 
        | Some s -> s 
        | None -> 
          let init = K.assume @@ mk_true () in 
            ctx.overapprox <- SMap.add (u, v) init ctx.overapprox; 
            init  

    (** set over-approximate procedure summary *)
    let set_over_proc_summary (ctx: t) ((u, v): ProcName.t) (w: K.t) =
        match SMap.find_opt (u, v) ctx.overapprox with
        | Some s -> 
          ctx.overapprox <- SMap.add (u, v) (K.conjunct s w) ctx.overapprox
        | None -> 
          ctx.overapprox <- SMap.add (u, v) w ctx.overapprox

  (** retrieve under-approximate procedure summary *)
  let under_proc_summary (ctx: t) ((u, v): ProcName.t) : K.t = 
    match SMap.find_default K.zero (u, v) ctx.underapprox |> K.project_mbp (V.is_global) with
    | `Sat tr -> tr  
    |  _ -> 
      log_weights "under_proc_summary: this weight is unsat: " [SMap.find_default K.zero (u, v) ctx.underapprox];
      K.zero 

    (** set under-approximate procedure summary *)
    let set_under_proc_summary (ctx: t) ((u, v): ProcName.t) (w: K.t) : unit = 
      ctx.underapprox <- SMap.add (u, v) w ctx.underapprox

    (** refinement of procedure summaries using a two-voc transition formula *)
    let refine_over_summary (ctx: t) ((u, v): ProcName.t) (rfn: K.t) =
        match SMap.find_opt (u, v) ctx.overapprox with
        | Some s -> 
          ctx.overapprox <- SMap.add (u, v) (K.conjunct s rfn) ctx.overapprox
        | None -> 
          ctx.overapprox <- SMap.add (u, v) rfn ctx.overapprox
      
    let refine_under_summary (ctx: t) ((u, v): ProcName.t) (w:K.t) : unit = 
      let summary = under_proc_summary ctx (u, v) in 
      let summary' = K.add summary w in 
      log_weights "under-approx summary refined to " [summary'];
      set_under_proc_summary ctx (u, v) summary'
end
*)
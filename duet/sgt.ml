open Srk
module RG = Interproc.RG
module WG = Srk.WeightedGraph
module G = RG.G
module Int = SrkUtil.Int
module TF = TransitionFormula

module TransitionSystem = Srk.TransitionSystem
module Syntax = Srk.Syntax 
module Interpretation = Srk.Interpretation 

include Log.Make(struct let name = "sgt" end)
module DQ = BatDeque
module ARR = Batteries.DynArray 


module SummaryGuidedTesting      
(Ctx: Srk.Syntax.Context)
(** transition formula algebra *)
(K : sig
       type t
       val pp : Format.formatter -> t -> unit
       val guard : t -> Ctx.t Srk.Syntax.formula
       val assume : Ctx.t Srk.Syntax.formula -> t
       val interpolate_or_concrete_model : t list -> Ctx.t Srk.Syntax.formula 
             -> [`Valid of Ctx.t Srk.Syntax.formula list 
                  | `Invalid of Ctx.t Interpretation.interpretation | `Unknown ]
     end)
(TS : sig
    type vertex = int 
    type t 

    val edge_weight :
      t -> vertex -> vertex -> K.t Srk.TransitionSystem.label
    end)
(Summarizer : sig
  type t
  (** [init g s] returns a Summarizer.t type for a given transition system, source vertex pair (g, s). *)
  val init : TS.t -> TS.vertex -> TS.vertex -> bool -> t
  (** [path_weight_inter s u v] gives the inter-procedural path weight between (u, v) *)
  val path_weight_inter : t -> TS.vertex -> K.t
end)
(
  PathTree : sig
    type node
    type t
    exception Mexception of string
    val make : TS.t -> TS.vertex -> TS.vertex -> Summarizer.t -> t ref
    val get_err_loc : t ref -> TS.vertex
    val maps_to : t ref -> node -> TS.vertex
    val tree_path : t ref -> ?src:node -> node -> node list
    val expand :
      int -> t ref -> node -> Ctx.t Interpretation.interpretation -> (node * Ctx.t Interpretation.interpretation) list * node list

    val log_art : t ref -> unit 
    val of_node : node -> int
    val root : node
  end
) = struct 

  module IntMap = BatMap.Make(Int)
  module StringMap = BatMap.Make(String)
  type cfg_t = TS.t
  type idq_t = int BatDeque.t 
  type state_formula = Ctx.t Syntax.formula 
  exception Mexception of string 
  
  let mk_true () = Syntax.mk_true Ctx.context
  let mk_false () = Syntax.mk_false Ctx.context 
  
  let print_tree = false 
  
  let log_formulas prefix formulas = 
    List.iteri (fun i f -> logf "[formula] %s(%i): %a\n" prefix i (Syntax.pp_expr Ctx.context) f) formulas 
  
  let log_weights prefix weights = 
    List.iteri (fun i f -> logf "[weight] %s(%i): %a\n" prefix i K.pp f) weights
  
  
  let log_model prefix model = 
    logf "[model] %s: %a\n" prefix Interpretation.pp model  


  type context = {
    ts : cfg_t;
    entry : int;
    error : int;
    sum: Summarizer.t;
    pre_state : Ctx.t Syntax.formula;
    mutable art : PathTree.t ref;
    (* list for frontier nodes *)
    mutable worklist : PathTree.node DQ.t;
    (* list for executor states *)
    mutable execlist : (PathTree.node * Ctx.t Interpretation.interpretation) DQ.t;
  }

  let worklist_push  (i : 'a) (q : 'a DQ.t) = DQ.snoc q i 


  let run_test (ctx: context ref) =
    let round ctx = 
      match DQ.front (!ctx.execlist) with 
      | Some ((u, u_model), w) -> 
        if print_tree then 
          PathTree.log_art !ctx.art;
        logf " visit %d (%d)\n" (PathTree.of_node u) (PathTree.maps_to !ctx.art u);
        !ctx.execlist <- w;
        if (PathTree.maps_to !ctx.art u) = (PathTree.get_err_loc !ctx.art) then
          `Unsafe u 
        else begin
            logf "model of %d (%d): \n" (PathTree.of_node u) (PathTree.maps_to !ctx.art u);
            log_model "" u_model;
            let new_concolic_nodes, new_frontier_nodes = PathTree.expand 0 !ctx.art u u_model in 
              List.iter (fun concolic_node -> !ctx.execlist <- worklist_push concolic_node !ctx.execlist) new_concolic_nodes;
              List.iter (fun frontier_node -> !ctx.worklist <- worklist_push frontier_node !ctx.worklist) new_frontier_nodes;
              `Continue
        end
      | None -> 
        failwith "err: concolic_phase is reading from empty execution worklist" (* cannot happen *)
      in 
    let rtn = ref `Continue in 
      while !rtn = `Continue && ((DQ.size !ctx.execlist) > 0) do  
        rtn := round ctx 
      done;
    match !rtn with 
    | `Continue -> `Safe 
    | `Unsafe u -> `Unsafe u 


  let mk_context (ts: cfg_t) (entry: int) (error: int) (pre_state: state_formula) (enable_summary: bool) =
    let sum = Summarizer.init ts entry error enable_summary in 
    ref {
      ts = ts;
      entry = entry;
      error = error;
      sum = sum;
      pre_state = pre_state;
      art = PathTree.make ts entry error sum;
      worklist = DQ.empty;
      execlist = DQ.empty;
    }

    let path_condition (ctx: context ref) (v: PathTree.node) =
      let art = !ctx.art in 
      let cfg = !ctx.ts in 
      let art_nodes = PathTree.tree_path art v in 
      let cfg_nodes = List.map (fun x -> PathTree.maps_to art x) art_nodes in 
      let rec to_weights l : K.t Cra.label list = 
        match l with 
        | a :: b :: t -> 
          TS.edge_weight cfg a b :: (to_weights (b :: t)) 
        | _ -> []
        in 
      let pathcond = List.map (fun (weight: K.t Cra.label) -> 
        match weight with  
        | Call (_, _) -> failwith "encountered call edge"
        | Weight w -> w) (to_weights cfg_nodes) in 
        logf " ---- path_condition: path length: %d, before add1: %d\n" ((List.length pathcond)+1) (List.length pathcond);
      let l = (K.assume !ctx.pre_state) :: pathcond in 
          log_weights "path conditions " l; l
  

  let mk_post (ctx: context ref) (v: PathTree.node) =
    let art = !ctx.art in
    let post_path_summary = Summarizer.path_weight_inter (!ctx.sum) (PathTree.maps_to art v) in  
    log_weights "\npost_path_summary: " [post_path_summary];
    logf "\n";
    K.guard post_path_summary 

        

  (* Interpolate the path (entry) -> (CFG vertex corresponding to src node) -> (sink CFG vertex). If fail, then get model. *)
  let interpolate_or_get_model (ctx: context ref) (src : PathTree.node) = 
    let suffix = mk_post ctx src |> Syntax.mk_not Ctx.context in
    let prefix = path_condition ctx  src in 
    log_weights "\nprefix " prefix;
    log_formulas "\nsuffix " [suffix];
    logf "\n";
    K.interpolate_or_concrete_model prefix suffix


  let refine (ctx: context ref) (v: PathTree.node) = 
    logf "refining node %d\n" (PathTree.of_node v);
    let handle_failure v m = 
      logf " *********************** REFINEMENT FAILED *************************\n"; 
      let path_condition = path_condition ctx v 
      in `Failure (m, path_condition) 
    in
    match interpolate_or_get_model ctx v with 
    `Invalid v_model -> 
      logf "Unable to refine but got model\n";
      (* v is no longer a frontier node. *)
      handle_failure v v_model
    | `Unknown -> failwith "mc_refine: got UNKNOWN as a result for interpolate_or_get_model"
    | `Valid _ ->
      `Success 


  let execute (ts: cfg_t) (entry: int) (error: int) (pre_state: state_formula) (enable_summary: bool) : [`Safe | `Unsafe | `Error of string] = 
    let ctx = mk_context ts entry error pre_state enable_summary in 
    let state = ref `Unknown in 
      !ctx.worklist <- worklist_push (PathTree.root) !ctx.worklist;
      while (DQ.size !ctx.worklist > 0 || DQ.size !ctx.execlist > 0) && (!state = `Unknown) do
        logf " --- SGT: starting a new test execution phase\n";
        match run_test ctx with 
        | `Safe -> 
          begin match DQ.front !ctx.worklist with 
          | Some (u, worklist') -> 
            begin match refine ctx u with 
            | `Failure (m, _) -> 
              !ctx.execlist <- worklist_push (u, m) !ctx.execlist;
              !ctx.worklist <- worklist';
              state := `Unknown
            | `Success (* refinement succeeded. *) -> 
              logf " --- SGT: refinement success\n";
              !ctx.worklist <- worklist';
              state := `Unknown;
            end
          | None -> 
              state := `Safe 
          end
        | `Unsafe _ -> 
            logf " --- SGT: finished running, found a bug.\n";
            state := `Unsafe 
      done;
      logf " --- SGT: done performing execution.\n";
      match !state with 
      | `Unsafe -> `Unsafe 
      | `Unknown | `Safe -> `Safe 
end


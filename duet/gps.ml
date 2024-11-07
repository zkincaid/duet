open Core
open Srk
open CfgIr
open BatPervasives
open Cra 

(*module RG = Interproc.RG
module WG = WeightedGraph
module TLLRF = TerminationLLRF
module TDTA = TerminationDTA
module TPRF = TerminationPRF
module G = RG.G
(*module Ctx = Syntax.MakeSimplifyingContext ()*)
module Int = SrkUtil.Int
module TF = TransitionFormula*)
module TS = TransitionSystem.Make(Ctx)(V)(K)

include Log.Make(struct let name = "gps" end)

module ProcName = struct 
  type t = int * int 

  let make ((u, v) : TS.vertex * TS.vertex) : t = (u, v)

  let string_of (p: t) = 
    let u, v = p in Printf.sprintf "%d:%d" u v 
  
  let of_string (s: string) = 
    match String.split_on_char ':' s with 
    | [ us ; vs ] -> (make ((int_of_string us), (int_of_string vs)))
    | _ -> failwith @@ Printf.sprintf "illegal procedure identifier %s" s

  (* lexicographic comparison using Stdlib.compare *)
  let compare (p1: t) (p2: t) = Stdlib.compare p1 p2 
end

module ProcMap = BatMap.Make(ProcName)
module IntMap = BatMap.Make(Int)
module StringMap = BatMap.Make(String)
module ISet = BatSet.Make(Int)
module DQ = BatDeque
module ARR = Batteries.DynArray 
type cfg_t = TSG.t
type idq_t = int BatDeque.t 
type state_formula = Ctx.t Syntax.formula 
exception Mexception of string 
let mk_true () = Syntax.mk_true Ctx.context
let mk_false () = Syntax.mk_false Ctx.context 
let mk_query ts entry = TS.mk_query ts entry (if !monotone then (module MonotoneDom) else (module TransitionDom))

let log_formulas prefix formulas = 
  List.iteri (fun i f -> logf "[formula] %s(%i): %a\n" prefix i (Syntax.pp_expr srk) f) formulas 

let log_weights prefix weights = 
  List.iteri (fun i f -> logf "[weight] %s(%i): %a\n" prefix i K.pp f) weights


let log_model prefix model = 
  logf "[model] %s: %a\n" prefix Interpretation.pp model

(*
let assert_i = ref 0
let new_assert_var cond = 
  let i = !assert_i in 
  let name = "__assert" ^ (string_of_int i) in 
  let v = Varinfo.mk_global name (Concrete (Int 8)) |> Var.mk in 
  let assert_var = Syntax.mk_symbol srk ~name:name `TyInt in 
  let assert_term = Syntax.mk_const srk assert_var in 
  assert_i := !assert_i + 1;
  K.assign v cond

let process_interproc_assertion (ts: cfg_t) (phi: Ctx.formula) v = 
  let a_var, a_term = new_assert_var @@ Ctx.mk_not phi in 

*)

(* Convert assertion checking problem to vertex reachability problem. *)
let make_ts_assertions_unreachable (ts : cfg_t) assertions = 
  let err_loc = 1 + (WG.fold_vertex (fun v max -> if v > max then v else max) ts 0) in
  let ts = WG.add_vertex ts err_loc in
  let ts =
    SrkUtil.Int.Map.fold (fun v (phi, _, _) ts ->
        let s = Printf.sprintf " Adding assertion node %d -> %d for label " v err_loc in 
        log_formulas s [ Ctx.mk_not phi ] ; 
        WG.add_edge ts v (Weight (K.assume (Ctx.mk_not phi))) err_loc)
      assertions
      ts
  in
  (ts, err_loc)

let instrument_with_rets (ts : cfg_t) : cfg_t = 
  let mk_int k = Ctx.mk_real (QQ.of_int k) in 
  let largest = ref (WG.fold_vertex (fun v max -> if v > max then v else max) ts 0) in 
  let new_vtx () = 
    largest := !largest + 1; !largest in
  let hazard_var = Var.mk (Varinfo.mk_global "__duet_hazard" (Concrete (Int 8))) in 
  let hazard_var_sym = Syntax.mk_symbol srk ~name:"__duet_hazard" `TyInt in 
  let hazard_var_term = Syntax.mk_const srk hazard_var_sym in 
    let open Syntax.Infix(Ctx) in 
    let assume_true = K.assume (Syntax.mk_eq srk (hazard_var_term) (mk_int 1)) in
    let assign_zero = K.assign (VVal hazard_var) (mk_int 0) in 
    let assign_one  = K.assign (VVal hazard_var) (mk_int 1) in 
  let all_succs u = WG.U.succ u in 
  let _ = 
    Hashtbl.add V.sym_to_var hazard_var_sym (VVal hazard_var);
    ValueHT.add V.var_to_sym (VVal hazard_var) hazard_var_sym
  in ts

let instrument_with_gas (ts: cfg_t) = 
  let mk_int k = Ctx.mk_real (QQ.of_int k) in 
  let largest = ref (WG.fold_vertex (fun v max -> if v > max then v else max) ts 0) in 
  let new_vtx () = 
    largest := !largest + 1; !largest in
  let gas_var = Var.mk (Varinfo.mk_global "__duet_gas" (Concrete (Int 8))) in 
  let gas_var_sym = Syntax.mk_symbol srk ~name:"__duet_gas" `TyInt in  
  let gas_var_term = Syntax.mk_const srk gas_var_sym in 
  Hashtbl.add V.sym_to_var gas_var_sym (VVal gas_var);
  ValueHT.add V.var_to_sym (VVal gas_var) gas_var_sym;
  let gasexpr =
    let assume_positive = K.assume (Syntax.mk_lt srk (mk_int 0) gas_var_term) in
    let decr_by_one =
      Syntax.mk_sub srk gas_var_term (mk_int 1) |> K.assign (VVal gas_var)
    in
    K.mul assume_positive decr_by_one
  in
  (* for each call-edge, u->v, add new predecessor edge x->u->v where x->u is an instrumented edge. *)
  let loop_headers = 
    let module L = Loop.Make(TSG) in 
    List.map (fun loop -> L.header loop) @@ L.all_loops (L.loop_nest ts) in 
  let call_edge_headers = 
    WG.fold_edges (fun (u, w, _) ls -> 
      match w with 
      | Call _ -> u :: ls 
      | _ -> ls) ts [] in 
  let modify ts u =
    let g = ref ts in 
    (* step 1: add new in-edge to (u, v) *) 
    let x = new_vtx () in 
      g := WG.add_vertex !g x;
      (* step 2: add weighted edge x-(gasexpr)->u *)
      g := WG.add_edge !g x (Weight gasexpr) u;
      (* step 3: redirect every p->u to be y->x->u *)
      WG.iter_pred_e (fun (p, weight, _) -> 
        g := WG.add_edge !g p weight x;
        g := WG.remove_edge !g p u  
        ) ts u;
      !g in 
  let g = ref ts in 
  List.iter (fun u -> g := modify !g u) (loop_headers @ call_edge_headers);
  !g

module Summarizer = 
  struct 
      module SMap = BatMap.Make(ProcName)
      type t = {
        graph: cfg_t;
        src: int;
        query: TS.query;
        rev_query: TS.reverse_query;
        mutable underapprox: K.t SMap.t;
        mutable overapprox: K.t SMap.t; (* Caution: used only for silent mode where no CRA-generated summaries are used. *)
        silent: bool;
      }

      let init (graph: cfg_t) (src: int) (tgt: int) (enable_summary: bool) : t =
        let q = mk_query graph src in
        let rq = TS.mk_reverse_query q tgt in
        { graph = graph
        ; src = src
        ; query = q
        ; rev_query = rq
        ; underapprox = SMap.empty
        ; overapprox = SMap.empty  
        ; silent = not enable_summary }


      let filt_over (ctx: t) x = 
        if ctx.silent then begin 
          logf "filt_over: context is silent! \n";
          K.assume @@ mk_true ()  
        end 
        else begin 
          logf "filt_over: context isn't silent!\n";
          x end
      
      let filt_under (ctx: t) x = 
        if ctx.silent then K.assume @@ mk_false ()
        else x 

      (** retrieve over-approximate procedure summary *)
      let over_proc_summary (ctx: t) ((u, v) : ProcName.t) =
        if ctx.silent then begin 
          match SMap.find_opt (u, v) ctx.overapprox with 
          | Some s -> s 
          | None -> 
            let init = K.assume @@ mk_true () in 
            ctx.overapprox <- SMap.add (u, v) init ctx.overapprox; init  
        end else
          TS.get_summary ctx.query (u, v) 
          |> K.exists (V.is_global)
        
      (** set over-approximate procedure summary *)
      let set_over_proc_summary (ctx: t) ((u, v): ProcName.t) (w: K.t) =
        if ctx.silent then begin
          match SMap.find_opt (u, v) ctx.overapprox with
          | Some s -> 
            ctx.overapprox <- SMap.add (u, v) (K.conjunct s w) ctx.overapprox
          | None -> 
            ctx.overapprox <- SMap.add (u, v) w ctx.overapprox;
          end else 
            TS.set_summary ctx.query (u, v) w

      (** retrieve under-approximate procedure summary *)
      let under_proc_summary (ctx: t) ((u, v): ProcName.t) : K.t = 
        SMap.find_default K.zero (u, v) ctx.underapprox
        |> K.exists (V.is_global) 
        
      (** set under-approximate procedure summary *)
      let set_under_proc_summary (ctx: t) ((u, v): ProcName.t) (w: K.t) : unit = 
        ctx.underapprox <- SMap.add (u, v) w ctx.underapprox

      (** refinement of procedure summaries using a two-voc transition formula *)
      let refine_over_summary (ctx: t) ((u, v): ProcName.t) (rfn: K.t) =
        if ctx.silent then begin 
          match SMap.find_opt (u, v) ctx.overapprox with
          | Some s -> 
            ctx.overapprox <- SMap.add (u, v) (K.conjunct s rfn) ctx.overapprox
          | None -> 
            ctx.overapprox <- SMap.add (u, v) rfn ctx.overapprox
        end else 
          over_proc_summary ctx (u, v) 
          |> K.conjunct rfn 
          |> set_over_proc_summary ctx (u, v)
        
      let refine_under_summary (ctx: t) ((u, v): ProcName.t) (w:K.t) : unit = 
        let summary = under_proc_summary ctx (u, v) in 
        let summary' = K.add summary w in 
        log_weights "under-approx summary refined to " [summary'];
        set_under_proc_summary ctx (u, v) summary'
      
      let path_weight_intra (ctx: t) (src: int) (dst: int) =
          TS.exit_summary ctx.rev_query src dst
          |> filt_over ctx 
      
      let path_weight_inter (ctx: t) (src: int) =
          TS.target_summary ctx.rev_query src
          |> filt_over ctx 
      
  end


  type path_type = 
    | OverApprox 
    | UnderApprox

let log_labelled_weights s uu prefix weights = 
  List.iteri 
    (fun i f -> 
      match f with 
      | Call (u, v)-> 
        let p = 
          begin match uu with 
          | OverApprox -> Summarizer.over_proc_summary s (ProcName.make (u, v)) 
          | UnderApprox -> Summarizer.under_proc_summary s (ProcName.make (u, v)) 
        end in 
        logf "[labelled weight] %s(%i, call(%d,%d)): %a\n" prefix i u v K.pp p
      | Weight w -> 
        logf "[labelled weight] %s(%i): %a\n" prefix i K.pp w) weights

let srk = Ctx.context 

module GPS = struct
  (* vertex names module *)
  module VN = struct 
    let to_vertex (v : int) : TS.vertex = v 
    let of_vertex (v : TS.vertex) : int = v
  end
  (* we need to augment the `TS` module to include some extra stuff. *)
  module TS' = struct 
    include TS
    let iter_succ_e (f: (TS.vertex * (TS.transition label) * TS.vertex) -> unit) (g: TS.t) (v: TS.vertex) = WG.iter_succ_e f g v
    
    let fold_succ_e (f : (TS.vertex * (TS.transition label) * TS.vertex) -> 'b -> 'b) (g: TS.t) (u: TS.vertex) (s: 'b) = 
      WG.fold_succ_e f g u s 

    let edge_weight g u v = WG.edge_weight g u v 
  end
  (* ART module *)
  module ReachTree = ReachTree.ART(Ctx)(K)(TS')(ProcName)(VN)(Summarizer)

  (* to print the reachability tree (+ worklist), or not *) 
  let print_tree = false

  type global_context = {
    interproc: Summarizer.t;
  }
  and mc_result = 
    | Safe of K.t 
    | Unsafe of K.t


  (* contextual information maintained by GPS algorithm. *)
  (* intraprocedural context *)
  type intra_context = {
    id : ProcName.t;
    ts : cfg_t;
    recurse_level : int;
    precondition : K.t;
    pre_state : Ctx.t Syntax.formula;
    equalities: value ValueHT.t;
    mutable art : ReachTree.t ref;
    mutable worklist : ReachTree.node DQ.t;
    mutable execlist : (ReachTree.node * Ctx.t Interpretation.interpretation) DQ.t;
    global_ctx : global_context ref;
  } 
  (* global context *)
  (** some helper functions that operate on the context *)


  let demote_precondition (precondition: K.t) =
    let pre_guard, pre_transform = K.guard precondition, K.transform precondition in 
    let pre_state = ref @@ pre_guard in 
    let equalities = ValueHT.create 991 in 
    BatEnum.iter (fun (var, asgn) -> 
      let prophecy_var = V.prophesize var in 
      let prophecy_sym = V.symbol_of prophecy_var in 
      let prophecy_term = Syntax.mk_const srk prophecy_sym in 
      ValueHT.add equalities var prophecy_var;
      pre_state := Syntax.mk_and srk [!pre_state; (Syntax.mk_eq srk prophecy_term asgn)]) pre_transform;
    !pre_state, equalities 
  

  (* promote an arbitrary state formula (not necessarily the pre-state) to a transition formula. *)
  (* To do so, we substitute in fresh skolem symbols for all prophecy variables inside [f], and *)
  (* create a transform map, treating the substituted formula as guard. *)
  let promote (f : Ctx.t Syntax.formula) = 
    let sym_map = ValueHT.create 991 in 
    let substitute = Memo.memo (fun sym -> 
      match V.of_symbol sym with
      | Some v ->
        begin match V.var_of_prophecy_var v with 
        | Some original_var ->
          let fresh_skolem = Syntax.mk_symbol srk (Syntax.typ_symbol srk sym) in 
          let term = Syntax.mk_const srk fresh_skolem in 
          ValueHT.add sym_map original_var term;
          term 
        | None -> Syntax.mk_const srk sym 
        end
      | None -> Syntax.mk_const srk sym) in 
    K.construct (Syntax.substitute_const srk substitute f) (ValueHT.to_seq sym_map |> List.of_seq)


  let mk_intra_context (gctx: global_context ref) (id: ProcName.t) (ts: cfg_t) (recurse_level: int) (precondition: K.t) (entry: int) (err_loc: int)  =
    let pre_state, equalities = demote_precondition precondition in  
    ref {
      id = id;
      ts = ts;
      recurse_level = recurse_level;
      precondition = precondition;
      pre_state = pre_state;
      equalities = equalities;
      worklist = DQ.empty;
      execlist = DQ.empty;
      art = ReachTree.make ts entry err_loc pre_state !gctx.interproc;
      global_ctx = gctx;
    }
  and mk_mc_context (global_cfg: cfg_t) (global_src: int) (err_loc: int) enable_summary = 
    ref {
      interproc = Summarizer.init global_cfg global_src err_loc enable_summary;
    }

  (** place an element in front of the deque (worklist) *)
  let worklist_push  (i : 'a) (q : 'a DQ.t) = DQ.snoc q i 

  let get_summarizer intra_ctx = 
    !(!intra_ctx.global_ctx).interproc 

  let make_equalities (ctx: intra_context ref) = 
    ValueHT.fold (fun k v acc -> 
      let s = V.symbol_of k |> Syntax.mk_const srk in 
      let s' = V.symbol_of v |> Syntax.mk_const srk in 
      Syntax.mk_eq srk s s' :: acc) !ctx.equalities [Syntax.mk_true srk]
    |> Syntax.mk_and srk 

  let oracle ctx u v = 
    if !ctx.recurse_level = 0 then Summarizer.path_weight_inter (get_summarizer ctx) u
      else Summarizer.path_weight_intra (get_summarizer ctx) u v

  let rec art_cfg_path_pair (ctx: intra_context ref) (p: ReachTree.node list) = 
    match p with 
    | u :: v :: t ->
      let u_vtx = ReachTree.maps_to !ctx.art u in 
      let v_vtx = ReachTree.maps_to !ctx.art v in 
      (u, (u_vtx, v_vtx), v) :: (art_cfg_path_pair ctx (v :: t))
    | _ -> []

  (* turn tree path into a sequence of CFG edges. *)
  let rec cfg_path (ctx: intra_context ref) (p : ReachTree.node list) = 
    art_cfg_path_pair ctx p 
    |> List.map (fun (_, (u, v), _) -> (u, v))
  
  (* CFG path condition from art.src -> art.v *)
  let path_condition (ctx: intra_context ref) condition_type (v: ReachTree.node) =
    let art = !ctx.art in 
    let summarizer = get_summarizer ctx in   
    let cfg = !ctx.ts in 
    let art_nodes = ReachTree.tree_path art v in 
    let cfg_nodes = List.map (fun x -> ReachTree.maps_to art x) art_nodes in 
    let rec to_weights l : K.t label list = 
      match l with 
      | a :: b :: t -> 
        WG.edge_weight cfg a b :: (to_weights (b :: t)) 
      | _ -> []
      in 
    let pathcond = List.map (fun (weight: K.t label) -> 
      match weight with  
      | Call (src, dst) -> 
        begin match condition_type with 
        | OverApprox -> Summarizer.over_proc_summary summarizer (ProcName.make (src, dst))
        | UnderApprox -> Summarizer.under_proc_summary summarizer (ProcName.make (src, dst)) 
        end
      | Weight w -> w) (to_weights cfg_nodes) in 
      logf " ---- path_condition: path length: %d, before add1: %d\n" ((List.length pathcond)+1) (List.length pathcond);
    let l = (K.assume !ctx.pre_state) :: pathcond in 
        log_weights "path conditions " l; l

  let mk_post (ctx: intra_context ref) (v: ReachTree.node) (sink: TS.vertex) = 
    let art = !ctx.art in
    let post_path_summary = oracle ctx (ReachTree.maps_to art v) sink in  
    let equalities = make_equalities ctx |> K.assume in 
    log_weights "\npost_path_summary: " [post_path_summary];
    log_weights "\nequalities: " [equalities];
    logf "\n";
    K.guard (K.mul post_path_summary equalities) 

  (* Interpolate the path (entry) -> (CFG vertex corresponding to src node) -> (sink CFG vertex). If fail, then get model. *)
  let interpolate_or_get_model (ctx: intra_context ref) (src : ReachTree.node) (sink: TS.vertex) = 
    let suffix = mk_post ctx src sink |> Syntax.mk_not srk in
    let prefix = path_condition ctx OverApprox src in 
    log_weights "\nprefix " prefix;
    log_formulas "\nsuffix " [suffix];
    logf "\n";
    K.interpolate_or_concrete_model prefix suffix

  let get_global_ctx (ctx: intra_context ref) = (!ctx.global_ctx)

  (* refine path to (tree) node v. 
     Returns `Failure (u, m) with (u, m) being a new item to the concolic worklist if unable to refine.
     Returns `Success if refine is able to refine. *)
  let mc_refine (ctx: intra_context ref) (v: ReachTree.node) = 
    let handle_failure v m = 
      logf " *********************** REFINEMENT FAILED *************************\n"; 
      let path_condition = path_condition ctx OverApprox v 
      in `Failure (m, path_condition) 
    in let art = !ctx.art in 
    let path = ReachTree.tree_path art v in 
      match interpolate_or_get_model ctx v @@ ReachTree.get_err_loc art with 
      `Invalid v_model -> 
        logf "Unable to refine but got model\n";
        (* v is no longer a frontier node. *)
        handle_failure v v_model
      | `Unknown -> failwith "mc_refine: got UNKNOWN as a result for interpolate_or_get_model"
      | `Valid interpolants ->
        logf "--- mc_refine: interpolation succeeded. path length %d, interpolant length %d" (List.length path) (List.length interpolants);
        ReachTree.refine art path interpolants
        |> List.iter (fun x -> !ctx.worklist <- worklist_push x !ctx.worklist); 
        `Success 

  (* concolic phase of our model checking algorithm *)
  let concolic_phase (ctx: intra_context ref) =
    let round ctx = 
      match DQ.front (!ctx.execlist) with 
      | Some ((u, u_model), w) -> 
        if print_tree then 
        ReachTree.log_art !ctx.art;
        logf " visit %d (%d)\n" (ReachTree.of_node u) (ReachTree.maps_to !ctx.art u);
        !ctx.execlist <- w;
        if (ReachTree.maps_to !ctx.art u) = (ReachTree.get_err_loc !ctx.art) then
          begin match Smt.is_sat srk (make_equalities ctx) with 
          | `Sat -> 
          `ErrorReached u
          | _ -> !ctx.worklist <- worklist_push u !ctx.worklist; `Continue
          end
        else begin
            logf "model of %d (%d): \n" (ReachTree.of_node u) (ReachTree.maps_to !ctx.art u);
            log_model "" u_model;
            let new_concolic_nodes, new_frontier_nodes = ReachTree.expand !ctx.recurse_level !ctx.art u u_model in 
              List.iter (fun concolic_node -> !ctx.execlist <- worklist_push concolic_node !ctx.execlist) new_concolic_nodes;
              List.iter (fun frontier_node -> !ctx.worklist <- worklist_push frontier_node !ctx.worklist) new_frontier_nodes;
              `Continue
        end
      | None -> failwith "err: concolic_phase is reading from empty execution worklist" (* cannot happen *)
      in 
    let rtn = ref `Continue in 
    while !rtn = `Continue && ((DQ.size !ctx.execlist) > 0) do  
      rtn := round ctx 
    done;
    match !rtn with 
    | `Continue -> `Safe 
    | `ErrorReached u -> `Unsafe u 


  (* refinement phase of our model checking algorithm *)
  let refinement_phase (ctx: intra_context ref) = 
    let worklist_push_all ls = 
      List.iter (fun x -> !ctx.worklist <- worklist_push x !ctx.worklist) ls in 
    match DQ.front (!ctx.worklist) with 
    | Some (u, w) -> 
      if print_tree then 
      ReachTree.log_art !ctx.art;
      !ctx.worklist <- w;
      (* Fetched tree node u from work list. First attempt to close it. *)
      if not (ReachTree.is_covered !ctx.art u) then 
        begin
          logf " uncovered. try close\n";
          begin match ReachTree.lclose !ctx.art u with (* Close succeeded. No need to further explore it. *)
          | true, leaves ->  
            logf "Close succeeded.\n"; 
            worklist_push_all leaves;
            `Continue
          | false, leaves -> (* u is uncovered. *)
            worklist_push_all leaves;
            begin match mc_refine ctx u with 
              | `Success -> (* refinement succeeded *)
                logf "refinement_phase: refinement succeeded\n";
                (* for every node along path of refinement try close *)
                let path = ReachTree.tree_path !ctx.art u in 
                  List.iter 
                    (fun x -> let (_, ls) = ReachTree.close !ctx.art x in 
                      worklist_push_all ls) path;
                  `Continue 
              | `Failure (u_m, _) -> 
                !ctx.execlist <- worklist_push (u, u_m) !ctx.execlist; (* put u onto execlist since it now has a model. *)
                (* for every node along path of refinement try close *)
                let path = ReachTree.tree_path !ctx.art u in 
                  List.iter (fun x -> let (_, ls) = ReachTree.close !ctx.art x in 
                    worklist_push_all ls) path 
                ; `Continue
              end
          end
        end
      else begin 
        logf "refinement_phase: %d is covered\n" (ReachTree.of_node u);
        `Continue
      end
    | None -> failwith "refinement_phase: encountered an empty worklist for refinement\n" (* cannot happen *)


  let extract_refinement (ctx: intra_context ref) = 
    let art = !ctx.art in
    let rfn = ReachTree.label art ReachTree.root |> promote in 
    K.exists (fun v -> V.is_global v) rfn 
  
  let seq = List.fold_left K.mul K.one (* sequentially multiply, left-right *)


  let rec handle_path_to_error ctx left curr right dir err_leaf : [`Unsafe of K.t | `Safe] = 
    let handle_right_case caller_id = 
      let f = List.map (fun (_, w, _) -> w) in 
      let left = f left in 
      let right = f right in
      match K.project_mbp (V.is_global) (path_condition ctx UnderApprox err_leaf |> seq) with 
      | `Sat t -> `Unsafe t 
      | _ -> 
        logf " ------------------------ handle_path_to_error debug info: called by case %s ------------------\n" caller_id; 
        log_weights "faulty weight: " (path_condition ctx UnderApprox err_leaf);
        logf "\nlength of left path: %d" (List.length left);
        logf "\nlength of right path: %d" (List.length right);
        logf "\nPrinting left path... \n";
        log_labelled_weights (get_summarizer ctx) UnderApprox "left path - " left;
        failwith "error: handle_path_to_error: cannot project path condition" in 
    let handle_left_case caller_id =
      logf "handle_path_to_error: %s\n" caller_id;
      `Safe in 
    match curr with 
    | (_, Weight _, _) -> 
      begin match left, dir, right with 
      | [], `Left, _ -> 
        handle_left_case "reached leftmost item, `curr` variable is NOT a call-edge" 
      | _, `Right, [] -> 
          handle_right_case "reached rightmost item, `curr` variable is NOT a call-edge" 
      | a :: left', `Left, _ -> handle_path_to_error ctx left' a (curr :: right) dir err_leaf 
      | _, `Right, a :: right' -> handle_path_to_error ctx (curr :: left) a right' dir err_leaf 
      end
    | (u, (Call (src, dst)), _) ->
      let prefix = path_condition ctx UnderApprox u |> seq in 
      let suffix = 
        List.map (fun (_, ew, _) -> 
          match ew with 
          | Weight w -> w 
          | Call (s, t) -> Summarizer.over_proc_summary (get_summarizer ctx) (ProcName.make (s, t))) 
        right 
        |> seq in 
      let summary = Summarizer.over_proc_summary (get_summarizer ctx) (ProcName.make (src, dst)) in 
      begin match K.contextualize prefix summary suffix with 
      | `Sat query -> 
        let answer =
          mk_intra_context (!ctx.global_ctx) (ProcName.make (src, dst)) !ctx.ts  (!ctx.recurse_level + 1) query src dst 
          |> intraproc_check 
        in begin match answer with 
           | Safe r -> 
            Summarizer.refine_over_summary (get_summarizer ctx) (ProcName.make (src, dst)) r;
            handle_path_to_error ctx left curr right dir err_leaf
           | Unsafe trs -> 
            begin match trs |> K.project_mbp (V.is_global) with 
            | `Sat tr -> 
              Summarizer.refine_under_summary (get_summarizer ctx) (ProcName.make (src, dst)) tr;
              begin match right with 
              | a :: right' -> 
                handle_path_to_error ctx (curr::left) a right' `Right err_leaf 
              | [] -> (* we're done *) 
                handle_right_case "rightmost edge is call-edge, underapproximation successful"
              end
            | _ -> failwith "error: cannot do mbp on returned error trace in handle_path_to_error" 
            end
        end
      | `Unsat -> (* procedure summary at `curr` is UNSAT, so backtrack *) 
        begin match left with 
        | a :: left' -> 
          handle_path_to_error ctx left' a (curr :: right) `Left err_leaf
        | [] -> (* at the very left. we're done *)
           handle_left_case "at the leftmost edge, is a call-edge, done"
      end
      end
  
    
  and intraproc_check (ctx: intra_context ref) : mc_result = 
    logf " *********************************************** recurse_level: %d\n" !ctx.recurse_level;
    let continue = ref true in 
    let state = ref `Continue in
      !ctx.worklist <- worklist_push (ReachTree.root) !ctx.worklist; 
      while !continue && (DQ.size (!ctx.worklist) > 0 || DQ.size (!ctx.execlist) > 0) do
        if DQ.size (!ctx.execlist) > 0 then begin 
          (* concolic phase *)
          begin match concolic_phase ctx with 
          | `Unsafe w -> 
            logf "--- concolic_mcmillan_execute: found path-to-error at tree node %d (cfg vertex %d) \n" (ReachTree.of_node w) (ReachTree.maps_to !ctx.art w);
            let path_to_w = 
              ReachTree.tree_path !ctx.art w 
              |> art_cfg_path_pair ctx 
              |> List.map (fun (u, (u_vtx, v_vtx), v) -> (u, WG.edge_weight !ctx.ts u_vtx v_vtx, v)) in
            begin match path_to_w with 
            | curr :: right -> 
              begin match handle_path_to_error ctx [] curr right `Right w with 
                | `Safe -> (* path-to-error concretization failed. frontier_node is the src node of a call-edge. *)
                  (* we can mark `w` as a frontier node to be refined, and continue. *)
                  !ctx.worklist <- worklist_push w !ctx.worklist;
                  continue := true
                | `Unsafe pathcond ->  
                  logf "--- conoclic_mcmilan_execute: managed to concretize an intraprocedural path-to-error. returning... ";
                  state := `Concretized (pathcond);
                  continue := false
                end
            | [] -> 
              (* corner case: the path to error is of length 0. *)
              state := `Concretized (K.one)  
            end
          | `Safe -> 
            state := `Continue
          end
        end else begin 
          (* refinement phase *)
          state := refinement_phase ctx
        end
      done; 
      match !state with 
      | `Continue -> Safe (extract_refinement ctx)
      | `Concretized cond -> Unsafe (cond) 
  

  let execute (ts : cfg_t) (entry : int) (err_loc : int) (enable_summary:bool) : mc_result = 
    (**
    * Set up data structures used by the algorithm: worklist, 
    * vtxcnt (keeps track of largest unused vertex number in tree), 
    * ptt is a pointer to the reachability tree.
    *)
    let global_context = mk_mc_context ts entry err_loc enable_summary in 
    logf "executing concolic mcmillan's algorithm\n";
    (*let ts_with_gas = instrument_with_gas ts in *)
    let main_context = mk_intra_context global_context (entry, err_loc) ts 0 K.one entry err_loc in 
    intraproc_check main_context 
    end


module BM = BatMap.Make(Int)


let analyze_concolic_mcl enable_gas enable_summary file = 
  let open Srk.Iteration in 
  populate_offset_table file;
  K.domain := split (product [ PolyhedronGuard.exp
                             ; LossyTranslation.exp ]);
  match file.entry_points with
  | [main] -> begin
      let rg = Interproc.make_recgraph file in
      let entry = (RG.block_entry rg main).did in
      let (ts, assertions) = make_transition_system rg in
      let ts = if enable_gas then instrument_with_gas ts else ts in
      let ts, err_loc = make_ts_assertions_unreachable ts assertions in 
      if !CmdLine.display_graphs then TSDisplay.display ts;
      logf "\nentry: %d\n" entry; 
      Printf.printf "testing reachability of location %d\n" err_loc ; 
      Printf.printf "------------------------------\n";
      begin match GPS.execute ts entry err_loc enable_summary with 
      | Safe _ -> Printf.printf "  proven safe\n";
      | Unsafe _ -> Printf.printf "  proven unsafe\n"
      end;
      Printf.printf "------------------------------\n"
    end
  | _ -> assert false

(** dump simplified CFG before doing model checking / CRA / concolic execution *)
let dump_cfg simplify file = 
  populate_offset_table file;
  match file.entry_points with 
  | [main] ->
    begin 
      let rg = Interproc.make_recgraph file in 
      let _ (* entry *) = (RG.block_entry rg main).did in 
      let (ts, assertions) = make_transition_system ~simplify:simplify rg in 
      let ts, _ = make_ts_assertions_unreachable ts assertions in 
      TSDisplay.display ts
    end
  | _ -> assert false

let _ = 
  CmdLine.register_pass 
    ("-mcl-concolic", analyze_concolic_mcl false true, " GPS model checking algorithm");
  CmdLine.register_pass
    ("-mcl-concolic-gas", analyze_concolic_mcl true true, " GPS model checking algorithm");
  CmdLine.register_pass
    ("-mcl-concolic-nosum", analyze_concolic_mcl false false, "GPS without CRA-generated summary");
  CmdLine.register_pass
    ("-dump-unsimplified-cfg", dump_cfg false, "dump unsimplified CFG");
  CmdLine.register_pass
    ("-dump-simplified-cfg", dump_cfg true, "dump simplified CFG")
open Core
open Srk
open CfgIr
open BatPervasives
open Cra

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
  let hash = Hashtbl.hash
  let equal = (=)
end

module ProcHT = BatHashtbl.Make(ProcName)
module ProcMap = BatMap.Make(ProcName)
module IntMap = BatMap.Make(Int)
module StringMap = BatMap.Make(String)
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

module Summarizer =
  struct
      module SMap = BatMap.Make(ProcName)
      type t = {
        query: TS.query;
        rev_query: TS.reverse_query;
        mutable underapprox: K.t SMap.t;
        mutable overapprox: K.t SMap.t; (* Caution: used only for silent mode where no CRA-generated summaries are used. *)
        silent: bool;
      }

      let init (graph: cfg_t) (src: int) (tgt: int) (enable_summary: bool) : t =
        let q = mk_query graph src in
        let rq = TS.mk_reverse_query q tgt in
        { query = q
        ; rev_query = rq
        ; underapprox = SMap.empty
        ; overapprox = SMap.empty
        ; silent = not enable_summary }


      let filt_over (ctx: t) x =
        if ctx.silent then begin
          (*logf "filt_over: context is silent! \n";*)
          K.assume @@ mk_true ()
        end
        else begin
          (*logf "filt_over: context isn't silent!\n";*)
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

let srk = Ctx.context

module GPS = struct
  module Graph = struct
    type t =
      { graph : cfg_t
      ; call_summary : ProcName.t -> K.t
      ; target_summary : int -> K.t }

    type vertex = TS.vertex

    type weight = K.t

    let edge_label g u v = WG.edge_weight g.graph u v

    let weight g u v =
      match WG.edge_weight g.graph u v with
      | Call (src, dst) ->
         g.call_summary (src, dst)
      | Weight w -> w

    let fold_succ f g u acc =
      WG.U.fold_succ f (WG.forget_weights g.graph) u acc

    let summary g src = g.target_summary src

    let compare_vertex = Stdlib.compare
    let pp_vertex = Format.pp_print_int
  end

  module Label = struct
    type t = Ctx.t Syntax.formula
    let top = Ctx.mk_true
    let bottom = Ctx.mk_false
    let meet f g = Ctx.mk_and [f; g]
    let leq f g =
      match Smt.entails Ctx.context f g with
      | `Yes -> true
      | _ -> false
    let negate f = Ctx.mk_not f
    let pp = Syntax.Formula.pp srk
  end
  module Transition = struct
    type t = K.t
    type label = Ctx.t Syntax.formula
    type state = Ctx.t Interpretation.interpretation
    let check pre trs post =
      K.interpolate_or_concrete_model ((K.assume pre)::trs) post

    let is_deterministic =
      let is_det tr =
        not (K.contains_havoc tr) || K.is_deterministic tr
      in
      Memo.memo is_det

    let post_model = K.get_post_model
    let pp = K.pp
    let mul = K.mul
    let assume = K.assume
    let guard = K.guard
    let pp_state = Interpretation.pp
  end

  (* ART module *)
  (*  module ReachTree = ReachTree.ART(Ctx)(K)(TS')(ProcName)(VN)(Summarizer)*)
  module ReachTree = ReachTree.ART(Graph)(Label)(Transition)

  let generate_test_sgt art node =
    logf "Generating test @ %a\n" ReachTree.pp_node node;
    let post = Ctx.mk_not (K.guard (ReachTree.path_to_error art node)) in
    let rec path_weight v =
      match ReachTree.parent_weight art v with
      | Some (parent, w) -> K.mul (path_weight parent) w
      | None -> K.one
    in
    match K.interpolate_or_concrete_model [path_weight node] post with
    | `Invalid v_model -> `Test v_model
    | `Unknown -> failwith "generate_test_sgt: got UNKNOWN as a result for interpolate_or_get_model"
    | `Valid _ -> `Pruned

  let sgt graph src dst =
    let art = ReachTree.make graph Ctx.mk_true ~src ~dst in
    let rec loop () =
      match ReachTree.deque_frontier art with
      | None -> `Safe
      | Some node ->
         match generate_test_sgt art node with
         | `Pruned -> loop ()
         | `Test state ->
            match ReachTree.execute art node state with
            | `Safe -> loop ()
            | `Unsafe _ -> `Unsafe
    in
    loop ()


  (* to print the reachability tree (+ worklist), or not *)
  (* RF 3/2/25: If you enable this flag, and even if     *)
  (* the logf output stream is suppressed, it incurs a _huge_ *)
  (* performance penalty. *)
  let print_tree = false

  type global_context =
    { g_graph : cfg_t
    ; g_summarizer : Summarizer.t
    ; g_errloc : int }

  and mc_result =
    | Safe of K.t
    | Unsafe of K.t


  (* contextual information maintained by GPS algorithm. *)
  (* intraprocedural context *)
  type intra_context = {
    id : ProcName.t;
    cfg : Graph.t;
    mutable art : ReachTree.t;
    global_ctx : global_context;
  }
  (* global context *)
  (** some helper functions that operate on the context *)
  let get_summarizer ctx = ctx.global_ctx.g_summarizer

  let log_labelled_weights ctx uu prefix weights =
  List.iteri
    (fun i f ->
      match f with
      | Call (u, v) ->
        let p =
          begin match uu with
          | OverApprox -> Summarizer.over_proc_summary ctx.g_summarizer (ProcName.make (u, v))
          | UnderApprox -> Summarizer.under_proc_summary ctx.g_summarizer (ProcName.make (u, v))
        end in
        logf "[labelled weight] %s(%i, call(%d,%d)): %a\n" prefix i u v K.pp p
      | Weight w ->
        logf "[labelled weight] %s(%i): %a\n" prefix i K.pp w) weights


  (* Express a relational query as a precondition/postcondition pair over
     prophecy variables *)
  let demote_precondition (query : K.t) =
    let preconditions, postconditions =
    BatEnum.fold (fun (preconditions, postconditions) (var, asgn) ->
        let prophecy_var = V.prophesize var in
        let prophecy_sym = V.symbol_of prophecy_var in
        let prophecy_term = Syntax.mk_const srk prophecy_sym in
        let var_term = Syntax.mk_const srk (V.symbol_of var) in
        (Syntax.mk_eq srk prophecy_term asgn::preconditions,
         Syntax.mk_eq srk prophecy_term var_term::postconditions))
      ([K.guard query], [])
      (K.transform query)
    in
    (Syntax.mk_and srk preconditions, Syntax.mk_and srk postconditions)


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
    K.construct (Syntax.substitute_const srk substitute (Syntax.mk_not srk f)) (ValueHT.to_seq sym_map |> List.of_seq)


  let mk_intra_context (gctx: global_context) ((src,tgt): ProcName.t) (query: K.t) =
    let pre_state, equalities = demote_precondition query in
    let target_summary v =
      K.mul
        (Summarizer.path_weight_intra gctx.g_summarizer v tgt)
        (K.assume equalities)
    in
    let dst = gctx.g_errloc in
    let graph =
      Graph.{ graph = WG.add_edge (gctx.g_graph) tgt (Weight (K.assume equalities)) dst
            ; call_summary = Summarizer.over_proc_summary gctx.g_summarizer
            ; target_summary = target_summary }
    in
    {
      id = (src,dst);
      cfg = graph;
      art = ReachTree.make graph pre_state ~src ~dst;
      global_ctx = gctx;
    }

  let rec art_cfg_path_pair (ctx: intra_context) (p: ReachTree.node list) =
    match p with
    | u :: v :: t ->
      let u_vtx = ReachTree.maps_to ctx.art u in
      let v_vtx = ReachTree.maps_to ctx.art v in
      (u, (u_vtx, v_vtx), v) :: (art_cfg_path_pair ctx (v :: t))
    | _ -> []


  let print_vocabulary tr =
    let g_vocab, l_vocab = K.vocabulary tr in
    let vname x =
      match V.of_symbol x with
      | Some var -> V.show var
      | None -> " [havoc] "
    in
    log_weights " [vocabulary of transition] " [tr];
    logf " ------ globals: ---- {\n";
    List.iter (fun x -> logf "     %s %s\n" (Syntax.show_symbol srk x) (vname x)) g_vocab;
    logf "}\n ------ locals:  ---- {\n";
    List.iter (fun x -> logf "     %s %s\n" (Syntax.show_symbol srk x) (vname x)) l_vocab

  (* CFG path condition from art.src -> art.v *)
  let path_condition (ctx: intra_context) condition_type (v: ReachTree.node) =
    let art = ctx.art in
    let art_nodes = ReachTree.tree_path art v in
    let ts = ctx.cfg.Graph.graph in
    let cfg_nodes = List.map (fun x -> ReachTree.maps_to art x) art_nodes in
    let rec to_weights l : K.t label list =
      match l with
      | a :: b :: t ->
        WG.edge_weight ts a b :: (to_weights (b :: t))
      | _ -> []
    in
    let summ = get_summarizer ctx in
    let pathcond = List.map (fun (weight: K.t label) ->
      match weight with
      | Call (src, dst) ->
        begin match condition_type with
        | OverApprox -> Summarizer.over_proc_summary summ (ProcName.make (src, dst))
        | UnderApprox ->
            let under = Summarizer.under_proc_summary summ (ProcName.make (src, dst)) in
              log_weights "underapproximate summary" [under];
              print_vocabulary under;
              under
        end
      | Weight w -> w) (to_weights cfg_nodes) in
      logf " ---- path_condition: path length: %d, before add1: %d\n" ((List.length pathcond)+1) (List.length pathcond);
    let l = (K.assume (ReachTree.get_precondition ctx.art)) :: pathcond in
        log_weights "path conditions " l; l

  let get_global_ctx (ctx: intra_context) = ctx.global_ctx

  let extract_refinement (ctx: intra_context) =
    let art = ctx.art in
    let rfn = ReachTree.label art ReachTree.root |> promote in
    log_weights "refinement: " [rfn];
    K.exists (fun v -> V.is_global v) (rfn)

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

        log_labelled_weights ctx.global_ctx UnderApprox "left path - " left;
        logf "error: handle_path_to_error: cannot project path condition" ;
        `Safe in
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
      let summ = get_summarizer ctx in
      let suffix =
        List.map (fun (_, ew, _) ->
          match ew with
          | Weight w -> w
          | Call (s, t) -> Summarizer.over_proc_summary summ (ProcName.make (s, t)))
        right
        |> seq in
      let summary = Summarizer.over_proc_summary summ (ProcName.make (src, dst)) in
      begin match K.contextualize prefix summary suffix with
      | `Sat query ->
        let answer =
          mk_intra_context (ctx.global_ctx) (ProcName.make (src, dst)) query
          |> intraproc_check
        in begin match answer with
           | Safe r ->
              Summarizer.refine_over_summary summ (ProcName.make (src, dst)) r;
            handle_path_to_error ctx left curr right dir err_leaf
           | Unsafe trs ->
            begin match trs |> K.project_mbp (V.is_global) with
            | `Sat tr ->
               Summarizer.refine_under_summary summ (ProcName.make (src, dst)) tr;
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


  and intraproc_check (ctx: intra_context) : mc_result =
    match ReachTree.gps ctx.art with
    | `Safe -> Safe (extract_refinement ctx)
    | `Unsafe w ->
       logf "--- GPS: found path-to-error at tree node %d (cfg vertex %d) \n" (ReachTree.of_node w) (ReachTree.maps_to ctx.art w);
       logf " --- forming path to error... \n";
       let has_calls, path_to_w =
         ReachTree.tree_path ctx.art w
         |> art_cfg_path_pair ctx
         |> List.map (fun (u, (u_vtx, v_vtx), v) -> (u, WG.edge_weight ctx.cfg.Graph.graph u_vtx v_vtx, v))
         |> List.fold_left (fun (has_call, l) (u, w, v) ->
                match w with
                | Call _ -> (true, (u, w, v) :: l)
                | _ -> (has_call, (u, w, v) :: l)
              ) (false, [])
       in
       logf " --- finished forming path to error, calling handle_path_to_error ... \n";
       begin match has_calls, path_to_w with
       | true, curr :: right ->
          begin match handle_path_to_error ctx [] curr right `Right w with
          | `Safe -> (* path-to-error concretization failed. frontier_node is the src node of a call-edge. *)
             (* we can mark `w` as a frontier node to be refined, and continue. *)
             ReachTree.add_frontier ctx.art w;
             intraproc_check ctx
          | `Unsafe pathcond ->
             logf "--- GPS: managed to concretize an intraprocedural path-to-error. returning... ";
             Unsafe pathcond end
       | false, _::_ ->
          (* TODO! *)
(*          Unsafe (seq (List.map (fun (_, w, _) ->
                           match w with
                           | Weight w -> w
                           | _ -> assert false)
                         path_to_w))
 *)

          Unsafe K.one
       | _, [] ->
          (* corner case: either no calls along the path, or if the path to error is of length 0. *)
          Unsafe K.one
       end


  let execute (ts : cfg_t) (entry : int) (err_loc : int) (enable_summary:bool) : mc_result =
    let gctx =
      { g_graph = ts
      ; g_summarizer = Summarizer.init ts entry err_loc enable_summary
      ; g_errloc = err_loc }
    in
    (* interproc_graph represents the language of interprocedural paths from
       entry to err_loc (including interprocedural paths that make calls that
       never return---i.e., the ``unbalanced left'' language of
       interprocedurally-valid paths) *)
    let interproc_graph =
      WG.fold_edges (fun (u, w, _) interproc_graph ->
          match w with
          | Call (en, _) ->
             WG.add_edge interproc_graph u (Weight K.one) en
          | Weight _ -> interproc_graph)
        ts
        ts
    in
    let graph =
      Graph.{ graph = interproc_graph
            ; call_summary = Summarizer.over_proc_summary gctx.g_summarizer
            ; target_summary = Summarizer.path_weight_inter gctx.g_summarizer }
    in
    let main_context =
      {
        id = (entry,err_loc);
        cfg = graph;
        art = ReachTree.make graph Ctx.mk_true ~src:entry ~dst:err_loc;
        global_ctx = gctx;
      }
    in
    logf "executing GPS: start\n";
    intraproc_check main_context
end


module BM = BatMap.Make(Int)


let analyze_mc enable_gas enable_summary file =
  let open Srk.Iteration in
  populate_offset_table file;
  K.domain := split (product [ PolyhedronGuard.exp
                             ; LossyTranslation.exp ]);
  match file.entry_points with
  | [main] -> begin
      let rg = Interproc.make_recgraph file in
      let entry = (RG.block_entry rg main).did in
      let (ts, assertions) = make_transition_system ~simplify:true ~instr_gas:enable_gas entry rg in
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


let analyze_sgt enable_gas enable_summary file =
    let open Srk.Iteration in
    populate_offset_table file;
    K.domain := split (product [ PolyhedronGuard.exp
                               ; LossyTranslation.exp ]);
    match file.entry_points with
    | [main] -> begin
        let rg = Interproc.make_recgraph file in
        let entry = (RG.block_entry rg main).did in
        let (ts, assertions) = make_transition_system ~simplify:true ~instr_gas:enable_gas entry rg in
        let ts, err_loc = make_ts_assertions_unreachable ts assertions in
        if !CmdLine.display_graphs then TSDisplay.display ts;
        logf "\nentry: %d\n" entry;
        Printf.printf "testing reachability of location %d\n" err_loc ;
        Printf.printf "------------------------------\n";
        let summ = Summarizer.init ts entry err_loc enable_summary in
        let graph =
          GPS.Graph.{ graph = ts
                    ; call_summary = (fun _ -> failwith "SGT: procedure call")
                    ; target_summary = Summarizer.path_weight_inter summ }
        in
        begin match GPS.sgt graph entry err_loc with
        | `Safe  -> Printf.printf "  proven safe\n";
        | `Unsafe -> Printf.printf "  proven unsafe\n"
        | `Error s -> Printf.printf "ERR: %s\n" s
        end;
        Printf.printf "------------------------------\n"
      end
    | _ -> assert false

let analyze_impact file =
    let open Srk.Iteration in
    populate_offset_table file;
    K.domain := split (product [ PolyhedronGuard.exp
                               ; LossyTranslation.exp ]);
    match file.entry_points with
    | [main] -> begin
        let rg = Interproc.make_recgraph file in
        let entry = (RG.block_entry rg main).did in
        let (ts, assertions) = make_transition_system ~simplify:true entry rg in
        let ts, err_loc = make_ts_assertions_unreachable ts assertions in
        if !CmdLine.display_graphs then TSDisplay.display ts;
        logf "\nentry: %d\n" entry;
        Printf.printf "testing reachability of location %d\n" err_loc ;
        Printf.printf "------------------------------\n";
        let graph =
          GPS.Graph.{ graph = ts
                    ; call_summary = (fun _ -> failwith "IMPACT: procedure call")
                    ; target_summary = (fun _ -> K.one) }
        in
        let module ART = GPS.ReachTree in
        let art = ART.make graph Ctx.mk_true ~src:entry ~dst:err_loc in
        let rec loop () =
          match ART.deque_frontier art with
          | None -> `Safe
          | Some u ->
             (* Fetched tree node u from work list. First attempt to close it. *)
             if ART.is_covered art u then loop ()
             else if ART.lclose art u then loop ()
             else if ART.maps_to art u == err_loc then
               match ART.generate_test art u with
               | `Pruned ->
                  List.iter (fun v -> ignore (ART.close art v)) (ART.tree_path art u);
                  loop ()
               | `Test _ -> `Unsafe
             else (ART.expand art u; loop ())
        in
        begin match loop () with
        | `Safe  -> Printf.printf "  proven safe\n";
        | `Unsafe -> Printf.printf "  proven unsafe\n"
        | `Error s -> Printf.printf "ERR: %s\n" s
        end;
        Printf.printf "------------------------------\n"
      end
    | _ -> assert false


(** dump simplified CFG before doing model checking / CRA / concolic execution *)
let dump_cfg simplify instrument file =
  populate_offset_table file;
  match file.entry_points with
  | [main] ->
    begin
      let rg = Interproc.make_recgraph file in
      let entry  = (RG.block_entry rg main).did in
      let (ts, assertions) = make_transition_system ~simplify:simplify ~instr_gas:instrument entry rg in
      let ts, _ = make_ts_assertions_unreachable ts assertions in
      TSDisplay.display ts
    end
  | _ -> assert false

let _ =
  CmdLine.register_pass
    ("-gps", analyze_mc false true, " GPS model checking algorithm, without gas-instrumentation");
  CmdLine.register_pass
    ("-gps-gas", analyze_mc true true, " GPS model checking algorithm, with gas-instrumentation (i.e., refutation-complete)");
  CmdLine.register_pass
    ("-gps-nosum", analyze_mc false false, "GPS with neither gas nor CRA-generated summary");
  CmdLine.register_pass
    ("-gps-nosum-nogas", analyze_mc true false, "GPS with gas but without CRA-generated summary (i.e., refutation-complete)");

  CmdLine.register_pass
    ("-sgt", analyze_sgt false true, "Summary-guided testing, without gas-instrumentation");
  CmdLine.register_pass
    ("-sgt-gas", analyze_sgt true true, "Summary-guided testing, with gas");
  CmdLine.register_pass
    ("-sgt-nosum", analyze_sgt false false, "Summary-guided testing without CRA-generated summary");
  CmdLine.register_pass
    ("-sgt-nosum-nogas", analyze_sgt true false, "Summary-guided testing with gas but without CRA-generated summary");

    CmdLine.register_pass
    ("-impact", analyze_impact, "Lazy abstraction with interpolants");

  CmdLine.register_pass
    ("-dump-unsimplified-cfg", dump_cfg false false, "dump unsimplified CFG");
  CmdLine.register_pass
    ("-dump-simplified-cfg", dump_cfg true false, "dump simplified CFG");
  CmdLine.register_pass
    ("-dump-instrumented-unsimplified-cfg", dump_cfg false true, "dump unsimplified CFG");
  CmdLine.register_pass
    ("-dump-instrumented-simplified-cfg", dump_cfg true true, "dump simplified CFG");

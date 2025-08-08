open Core
open Srk
open CfgIr
open BatPervasives
open Cra

module TS = TransitionSystem.Make(Ctx)(V)(K)

include Log.Make(struct let name = "gps" end)

(** some global flags for GPS *)
let enable_gas = ref true 
let enable_summary = ref true 
let enable_refinement = ref true (* main distinction between GPS / GPSLite *)
let enable_inlining = ref true
let enable_acceleration = ref true
let enable_ts_simplify = ref true
let print_stats = ref false

let num_check_calls = ref 0
let num_tests_generated = ref 0

let num_interpolants_generated = ref 0 

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


(* Convert assertion checking problem to vertex reachability problem. *)
let safety_to_reachability (ts : cfg_t) assertions =
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
  module ReachTree = ReachTree.ART(Graph)(Label)(Transition)

  let generate_test art node =
    let post = Ctx.mk_not (K.guard (ReachTree.path_to_error art node)) in
    let rec get_path rest node =
      match ReachTree.parent_weight art node with
      | Some (p, weight) -> get_path (weight::rest) p
      | None -> rest
    in
    let path = get_path [] node in
    num_check_calls := !num_check_calls + 1;
    match K.interpolate_or_concrete_model ((K.assume @@ ReachTree.get_precondition art) :: path) post with
    | `Invalid v_model ->
       logf ~level:`trace "-> found test";
       num_tests_generated := !num_tests_generated + 1;
       `Test v_model
    | `Unknown -> failwith "generate_test: got UNKNOWN as a result for interpolate_or_get_model"
    | `Valid interpolants ->
        num_interpolants_generated := !num_interpolants_generated + 1;
       logf ~level:`trace "-> pruned";
       log_formulas "interpolants - " interpolants;
       `Pruned (interpolants)

  let gps graph src dst =
    let art = ReachTree.make graph Ctx.mk_true ~src ~dst in 
    let rec loop () =
      match ReachTree.deque_frontier art with
      | None -> `Safe art
      | Some u ->
         (* Fetched tree node u from work list. First attempt to close it. *)
         logf ~level:`trace "At frontier node %d:" (ReachTree.of_node u);
         if !enable_refinement && (ReachTree.is_covered art u) then
           (logf ~level:`trace "-> covered";
            loop ())
         else begin
             if !enable_refinement && (ReachTree.lclose art u) then (* Close succeeded. No need to further explore it. *)
               (logf ~level:`trace "-> closed"; loop ())
             else begin
                 (* u is uncovered. *)
                 match generate_test art u with
                 | `Pruned (interpolants) -> 
                    if !enable_refinement then begin 
                      (* refinement *)
                      logf ~level:`trace " * refinement: path length %d\n" (List.length (ReachTree.tree_path art u));
                      logf ~level:`trace " * interpolants length: %d\n" (List.length interpolants);
                      ReachTree.refine art (ReachTree.tree_path art u) interpolants;
                      (* for every node along path of refinement try close *)
                      List.iter (fun v -> ignore (ReachTree.close art v)) (ReachTree.tree_path art u);
                      loop ()
                    end else begin (* GPSlite, no refinement *)
                      loop ()
                    end 
                 | `Test state ->
                    logf ~level:`trace "-> found test";
                    match ReachTree.execute art u state with
                    | `Safe -> loop ()
                    | `Unsafe n -> `Unsafe (n, art)
               end
           end
    in
    loop ()
end


let analyze_mc file =
  let open Srk.Iteration in
  populate_offset_table file;
  K.domain := split (product [ PolyhedronGuard.exp
                             ; LossyTranslation.exp ]);
  match file.entry_points with
  | [main] -> begin
      let rg = Interproc.make_recgraph file in
      let entry = (RG.block_entry rg main).did in
      let (ts, assertions) = make_transition_system ~simplify:(!enable_ts_simplify) ~instr_gas:!enable_gas entry rg in
      let ts, err_loc = safety_to_reachability ts assertions in
      if !CmdLine.display_graphs then TSDisplay.display ts;
      logf "\nentry: %d\n" entry;
      Printf.printf "testing reachability of location %d\n" err_loc ;
      Printf.printf "------------------------------\n";
      let summ = Summarizer.init ts entry err_loc !enable_summary in 
      let graph =
          GPS.Graph.{ graph = ts
                    ; call_summary = (fun _ -> failwith "GPS: procedure call")
                    ; target_summary = (Summarizer.path_weight_inter summ) }
        in
      let art = 
        begin match GPS.gps graph entry err_loc with
        | `Safe art -> Printf.printf "  proven safe\n"; art
        | `Unsafe (_, art) -> Printf.printf "  proven unsafe\n"; art
        end in 
      if !print_stats then begin 
        let statistics = GPS.ReachTree.get_statistics art in 
          Printf.printf " Statistics\n";
          Printf.printf "  Number of check calls: %d\n" !num_check_calls;
          Printf.printf "  Number of tests generated: %d\n" !num_tests_generated;
          Printf.printf "  Number of dead-end-interpolants generated: %d\n" !num_interpolants_generated;
          Printf.printf "  Number of refinements performed: %d\n" statistics.num_refinements_performed;
          Printf.printf "  Number of coverings added: %d\n" statistics.num_covers_added;
          Printf.printf "  Number of coverings removed: %d\n" statistics.num_covers_removed
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
        let ts, err_loc = safety_to_reachability ts assertions in
        if !CmdLine.display_graphs then TSDisplay.display ts;
        logf "\nentry: %d\n" entry;
        logf "testing reachability of location %d\n" err_loc ;
        logf "------------------------------\n";
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
               match GPS.generate_test art u with
               | `Pruned interpolants ->
                  ART.refine art (ART.tree_path art u) interpolants;
                  List.iter (fun v -> ignore (ART.lclose art v)) (ART.tree_path art u);
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
      let ts, _ = safety_to_reachability ts assertions in
      TSDisplay.display ts
    end
  | _ -> assert false

let _ =
  CmdLine.register_config 
    ("-gps-disable-gas", Arg.Clear enable_gas, " Disable gas-instrumentation in GPS (enabled by default)");
  CmdLine.register_config 
    ("-gps-disable-summary", Arg.Clear enable_summary, " Disable CRA-generated summaries in GPS (enabled by default)");
  CmdLine.register_config
    ("-gps-disable-acceleration", Arg.Clear enable_acceleration, " Disable loop acceleration during preprocessing (enabled by default)");
  CmdLine.register_config
    ("-gps-disable-simplify", Arg.Clear enable_ts_simplify, " Disable CFG simplification (enabled by default)");
  CmdLine.register_config
    ("-gps-disable-refinement", Arg.Clear enable_refinement, " Disable invariant synthesis capabilities of GPS");
  CmdLine.register_config
    ("-gps-stats", Arg.Unit (fun () -> print_stats := true), " Enable statistics reporting of a GPS run (disabled by default)");
  CmdLine.register_pass
    ("-gps", analyze_mc, " GPS model checker for intraprocedural programs");
  CmdLine.register_pass
    ("-impact", analyze_impact, " Lazy abstraction with interpolants");

  CmdLine.register_pass
    ("-dump-unsimplified-cfg", dump_cfg false false, " dump unsimplified CFG");
  CmdLine.register_pass
    ("-dump-simplified-cfg", dump_cfg true false, " dump simplified CFG");
  CmdLine.register_pass
    ("-dump-instrumented-unsimplified-cfg", dump_cfg false true, " dump unsimplified CFG");
  CmdLine.register_pass
    ("-dump-instrumented-simplified-cfg", dump_cfg true true, " dump simplified CFG");

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
         (PathTree : sig
            type node
            type t
            type state
            val check :  t -> node -> [ `Feasible of state | `Infeasible | `Unknown ]
            val expand : t -> node -> state -> (node * state) list * node list
            val log_art : t -> unit
            val pp_node : t -> Format.formatter -> node -> unit
            val pp_state : Format.formatter -> state -> unit
            val is_err_loc : t -> node -> bool
          end) = struct

  let print_tree = false 
  
  let log_model prefix model = 
    logf "[model] %s: %a\n" prefix PathTree.pp_state model  


  type context = {
    mutable art : PathTree.t ref;
    (* list for frontier nodes *)
    mutable worklist : PathTree.node DQ.t;
    (* list for executor states *)
    mutable execlist : (PathTree.node * PathTree.state) DQ.t;
  }

  let worklist_push  (i : 'a) (q : 'a DQ.t) = DQ.snoc q i 


  let run_test (ctx: context ref) =
    let round ctx = 
      match DQ.front (!ctx.execlist) with 
      | Some ((u, u_model), w) -> 
        if print_tree then 
          PathTree.log_art !(!ctx.art);
        logf " visit %a\n" (PathTree.pp_node !(!ctx.art)) u;
        !ctx.execlist <- w;
        if PathTree.is_err_loc !(!ctx.art) u then
          `Unsafe u 
        else begin
            logf "model of %a: \n" (PathTree.pp_node !(!ctx.art)) u;
            log_model "" u_model;
            let new_concolic_nodes, new_frontier_nodes = PathTree.expand !(!ctx.art) u u_model in 
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


  let mk_context art =
    ref {
      art = ref art;
      worklist = DQ.empty;
      execlist = DQ.empty;
    }


  let execute art root : [`Safe | `Unsafe | `Error of string] = 
    let ctx = mk_context art in
    let state = ref `Unknown in 
      !ctx.worklist <- worklist_push root !ctx.worklist;
      while (DQ.size !ctx.worklist > 0 || DQ.size !ctx.execlist > 0) && (!state = `Unknown) do
        logf " --- SGT: starting a new test execution phase\n";
        match run_test ctx with 
        | `Safe -> 
          begin match DQ.front !ctx.worklist with 
          | Some (u, worklist') -> 
            begin match PathTree.check art u with 
            | `Feasible m ->
               Log.errorf "HERE!";
              !ctx.execlist <- worklist_push (u, m) !ctx.execlist;
              !ctx.worklist <- worklist';
              state := `Unknown
            | `Infeasible -> 
              !ctx.worklist <- worklist';
              state := `Unknown;
            | `Unknown ->
               logf "--- SGT:  UNKNOWN!"
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

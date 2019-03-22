open Core
open Apak
open CfgIr
open Srk

module RG = Interproc.RG
module G = RG.G
module K = NewtonDomain.ICRASum
module Ctx = NewtonDomain.Ctx

include Log.Make(struct let name = "cra_newton" end)
module A = Interproc.MakePathExpr(Cra.K)

external add_wpds_rule: K.t -> int -> int -> unit = "add_wpds_rule"
external set_vertices: int -> int -> unit = "set_vertices_wfa"
external set_cWeight: K.t -> unit = "set_compare_weight"
external add_wpds_call_rule: K.t -> int -> int -> int -> unit = "add_wpds_call_rule"
external add_wpds_epsilon_rule: K.t -> int -> unit = "add_wpds_epsilon_rule"
external add_wpds_error_rule: K.t -> int -> int -> unit = "add_wpds_error_rule"
external add_wpds_print_hull_rule: int -> int -> int -> unit = "add_wpds_print_hull_rule"

let analyze_basic file =
  Cra.populate_offset_table file;
  match file.entry_points with
  | [main] -> begin
      let rg = Interproc.make_recgraph file in
      let (ts, assertions) = Cra.make_transition_system rg in
      ts |> WeightedGraph.iter_edges (fun (u, label, v) ->
          match label with
          | WeightedGraph.Call (s, t) ->
            add_wpds_epsilon_rule (K.one ()) t;
            add_wpds_call_rule (K.one ()) u s v
          | WeightedGraph.Weight tr ->  
            if !K.use_left then
              add_wpds_rule (K.make_left tr) u v
            else
              add_wpds_rule (K.make_right (NewtonDomain.RK.lift_dnf tr)) u v);
      assertions |> SrkUtil.Int.Map.iter (fun v (phi, loc, msg) ->
            add_wpds_error_rule
              (K.assume (Ctx.mk_not phi))
              v
              loc.Cil.line);
      RG.vertices rg |> BatEnum.iter (fun (_, def) ->
          match def.dkind with
          | Builtin (PrintBounds v) ->
            add_wpds_print_hull_rule
              def.did
              (Def.get_location def).Cil.line
              (Var.get_id v)
          | _ -> ());
      add_wpds_epsilon_rule (K.one ()) (RG.block_exit rg main).did;
      set_vertices (RG.block_entry rg main).did (RG.block_exit rg main).did;
      set_cWeight (K.zero ());
      Callback.register "procedure_of_vertex_callback" (fun vertex ->
          (Interproc.RG.vertices rg)
          |> BatEnum.find (fun (block, v) -> vertex = v.did)
          |> fst
          |> Varinfo.show)
    end
  | _ -> assert false

let _ =
  CmdLine.register_pass
    ("-cra_newton_basic",
     analyze_basic,
     " Compositional recurrence analysis via FWPDS")

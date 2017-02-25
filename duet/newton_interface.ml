open Core
open Apak
open CfgIr
open Ark

module RG = Interproc.RG
module G = RG.G
module K = NewtonDomain.K
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

(*Create a function to call out to the weight maker and create a wpds in c*)
let iter_helper rg vertexa vertexb =
  match RG.classify vertexa with
  | `Atom _ ->
    add_wpds_rule (Cra.weight vertexa) vertexa.did vertexb.did
  | `ParBlock func | `Block func ->
    let vertext = (RG.block_entry rg func) in
    add_wpds_call_rule K.one vertexa.did vertext.did vertexb.did

let block_iter rg b = 
  RG.G.iter_edges (iter_helper rg) (RG.block_body rg b);
  add_wpds_epsilon_rule K.one (RG.block_exit rg b).did

let analyze_basic file =
  match file.entry_points with
  | [main] -> begin
      let rg = Interproc.make_recgraph file in
      let rg =
        if !Cra.forward_inv_gen
        then Log.phase "Forward invariant generation" Cra.decorate rg
        else rg
      in
      BatEnum.iter (block_iter rg) (Interproc.RG.blocks rg);
      Interproc.RG.vertices rg |> BatEnum.iter (fun (_, vertex) ->
          match vertex.dkind with
          | Assert (phi, _) ->
            add_wpds_error_rule
              (K.assume (Ctx.mk_not (NewtonDomain.tr_bexpr phi)))
              vertex.did
              (Def.get_location vertex).Cil.line
          | AssertMemSafe (expr, _) -> begin
              let open NewtonDomain in
              match tr_expr expr with
              | TInt _ -> assert false
              | TPointer p ->
                begin
                  let phi =
                    Ctx.mk_and [Ctx.mk_leq (Ctx.mk_real QQ.zero) p.ptr_pos;
                                Ctx.mk_lt p.ptr_pos p.ptr_width]
                  in
                  add_wpds_error_rule
                    (K.assume (Ctx.mk_not phi))
                    vertex.did
                    (Def.get_location vertex).Cil.line
               end
            end
          | Builtin (PrintBounds v) ->
            add_wpds_print_hull_rule
              vertex.did
              (Def.get_location vertex).Cil.line
              (Var.get_id v)
          | _ -> ()
        );
      logf ">> entry: %d" (RG.block_entry rg main).did;
      set_vertices (RG.block_entry rg main).did (RG.block_exit rg main).did;
      set_cWeight K.zero;
      Callback.register "procedure_of_vertex_callback" (fun vertex ->
          logf ">> actually here";
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

open Core
open Apak
open CfgIr

module RG = Interproc.RG
module G = RG.G

include Log.Make(struct let name = "cra_newton" end)
module A = Interproc.MakePathExpr(Cra.K)

external caml_add_wpds_rule: Cra.K.t -> int -> int -> unit = "add_wpds_rule"
external set_vertices: int -> int -> unit = "set_vertices_wfa"
external set_cWeight: Cra.K.t -> unit = "set_compare_weight"
external caml_add_wpds_call_rule: Cra.K.t -> int -> int -> int -> unit = "add_wpds_call_rule"
external caml_add_wpds_epsilon_rule: Cra.K.t -> int -> unit = "add_wpds_epsilon_rule"

(*Create a function to call out to the weight maker and create a wpds in c*)
let iter_helper vertexa vertexb rg =
   match RG.classify vertexa with
   | `Atom _ -> begin
   	let tmp = Cra.weight vertexa in
     		caml_add_wpds_rule tmp vertexa.did vertexb.did;
		rg
        end
   | `ParBlock func | `Block func -> begin
	let vertext = (RG.block_entry rg func) in
		let oneW = Cra.K.one in
		caml_add_wpds_call_rule oneW vertexa.did vertext.did vertexb.did;
		rg
   	end
  
let block_iter rg b = 
	RG.G.fold_edges iter_helper (RG.block_body rg b) rg;
	let oneW = Cra.K.one in
	caml_add_wpds_epsilon_rule oneW (RG.block_exit rg b).did;
	rg

let analyze_basic file =
  match file.entry_points with
  | [main] -> begin
      let rg = Interproc.make_recgraph file in
	BatEnum.fold block_iter rg (Interproc.RG.blocks rg);
          set_vertices (RG.block_entry rg main).did (RG.block_exit rg main).did;
          let local _ _ = false in
            let query = A.mk_query rg Cra.weight local main in
            A.compute_summaries query;
            set_cWeight (A.get_summary query main)
      end
  | _ -> assert false

let _ =
  CmdLine.register_pass
    ("-cra_newton_basic", analyze_basic, " Compositional recurrence analysis via FWPDS")

open Core
open CfgIr
open Apak

(*******************************************************************************
 ** Command line interface
 ******************************************************************************)
(*
let _ =
  let input = ref "" in
  let go output =
    let file = CfgIr.get_gfile() in
    let dfg = AliasLogic.construct_dg file in
    let chan = open_out output in
    Marshal.to_channel chan dfg [];
    close_out chan;
    print_endline ("Wrote dataflow graph to " ^ output)
  in
  CmdLine.register_debug
    ("-dfg",
     Arg.String go,
     " Compute a data flow graph and write it to disk")
*)
(* Debugging *)

let _ =
  let go file =
    let display f =
      Format.printf "Display `%a'? [y/n] @?" Varinfo.format f.fname;
      if (read_line ()) = "y" then CfgIr.Cfg.display f.cfg
    in
    Pa.simplify_calls file;
    List.iter display file.funcs
  in
  CmdLine.register_debug_pass
    ("-cfg",
     go,
     " Print control flow graphs for each thread (Requires Eye of Gnome)")

(*
let _ =
  let go file = CfgIr.display_callgraph (build_callgraph file) in
  CmdLine.register_debug_pass
    ("-callgraph",
     go,
     " Print callgraph (requires Eye of Gnome)")
*)

(*
let _ =
  let go file =
    List.iter (fun f -> Region.display_scc (Region.cfg_loop f.cfg)) file.funcs
  in
  CmdLine.register_debug_pass
    ("-scc",
     go,
     " Display CFG SCCs (Requires Eye of Gnome)")
*)

(*
let _ =
  let go file = Region.region_info file in
  CmdLine.register_debug_pass ("-region", go, " Display region information")
*)
module DG = Afg.G
module DGD = ExtGraph.Display.MakeSimple(DG)(Def)
let _ =
  let pack = Var.Set.singleton in
  let uses = Live.may_use in
  let go file = DGD.display (DG.minimize (Dg.construct file pack uses)) in
  CmdLine.register_debug_pass ("-dg", go, " Print sequential dependence graph")

(*
module Cfg = CfgIr.Cfg
let _ =
  let go file =
    let show_product t0 t1 =
      let t0 = lookup_function t0 file in
      let t1 = lookup_function t1 file in
      let product = CfgIr.product_cfg t0.cfg  t1.cfg in
	Cfg.display product;
	t0.cfg <- product;
	file.threads <- [t0.fname];
	let dg = SDG.construct file in
	  SDGD.display dg;
	  SDGD.display (SDG.minimize dg)
    in
      match file.threads with
	| [t0; t1] -> show_product t0 t1
	| _ -> failwith "-min-product requires a file with exactly two threads!"
  in
  CmdLine.register_debug_pass
    ("-min-product", go, " Minimal DG of product CFG")
*)

let usage_msg = "Duet program analyzer\nUsage: duet [OPTIONS] file.[c|bp|goto]"

let anon_fun s = ignore (CmdLine.parse s)

let _ =
  Sys.set_signal Sys.sigtstp (Sys.Signal_handle (fun _ -> Log.print_stats ()));
  let spec_list = CmdLine.spec_list () in
  Arg.parse (Arg.align spec_list) anon_fun usage_msg;
  match !CfgIr.gfile with
  | None -> begin
    prerr_endline "You must supply a program to be analyzed";
    Arg.usage (Arg.align spec_list) usage_msg
  end
  | Some x -> begin
    CmdLine.run (CfgIr.get_gfile());
    if !CmdLine.show_stats then Log.print_stats ()
  end

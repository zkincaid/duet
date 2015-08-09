open Core
open CfgIr
open FeConfig

module Def = Definition

let output = ref ""

let output_arg =
  ("-o", Arg.Set_string output, " Set output file")

let fspa_arg =
  let go s =
    let file = parseFile s in
    let dg = AliasLogic.construct_dg file in
    let state = Fspa.Solve.mk_state dg  in
    let result = Fspa.Solve.do_analysis state dg in
    let chan = open_out_bin !output in
    output_string chan "fspa\n";
    Marshal.to_channel chan result [];
    close_out chan
  in
  ("-fspa", Arg.String go, " Flow-sensitive pointer analysis")

let idg_arg =
  let go s =
    let file = parseFile s in
    let dg = AliasLogic.construct_dg file in
    let state = AliasLogic.IntervalAnalysis.mk_state dg  in
    let result = AliasLogic.IntervalAnalysis.do_analysis state dg in
    let f def absval map = Def.Map.add def absval map in
    let map = AliasLogic.IntervalAnalysis.S.fold_input f result Def.Map.empty in
    let chan = open_out_bin !output in
    output_string chan "idg\n";
    Marshal.to_channel chan map [];
    close_out chan
  in
  let desc = " Interval analysis with an interprocedural dependence graph" in
  ("-idg", Arg.String go, desc)

let diff_ivl_map a b =
  let f def a_val =
    try
      let b_val = Def.Map.find def b in
      if not (AliasLogic.I.equal a_val b_val)
      then print_endline "diff"
    with Not_found -> ()
  in
  Def.Map.iter f a

let diff_arg =
  let a = ref "" in
  let go b =
    let a_chan = open_in_bin (!a) in
    let b_chan = open_in_bin b in
    let analysis = input_line a_chan in
    let b_analysis = input_line b_chan in
    if analysis <> b_analysis
    then begin
      prerr_endline "Cannot diff: different analysis types";
      prerr_endline ("  a: " ^ analysis);
      prerr_endline ("  b: " ^ b_analysis);
      exit 0
    end else begin match analysis with
      | "fspa" ->
        Fspa.diff
          (Marshal.from_channel a_chan)
          (Marshal.from_channel b_chan)
      | "idg" ->
        Apron.Manager.set_deserialize AliasLogic.man;
        diff_ivl_map
          (Marshal.from_channel a_chan)
          (Marshal.from_channel b_chan)
      | _ -> failwith ("Unknown analysis: " ^ analysis)
    end;
    close_in a_chan;
    close_in b_chan
  in
  ("-diff",
   Arg.Tuple [Arg.Set_string a;
              Arg.String go],
   " Compare analysis results")

let spec_list =
  [ fspa_arg;
    idg_arg;
    output_arg;
    diff_arg ]
  @ Config.option_args

let usage_msg = "Duet program analysis differencing tool"

let anon_fun s = raise (Arg.Bad (s ^ " is not recognized"))

let _ =
  Arg.parse (Arg.align spec_list) anon_fun usage_msg;

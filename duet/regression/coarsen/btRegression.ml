open Core
open Dependence

let parse_file filename =
  if Filename.check_suffix filename "c"
  then TranslateCil.file_of_cil_file (TranslateCil.parse filename)
  else if Filename.check_suffix filename "bp"
  then TranslateCbp.translate (TranslateCbp.parse filename)
  else failwith "Unrecognized file extension"

let baseline_name name = "bt/baselines/" ^ name
let src_name name = "bt/code/" ^ name

let write_baseline file name =
  let chan = open_out (baseline_name name) in
    Marshal.to_channel chan file [];
    close_out chan

let read_baseline name =
  let chan = open_in (baseline_name name) in
  let res = Marshal.from_channel chan in
    close_in chan;
    res

let gen test =
  let file = CfgIr.from_file_ast (parse_file (src_name test)) in
  let run dir =
    let module R =
      Dependence(struct
		   type t = Box.t
		   let man = Box.manager_alloc ()
		   let file = file
		   let dir = dir
		   let rep ap = ap
		   let unrep = AP.Set.singleton
		 end)
    in
    let (dg, _) = R.run () in
      write_baseline dg test
  in
    Cdfautil.with_temp_dir "dep" run

let run name =
  let file = CfgIr.from_file_ast (parse_file (src_name name)) in
  let run dir =
    let module R =
      Dependence(struct
		   type t = Box.t
		   let man = Box.manager_alloc ()
		   let file = file
		   let dir = dir
		   let rep ap = ap
		   let unrep = AP.Set.singleton
		 end)
    in
    let (dg, _) = R.run () in
    let base_dg = read_baseline name in
      R.Afg.equiv dg base_dg
  in
    Cdfautil.with_temp_dir "dep" run

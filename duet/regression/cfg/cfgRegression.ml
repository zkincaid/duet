(* Construct IR *)
let parse_file filename =
  if Filename.check_suffix filename "c"
  then TranslateCil.file_of_cil_file (TranslateCil.parse filename)
  else if Filename.check_suffix filename "bp"
  then TranslateCbp.translate (TranslateCbp.parse filename)
  else failwith "Unrecognized file extension"

let baseline_name name = "cfg/baselines/" ^ name
let src_name name = "cfg/code/" ^ name

let write_baseline file name =
  let chan = open_out (baseline_name name) in
    Marshal.to_channel chan file [];
    close_out chan

let read_baseline name =
  let chan = open_in (baseline_name name) in
  let cfg = Marshal.from_channel chan in
    close_in chan;
    cfg

let gen test =
  let file = CfgIr.from_file_ast (parse_file (src_name test)) in
    write_baseline file test

let run test =
  let file = CfgIr.from_file_ast (parse_file (src_name test)) in
  let baseline = read_baseline test in
    CfgIr.file_equiv file baseline

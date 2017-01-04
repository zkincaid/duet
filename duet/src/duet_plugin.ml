open CfgIr
open Printf

(* Analyses *)

let usage_msg = "Duet program analyzer\nUsage: duet [OPTIONS] file.[c|bp|duet]"

let anon_fun s = ignore (CmdLine.parse s)

module Duet_init = struct

let duet_main () =
  let file = Conversion.convert_duet () in
  CfgIr.write_file file stdout
end

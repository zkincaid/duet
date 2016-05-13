(** Error reporting *)
open Printf

let errors = ref ""
let error_count = ref 0
let safe_count = ref 0
let unreachable_count = ref 0

let errors = ref []
let error_count = ref 0
let safe_count = ref 0
let unreachable_count = ref 0

let log_error loc txt = 
  incr error_count;
  errors := (loc,txt)::(!errors);
  let ofile = open_out_gen [Open_creat; Open_text; Open_append] 0o640 "../WALi-OpenNWA/Examples/cprover/tests/regression/outputs/__result.out" in
  Printf.fprintf ofile "FAIL ";
  close_out ofile

let log_safe () = incr safe_count;
  let ofile = open_out_gen [Open_creat; Open_text; Open_append] 0o640 "../WALi-OpenNWA/Examples/cprover/tests/regression/outputs/__result.out" in
  Printf.fprintf ofile "PASS ";
  close_out ofile

let log_safe_unreachable () = incr safe_count; incr unreachable_count

let print_errors () =
  if !error_count > 0 then begin
    let print (loc, txt) =
      Format.printf "%s:%d >> %s@\n@?" loc.Cil.file loc.Cil.line txt
    in
    List.iter print (BatList.sort compare (!errors));
    Format.printf "@\n"
  end;
  Format.printf "%d errors total@\n@?" (!error_count)

let print_safe () =
  Format.printf "%d safe assertions" (!safe_count);
  if !unreachable_count > 0 then
    Format.printf " (%d statically unreachable)@\n@?" (!unreachable_count)
  else
    Format.printf "@\n@?"

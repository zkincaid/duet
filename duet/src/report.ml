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
  errors := (loc,txt)::(!errors)

let log_safe () = incr safe_count

let log_safe_unreachable () = incr safe_count; incr unreachable_count

let print_errors () =
  Printf.printf "Entering errors\n"; flush stdout;
  if !error_count > 0 then begin
    let print (loc, txt) =
      Format.printf "%s:%d >> %s@\n@?" loc.Cil.file loc.Cil.line txt
    in
    List.iter print (BatList.sort compare (!errors));
    Format.printf "@\n"
  end;
  Format.printf "%d errors total@\n@?" (!error_count)

let print_safe () =
  Printf.printf "Entering safe\n"; flush stdout;
  Format.printf "%d safe assertions" (!safe_count);
  if !unreachable_count > 0 then
    Format.printf " (%d statically unreachable)@\n@?" (!unreachable_count)
  else
    Format.printf "@\n@?"

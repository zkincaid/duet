(** Error reporting *)

let errors = ref ""
let error_count = ref 0
let safe_count = ref 0
let unreachable_count = ref 0

let log_error loc txt = 
  incr error_count;
  errors := !errors ^
    (Format.sprintf "%s:%d >> %s@\n" loc.Cil.file loc.Cil.line txt)

let log_safe () = incr safe_count

let log_safe_unreachable () = incr safe_count; incr unreachable_count

let print_errors () =
  if !error_count > 0 then print_endline (!errors) else ();
  print_endline ((string_of_int (!error_count)) ^ " errors total")

let print_safe () =
  print_endline ((string_of_int (!safe_count)) ^ " safe assertions"
		 ^ (if !unreachable_count > 0 then
		      " (" ^ (string_of_int (!unreachable_count))
		      ^ " statically unreachable)"
		    else ""))


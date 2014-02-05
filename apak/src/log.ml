(** Options *)
let debug_mode      = ref false
let default_debug   = ref false
let debug_phases    = ref ([] : string list)
let verbosity_level = ref 0

(** Verbosity levels *)
let top    = 0   (** print only errors *)
let phases = 1   (** print phases *)
let fix    = 3   (** print steps in fixpoint computation *)
let bottom = 4   (** print everything *)
let info   = 2   (** print extra information *)

let debug_formatter =
  let chan = stdout in
  let out buf pos len =
    if !debug_mode then output chan buf pos len
    else ()
  in
  let flush () = flush chan in
  Format.make_formatter out flush

let log level str =
  if !verbosity_level >= level
  then (print_endline str; flush stdout)

let log_pp level pp x =
  if !verbosity_level >= level then begin
    pp Format.std_formatter x;
    Format.pp_print_newline Format.std_formatter ();
    flush stdout;
  end

let logf level fmt =
  if !verbosity_level >= level then Format.printf (fmt ^^ "@\n@?")
  else Format.ifprintf Format.std_formatter fmt
  
let debug msg =
  if !debug_mode
  then (print_endline ("DEBUG: " ^ msg); flush stdout)

let debug_pp pp x =
  if !debug_mode then begin
    Format.pp_print_string Format.std_formatter "DEBUG:";
    pp Format.std_formatter x;
    Format.pp_print_newline Format.std_formatter ();
    Format.pp_print_flush Format.std_formatter ()
  end

let debugf fmt =
  if !debug_mode then Format.printf ("DEBUG: " ^^ fmt ^^ "@\n@?")
  else Format.ifprintf Format.std_formatter fmt

let errorf fmt = Format.eprintf ("\x1b[31;1m" ^^ fmt ^^ "\x1b[0m@\n@?")
let error msg = errorf msg
let error_pp pp x = errorf "%a" pp x

let phases_ht = Hashtbl.create 32
let time str f arg =
  let start_time = Unix.gettimeofday () in
  let result = f arg in
  let time = (Unix.gettimeofday ()) -. start_time in
    (try Hashtbl.replace phases_ht str (Hashtbl.find phases_ht str +. time)
     with Not_found -> Hashtbl.add phases_ht str time);
    result

let phase str f arg =
  let padding =
    try String.make (77 - (String.length str)) '='
    with Invalid_argument _ -> ""
  in
    log phases ("\x1b[32;1m= " ^ str ^ " " ^ padding ^ "\x1b[0m");
    if List.exists (fun x -> x = str) !debug_phases then begin
      let old_debug = !debug_mode in
	debug_mode := true;
	let result = time str f arg in
	  debug_mode := old_debug;
	  result
    end else time str f arg

let start_time = Unix.gettimeofday ()
let print_stats () =
  let f stat time =
    if time > 1.0 then print_endline (stat ^ ": " ^ (string_of_float time))
  in
    Hashtbl.iter f phases_ht;
    print_endline ("Total time: "
		   ^ (string_of_float (Unix.gettimeofday () -. start_time)))

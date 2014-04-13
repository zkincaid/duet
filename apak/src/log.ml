(** Options *)
let debug_mode      = ref false
let default_debug   = ref false
let debug_phases    = ref ([] : string list)
let verbosity_level = ref 0

let terminal_supports_colors =
  let term = Unix.getenv "TERM" in
  let in_channel =
    Unix.open_process_in ("tput -T" ^ term ^ " colors")
  in
  try
    begin
      try
	Scanf.fscanf in_channel "%d"
	  (fun colors ->
	    ignore (Unix.close_process_in in_channel);
	    colors >= 8)
      with End_of_file ->
	ignore (Unix.close_process_in in_channel);
	false
    end
  with e ->
    ignore (Unix.close_process_in in_channel);
    raise e

(** Verbosity levels *)
let top    = 0   (** print only errors *)
let phases = 1   (** print phases *)
let fix    = 3   (** print steps in fixpoint computation *)
let bottom = 4   (** print everything *)
let info   = 2   (** print extra information *)

type attributes =
| Black | Red | Green | Yellow | Blue | Magenta | Cyan | White
| Bold | Underline

let attr_code = function
  | Black -> "\x1b[30m"
  | Red -> "\x1b[31m"
  | Green -> "\x1b[32m"
  | Yellow -> "\x1b[33m"
  | Blue -> "\x1b[34m"
  | Magenta -> "\x1b[35m"
  | Cyan -> "\x1b[36m"
  | White -> "\x1b[37m"
  | Bold -> "\x1b[1m"
  | Underline -> "\x1b[4m"
let reset_attributes = "\x1b[0m"

let loggers = Hashtbl.create 32
let set_verbosity_level name value =
  try (Hashtbl.find loggers name) := value
  with Not_found ->
    invalid_arg ("Log.set_verbosity_level: `" ^ name ^ "' is not registered")

module Make(M : sig val name : string end) = struct
  let my_verbosity_level = ref 0
  let _ =
    if Hashtbl.mem loggers M.name
    then failwith ("Duplicate logger name: `" ^ M.name ^ "'");
    Hashtbl.add loggers M.name my_verbosity_level

  let logf ?(level=info) ?(attributes=[]) fmt =
    let (start, reset) =
      Obj.magic
	(if terminal_supports_colors
	 then (String.concat "" (List.map attr_code attributes), "\x1b[0m@\n@?")
	 else ("", ""))
    in
    if !verbosity_level >= level || !my_verbosity_level >= level
    then Format.printf (start ^^ fmt ^^ reset)
    else Format.ifprintf Format.std_formatter fmt

  let log ?(level=info) ?(attributes=[]) str =
    logf ~level:level ~attributes:attributes "%s" str

  let log_pp ?(level=info) ?(attributes=[]) pp x =
    logf ~level:level ~attributes:attributes "%a" pp x
end

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

let errorf fmt =
  if terminal_supports_colors
  then Format.eprintf ("\x1b[31;1m" ^^ fmt ^^ "\x1b[0m@\n@?")
  else Format.eprintf fmt
let error msg = errorf msg
let error_pp pp x = errorf "%a" pp x

let phases_ht = Hashtbl.create 32
let time str f arg =
  let start_time = Unix.gettimeofday () in
  let record_time () =
    let time = (Unix.gettimeofday ()) -. start_time in
    try Hashtbl.replace phases_ht str (Hashtbl.find phases_ht str +. time)
    with Not_found -> Hashtbl.add phases_ht str time
  in
  try
    let result = f arg in
    record_time();
    result
  with exn -> record_time(); raise exn

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

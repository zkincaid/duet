(** Logging *)

(** Verbosity levels - from BatLog *)
type level = [ `trace | `debug | `info | `warn | `error | `fatal | `always ]
let level_leq x y =
  let to_int = function
    | `trace -> 0 | `debug -> 1 | `info -> 2 | `warn -> 3
    | `error -> 4 | `fatal -> 5 | `always -> 6
  in
  (to_int x) <= (to_int y)


let debug_mode      = ref false
let default_debug   = ref false
let debug_phases    = ref ([] : string list)
let verbosity_level : level ref = ref `always
let colorize        = ref (Unix.isatty Unix.stdout)

let level_of_string = function
  | "trace" -> `trace
  | "debug" -> `debug
  | "info" -> `info
  | "warn" -> `warn
  | "error" -> `error
  | "fatal" -> `fatal
  | "always" -> `always
  | lev ->
    Format.ksprintf invalid_arg "Unrecognized level: `%s'" lev

let loggers = Hashtbl.create 32
let set_verbosity_level name (value : level) =
  try (Hashtbl.find loggers name) := value
  with Not_found ->
    invalid_arg ("Log.set_verbosity_level: `" ^ name ^ "' is not registered")

module Make(M : sig val name : string end) = struct
  let my_verbosity_level = ref `always
  let _ =
    if Hashtbl.mem loggers M.name
    then failwith ("Duplicate logger name: `" ^ M.name ^ "'");
    Hashtbl.add loggers M.name my_verbosity_level

  let logf ?(level=`info) ?(attributes=[]) fmt =
    let attr_code = function
      | `Black -> format_of_string "\x1b[30m"
      | `Red -> "\x1b[31m"
      | `Green -> "\x1b[32m"
      | `Yellow -> "\x1b[33m"
      | `Blue -> "\x1b[34m"
      | `Magenta -> "\x1b[35m"
      | `Cyan -> "\x1b[36m"
      | `White -> "\x1b[37m"
      | `Bold -> "\x1b[1m"
      | `Underline -> "\x1b[4m"
    in
    let format_of_attrs =
      List.fold_left
        (fun fmt attr -> fmt ^^ (format_of_string (attr_code attr)))
        ""
    in
    let (start, reset) =
      if !colorize && attributes != [] then
        (format_of_attrs attributes, format_of_string "\x1b[0m@\n@?")
      else
        ("", "@\n@?")
    in
    if level_leq (!verbosity_level) level
       || level_leq (!my_verbosity_level) level
    then
      Format.fprintf Format.std_formatter (start ^^ fmt ^^ reset)
    else
      Format.ifprintf Format.std_formatter fmt


  let log ?(level=`info) ?(attributes=[]) str =
    logf ~level ~attributes "%s" str

  let log_pp ?(level=`info) ?(attributes=[]) pp x =
    logf ~level ~attributes "%a" pp x

end

include Make(struct let name = "default" end)

let debug_formatter =
  let chan = stdout in
  let out buf pos len =
    if !debug_mode then output_substring chan buf pos len
    else ()
  in
  let flush () = flush chan in
  Format.make_formatter out flush

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
  if !colorize
  then Format.eprintf ("\x1b[31;1m" ^^ fmt ^^ "\x1b[0m@\n@?")
  else Format.eprintf (fmt ^^ "@\n@?")
let error msg = errorf msg
let error_pp pp x = errorf "%a" pp x

let fatalf fmt =
  let fmt =
    if !colorize
    then ("\x1b[31;1m" ^^ fmt ^^ "\x1b[0m@\n@?")
    else fmt
  in
  Format.kfprintf (fun _ -> exit (-1)) Format.err_formatter fmt

let fatal msg = fatalf msg

let invalid_argf fmt = Format.ksprintf invalid_arg fmt

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
  logf ~level:`info ~attributes:[`Bold; `Green] "= %s %s" str padding;
  if List.exists (fun x -> x = str) !debug_phases then begin
    let old_debug = !debug_mode in
    debug_mode := true;
    let result = time str f arg in
    debug_mode := old_debug;
    result
  end else time str f arg

let start_time = Unix.gettimeofday ()
let print_stats () =
  let f stat time = print_endline (stat ^ ": " ^ (string_of_float time))
  in
  Hashtbl.iter f phases_ht;
  print_endline ("Total time: "
                 ^ (string_of_float (Unix.gettimeofday () -. start_time)))

open Apak
open Arg

let parameterized   = ref false

let sanity_checks   = ref true
let display_graphs  = ref false
let show_stats      = ref false
let library_path    = ref "" (** Path to standard libraries *)

let widening        = ref true

(** Enable/disable possibility of failure for builtin functions *)
let fail_malloc     = ref false
let fail_fork       = ref false

(* Command line arguments *****************************************************)

let verbosity_arg =
  ("-verbosity",
   Arg.Set_int Log.verbosity_level,
   " Set verbosity level (higher = more verbose; defaults to 0)")

let stats_arg =
  ("-stats", Arg.Set show_stats, " Display statistics")

let lib_arg =
  ("-lib",
   Arg.Set_string library_path,
   " Change path to standard libraries")

(** Set the load path.  The load path should be a colon-delimited list
    of directories.  The load path determines which directories that
    {!find_file} looks in. *)

let load_path_arg =
  ("-loadpath", Arg.String Putil.set_load_path, " Set load path")

(* default load path *)
let _ = Putil.set_load_path "/usr/share/duet:."

let parameterized_arg =
  ("-parameterized", Arg.Set parameterized, " Use parameterized model")

let whole_program_arg =
  ("-no-whole-program",
   Arg.Clear CfgIr.whole_program,
   " Turn off whole-program analysis")

let temp_dir_arg =
  ("-temp-dir",
   Arg.String (Putil.set_temp_dir),
   " Set temp dir")

let fail_malloc_arg =
  ("-fail-malloc", Arg.Set fail_malloc, " Allow mallocs to fail")

let fail_fork_arg =
  ("-fail-fork", Arg.Set fail_fork, " Allow forks to fail")


(** Debug args *)
let debug_arg =
  ("-debug", Arg.Set Log.debug_mode, " Print debugging information")

let debug_phase_arg =
  let add_debug_phase phase =
    Log.debug_phases := phase::(!Log.debug_phases)
  in
    ("-debug-phase",
     Arg.String add_debug_phase,
     " Print debugging information for a particular phase")

let sanity_check_arg =
  ("-no-sanity-check", Arg.Clear sanity_checks, " Disable sanity checks")

let display_graphs_arg =
  ("-display-graphs",
   Arg.Set display_graphs,
   " Display graphs (requires Eye of Gnome)")

let pass_args : (key * spec * doc) list ref = ref []

let debug_args = ref
  [
    debug_arg;
    debug_phase_arg;
    sanity_check_arg;
    display_graphs_arg;
  ]

let config_args = ref
  [
    verbosity_arg;
    stats_arg;
    whole_program_arg;
    lib_arg;
    load_path_arg;
    parameterized_arg;
    temp_dir_arg;
    fail_malloc_arg;
    fail_fork_arg;
  ]

let passes : (CfgIr.file -> unit) list ref = ref []
let run file = List.iter (fun f -> f file) (List.rev (!passes))

let register_pass (name, pass, doc) =
  let a = (name, Arg.Unit (fun () -> passes := pass::(!passes)), doc) in
  pass_args := a::!pass_args
let register_debug a = debug_args := a::!debug_args
let register_debug_pass (name, pass, doc) =
  let a = (name, Arg.Unit (fun () -> passes := pass::(!passes)), doc) in
  debug_args := a::!debug_args
let register_config a = config_args := a::!config_args

let spec_list () = (!pass_args) @ (!config_args) @ (!debug_args)

let parsers : (string * (string -> CfgIr.file)) list ref = ref []
let register_parser p = parsers := p::!parsers
let parse filename =
  let rec go = function
    | ((suffix, parse)::tl) ->
      if Filename.check_suffix filename suffix then begin
	let file = Log.phase "Parsing" parse filename in
	CfgIr.gfile := Some file;
	file
      end else go tl
    | [] -> failwith "Unrecognized file extension"
  in
  go (!parsers)

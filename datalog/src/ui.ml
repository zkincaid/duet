open Apak
open DatalogCore
open Datalog

(** Lines of the source file classified by how they will be parsed. *)
type pr =
    { mutable directives: string list;
      mutable doms: string list;
      mutable rels: string list;
      mutable ruls: string list }



let read_program dir file =
  let lines = ref [] in
  let chan = open_in (Filename.concat dir file) in
  try
    while true; do
      lines := input_line chan :: !lines
    done; []
  with End_of_file ->
    close_in chan;
    List.rev !lines

let get_domains line =
  let l1 = BatString.nsplit line " " in
    List.map (fun k ->
        let l3 = BatString.nsplit k ":" in
        let a = List.hd l3 in
        let offset =
            int_of_char (String.get a (String.length a - 1))
        in
        let dom = Str.string_before a (String.length a -1) in
            (dom,offset)) 
        (List.tl l1) (* everything after the leading '# ' *)

let inputTuples d rels dir =
  let addTuples rel =
    Log.debug ("Loading tuples for relation: " ^ rel);
    let chan = open_in (Filename.concat dir (rel^".tuples")) in
    let fst_line = input_line chan in
    let get_line () =
      List.map int_of_string (BatString.nsplit (input_line chan) " ")
    in
    let rec get_nonempty_line () =
      let line = get_line () in
	if List.length line = 0 then get_nonempty_line ()
	else line
    in
    let doms_lst = get_domains fst_line in
      Log.debug ("Domain for " ^ rel ^ ": "
		 ^ (String.concat ", " (List.map fst doms_lst)));
      let emit = d#input_tuples rel doms_lst in
	try
	  while true do
	    emit (get_nonempty_line ())
	  done
	with End_of_file -> ()
  in
    List.iter addTuples rels

let parse_update stmt lst =
  let add_revoke = 
    if (String.get stmt 0 = '+') then
      true
    else false
  in
  let rel_name = 
    let last = String.index stmt '(' in
      Str.string_after (Str.string_before stmt last) 1
  in
  let bdd_lst =
    let first = String.index stmt '(' in
    let last = String.index stmt ')' in
    let str_lst = Str.string_after (Str.string_before stmt last) (first+1) in
      print_endline str_lst;
      List.fold_right (fun k lst -> (int_of_string k)::lst) (BatString.nsplit str_lst ",") []
  in
    (rel_name, bdd_lst, add_revoke) :: lst

(*******************************************************************************
 ** Command line interface
 ******************************************************************************)
let updates = ref []
let update_go s = updates := s::(!updates)
let program = ref ""
let program_go s = program := s

let main_program =
  ("-main_program", Arg.String program_go, " run main program")

let update =
  ("-update", Arg.String update_go, " run update")

let verbosity_arg =
  ("-verbosity",
   Arg.Set_int Log.verbosity_level,
   " Set verbosity level (higher = more verbose; defaults to 0)")

(* Debugging *)
let debug_arg =
  ("-debug", Arg.Set Log.debug_mode, " Print debugging information")

let strategy =
  let go = function
    | "polar" -> Incremental.incr_strategy := Incremental.ISPolar
    | "simple" -> Incremental.incr_strategy := Incremental.ISSimple
    | "revoke" -> Incremental.incr_strategy := Incremental.ISRevoke
    | _ -> failwith "Unrecognized incremental strategy"
  in
    ("-strategy",
     Arg.String go,
     " change incremental strategy: simple, polar, or revoke")

let spec_list =
  [
    main_program;
    update;
    strategy;
    verbosity_arg;
    debug_arg
  ]

let usage_msg = "This is the main interface."

let anon_fun s = raise (Arg.Bad (s ^ " is not recognized"))

let run_program pr updates = 
  let dir = Filename.dirname pr in
  let name = Filename.basename pr in
  let d = new Datalog.mysolver dir name in
  let run_update file =
    let chan = open_in (Filename.concat dir file) in
    let tuples =
      let rec go lst =
	try go (parse_update (input_line chan) lst)
	with End_of_file -> (close_in chan; lst)
      in
	go []
    in
      List.iter (fun (k,l,m) ->
		   print_endline ("Tuple: " ^ k ^ "/" ^ (String.concat "," (List.map string_of_int l)));
		   if m then d#add_init_tuple k l
		   else d#remove_init_tuple k l) tuples;
      d#run ()
  in
  let run_update file = Log.phase ("Update " ^ file) run_update file in
  let output_relation rel =
    let chan = open_out (Filename.concat dir (rel ^ ".tuples")) in
    let output_tuple x =
      output_string chan (String.concat " " (List.map string_of_int x) ^ "\n")
    in
      Log.debug ("Writing " ^ rel ^ " to disk");
      d#iter_tuples output_tuple rel;
      close_out chan
  in
    List.iter d#emit (read_program dir name);
  let parsed = d#parse () in
    List.iter print_endline parsed.output_rels;
    inputTuples d parsed.input_rels dir;
    d#run ();
    List.iter run_update updates;
    List.iter output_relation parsed.output_rels;
    d#kill ()

let _ =
  Buddy.bdd_init ~nodenum:500000 ~cachesize:125000 ();
  Arg.parse (Arg.align spec_list) anon_fun usage_msg;
  if (!program = "") then
    (Arg.usage (Arg.align spec_list) "Empty or nonexistent -main_program";
    exit 1)
  else
    run_program !program !updates;

open Buddy
open Graph
open DatalogCore
open DatalogParser
open Rename
open Interpreter
open Incremental
open Apak

let use_bddbddb = ref false

let update_string_map map key update =
  StringMap.add key (update (StringMap.find key map)) map

class mysolver dir name =
object (self)
  val mutable globals = {dvars = HT.create 32; size = HT.create 32}
  val mutable domains = []

  val mutable initial_state = StringMap.empty
  val mutable removed_tuples = StringMap.empty
  val mutable added_tuples = StringMap.empty
  val mutable dependence_graph = None
  val mutable relations = []
  val mutable parsed = None

  val state = State.empty ()

  val datalog_buf = Buffer.create 1024

  method get_state () =
    state

  (** Emit a line of datalog source code *)
  method emit line =
    Buffer.add_string datalog_buf line;
    Buffer.add_char datalog_buf '\n'

  (** Create a new domain *)
  method new_domain name size = 
    domains <- (name,size) :: domains;
    HT.add globals.size name size

  method bdd_varorder (lst : (string * int) list) =
    List.iter (fun (x,y) ->
		 let a = dom_size x globals in
		 let var = fdd_extdomain a in
		   HT.add globals.dvars (x,y) var)
      (List.rev lst);
    bdd_setvarorder (List.rev (bdd_getvarorder ()))

  method new_relation rel domains =
    if not (StringMap.mem rel initial_state) then begin
      let canonical = snd (rename_relation (rel, domains) globals) in
	State.new_relation state rel canonical;
	relations <- (rel, domains)::relations;
	initial_state <- StringMap.add rel bdd_false initial_state;
	removed_tuples <- StringMap.add rel bdd_false removed_tuples;
	added_tuples <- StringMap.add rel bdd_false added_tuples
    end

  method add_init_bdd rel bdd =
    let remove_tup x = bdd_diff x bdd in
      added_tuples <- update_string_map added_tuples rel (bdd_or bdd);
      removed_tuples <- update_string_map removed_tuples rel remove_tup

  method add_init_tuple rel tup =
    self#add_init_bdd rel (tuple (State.canonical state rel) tup)

  method remove_init_tuple rel tup =
    let tup_bdd = tuple (State.canonical state rel) tup in
    let remove_tup x = bdd_diff x tup_bdd in
      added_tuples <- update_string_map added_tuples rel remove_tup;
      removed_tuples <- update_string_map removed_tuples rel (bdd_or tup_bdd)

  method input_tuples name (typ : (string * int) list) =
    self#new_relation name (List.map fst typ);
    (self#add_init_tuple name)

  method get_new_rules parsed_program =
    let num_of_helpers = ref 0 in
    let get_new_rules rul =
      let new_rul_lst =
        (* XXX passing in parsed.domainpsets is kind of ugly *)
	build_and_exist_structure rul globals relations parsed_program.domainpsets (!num_of_helpers)
      in
	match new_rul_lst with
	  | [(x,y,Empty)] ->
	      self#add_init_bdd x (eval_head (x,y) state bdd_true []);
	      new_rul_lst
	  | _ -> new_rul_lst
    in
    let renamed_rules =
      List.fold_left (fun new_rules r -> try (get_new_rules r) @ new_rules
		      with NotEqualConstants -> new_rules)
	[]
	parsed_program.rules
    in
      renamed_rules

  method iter_tuples (f: int list -> unit) relation = 
    fdd_allsat f (State.value state relation) (State.canonical state relation)

  method get_dependence_graph () =
    match dependence_graph with
      | Some dg -> dg
      | None -> begin
            let program = self#parse () in
            List.iter
	      (fun (rel, domains) -> self#new_relation rel domains)
              program.relations;
            let new_rules = self#get_new_rules program in
            let dg = construct_dependence_graph new_rules in (
              self#bdd_varorder program.varorder;
              dependence_graph <- Some dg;
              dg)
        end

  method parse () =
    match parsed with
    | Some p -> p
    | None -> begin
        let p = parse (Buffer.contents datalog_buf) in
            parsed <- Some p;
            List.iter
                (function (domain_name, domain_size) ->
		    self#new_domain domain_name domain_size)
                p.domains;
            p
        end

  method run_impl () =
    let dependence_graph = self#get_dependence_graph () in
    let init_val rel = StringMap.find rel initial_state in
    let added =
      let f rel bdd = bdd_diff bdd (init_val rel) in
	StringMap.mapi f added_tuples
    in
    let removed =
      let f rel bdd = bdd_and bdd (init_val rel) in
	StringMap.mapi f removed_tuples
    in
    let added_val rel = StringMap.find rel added in
    let removed_val rel = StringMap.find rel removed in
    let new_initial =
      let f rel bdd = bdd_diff (bdd_or bdd (added_val rel)) (removed_val rel) in
	StringMap.mapi f initial_state
    in
      Log.phase "Run datalog program" (change_tuples state initial_state added removed) dependence_graph;
      initial_state <- new_initial;
      added_tuples <- StringMap.map (fun _ -> bdd_false) added_tuples;
      removed_tuples <- StringMap.map (fun _ -> bdd_false) removed_tuples

  method run () = Log.phase "Datalog" self#run_impl ()
  method kill () =
    bdd_done ()

end;;

(** Locate the bddbddb jar file *)
let find_bddbddb () =
  match Putil.find_file "bddbddb.jar" with
  | Some file -> file
  | None ->
    failwith ("Cannot locate bddbddb.  Please specify the location of "
	      ^ "bddbddb with -loadpath")

let find_libbuddy () =
  match Putil.find_file "libbuddy.so" with
  | Some file -> file
  | None ->
    failwith ("Cannot locate libbuddy.  Please specify the location of "
	      ^ "libbuddy.so with -loadpath")

let wait_for_bddbddb input =
  let ss = ref "" in
    while String.length (!ss) != 1 do
      ss := input_line input;
      print_endline (!ss)
    done

exception Domain_not_found of string

(** monolithicSolver reinstantiates the datalog solver at every call
    to run.  This is generally slower than incrementalSolver, but can
    be used when the fact databases are not monotone. *)
class monolithicSolver dir name  =
object (self)
  val mutable channels = []
  val domains = HT.create 16
  val datalog_buf = Buffer.create 1024

  (** Emit a line of datalog source code *)
  method emit line =
    Buffer.add_string datalog_buf line;
    Buffer.add_char datalog_buf '\n'

  method write_program () =
    let datalog_chan = open_out (dir ^ "/" ^ name ^ ".datalog") in
    let print_domain name size =
      output_string datalog_chan (name ^ " " ^ (string_of_int (1+size)) ^ "\n")
    in
      HT.iter print_domain domains;
      output_string datalog_chan (Buffer.contents datalog_buf);
      close_out datalog_chan

  (** Create a new domain *)
  method new_domain name = HT.add domains name 0

  method ensure_domain_capacity name size =
    try HT.replace domains name (max size (HT.find domains name))
    with Not_found -> raise (Domain_not_found name)

  (** Create a new relation, whose tuples will be loaded from a file.
      The input to this method is the name of the new relation and a
      list of domains indicating the type of the relation.  This
      method returns a function that takes a tuple as input and writes
      it to a file.  May raise {!Domain_not_found} if one of the
      domains in the type as not already been created (via
      {!new_domain}). *)
  method input_tuples name typ =
    let chan = open_out (dir ^ "/" ^ name ^ ".tuples") in
    let list_str delim str xs = String.concat delim (List.map str xs) in
    let var_id = ref 0 in
    let var_str (domain,_) = 
      var_id := !var_id + 1;
      ("v" ^ (string_of_int (!var_id)) ^ ":" ^ domain)
    in
    let typ_header (name,level) =
      try name ^ (string_of_int level) ^ ":32" (* 32 doesn't matter *)
      with Not_found -> raise (Domain_not_found name)
    in
    let increase_domain (name, _) size =
      self#ensure_domain_capacity name size
    in
    let add_tuple tup =
      List.iter2 increase_domain typ tup;
      output_string chan ((list_str " " string_of_int tup) ^ "\n")
    in
      channels <- chan::channels;
      self#emit (name ^ "(" ^ (list_str "," var_str typ) ^ ") inputtuples");
      output_string chan ("# " ^ (list_str " " typ_header typ) ^ "\n");
      add_tuple

  method run () =
    self#write_program ();
    List.iter flush channels;
    let cmd =
      "export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:"
      ^ (Filename.dirname (find_libbuddy ()))
      ^ " && java -Xmx1024m -jar " ^ (find_bddbddb ())
      ^ " " ^ dir ^ "/" ^ name ^ ".datalog"
      ^ " 1> /dev/null 2> /dev/null"
    in
      ignore (Log.phase "Datalog query" Sys.command cmd)

  method kill () = ()

  (** Iterate a function over all tuples inferred for a particular
      relation, (which should have been declared as an output
      relation) *)
  method iter_tuples (f:int list -> unit) relation =
    let chan = open_in (dir ^ "/" ^ relation ^ ".tuples") in
      try
	ignore (input_line chan); (* kill header *)
	while true do
	  let x = BatString.rchop (input_line chan) in
	  f (List.map int_of_string (BatString.nsplit x " "))
	done
      with End_of_file -> close_in chan
      | Failure "int_of_string" -> assert false

  (** Pretty print a tuples file, and store it in relation.tuples.pretty *)
  method pretty_tuples (fs : (int -> string) list) relation =
    let chan = open_out (dir ^ "/" ^ relation ^ ".tuples.pretty") in
    let f tup =
      try
	let strings =
	  List.fold_right2 (fun f x rest -> (f x)::rest) fs tup []
	in
	  output_string chan ((String.concat "  " strings) ^ "\n");
      with Enumeration.Not_in_enumeration _ -> () (* ignore *)
    in
      self#iter_tuples f relation;
      close_out chan
end;;

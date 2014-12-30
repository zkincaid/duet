open Apak

module HT = Hashtbl

let wait_for_bddbddb input =
  let ss = ref "" in
    while String.length (!ss) != 1 do
      ss := input_line input;
      print_endline (!ss)
    done

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
    with Not_found -> invalid_arg "ensure_domain_capacity"

  (** Create a new relation, whose tuples will be loaded from a file.  The
      input to this method is the name of the new relation and a list of
      domains indicating the type of the relation.  This method returns a
      function that takes a tuple as input and writes it to a file.  Raises
      {!Invalid_arg} if one of the domains in the type as not already been
      created (via {!new_domain}). *)
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
      with Not_found -> invalid_arg "input_tupes"
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
    if Sys.command "java -version 2>/dev/null" != 0 then begin
      failwith "Java not found"
    end;
    let cmd =
      "export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:"
      ^ Config.bddbddb_path
      ^ " && java -Xmx1024m -jar " ^ Config.bddbddb_path ^ "/bddbddb.jar"
      ^ " " ^ dir ^ "/" ^ name ^ ".datalog"
      ^ " 1> /dev/null 2> /dev/null"
    in
    Sys.command cmd

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
end

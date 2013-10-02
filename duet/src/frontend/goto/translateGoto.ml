open Goto
open Core
open Expr
open CfgIr
open Apak

type symtbl =
    { identifiers : (string, varinfo) Hashtbl.t;
      types : (string, ctyp ref) Hashtbl.t;
      macros : (string, expr) Hashtbl.t;
      instrs : (goto_instr, def) Hashtbl.t;
      mutable final : bool }

let rec iter_between f = function
  | (x::(y::z)) -> f x y; iter_between f (y::z)
  | _ -> ()

let find_ident tbl sym =
  try Hashtbl.find tbl.identifiers sym
  with Not_found -> failwith ("No symbol table entry for " ^ sym)


let find_type tbl typ =
  try Named (typ, Hashtbl.find tbl.types typ)
  with Not_found ->
    if tbl.final then failwith ("No symbol table entry for type " ^ typ)
    else let tref = ref Void in
      Hashtbl.add tbl.types typ tref;
      Named (typ, tref)

let add_type tbl name typ =
  try let tref = Hashtbl.find tbl.types name in
    if !tref = Void then tref := typ;
    Named (name, tref)
  with Not_found ->
    let tref = ref typ in
      Hashtbl.add tbl.types name (ref typ);
      Named (name, tref)

let int_of_binary_string x =
  let x_int = ref 0 in
    for i = 0 to String.length x - 1 do
      x_int := !x_int lsl 1;
      match String.get x i with
	| '0' -> ()
	| '1' -> x_int := !x_int + 1
	| _ -> failwith "Illegal character in binary string"
    done;
    !x_int

let tr_location loc =
  { Cil.line = (try int_of_string (irep_find_string loc "line")
		with Failure _ -> -1);
    Cil.file = irep_find_string loc "file";
    Cil.byte = -1 (* unused *) }

let rec tr_typ symtbl irep =
  match irep_id irep with
    | "signedbv" | "unsignedbv" ->
	let ik = match irep_find_string irep "width" with
	  | "1" -> IBool
	  | "8" -> IChar
	  | "16" -> IShort
	  | "32" -> IInt
	  | "48" -> ILongLong (* todo *)
	  | "64" -> ILongLong
	  | x -> failwith ("Unknown integer width: " ^ x)
	in
	  Concrete (Int ik)
    | "floatbv" | "fixedbv" ->
	let fk = match irep_find_string irep "width" with
	  | "32" -> FFloat
	  | "64" -> FDouble
	  | "80" -> FLongDouble (* Not robust! *)
	  | x -> failwith ("Unknown float width: " ^ x)
	in
	  Concrete (Float fk)
    | "bool" -> Concrete (Int IBool)
    | "code" ->
	let args_irep = irep_arguments irep in
	let return = tr_typ symtbl (irep_find irep "return_type") in
	let args =
	  List.map (fun x -> tr_typ symtbl (irep_find x "type")) args_irep
	in
	  Concrete (Func (return, args))
    | "empty" -> Concrete Void
    | "pointer" ->
	let subtype = tr_typ symtbl (irep_find irep "subtype") in
	  Concrete (Pointer subtype)
    | "array" -> (* todo: get size! *)
	let subtype = tr_typ symtbl (irep_find irep "subtype") in
	  Concrete (Array (subtype, None))
    | "symbol" ->
	find_type symtbl (irep_find_string irep "identifier")
    | "struct" ->
	let ri = tr_record_info irep symtbl in
	let typ = Record ri in
	  ignore (add_type symtbl ("c::tag-" ^ ri.rname) typ);
	  Concrete typ
    | "union" ->
	let ri = tr_record_info irep symtbl in
	let typ = Union ri in
	  ignore (add_type symtbl ("c::tag-" ^ ri.rname) typ);
	  Concrete typ
    | "c_enum" ->
	let tag = (irep_find_string irep "tag") in
	let ei = { enname = tag;
		   enitems = [] (* These are filled in later *)
		 }
	in
	  add_type symtbl tag (Enum ei)
    | "incomplete_struct" -> find_type symtbl (irep_find_string irep "tag")
    | "nil" -> Concrete Void
    | x -> (print_irep irep;
	    failwith ("No translation for type: " ^ x))
and tr_record_info irep symtbl =
  let name = irep_find_string irep "tag" in
  let components = irep_components irep in
  let field_of_component component =
    { finame = irep_find_string component "name";
      fityp = tr_typ symtbl (irep_find component "type");
      fioffset = 0; (* todo *) }
  in
    { rname = name;
      rfields = List.map field_of_component components;
      rkey = 0 (* todo *) }

let overflow_char expr = BoolExpr (Atom (Lt, expr, Expr.const_int 128))
let overflow expr = BoolExpr (Atom (Lt, expr, Expr.const_int 1073741824))

let rec tr_expr symtbl irep =
  let typ = tr_typ symtbl (irep_find irep "type") in
    match irep_id irep, irep_operands irep with
      | (op, [x;y]) ->
	  let (x,y) = (tr_expr symtbl x, tr_expr symtbl y) in
	    begin match op with
	      | "and" -> BoolExpr (And (Bexpr.of_expr x, Bexpr.of_expr y))
	      | "or" -> BoolExpr (Or (Bexpr.of_expr x, Bexpr.of_expr y))
	      | "=>" ->
		BoolExpr (Bexpr.implies (Bexpr.of_expr x) (Bexpr.of_expr y))
	      | "<" -> BoolExpr (Atom (Lt, x, y))
	      | "<=" -> BoolExpr (Atom (Le, x, y))
	      | ">" -> BoolExpr (Bexpr.gt x y)
	      | ">=" -> BoolExpr (Bexpr.ge x y)
	      | "notequal" -> BoolExpr (Atom (Ne, x, y))
	      | "=" -> BoolExpr (Atom (Eq, x, y))
	      | "+" -> BinaryOp (x, Add, y, typ)
	      | "-" -> BinaryOp (x, Minus, y, typ)
	      | "*" -> BinaryOp (x, Mult, y, typ)
	      | "/" -> BinaryOp (x, Div, y, typ)
	      | "mod" -> BinaryOp (x, Mod, y, typ)
	      | "shl" -> BinaryOp (x, ShiftL, y, typ)
	      | "shr" -> BinaryOp (x, ShiftR, y, typ)
	      | "ashr" -> BinaryOp (x, ShiftR, y, typ) (* todo *)
	      | "bitor" -> BinaryOp (x, BOr, y, typ)
	      | "bitand" -> BinaryOp (x, BAnd, y, typ)
	      | "bitxor" -> BinaryOp (x, BXor, y, typ)
	      | "index" -> begin
		  (* todo *)
		  match x,y with
		    | (AccessPath ap, _) -> AccessPath (Deref (BinaryOp (AccessPath ap, Add, y, Concrete Dynamic)))
		    | _ -> failwith ("Can't index an expression: "
				     ^ (Expr.show x)
				     ^ (Expr.show y))
		end
	      | "overflow-+" ->
		  overflow (BinaryOp (x, Add, y, typ))
	      | "overflow--" ->
		  overflow (BinaryOp (x, Minus, y, typ))
	      | "overflow-*" ->
		  overflow (BinaryOp (x, Mult, y, typ))
	      | _ -> (print_irep irep;
		      failwith ("Didn't understand binary goto expression: "
				^ op))
	    end
      | (op, [x]) ->
	  begin match op with
	    | "not" ->
	      BoolExpr (Bexpr.negate (Bexpr.of_expr (tr_expr symtbl x)))
	    | "bitnot" -> UnaryOp (BNot, (tr_expr symtbl x), typ)
	    | "dereference" | "pointer_offset" -> AccessPath (Deref (tr_expr symtbl x))
	    | "invalid-pointer" ->
		BoolExpr (Atom (Ne, tr_expr symtbl x, Expr.zero))
	    | "array_of" -> tr_expr symtbl x (* todo *)
	    | "address_of" -> begin
		match irep_id x, irep_operands x with
		  | ("index", [y;z]) ->
		      if (irep_id y = "string-constant"
			  && (tr_expr symtbl z = (Constant (CInt (0, IInt)))))
		      then tr_expr symtbl y
		      else (match tr_expr symtbl x with
			      | AccessPath ap -> AddrOf ap
				  (* todo: need the offset *)
			      | _ ->
				  failwith ("Can't take the address of "
					    ^ "an expression"))

		  | _ -> begin
		      match tr_expr symtbl x with
			| AccessPath ap -> AddrOf ap
			| _ ->
			    failwith "Can't take the address of an expression"
		    end
	      end
	    | "member" -> begin
		match tr_expr symtbl x with
		  | AccessPath ap ->
(*		      let name = irep_find_string irep "component_name" in*)
			(*AccessPath (FieldOffset (ap, name, typ))*) (* todo *)
		      AccessPath (AP.offset ap OffsetUnknown)
		  | _ -> failwith "Can't access fields of an expression"
	      end
	    | "typecast" -> Cast (typ, tr_expr symtbl x)
	    | "unary-" -> UnaryOp (Neg, tr_expr symtbl x, typ)
	    | "overflow-unary-" ->
		overflow (UnaryOp (Neg, tr_expr symtbl x, typ))
	    | "overflow-typecast-31" -> (* todo *)
		overflow (UnaryOp (Neg, tr_expr symtbl x, typ))
	    | "overflow-typecast-7" -> (* todo *)
		overflow (UnaryOp (Neg, tr_expr symtbl x, typ))
	    | "sideeffect" -> Havoc typ
	    | _ -> (print_irep irep;
		    failwith ("Didn't understand unary goto expression: " ^ op))
	  end
      | ("if", [test;bthen;belse]) -> assert false
      | ("constant", []) -> begin
	  let v = irep_find_string irep "value" in
	    match resolve_type typ with
	      | Int IBool -> begin
		  match v with
		    | "0" | "false" -> Constant (CInt (0, IBool))
		    | "1" | "true" -> Constant (CInt (1, IBool))
		    | _ -> failwith ("Unknown boolean constant: " ^ v)
		end
	      | Int ik -> Constant (CInt (int_of_binary_string v, ik))
	      | Pointer t ->
		  if v = "NULL" then Expr.null t
		  else failwith "Unknown pointer constant"
	      | Float fk ->
		  let ival = int_of_binary_string v in
		    if ival != 0 then failwith "Float constant!"
		    else Constant (CFloat (0.0, fk))
	      | Enum _ -> Constant (CInt (int_of_string v, IInt))
	      | t -> failwith ("Constant of unknown type: "
			       ^ (Putil.pp_string format_typ (Concrete t)))
	end
      | ("string-constant", []) ->
	  Constant (CString (irep_find_string irep "value"))
      | ("symbol", []) ->
	  let name = irep_find_string irep "identifier" in
	    AccessPath (Variable (Var.mk (find_ident symtbl name)))
      | ("sideeffect", []) -> begin
	  match irep_find_string irep "statement" with
	    | "nondet" -> Havoc typ
	    | x -> failwith ("Unrecognized side effect: " ^ x)
	end
      | (op, operands) ->
	  failwith ("Didn't understand goto expression: " ^ op ^ " with arity "
		    ^ (string_of_int (List.length operands)))
	  let tr_expr symtbl expr = Expr.simplify (tr_expr symtbl expr)

let build_symbol_table program file =
  (* override find_type *)
  let symtbl =
    { identifiers = Hashtbl.create 128;
      types = Hashtbl.create 32;
      macros = Hashtbl.create 32;
      instrs = Hashtbl.create 128;
      final = false }
  in
  let add_lvalue name sym =
    Log.debug ("Add lvalue symbol: " ^ name);
    let typ = tr_typ symtbl (symbol_type sym) in
    let pretty_name = symbol_base_name sym in
    let loc = symbol_location sym in
    let func_name = irep_find_string loc "function" in
    let var =
      if symbol_static_lifetime sym then
	mk_global_var file name typ
      else
	try let func =
	  List.find (fun f -> (Varinfo.show f.fname) = func_name) file.funcs
	in
	  mk_local_var func pretty_name typ
	with Not_found ->
	  mk_global_var file name typ
    in
      Hashtbl.add symtbl.identifiers name var
  in
  let add_type_symbol name sym =
    let ctyp = resolve_type (tr_typ symtbl (symbol_type sym)) in
      Log.debug ("Add Type symbol: " ^ name);
      ignore (add_type symtbl name ctyp);
      Log.debug_pp format_typ (Concrete ctyp)
  in
  let add_macro_symbol name sym =
    Log.debug ("Add macro symbol");
    (* As far as I know, the only macro symbols are actually just definitions
       of enumeration items.  This function will fail on anything else. *)
    let typ = tr_typ symtbl (symbol_type sym) in
    let ctyp = resolve_type typ in
    let value = tr_expr symtbl (symbol_value sym) in
      match ctyp, value with
	| (Enum ei, Constant (CInt (i, _))) ->
	    ei.enitems <- (name, i)::ei.enitems
	| (Enum _, _) ->
	    failwith "Only integer constants can be associated with enum items"
	| (Void, Constant (CInt (i, _))) -> begin match typ with
	    | Named (tname, tref) ->
		tref := Enum { enname = tname;
			       enitems = [(name, i)] }
	    | _ -> failwith "add enum item"
	  end
	| (typ, _) -> (print_symbol sym;
		       Log.debug_pp format_typ (Concrete typ);
		failwith "Can't add enum items to a non-enumeration type")
  in
  let add_symbol name sym =
    if symbol_is_lvalue sym || name = "main" then add_lvalue name sym
    else if symbol_is_type sym then add_type_symbol name sym
    else if symbol_is_macro sym then add_macro_symbol name sym

  (* Skip symbols we don't know about.  goto-cc doesn't remove undefined
     function symbols from the context after inlining & unused function
     removal - these can safely be skipped.  Hopefully, that's the only kind
     of undefined symbol. *)
  (*
    else begin
    print_endline "Symbol: ";
    print_symbol sym;
    failwith "Don't know what to do with this symbol"
    end
  *)

  in
  let add_fun_symbol f =
    f.fname <- find_ident symtbl (Varinfo.show f.fname)
  in
    iter_symbol add_symbol program;
    List.iter add_fun_symbol file.funcs;
    symtbl.final <- true;
    symtbl

let rec tr_assign symtbl cfg ap rhs =
  match resolve_type (tr_typ symtbl (irep_find rhs "type")) with
    | Array _ ->
	let mk i e = tr_assign symtbl cfg (Deref (BinaryOp (AccessPath ap, Add, Expr.const_int i, Concrete Dynamic))) e in
(*ArrayOffset (ap, expr_of_int i)) e in*)(* todo *)
	  List.concat (BatList.mapi mk (irep_operands rhs))
    | Record ri ->
(*	let offset field = FieldOffset (ap, field.finame, field.fityp) in*)
	(*todo *)
	let offset field = ap in
	  if irep_id rhs = "sideeffect" then begin
	    let mk f = Store (offset f, Havoc f.fityp) in
	      List.map mk ri.rfields
	  end else begin
	    let mk f e = tr_assign symtbl cfg (offset f) e in
	      List.concat (List.map2 mk ri.rfields (irep_operands rhs))
	  end
    | _ -> [Store (ap, tr_expr symtbl rhs)]

let tr_funcall symtbl instr =
  match instr_operands instr with
    | [lhs; func; args] ->
	let lhs =
	  if irep_id lhs = "nil" then None
	  else (match (tr_expr symtbl lhs) with
		  | AccessPath ap -> Some ap
		  | _ -> failwith "LHS not an AP")
	in
	let func = tr_expr symtbl func in
	let args = List.map (tr_expr symtbl) (irep_operands args) in
	  Call (lhs, func, args)
    | _ -> failwith "Wrong arity for function call"

let nodef = Def.HT.create 32
let find_instr tbl cfg id =
  try Hashtbl.find tbl.instrs id
  with Not_found ->
    let loc = tr_location (instr_location id) in
    let def = mk_def loc (Assert (Bexpr.kfalse, "GOTO INTERNAL")) in
      Hashtbl.add tbl.instrs id def;
      Def.HT.add nodef def id;
      Cfg.add_vertex cfg def;
      def

let rec tr_instr symtbl func cfg instr =
  let def () = find_instr symtbl cfg instr in
  let get_guard () = Bexpr.of_expr (tr_expr symtbl (instr_guard instr)) in
  let get_operands () = List.map (tr_expr symtbl) (instr_operands instr) in
  let set_def kind = (def ()).dkind <- kind; Def.HT.remove nodef (def ()) in
  let get_successors () =
    List.map (find_instr symtbl cfg) (instr_successors func instr)
  in
  let add_edge = Cfg.add_edge cfg in
  let add_successor_edges () =
    let d = def () in
      List.iter (add_edge d) (get_successors ())
  in
    match instr_type instr with
      | GNoInstructionType -> print_instr instr; failwith "GNoInstructionType"
      | GGoto ->
	  let guard = get_guard () in
	  let def = def () in
	    begin
	      set_def (Assume Bexpr.ktrue);
	      match get_successors () with
		| [succ] -> add_successor_edges ()
		| [bthen;belse] -> begin
		    let assume_true = mk_def unknown_loc (Assume guard) in
		    let assume_false =
		      mk_def unknown_loc (Assume (negate guard))
		    in
		      add_edge def assume_true;
		      add_edge def assume_false;
		      add_edge assume_true bthen;
		      add_edge assume_false belse
		  end
		| _ -> failwith "Wrong arity for goto"
	    end
      | GAssume ->
	  set_def (Assume (get_guard ()));
	  add_successor_edges ()
      | GAssert ->
	  let guard = get_guard () in
	  set_def (Assert (guard, show_bexpr guard));
	  add_successor_edges ()
      | GOther -> begin
	  match instr_operands instr with
	    | [op] ->
		(* expression instruction, like "3*5;".  We'll translate it to
		   assume(3*5 != 0 || havoc) *)
		let expr = tr_expr symtbl op in
		let havoc = Havoc (Concrete (Int IBool)) in
		  set_def (Assume (Or (Bexpr.of_expr expr,
				       (Bexpr.of_expr havoc))));
		  add_successor_edges ()
	    | _ -> print_instr instr; failwith "GOther"
	end

      | GStartThread -> print_instr instr; failwith "GStartThread"
      | GEndThread -> print_instr instr; failwith "GEndThread"
    (*      | GEndFunction -> print_instr instr; failwith "GEndFunction" *)
      | GAtomicBegin ->
	  set_def (Builtin AtomicBegin);
	  add_successor_edges ()
      | GAtomicEnd ->
	  set_def (Builtin AtomicEnd);
	  add_successor_edges ()
      | GReturn -> begin match get_operands () with
	  | [] -> set_def (Return None)
	  | [x] -> set_def (Return (Some x))
	  | _ -> failwith "Wrong arity for return"
	end
      | GAssign -> begin match instr_operands instr with
	  | [x; y] -> begin match tr_expr symtbl x with
	      | AccessPath ap ->
		  let def = def () in
		  let instrs = tr_assign symtbl cfg ap y in
		  let instr_defs =
		    List.map (mk_def unknown_loc) (List.tl instrs)
		  in
		    set_def (List.hd instrs);
		    if List.length instr_defs > 0 then begin
		      iter_between add_edge instr_defs;
		      add_edge def (List.hd instr_defs);
		      let last =
			List.nth instr_defs ((List.length instr_defs) - 1)
		      in
			List.iter (add_edge last) (get_successors ())
		    end else add_successor_edges ()
	      | _ -> failwith ("LHS of assignment not an AP")
	    end
	  | ops -> failwith ("Wrong arity for assignment")
	end
	  (*      | GDecl -> print_instr instr; failwith "GDecl" *)
      | GDead -> print_instr instr; failwith "GDead"
      | GFunctionCall ->
	  set_def (tr_funcall symtbl instr);
	  add_successor_edges ()
      | GThrow -> print_instr instr; failwith "GThrow"
      | GCatch -> print_instr instr; failwith "GCatch"
      | GEndFunction -> set_def (Assume (Bexpr.ktrue))

      (* skips *)
      | GSkip | GDecl | GLocation ->
	  set_def (Assume (Bexpr.ktrue));
	  add_successor_edges ()

let initialize_file filename goto_file =
  let file =
    { filename = filename;
      funcs = [];
      threads = [];
      entry_points = [];
      vars = [];
      CfgIr.types = []; (* Todo *)
      globinit = None;
    }
  in
  let f name _ =
    let func_ir =
      { fname = mk_global_var file name (Concrete (Int IInt)); (* todo *)
	formals = [];
	locals = [];
	cfg = Cfg.create ();
	file = Some file;
      }
    in
      file.funcs <- func_ir::file.funcs
  in
    iter_functions f goto_file;
    file

let read_file filename =
  let gp = read_binary filename in
  let file = initialize_file filename gp in
  let symtbl = build_symbol_table gp file in
  let build_cfg name func =
    let func_ir = lookup_function_name name file in
    let init_vertex = ref None in
    let f instr =
      tr_instr symtbl func func_ir.cfg instr;
      (match !init_vertex with
	 | Some _ -> ()
	 | None   -> init_vertex := Some (find_instr symtbl func_ir.cfg instr))
    in
      iter_instr f func;
      (*minimize_cfg func_ir.cfg;*)
      begin match !init_vertex with
	| Some init -> remove_unreachable func_ir.cfg init
	| None      -> failwith "TranslateGoto: No initial vertex for CFG"
      end;
      Cfg.sanity_check func_ir.cfg
  in
  let is_init f = (Varinfo.show f.fname) = "c::__CPROVER_initialize" in
    iter_functions build_cfg gp;
    begin
      match (List.partition is_init file.funcs) with
	| ([init], rest) -> (file.funcs <- rest; file.globinit <- Some init)
	| _ -> ()
    end;
    file.threads <- (if !CfgIr.whole_program
		     then [(lookup_function_name "main" file).fname]
		     else List.map (fun f -> f.fname) file.funcs);
    file.entry_points <- file.threads;
    if (Def.HT.length nodef > 0) then begin
      Def.HT.iter (fun k v -> print_instr v) nodef;
      failwith "Some def not set!"
    end;
    file

let _ = CmdLine.register_parser ("goto", read_file)

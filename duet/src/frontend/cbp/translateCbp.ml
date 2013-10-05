open CbpAst
open Core
open Ast
open Apak

exception No_translation of string
let typ_bool = Concrete (Int IBool)
let constant_bool k = Constant (CInt (k, IBool))
let ktrue = constant_bool 1
let kfalse = constant_bool 0

module VMemo = Memo.Make(struct
			   type t = CbpAst.var
			   let hash v = v.CbpAst.vid
			   let compare x y = compare x.CbpAst.vid y.CbpAst.vid
			   let equal x y = x.CbpAst.vid = y.CbpAst.vid
			 end);;
module Translation(S : sig
		     val cbp_file : CbpAst.program
		     val file : file
		   end) =
struct
  let translate_var =
    VMemo.memo (fun var ->
      (Var.mk (Varinfo.mk_local var.CbpAst.vname typ_bool)))
  let mk_stmt = mk_stmt S.file
  let ap_of_var v = AccessPath (Variable (translate_var v))
  let stmt_of_def def = mk_stmt (Instr [Def.mk def])

  (* maps cbp stmts to ast representations *)
  let stmt_map = Hashtbl.create 32
  let add_stmt_tr stmt tr = Hashtbl.add stmt_map stmt tr; tr
  let add_sk_tr stmt sk = add_stmt_tr stmt (mk_stmt sk)

  (* temporary variables *)
  let max_var = ref 0
  let new_var func =
    let id = !max_var in
    let name = "_tmp" ^ (string_of_int id) in
    let var = CbpAst.mk_var name in
      max_var := !max_var + 1;
      func.CbpAst.locals <- var::func.CbpAst.locals;
      var
  let new_global_var () =
    let id = !max_var in
    let name = "_tmp" ^ (string_of_int id) in
    let var = CbpAst.mk_var name in
      max_var := !max_var + 1;
      S.cbp_file.CbpAst.vars <- var::S.cbp_file.CbpAst.vars;
      (var, OffsetFixed 0)

  let rec remove_havoc func tr_stmt =
    let mk_ternary var cond bt be =
      tr_stmt (mk_lstmt []
		 (If (cond,
		      [mk_lstmt [] (CbpAst.Assign ([(var, bt)], None))],
		      [mk_lstmt [] (CbpAst.Assign ([(var, be)], None))])))
    in
(*
    let mk_choose var left right =
      let tr_var = Variable (translate_var var) in
      let lbranch = stmt_of_def (Assignment (tr_var, translate_expr left)) in
      let rbranch = stmt_of_def (Assignment (tr_var, translate_expr right)) in
	mk_stmt (Branch (lbranch, rbranch))
    in
*)
    let rm = function
      | OTrue -> ([], CbpAst.True)
      | OFalse -> ([], CbpAst.False)
      | OBinop (op, (lv, left), (rv, right)) ->
	  (lv@rv, Binop (op, left, right))
      | ONot (vars, expr) -> (vars, Not expr)
      | OVar v -> ([], Var v)
      | OPrimeVar v -> ([], PrimeVar v)
      | CbpAst.OHavoc -> ([], CbpAst.Havoc)
	  (* let v = new_var func in ([mk_havoc v], Var v) *)
      | OTernary ((cv, c), (tv, bt), (ev, be)) ->
	  let v = new_var func in
	    (cv@tv@ev@[mk_ternary v c bt be], Var v)
    in
      CbpAst.fold_expr rm

  and translate_expr =
    let f = function
      | OTrue -> constant_bool 1
      | OFalse -> constant_bool 0
      | OBinop (CbpAst.Implies, left, right) ->
	  let left = Bexpr.of_expr left in
	  let right = Bexpr.of_expr right in
	    BoolExpr (Or (Bexpr.negate left, right))
      | OBinop (CbpAst.Xor, left, right) ->
	  let left = Bexpr.of_expr left in
	  let right = Bexpr.of_expr right in
	    BoolExpr (Or (And (left, Bexpr.negate right),
			  And (Bexpr.negate left, right)))
      | OBinop (CbpAst.And, left, right) ->
	  let left = Bexpr.of_expr left in
	  let right = Bexpr.of_expr right in
	    BoolExpr (And (left, right))
      | OBinop (CbpAst.Or, left, right) ->
	  let left = Bexpr.of_expr left in
	  let right = Bexpr.of_expr right in
	    BoolExpr (Or (left, right))
      | OBinop (CbpAst.Eq, left, right) ->
	  BoolExpr (Atom (Eq, left, right))
      | OBinop (CbpAst.Neq, left, right) ->
	  BoolExpr (Atom (Ne, left, right))
      | OBinop (CbpAst.Choose, left, right) ->
	  let left = Bexpr.simplify (Bexpr.of_expr left) in
	  let right = Bexpr.simplify (Bexpr.of_expr right) in
	    (* SLAM *)
	    if (Bexpr.equal left (Bexpr.negate right)) then BoolExpr left
	    else BoolExpr (Or (And (Bexpr.of_expr (Havoc typ_bool),
				    Bexpr.negate right),
			       left))

	    (* boom *)
(*
	    BoolExpr (Or (And (Bexpr.of_expr Havoc, Expr.negate left),
			  right))
*)


	    (* Getafix *)
(*	    BoolExpr (Or (Or (left, right), Bexpr.of_expr Havoc)) *)
      | ONot expr -> BoolExpr (Bexpr.negate (Bexpr.of_expr expr))
      | CbpAst.OHavoc -> Havoc typ_bool
      | OTernary _ -> raise (No_translation "ternary as expr")
      | OVar v -> ap_of_var v
      | OPrimeVar v -> ap_of_var v
    in
      (fun expr -> Expr.simplify (CbpAst.fold_expr f expr))

  (* Translate expr, apply f to the translation, and return a list of
     statements equivalent such that the translated expr yields the
     same result as expr *)
  let with_expr func tr_stmt expr f =
    let (stmts, expr) = remove_havoc func tr_stmt expr in
      stmts @ (f (translate_expr expr))

  let with_expr_stmt func tr_stmt expr f =
    let (pre, expr) = remove_havoc func tr_stmt expr in
    let stmts = f (translate_expr expr) in
      match (pre, stmts) with
	| ([], [stmt]) -> stmt
	| _ -> mk_stmt (Block (pre @ stmts))

  let translate_stmt func =
    let mk_branch bthen belse cond =
      let c = Bexpr.of_expr cond in
	[Hlir.mk_if S.file c bthen belse]
    in
    let with_expr = with_expr func in
    let with_expr_stmt = with_expr_stmt func in
    let rec go stmt = match CbpAst.simplify (stmt_of_lstmt stmt) with
      | CbpAst.Skip -> 
	  add_sk_tr stmt (Instr [])
      | CbpAst.Goto [tgt] ->
	  add_sk_tr stmt (Goto (stmt_id (tr_stmt (lookup_label tgt))))
      | CbpAst.Goto _ -> failwith "Goto without single target"
      | CbpAst.Return [] -> add_stmt_tr stmt (stmt_of_def (Return None))
      | CbpAst.Return [v] ->
	  let mk_return expr = [stmt_of_def (Return (Some expr))] in
	    add_stmt_tr stmt (with_expr_stmt tr_stmt v mk_return)
      | CbpAst.Return _ -> raise (No_translation "Multiple returns")
      | CbpAst.Assign (xs, None) ->
	  let begin_atomic =
	    stmt_of_def (Builtin AtomicBegin)
	  in
	  let end_atomic =
	    stmt_of_def (Builtin AtomicEnd)
	  in
	  let stmts =
	    List.fold_left (fun pre asn -> pre @ (translate_asn asn)) [] xs
	  in
	    add_sk_tr stmt (Block ([begin_atomic]@stmts@[end_atomic]))
      | CbpAst.Assign (xs, Some constrain) ->
(*
	  let stmts =
	    List.fold_left (fun pre asn -> pre @ (translate_asn asn)) [] xs
	  in
	    (match stmts with
	       | [s] -> add_stmt_tr stmt s
	       | _   -> add_sk_tr stmt (Block stmts))

	    *)
	  let begin_atomic =
	    stmt_of_def (Builtin AtomicBegin)
	  in
	  let end_atomic =
	    stmt_of_def (Builtin AtomicEnd)
	  in
	  let add_prime_assign pre (v,expr) =
	    pre @ (translate_asn (CbpAst.get_primed v,expr))
	  in
	  let pre_constrain = List.fold_left add_prime_assign [] xs in
	  let constrain = split_assume constrain in
	  let post_constrain =
	    List.fold_left
	      (fun pre (v,_) -> pre @ (translate_asn (v, Var (get_primed v))))
	      []
	      xs
	  in
	    add_sk_tr stmt (Block ([begin_atomic]
				   @pre_constrain
				   @constrain
				   @post_constrain
				   @[end_atomic]))
      | CbpAst.If (expr, bthen, belse) ->
	  let tr = add_sk_tr stmt (Instr []) in
	  let bthen = List.map tr_stmt bthen in
	  let belse = List.map tr_stmt belse in
	  let if_stmt = with_expr_stmt tr_stmt expr (mk_branch bthen belse) in
	    tr.skind <- if_stmt.skind;
	    tr
      | CbpAst.Assert expr ->
	  add_stmt_tr stmt
	    (with_expr_stmt tr_stmt expr
	       (fun e ->
		 let cond = Bexpr.of_expr e in
		 let msg = Bexpr.show cond in
		 [stmt_of_def (Assert (cond, msg))]))
      | CbpAst.Assume expr ->
	  add_stmt_tr stmt
	    (with_expr_stmt tr_stmt expr
	       (fun e -> [stmt_of_def (Assume (Bexpr.of_expr e))]))
      | CbpAst.Call ([], func, args) ->
	  let f arg g =
	    fun args -> with_expr tr_stmt arg (fun e -> g (e::args))
	  in
	  let func_var = Varinfo.mk_global func typ_bool in
	  let z args =
	    [stmt_of_def (Call (None,
				AccessPath (Variable (Var.mk func_var)),
				args))]
	  in
	    add_sk_tr stmt (Block ((List.fold_right f args z) []))
      | CbpAst.Call ([v], func, args) ->
	  let var = translate_var v in
	  let f arg g =
	    fun args -> with_expr tr_stmt arg (fun e -> g (e::args))
	  in
	  let func_var = Varinfo.mk_global func typ_bool in
	  let z args =
	    [stmt_of_def (Call (Some var,
				AccessPath (Variable (Var.mk func_var)),
				args))]
	  in
	    add_sk_tr stmt (Block ((List.fold_right f args z) []))
      | CbpAst.Call _ ->
	  raise (No_translation "Parallel assignment in call")
      | CbpAst.AtomicBegin ->
	  add_stmt_tr stmt (stmt_of_def (Builtin AtomicBegin))
      | CbpAst.AtomicEnd ->
	  add_stmt_tr stmt (stmt_of_def (Builtin AtomicEnd))
      | CbpAst.While (cond, body) ->
	  let tr = add_sk_tr stmt (Instr []) in
	  let (pre, cond) = remove_havoc func tr_stmt cond in
	  let cond = Bexpr.of_expr (translate_expr cond) in
	  let body = List.map tr_stmt body in
	  let loop_start = Hlir.mk_skip S.file in
	  let loop_end = Hlir.mk_skip S.file in
	  let break = mk_stmt (Goto (stmt_id loop_end)) in
	  let continue = mk_stmt (Goto (stmt_id loop_start)) in
	    tr.skind <- Block ([loop_start]
			       @ pre
			       @ [Hlir.mk_if S.file cond
				    (body@[continue])
				    [break];
				  loop_end]);
	    tr
      | CbpAst.StartThreadGoto tgt ->
	  add_sk_tr stmt (ForkGoto (stmt_id (tr_stmt (lookup_label tgt))))
      | CbpAst.StartThread _ ->
	  failwith "No translation for StartThread"
      | CbpAst.EndThread -> add_stmt_tr stmt (stmt_of_def (Return None))
    and tr_stmt stmt =
      try Hashtbl.find stmt_map stmt
      with Not_found -> go stmt
    and translate_asn (v, expr) =
      let tr_var = translate_var v in
	with_expr tr_stmt expr
	  (fun e -> [stmt_of_def (Assign (tr_var, e))])
    and split_assume expr =
      let mk_assume expr =
	with_expr tr_stmt expr
	  (fun e -> [stmt_of_def (Assume (Bexpr.of_expr e))])
      in
	if CbpAst.expr_height expr <= 5 then mk_assume expr
	else begin
	  match expr with
	    | Binop (CbpAst.And, left, right) ->
		(split_assume left)@(split_assume right)
	    | _ -> mk_assume expr
	end
   in
      tr_stmt
  let translate_func f =
    let body = 
      List.map (translate_stmt f) (f.CbpAst.body)
    in
    let translate_var x = fst (translate_var x) in
      { fname = translate_var (CbpAst.mk_var f.CbpAst.name);
	formals = List.map translate_var (f.CbpAst.formals);
	locals = (List.map translate_var (f.CbpAst.locals)
		  @ (List.map (fun v -> translate_var (get_primed v)) (f.CbpAst.locals)));
	body = body;
        file = Some S.file }
end

let translate cbp_file =
  let file = mk_file "" in
  let module T = Translation(struct
			       let file = file
			       let cbp_file = cbp_file
			     end)
  in
  let translate_var x = fst (T.translate_var x) in
  let primed =
    List.map (fun v -> translate_var (get_primed v)) (cbp_file.CbpAst.vars)
  in
    file.funcs <- List.map T.translate_func (cbp_file.CbpAst.funcs);
    file.vars <- (List.map translate_var (cbp_file.CbpAst.vars) @ primed);
    List.iter Varinfo.set_global file.vars;
    file

let parse filename =
  let program = 
    CbpParse.program CbpLex.cbp (Lexing.from_channel (open_in filename))
  in
  let add_return func =
    let last xs = List.nth xs ((List.length xs) - 1) in
      match stmt_of_lstmt (last func.CbpAst.body) with
	| CbpAst.Return _ -> ()
	| _ -> let return = mk_lstmt [] (CbpAst.Return []) in
	    if func.CbpAst.returns != 0
	    then failwith "Missing return for non-void function";
	    func.CbpAst.body <- func.CbpAst.body @ [return]
  in
  List.iter add_return program.CbpAst.funcs;
  program

let _ =
  let go f =
    CmdLine.widening := false;
    CfgIr.from_file_ast (translate (parse f))
  in
  CmdLine.register_parser ("bp", go)

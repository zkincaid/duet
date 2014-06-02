(*pp camlp4find deriving.syntax *)

(** Internal representation based on control flow graphs *)
open Core
open Afg
open Ast
open Apak

module DefMemo = Memo.Make(Def)

let whole_program   = ref true

(** Control flow graph *)
module Cfg = struct
  module G = MakeFG(Graph.Imperative.Digraph.ConcreteBidirectional(Def))
  include G

  module Dfs = Graph.Traverse.Dfs(G)
  module D = ExtGraph.Display.MakeSimple(G)(Def)
  let display = D.display
  let clone = G.clone Def.clone

  (* Reverse postorder *)
  let reverse_postorder cfg =
    let rank = Def.HT.create 991 in
    let get_rank x =
      try Def.HT.find rank x
      with Not_found -> failwith ("No rank for " ^ (Def.show x))
    in
    let max_rank = ref 0 in
    let set_rank x =
      if not (Def.HT.mem rank x) then begin
	Def.HT.add rank x (!max_rank);
	max_rank := !max_rank + 1
      end
    in
    Dfs.postfix set_rank cfg; (* postorder *)
    fun x y -> Pervasives.compare (get_rank y) (get_rank x)

  let initial_vertex g =
    let init = enum_initial g in
    match BatEnum.get init with
    | Some x -> if BatEnum.is_empty init then x else assert false
    | _ -> assert false

  let sanity_check cfg =
    let init = enum_initial cfg in
    if BatEnum.count init = 1
    then Log.debug "CFG sanity check passed"
    else begin
      print_endline "Initial vertices:";
      BatEnum.iter (fun v -> print_endline (Def.show v)) init;
      D.display cfg;
      failwith "CFG sanity check failed"
    end

  (** Subdivide an edge.  As a precondition, the vertices u and v should have
      an edge between them.  This edge is removed, and edges from u to w and w
      to v are added. *)
  let subdivide g u w v =
    add_vertex g w;
    add_edge g u w;
    add_edge g w v;
    remove_edge g u v
end

module CfgBuilder = struct
  type ivl = Def.t * Def.t

  let mk_single cfg v =
    Cfg.add_vertex cfg v;
    (v, v)

  let mk_skip cfg = mk_single cfg (Def.mk (Assume (Bexpr.ktrue)))

  let mk_seq cfg (ventry, left) (right, vexit) =
    Cfg.add_edge cfg left right;
    (ventry, vexit)

  let mk_block cfg blocks =
    match blocks with
    | [] -> mk_skip cfg
    | (x::xs) ->
      List.fold_left (fun acc x -> mk_seq cfg acc x) x xs

  let mk_if cfg cond bthen belse =
    let ventry = mk_skip cfg in
    let vexit = mk_skip cfg in
    let bthen =
      mk_seq cfg (mk_single cfg (Def.mk (Assume cond))) bthen
    in
    let belse =
      mk_seq cfg (mk_single cfg (Def.mk (Assume (Bexpr.negate cond)))) belse
    in
    ignore (mk_seq cfg ventry bthen);
    ignore (mk_seq cfg ventry belse);
    ignore (mk_seq cfg bthen vexit);
    ignore (mk_seq cfg belse vexit);
    (fst ventry, fst vexit)

  let mk_while_do cfg cond body =
    let ventry = mk_single cfg (Def.mk (Assume cond)) in
    let vexit = mk_single cfg (Def.mk (Assume (Bexpr.negate cond))) in
    ignore (mk_seq cfg ventry body);
    ignore (mk_seq cfg body ventry);
    ignore (mk_seq cfg body vexit);
    (ventry, vexit)

  let mk_do_while cfg cond body =
    let vloop = mk_single cfg (Def.mk (Assume cond)) in
    let vexit = mk_single cfg (Def.mk (Assume (Bexpr.negate cond))) in
    ignore (mk_seq cfg vloop body);
    ignore (mk_seq cfg body vloop);
    ignore (mk_seq cfg body vexit);
    (fst body, vexit)
end

(** Inserts definition u into cfg directly before v *)
let insert_pre u v cfg =
  let add_edge u v = Cfg.add_edge cfg u v in
  let rem_edge u v = Cfg.remove_edge cfg u v in
    if not (Cfg.mem_vertex cfg u) then
      begin
        Cfg.add_vertex cfg u;
        Cfg.iter_pred (fun x -> rem_edge x v; add_edge x u) cfg v;
        add_edge u v
      end
    else failwith "Cannot insert_pre: vertex already belongs to the CFG!"

(** Inserts definition u into cfg directly after v *)
let insert_succ u v cfg =
  let add_edge u v = Cfg.add_edge cfg u v in
  let rem_edge u v = Cfg.remove_edge cfg u v in
    if not (Cfg.mem_vertex cfg u) then begin
        Cfg.add_vertex cfg u;
        Cfg.iter_succ (fun x -> rem_edge v x; add_edge u x) cfg v;
        add_edge v u
      end
    else failwith "Cannot insert_succ: vertex already belongs to the CFG!"

(** Remove a vertex and create edges between each predecessor and successor *)
let remove_inner_vertex u cfg =
  let add_edge u v = Cfg.add_edge cfg u v in
  let f x = Cfg.iter_succ (add_edge x) cfg u in
    Cfg.iter_pred f cfg u;
    Cfg.remove_vertex cfg u

module Dfs = Graph.Traverse.Dfs(Cfg)
module DfsTree = ExtGraph.DfsTree.Make(Cfg)

let mk_skip () = Def.mk (Assume (Bexpr.ktrue))

let vertex_list cfg = Cfg.fold_vertex (fun v vs -> v::vs) cfg []

module HT = Hashtbl.Make(Def.Set)

let factor_cfg cfg =
  let succs v = Cfg.fold_succ Def.Set.add cfg v Def.Set.empty in
  let succ_ht = HT.create 331 in
  let f v =
    let s = succs v in
    if Def.Set.cardinal s >= 2 then begin
      try HT.replace succ_ht s (v::(HT.find succ_ht s))
      with Not_found -> HT.add succ_ht s [v]
    end
  in
  let factor succs = function
    | [v] -> ()
    | vs ->
      let u = mk_skip () in
      let f v =
	Cfg.iter_succ (Cfg.remove_edge cfg v) cfg v;
	Cfg.add_edge cfg v u
      in
      List.iter f vs;
      Def.Set.iter (fun s -> Cfg.add_edge cfg u s) succs
  in
  let split v = (* insert structural skip vertices *)
    if Cfg.in_degree cfg v > 1 && Cfg.out_degree cfg v > 1
    then insert_succ (mk_skip ()) v cfg
  in
  Cfg.iter_vertex f cfg;
  HT.iter factor succ_ht;
  Cfg.iter_vertex split cfg

(** Normalize a CFG.  This function should be called immediately after
    constructing any CFG.  This function:
    - Removes 2-cycles (required for cycle equivalence testing)
    - Eliminates "boring" (const true/const false/havoc) assume vertices
    - Creates multi-way branches for if-then-elseif...-type constructions
    - Inserts skip vertices in places that are structurally convenient for
      SESE region detection
*)
let normalize_cfg cfg =
  let remove_2cycle u v =
    if Cfg.mem_edge cfg v u then Cfg.subdivide cfg u (mk_skip ()) v
  in
  let normalize_assume def = match def.dkind with
    | Assume c ->
	if Hlir.trivial_cond c then remove_inner_vertex def cfg
	else begin match Bexpr.eval c with
	  | Some true ->
	      if Cfg.in_degree cfg def > 0 then remove_inner_vertex def cfg
	  | Some false -> Cfg.remove_vertex cfg def
	  | None -> ()
	end
    | _ -> ()
  in
  let rec compress u = (* create multi-way branches *)
    if Cfg.mem_vertex cfg u then
      match u.dkind, Cfg.pred cfg u with
	| (Assume uexpr, [v]) -> begin match v.dkind, Cfg.pred cfg v with
	    | (Assume vexpr, [pred]) -> begin
		Cfg.add_edge cfg pred u;
		Cfg.remove_edge cfg v u;
		u.dkind <- Assume (And (vexpr, uexpr));
		if Cfg.out_degree cfg v = 0 then Cfg.remove_vertex cfg v;
		compress u
	      end
	    | (_, _) -> ()
	  end
	| (_, _) -> ()
  in
  let split v = (* insert structural skip vertices *)
    if Cfg.in_degree cfg v > 1 then insert_pre (mk_skip ()) v cfg;
    if Cfg.out_degree cfg v > 1 then insert_succ (mk_skip ()) v cfg
  in
    Cfg.iter_vertex normalize_assume cfg;
    Cfg.iter_vertex compress cfg;
    List.iter split (vertex_list cfg);
    Cfg.iter_edges remove_2cycle cfg

open Cfg

type func = {
  mutable fname : varinfo;
  mutable formals: varinfo list;
  mutable locals: varinfo list;
  mutable cfg: Cfg.t;
  mutable file: file option;
}
and file = {
  mutable filename : string;
  mutable funcs : func list;
  mutable threads : varinfo list;
  mutable entry_points : varinfo list;
  mutable vars : varinfo list;
  mutable types : typ list; (** named types *)
  mutable globinit : func option;
}

let mk_local_varinfo func name typ =
  let var = Varinfo.mk_local name typ in
    func.locals <- var::func.locals;
    var

let mk_global_varinfo file name typ =
  let var = Varinfo.mk_global name typ in
    file.vars <- var::file.vars;
    var

let mk_thread_local_varinfo file name typ =
  let var = Varinfo.mk_thread_local name typ in
    file.vars <- var::file.vars;
    var

let mk_local_var func name typ = Var.mk (mk_local_varinfo func name typ)
let mk_global_var file name typ = Var.mk (mk_global_varinfo file name typ)
let mk_thread_local_var file name typ =
  Var.mk (mk_thread_local_varinfo file name typ)

module FuncMemo = Memo.Make(Varinfo)
let return_var =
  let go func =
    match resolve_type (Varinfo.get_type func) with
      | Func (ret, _) ->
	Varinfo.mk_thread_local ((Varinfo.show func) ^ "$return") ret
      | _ -> failwith ("CfgIr.return_var: argument must be a function-typed"
		       ^ " variable")
  in
    FuncMemo.memo go

let lookup_function name file =
  try List.find (fun f -> Varinfo.equal name f.fname) file.funcs
  with Not_found -> begin
    Log.errorf "Can't find function `%a' in %s"
      Show.format<varinfo> name
      file.filename;
    assert false
  end

let lookup_function_name name file =
  try List.find (fun f -> (Varinfo.show f.fname) = name) file.funcs
  with Not_found -> begin
    Log.errorf "Can't find function `%s' in %s" name file.filename;
    assert false
  end

let defined_function name file =
  List.exists (fun f -> Varinfo.equal name f.fname) file.funcs

let is_local func var = List.exists (Varinfo.equal var) func.locals
let is_formal func var = List.exists (Varinfo.equal var) func.formals

let iter_vars f file =
  let vfunc func =
    List.iter f func.formals;
    List.iter f func.locals;
    f func.fname;
    f (return_var func.fname)
  in
    List.iter vfunc file.funcs;
    List.iter f file.vars;
    match file.globinit with
      | Some func -> vfunc func
      | None -> ()

(** Iterate over every definition of every thread of a file, as well as
    globinit *)
let iter_defs f file =
  let iter_cfg cfg = Cfg.iter_vertex f cfg in
    begin match file.globinit with
      | Some f -> iter_cfg f.cfg
      | None   -> ()
    end;
    List.iter (fun f -> iter_cfg f.cfg) file.funcs

let iter_func_defs f file =
  let iter_func func = Cfg.iter_vertex (f func.fname) func.cfg in
    begin match file.globinit with
      | Some f -> iter_func f
      | None   -> ()
    end;
    List.iter iter_func file.funcs

let iter_entry_points f file =
  let g thread = f (lookup_function thread file) in
    List.iter g file.entry_points

let clone_func func =
  let name = Varinfo.clone func.fname in
    begin match func.file with
      | Some file -> file.vars <- name::file.vars
      | None      -> ()
    end;
    { fname = name;
      formals = func.formals;
      locals = func.locals;
      cfg = Cfg.clone func.cfg;
      file = func.file }

(** Remove the vertices of a CFG that are not reachable from the
    initial vertex. *)
let remove_unreachable cfg start =
  let reachable = ref Def.Set.empty in
  let add_reachable v = reachable := Def.Set.add v (!reachable) in
    Dfs.prefix_component add_reachable cfg start;
    iter_vertex (fun v ->
		   if not (Def.Set.mem v (!reachable))
		   then (remove_vertex cfg v;
			 match v.dkind with
			   | Assert _ -> Report.log_safe_unreachable ()
			   | _ -> ()))
      cfg

(** Given a CFG {!g} and vertex {!v}, extract the sub-CFG with initial
    vertex {!v} consisting of all vertices of {!g} reachable from
    {!v}. *)
let extract_cfg cfg start =
  let extract = create () in
  let extract_vertex = add_vertex extract in
  let extract_edge e =
    if (mem_vertex extract (E.src e)) && (mem_vertex extract (E.dst e))
    then add_edge_e extract e
  in
    Dfs.prefix_component extract_vertex cfg start;
    iter_edges_e extract_edge cfg;
    extract

let extract_thread func name start =
  { fname = name;
    formals = [];
    locals = func.locals @ func.formals;
    cfg = extract_cfg func.cfg start;
    file = func.file }

let cfg_equal g h =
  (Cfg.nb_vertex g = Cfg.nb_vertex h)
  && (Cfg.nb_edges g = Cfg.nb_edges h)
  && (Cfg.fold_edges_e (fun e a -> a && (Cfg.mem_edge_e h e)) g true)

module DefPairHT = Hashtbl.Make(
  struct
    type t = def * def
    let equal (a,b) (c,d) = (Def.equal a c) && (Def.equal b d)
    let hash (a,b) = (a.did) + 10000*(b.did)
  end)
  
(** A reference to the current file.  This reference should be set as early as
    (in parseFile).  This will be deprecated once we start supporting projects
    with more than one file. *)
let gfile : file option ref = ref None

(** Retrieve the current file.  This will be deprecated once we start
    supporting projects with more than one file. *)
let get_gfile () = match !gfile with
  | Some file -> file
  | None      -> failwith "CfgIr.get_gfile: gfile not set!"

(** Rewrite a file by applying sub_expr to every expression, sub_bexpr to
    every boolean expression, and sub_ap to every access path that occurs in
    any definition of any thread or globinit *)
let rewrite sub_expr sub_bexpr sub_ap sub_var file =
  let sub_builtin = function
    | Alloc (lhs, expr, loc) -> Alloc (sub_var lhs, sub_expr expr, loc)
    | Free expr -> Free (sub_expr expr)
    | Fork (Some lhs, func, args) ->
	Fork (Some (sub_var lhs), sub_expr func, List.map sub_expr args)
    | Fork (None, func, args) ->
	Fork (None, sub_expr func, List.map sub_expr args)
    | Acquire expr -> Acquire (sub_expr expr)
    | Release expr -> Release (sub_expr expr)
    | AtomicBegin -> AtomicBegin
    | AtomicEnd -> AtomicEnd
    | Exit -> Exit
  in
  let sub_def d =
    let dk =
      match d.dkind with
	| Store (ap, expr) -> Store (sub_ap ap, sub_expr expr)
	| Assign (var, expr) -> Assign (sub_var var, sub_expr expr)
	| Call (Some lhs, func, args) ->
	    Call (Some (sub_var lhs), sub_expr func, List.map sub_expr args)
	| Call (None, func, args) ->
	    Call (None, sub_expr func, List.map sub_expr args)
	| Assume expr -> Assume (sub_bexpr expr)
	| Initial -> Initial
	| Assert (expr, msg) -> Assert (sub_bexpr expr, msg)
	| AssertMemSafe (expr, msg) -> AssertMemSafe (sub_expr expr, msg)
	| Return (Some expr) -> Return (Some (sub_expr expr))
	| Return None -> Return None
	| Builtin x -> Builtin (sub_builtin x)
    in
      d.dkind <- dk
  in
    iter_defs sub_def file

let normalize file =
  let normalize_func func =
    let str_const_rhs def = match def.dkind with
      | Store (lhs, rhs) ->
	begin match Expr.strip_casts rhs with
	| Constant (CString _) ->
	  let tmp =
	    mk_local_var func
	      "duet_str_const"
	      (Concrete (Pointer (Concrete (Int char_width))))
	  in
	  let tmp_assign =
	    Def.mk ~loc:(Def.get_location def) (Assign (tmp, rhs))
	  in
	  def.dkind <- begin match rhs with
	  | Constant _ -> Store (lhs, AccessPath (Variable tmp))
	  | Cast (typ, _) -> Store (lhs, Cast (typ, AccessPath (Variable tmp)))
	  | _ -> assert false
	  end;
	  insert_pre tmp_assign def func.cfg
	| _ -> ()
	end
      | _ -> ()
    in
    remove_unreachable func.cfg (Cfg.initial_vertex func.cfg);
    factor_cfg func.cfg;
    Cfg.iter_vertex str_const_rhs func.cfg
  in
  List.iter normalize_func file.funcs

(******************************************************************************)
(* Translation from AST IR *)

(* Construct control flow graphs for a function.  Returns a pair
   {!(cfg,threads)} consisting of the CFG for the function and a list of
   threads whose spawn points reside in the function. *)
let from_func_ast file func_ast =
  let cfg = create ~size:32 () in
  let func = { fname = func_ast.Ast.fname;
	       formals = func_ast.Ast.formals;
	       locals = func_ast.Ast.locals;
	       cfg = cfg;
	       file = None }
  in
  let threads = ref [] in
  let max_thread = ref 0 in
  let add_thread stmt =
    let thread_id = string_of_int (!max_thread) in
    let thread_name = (Varinfo.show func.fname) ^ "$fork" ^ thread_id in
    let thread_var =
      Varinfo.mk_global thread_name (Concrete (Func (Concrete Void, [])))
    in
      incr max_thread;
      threads := (stmt, thread_var)::(!threads);
      thread_var
  in
  let fork_lookup =
    Memo.memo (fun stmt ->
		 match stmt_kind stmt with
		   | ForkGoto tgt ->
		       let thread_name = add_thread (lookup_stmt file tgt) in
		       let fork =
			 Expr.addr_of (Variable (Var.mk thread_name))
		       in
			 Def.mk (Builtin (Fork (None, fork, [])))
		   | _ -> failwith "add_fork: Not a fork!")
  in
  let stmt_cfg = Ast.construct_cfg file func_ast in
  let rec initial_defs_impl reached stmt =
    if StmtSet.mem stmt (!reached) then [] else begin
      reached := StmtSet.add stmt !reached;
      match stmt_kind stmt with
	| Instr (x::xs) -> [x]
	| ForkGoto _ -> [fork_lookup stmt]
	| _ -> next_defs_impl reached stmt
    end
  and next_defs_impl reached stmt =
    StmtCfg.fold_succ
      (fun v ds -> (initial_defs_impl reached v)@ds)
      stmt_cfg
      stmt
      []
  in
  let next_defs stmt = next_defs_impl (ref StmtSet.empty) stmt in
  let initial_defs stmt = initial_defs_impl (ref StmtSet.empty) stmt in

  (* Return the vertex of a definition. If one doesn't exist, then
     create one *)
  let get_node =
    DefMemo.memo (fun def -> let v = V.create def in add_vertex cfg v; v)
  in
  let process_stmt stmt =
    match stmt_kind stmt with
      | Instr (d::ds as defs) ->
	let enum = Putil.adjacent_pairs (BatList.enum defs) in
	BatEnum.iter (fun (x,y) -> Cfg.add_edge cfg x y) enum;
	List.iter (Cfg.add_edge cfg (BatList.last defs)) (next_defs stmt)
      | ForkGoto _ ->
	    List.iter (Cfg.add_edge cfg (fork_lookup stmt)) (next_defs stmt)
      | _ -> ()
  in
  let handle_return v = match v.dkind with
    | Return _ -> iter_succ_e (remove_edge_e cfg) cfg v
    | _ -> ()
  in
  let create_thread (stmt, name) =
    let initial_def = Def.mk (Assume Bexpr.ktrue) in
      List.iter (Cfg.add_edge cfg initial_def) (initial_defs stmt);
      let func = extract_thread func name (get_node initial_def) in
	normalize_cfg func.cfg;
	if !Log.debug_mode then sanity_check func.cfg;
	func
  in
  let init = Def.mk (Assume Bexpr.ktrue) in
    Cfg.add_vertex cfg init;
    StmtCfg.iter_vertex process_stmt stmt_cfg;
    List.iter (add_edge cfg init) (initial_defs (List.hd func_ast.Ast.body));
    iter_vertex handle_return cfg;
    let threads = List.map create_thread (!threads) in
      (* this should be uncommented if there is thread creation *)
(*      remove_unreachable cfg (get_node init); *)
      normalize_cfg cfg;
      remove_unreachable cfg (get_node init);
      List.iter
	(fun t -> normalize_cfg t.cfg)
	threads;
      if !Log.debug_mode then sanity_check cfg;
      (func, threads)

let from_file_ast file =
  (* todo: merge globinit with init, if it exists *)
  let (init, funcs) =
    if !whole_program then (None, file.Ast.funcs)
    else begin
      let is_init f = (Varinfo.show f.Ast.fname) = "init" in
	match List.partition is_init file.Ast.funcs with
	  | ([init], funcs) ->
	      let (f,_) = from_func_ast file init in (Some f, funcs)
	  | _               -> (None, file.Ast.funcs)
    end
  in
  let (funcs, threads) =
    List.fold_left (fun (fs,ts) func ->
		      let (f, ts2) = from_func_ast file func in
			(f::fs,ts2@ts))
      ([],[])
      funcs
  in
  let find_fun name =
    try List.find (fun f -> (Varinfo.show f.fname) = name) funcs
    with Not_found -> failwith ("CfgIr.find_fun " ^ name)
  in
  let (entry_points, threads) =
    if !whole_program then begin
      let main_thread =
	try find_fun "main"
	with Not_found ->
	  failwith "Main function required for whole program analysis"
      in
	([main_thread], main_thread::threads)
    end else (funcs, funcs @ threads)
  in
  let file = { filename = file.Ast.filename;
	       funcs = funcs@threads;
	       threads = List.map (fun x -> x.fname) threads;
	       entry_points = List.map (fun x -> x.fname) entry_points;
	       vars = file.Ast.vars;
	       types = file.Ast.types;
	       globinit = init;
	     }
  in
  let set_file func = func.file <- Some file in
  List.iter set_file file.funcs;
  normalize file;
  file

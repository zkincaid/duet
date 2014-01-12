(*pp camlp4find deriving.syntax *)
open Core
open Apak
open Ark
open CfgIr
open BatPervasives
open ArkPervasives

module RG = Interproc.RG
module G = RG.G

(* Decorate the program with numerical invariants *)

module MakeDecorator(M : sig
  type t
  val manager_alloc : unit -> t Apron.Manager.t
end) = struct

  module ApronI =
    Ai.ApronInterpretation
  module I = Ai.IExtra(ApronI)

  module SCCG = Loop.SccGraph(G)
  let enum_loop_headers rg = SCCG.enum_headers (SCCG.construct rg)

  module NA = struct
    type absval = I.t
    type st = unit
    module G = Interproc.RG.G
    let transfer _ flow_in def =
      match def.dkind with
      | Call (None, AddrOf (Variable (func, OffsetFixed 0)), []) ->
	if CfgIr.defined_function func (CfgIr.get_gfile()) then
	(* Havoc the global variables *)
	  let open ApronI in
	  let global_aps =
	    Env.fold
	      (fun ap _ aps ->
		if AP.is_global ap then AP.Set.add ap aps else aps)
	      flow_in.env
	      AP.Set.empty
	  in
	  I.cyl flow_in global_aps
	else flow_in (* Treat undefined functions as no-ops *)
      | _ -> I.transfer def (I.inject flow_in (Def.get_uses def))
    let flow_in _ graph val_map v =
      let add_pred v value = I.join (val_map v) value in
      G.fold_pred add_pred graph v (I.bottom AP.Set.empty)
    let join _ _ x y =
      let newv = I.join x y in
      if I.equal x newv then None else Some newv
    let widen =
      let f _ _ old_val new_val =
	let wide_val = I.widen old_val new_val in
	if I.equal old_val wide_val then None else Some wide_val
      in
      Some f
    let name = "Numerical analysis"
    let format_vertex = Def.format
    let format_absval = I.format
  end
  module NumAnalysis = Solve.Mk(NA)

  let decorate rg =
    let decorate_block block body =
      let result = NumAnalysis.empty_result () body in
      let entry = RG.block_entry rg block in
      NumAnalysis.init_result result body (fun d ->
	if Def.equal entry d
	then I.top AP.Set.empty
	else I.bottom AP.Set.empty);
      NumAnalysis.solve result (G.fold_vertex (fun x xs -> x::xs) body []);
      let f body v =
	let value = NumAnalysis.output result v in
	let bexpr = ApronI.bexpr_of_av value in
	let def = Def.mk (Assume bexpr) in
	G.split body v ~pred:v ~succ:def
      in
      BatEnum.fold f body (enum_loop_headers body)
    in
    RG.map decorate_block rg
end

type abstract_domain = Box | Octagon | Polyhedron
let default_domain = ref Box

let decorate rg =
  match !default_domain with
  | Box ->
    let module D = MakeDecorator(Box) in
    D.decorate rg
  | Octagon ->
    let module D = MakeDecorator(Oct) in
    D.decorate rg
  | Polyhedron ->
    let module D = MakeDecorator(struct
      type t = Polka.loose Polka.t
      let manager_alloc = Polka.manager_alloc_loose
    end) in
    D.decorate rg

let tr_typ typ = match resolve_type typ with
  | Int _   -> TyInt
  | Float _ -> TyReal
  | Pointer _ -> TyInt
  | Enum _ -> TyInt
  | Array _ -> TyInt
  | Dynamic -> TyReal
  | _ -> assert false

module V = struct
  include Var
  let prime var = subscript var 1
  module E = Enumeration.Make(Var)
  let enum = E.empty ()
  let of_smt sym = match Smt.symbol_refine sym with
    | Z3.Symbol_int id -> E.from_int enum id
    | Z3.Symbol_string _ -> assert false
  let typ v = tr_typ (Var.get_type v)
  let to_smt v =
    let ctx = Smt.get_context () in
    let id = E.to_int enum v in
    match typ v with
    | TyInt ->
      Z3.mk_const ctx (Z3.mk_int_symbol ctx id) (Smt.mk_int_sort ())
    | TyReal ->
      Z3.mk_const ctx (Z3.mk_int_symbol ctx id) (Smt.mk_real_sort ())
  let tag = E.to_int enum
end

module K = struct
  include Transition.Make(V)
(*
  let simplify tr =
    Log.logf Log.info
      "Simplifying formula: %d atoms, %d size, %d max dnf, %d program, %d tmp"
      (F.nb_atoms tr.guard)
      (F.size tr.guard)
      (F.dnf_size tr.guard)
      (VarSet.cardinal (formula_free_program_vars tr.guard))
      (VSet.cardinal (formula_free_tmp_vars tr.guard));
    let simplified = simplify tr in
    Log.logf Log.info
      "Simplified:          %d atoms, %d size, %d max dnf, %d program, %d tmp"
      (F.nb_atoms simplified.guard)
      (F.size simplified.guard)
      (F.dnf_size simplified.guard)
      (VarSet.cardinal (formula_free_program_vars simplified.guard))
      (VSet.cardinal (formula_free_tmp_vars simplified.guard));
    simplified
*)
(*
  let mul x y = simplify (mul x y)
  let add x y = simplify (add x y)
  let exists p tr = simplify (exists p tr)
*)
end
module A = Interproc.MakePathExpr(K)

let _ =
  let open K in
  opt_higher_recurrence := true;
  opt_disjunctive_recurrence_eq := true;
  opt_recurrence_ineq := false;
  opt_higher_recurrence_ineq := false;
  opt_unroll_loop := false;
  opt_loop_guard := true;
  F.opt_simplify_strategy := []

let prime_bexpr = Bexpr.subst_var V.prime

let tr_expr expr =
  let open K in
  let alg = function
    | OHavoc typ -> T.var (V.mk_tmp "havoc" (tr_typ typ))
    | OConstant (CInt (k, _)) -> T.int (ZZ.of_int k)
    | OConstant (CFloat (k, _)) -> T.const (QQ.of_float k)
    | OCast (_, expr) -> expr
    | OBinaryOp (a, Add, b, _) -> T.add a b
    | OBinaryOp (a, Minus, b, _) -> T.sub a b
    | OBinaryOp (a, Mult, b, _) -> T.mul a b
    | OBinaryOp (a, Div, b, _) -> T.div a b
    | OUnaryOp (Neg, a, _) -> T.neg a
    | OAccessPath (Variable v) -> T.var (V.mk_var v)

    (* No real translations for anything else -- just return a free var "tr"
       (which just acts like a havoc). *)
    | OBinaryOp (_, _, _, typ) -> T.var (V.mk_tmp "tr" (tr_typ typ))
    | OUnaryOp (_, _, typ) -> T.var (V.mk_tmp "tr" (tr_typ typ))
    | OAddrOf _ -> T.var (V.mk_int_tmp "tr")
    | OBoolExpr _ -> T.var (V.mk_int_tmp "tr")
    | OAccessPath ap -> T.var (V.mk_tmp "tr" (tr_typ (AP.get_type ap)))
    | OConstant _ -> T.var (V.mk_int_tmp "tr")
  in
  Expr.fold alg expr

let tr_bexpr bexpr =
  let open K in
  let alg = function
    | Core.OAnd (a, b) -> F.conj a b
    | Core.OOr (a, b) -> F.disj a b
    | Core.OAtom (pred, x, y) ->
      let x = tr_expr x in
      let y = tr_expr y in
      begin
	match pred with
	| Lt -> F.lt x y
	| Le -> F.leq x y
	| Eq -> F.eq x y
	| Ne -> F.disj (F.lt x y) (F.gt x y)
      end
  in
  Bexpr.fold alg bexpr

let weight def =
  let open K in
  match def.dkind with
  | Assume phi | Assert (phi, _) -> K.assume (tr_bexpr phi)
  | Assign (lhs, rhs) -> K.assign lhs (tr_expr rhs)
  | Return None -> one
  | _ ->
    Log.errorf "No translation for definition: %a" Def.format def;
    assert false


let analyze file =
  match file.entry_points with
  | [main] -> begin
    (*    let rg = decorate (Interproc.make_recgraph file) in*)
    let rg = Interproc.make_recgraph file in
    let local func_name =
      let func = lookup_function func_name (get_gfile()) in
      let vars =
	Varinfo.Set.remove (return_var func_name)
	  (Varinfo.Set.of_enum
	     (BatEnum.append
		(BatList.enum func.formals)
		(BatList.enum func.locals)))
      in
      Log.logf Log.info "Locals for %a: %a"
	Varinfo.format func_name
	Varinfo.Set.format vars;
      fun (x,_) -> (Varinfo.Set.mem x vars)
    in
    let query = A.mk_query rg weight local main in
    let is_assert def = match def.dkind with
      | Assert (_, _) -> true
      | _             -> false
    in
    let s = new Smt.solver in
    let check_assert def path = match def.dkind with
      | Assert (phi, msg) -> begin
	s#push ();
	s#assrt (K.to_smt path);

	let phi = tr_bexpr phi in
	let sigma v = match K.V.lower v with
	  | None -> K.T.var v
	  | Some v ->
	    try K.M.find v path.K.transform
	    with Not_found -> K.T.var (K.V.mk_var v)
	in
	let phi = K.F.subst sigma phi in
	s#assrt (Smt.mk_not (K.F.to_smt phi));
	begin match Log.time "smt" s#check () with
	| Smt.Unsat -> Report.log_safe ()
	| Smt.Sat | Smt.Undef -> Report.log_error (Def.get_location def) msg
	end;
	s#pop ()
      end
      | _ -> ()
    in
    A.single_src_restrict query is_assert check_assert;
    Report.print_errors ();
    Report.print_safe ();
    if !CmdLine.show_stats then begin
      K.T.log_stats ();
      K.F.log_stats ()
    end
  end
  | _ -> assert false

let _ =
  CmdLine.register_pass
    ("-lra", analyze, " Linear recurrence analysis")

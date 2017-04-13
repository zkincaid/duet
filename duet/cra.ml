open Core
open Apak
open Ark
open CfgIr
open BatPervasives
open Pathexp

module RG = Interproc.RG
module G = RG.G
module Ctx = Syntax.MakeSimplifyingContext ()
let ark = Ctx.context

include Log.Make(struct let name = "cra" end)

let forward_inv_gen = ref false
let use_ocrs = ref false
let split_loops = ref false
let dump_goals = ref false
let nb_goals = ref 0

let dump_goal loc path_condition =
  if !dump_goals then begin
    let filename =
      Format.sprintf "%s%d-line%d.smt2"
        (Filename.chop_extension (Filename.basename loc.Cil.file))
        (!nb_goals)
        loc.Cil.line
    in
    let chan = Pervasives.open_out filename in
    let formatter = Format.formatter_of_out_channel chan in
    logf ~level:`always "Writing goal formula to %s" filename;
    Syntax.pp_smtlib2 ark formatter path_condition;
    Format.pp_print_newline formatter ();
    Pervasives.close_out chan;
    incr nb_goals
  end

let _ =
  CmdLine.register_config
    ("-cra-forward-inv",
     Arg.Set forward_inv_gen,
     " Forward invariant generation");
  CmdLine.register_config
    ("-cra-split-loops",
     Arg.Set split_loops,
     " Turn on loop splitting");
  CmdLine.register_config
    ("-use-ocrs",
     Arg.Set use_ocrs,
     " Use OCRS for recurrence solving");
  CmdLine.register_config
    ("-dump-goals",
     Arg.Set dump_goals,
     " Output goal assertions in SMTLIB2 format")

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
    let nonvariable = function
      | Variable _ -> false
      | Deref _ -> true
    let safe_cyl av aps = I.cyl (I.inject av aps) aps
    let transfer _ flow_in def =
(*
      Log.logf 0 "Transfer: %a" Def.format def;
      let flow_in_i = I.inject flow_in (Def.get_uses def) in
      Log.logf 0 "Input: %a" I.format flow_in_i;
*)
      let res = 
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
        | Assign (var, expr) ->
          begin
            match resolve_type (Var.get_type var) with
            | Int _ | Pointer _ | Dynamic ->
              if AP.Set.exists nonvariable (Expr.get_uses expr)
              then safe_cyl flow_in (AP.Set.singleton (Variable var))
              else I.transfer def (I.inject flow_in (Def.get_uses def))
            | _ -> flow_in
          end
        | Store (lhs, _) ->
          (* Havoc all the variables lhs could point to *)
          let open PointerAnalysis in
          let add_target memloc set = match memloc with
            | (MAddr v, offset) -> AP.Set.add (Variable (v, offset)) set
            | _, _ -> set
          in
          let vars = MemLoc.Set.fold add_target (resolve_ap lhs) AP.Set.empty in
          safe_cyl flow_in vars
        | Assume bexpr | Assert (bexpr, _) ->
          if AP.Set.exists nonvariable (Bexpr.get_uses bexpr)
          then flow_in
          else I.transfer def (I.inject flow_in (Def.get_uses def))
        | Builtin (Alloc (v, _, _)) ->
          safe_cyl flow_in (AP.Set.singleton (Variable v))
        | Initial -> I.transfer def flow_in
        | _ -> flow_in
      in
      res
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
    let pp_vertex = Def.pp
    let pp_absval = I.pp
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
  | Int _   -> `TyInt
  | Float _ -> `TyReal
  | Pointer _ -> `TyInt
  | Enum _ -> `TyInt
  | Array _ -> `TyInt
  | Dynamic ->
    (* TODO : we should conservatively translate Dynamic as a real, but SMT
       solvers struggled with the resulting mixed int/real constraints.  To
       make this sound we should do a type analysis to determine when a
       dynamic type can be narrowed to an int.  The main place this comes up
       is in formal parameters, which are typed dynamic to make indirect calls
       easier to handle. *)
    `TyInt
  | _ -> `TyInt

type value =
  | VVal of Var.t
  | VPos of Var.t
  | VWidth of Var.t
    [@@deriving ord]

module Value = struct
  type t = value
  let hash = function
    | VVal v -> Hashtbl.hash (0, Var.hash v)
    | VPos v -> Hashtbl.hash (1, Var.hash v)
    | VWidth v -> Hashtbl.hash (2, Var.hash v)
  let equal x y = compare_value x y = 0
end
module ValueHT = Hashtbl.Make(Value)

let var_of_value = function
  | VVal v | VPos v | VWidth v -> v
let map_value f = function
  | VVal v -> VVal (f v)
  | VPos v -> VPos (f v)
  | VWidth v -> VWidth (f v)

module V = struct

  module I = struct
    type t = value [@@deriving ord]
    let pp formatter = function
      | VVal v -> Var.pp formatter v
      | VWidth v -> Format.fprintf formatter "%a@@width" Var.pp v
      | VPos v -> Format.fprintf formatter "%a@@pos" Var.pp v
    let show = Putil.mk_show pp
    let equal x y = compare x y = 0
    let hash = function
      | VVal v -> Hashtbl.hash (Var.hash v, 0)
      | VPos v -> Hashtbl.hash (Var.hash v, 1)
      | VWidth v -> Hashtbl.hash (Var.hash v, 2)
  end
  include I

  let sym_to_var = Hashtbl.create 991
  let var_to_sym = ValueHT.create 991

  let typ v = tr_typ (Var.get_type (var_of_value v))

  let symbol_of var =
    if ValueHT.mem var_to_sym var then
      ValueHT.find var_to_sym var
    else begin
      let sym = Ctx.mk_symbol ~name:(show var) (typ var) in
      ValueHT.add var_to_sym var sym;
      Hashtbl.add sym_to_var sym var;
      sym
    end

  let of_symbol sym =
    if Hashtbl.mem sym_to_var sym then
      Some (Hashtbl.find sym_to_var sym)
    else
      None
end

module K = struct
  include Transition.Make(Ctx)(V)

  let star x =
    Log.time "cra:star"
      (star ~split:(!split_loops) ~use_ocrs:(!use_ocrs))
      x

  let add x y =
    if is_zero x then y
    else if is_zero y then x
    else add x y

  let mul x y =
    if is_zero x || is_zero y then zero
    else if is_one x then y
    else if is_one y then x
    else mul x y
end
module A = Interproc.MakePathExpr(K)

type ptr_term =
  { ptr_val : Ctx.term;
    ptr_pos : Ctx.term;
    ptr_width : Ctx.term }

type term =
  | TInt of Ctx.term
  | TPointer of ptr_term

let int_binop op left right =
  match op with
  | Add -> Ctx.mk_add [left; right]
  | Minus -> Ctx.mk_sub left right
  | Mult -> Ctx.mk_mul [left; right]
  | Div -> Ctx.mk_idiv left right
  | Mod -> Ctx.mk_mod left right
  | _ -> Ctx.mk_const (Ctx.mk_symbol ~name:"havoc" `TyInt)

let term_binop op left right = match left, op, right with
  | (TInt left, op, TInt right) ->
    TInt (int_binop op left right)
  | (TPointer ptr, Add, TInt offset)
  | (TInt offset, Add, TPointer ptr) ->
    let p =
      { ptr_val = int_binop Add ptr.ptr_val offset;
        ptr_pos = int_binop Add ptr.ptr_pos offset;
        ptr_width = ptr.ptr_width }
    in
    TPointer p
  | (TPointer ptr, Minus, TInt offset) ->
    let p =
      { ptr_val = int_binop Minus ptr.ptr_val offset;
        ptr_pos = int_binop Minus ptr.ptr_pos offset;
        ptr_width = ptr.ptr_width }
    in
    TPointer p
  | (TInt offset, Minus, TPointer ptr) ->
    let p =
      { ptr_val = int_binop Minus offset ptr.ptr_val;
        ptr_pos = int_binop Minus offset ptr.ptr_pos;
        ptr_width = ptr.ptr_width }
    in
    TPointer p
  | (TPointer left, op, TInt right) ->
    TInt (int_binop op left.ptr_val right)
  | (TInt left, op, TPointer right) ->
    TInt (int_binop op left right.ptr_val)
  | (TPointer left, op, TPointer right) ->
    TInt (int_binop op left.ptr_val right.ptr_val)

let typ_has_offsets typ = is_pointer_type typ || typ = Concrete Dynamic

let nondet_const name typ = Ctx.mk_const (Ctx.mk_symbol ~name typ)

let tr_expr expr =
  let alg = function
    | OHavoc typ -> TInt (nondet_const "havoc" (tr_typ typ))
    | OConstant (CInt (k, _)) -> TInt (Ctx.mk_real (QQ.of_int k))
    | OConstant (CFloat (k, _)) -> TInt (Ctx.mk_real (QQ.of_float k))
    | OCast (_, expr) -> expr
    | OBinaryOp (a, op, b, _) -> term_binop op a b

    | OUnaryOp (Neg, TInt a, _) -> TInt (Ctx.mk_neg a)
    | OUnaryOp (Neg, TPointer a, _) -> TInt (Ctx.mk_neg a.ptr_val)
    | OAccessPath (Variable v) ->
      if typ_has_offsets (Var.get_type v) then
        TPointer { ptr_val = Ctx.mk_const (V.symbol_of (VVal v));
                   ptr_width = Ctx.mk_const (V.symbol_of (VWidth v));
                   ptr_pos = Ctx.mk_const (V.symbol_of (VPos v)) }
      else TInt (Ctx.mk_const (V.symbol_of (VVal v)))

    | OAddrOf _ ->
      (* Todo: width and pos aren't correct. *)
      TPointer { ptr_val = nondet_const "tr" `TyInt;
                 ptr_width = Ctx.mk_real QQ.one;
                 ptr_pos = Ctx.mk_real QQ.zero }

    (* No real translations for anything else -- just return a free var "tr"
       (which just acts like a havoc). *)
    | OUnaryOp (_, _, typ) -> TInt (nondet_const "tr" (tr_typ typ))
    | OBoolExpr _ -> TInt (nondet_const "tr" `TyInt)
    | OAccessPath ap -> TInt (nondet_const "tr" (tr_typ (AP.get_type ap)))
    | OConstant _ -> TInt (nondet_const "tr" `TyInt)
  in
  Expr.fold alg expr

let tr_expr_val expr = match tr_expr expr with
  | TInt x -> x
  | TPointer x -> x.ptr_val

let tr_bexpr bexpr =
  let alg = function
    | Core.OAnd (a, b) -> Ctx.mk_and [a; b]
    | Core.OOr (a, b) -> Ctx.mk_or [a; b]
    | Core.OAtom (pred, x, y) ->
      let x = tr_expr_val x in
      let y = tr_expr_val y in
      begin
        match pred with
        | Lt -> Ctx.mk_lt x y
        | Le -> Ctx.mk_leq x y
        | Eq -> Ctx.mk_eq x y
        | Ne -> Ctx.mk_not (Ctx.mk_eq x y)
      end
  in
  Bexpr.fold alg bexpr


let weight def =
  let open K in
  match def.dkind with
  | Assume phi -> K.assume (tr_bexpr phi)
  | Assign (lhs, rhs) ->
    if typ_has_offsets (Var.get_type lhs) then begin
      match tr_expr rhs with
      | TPointer rhs ->
        BatList.reduce K.mul [
          K.assign (VVal lhs) rhs.ptr_val;
          K.assign (VPos lhs) rhs.ptr_pos;
          K.assign (VWidth lhs) rhs.ptr_width;
        ]
      | TInt tint -> begin
          (match Var.get_type lhs, rhs with
           | (_, Havoc _) | (Concrete Dynamic, _) -> ()
           | _ -> Log.errorf "Ill-typed pointer assignment: %a" Def.pp def);
          BatList.reduce K.mul [
            K.assign (VVal lhs) tint;
            K.assign (VPos lhs) (nondet_const "type_err" `TyInt);
            K.assign (VWidth lhs) (nondet_const "type_err" `TyInt)
          ]
        end
    end else K.assign (VVal lhs) (tr_expr_val rhs)
  | Store (lhs, _) ->
    (* Havoc all the variables lhs could point to *)
    let open PointerAnalysis in
    let add_target memloc tr = match memloc with
      | (MAddr v, offset) ->
        if typ_has_offsets (Var.get_type (v,offset)) then begin
          BatList.reduce K.mul [
            tr;
            K.assign (VVal (v,offset)) (nondet_const "store" `TyInt);
            K.assign (VPos (v,offset)) (nondet_const "store" `TyInt);
            K.assign (VWidth (v,offset)) (nondet_const "store" `TyInt)
          ]
        end else begin
          K.mul tr (K.assign (VVal (v,offset)) (nondet_const "store" `TyInt))
        end
      | _, _ -> tr
    in
    MemLoc.Set.fold add_target (resolve_ap lhs) one
  | Builtin Exit -> zero
  | Builtin (Alloc (v, size, _)) ->
    BatList.reduce K.mul [
      K.assign (VVal v) (nondet_const "alloc" `TyInt);
      K.assign (VWidth v) (tr_expr_val size);
      K.assign (VPos v) (Ctx.mk_real QQ.zero)
    ]
  | Builtin AtomicBegin | Builtin AtomicEnd
  | Builtin (Acquire _) | Builtin (Release _)
  | Builtin (Free _)
  | Initial | Assert (_, _) | AssertMemSafe (_, _) | Return None
  | Builtin (PrintBounds _) -> one
  | _ ->
    Log.errorf "No translation for definition: %a" Def.pp def;
    assert false

let analyze file =
  match file.entry_points with
  | [main] -> begin
      let rg = Interproc.make_recgraph file in
      let rg =
        if !forward_inv_gen
        then Log.phase "Forward invariant generation" decorate rg
        else rg
      in
(*
      BatEnum.iter (Interproc.RGD.display % snd) (RG.bodies rg);
*)
      let local _ v = not (Var.is_global (var_of_value v)) in
      let query = A.mk_query rg weight local main in
      let is_assert def = match def.dkind with
        | Assert (_, _) | AssertMemSafe _ -> true
        | _             -> false
      in
      let check_assert def path =
        match def.dkind with
        | AssertMemSafe (expr, msg) -> begin
            match tr_expr expr with
            | TInt _ ->
              Report.log_error (Def.get_location def) "Memory safety (type error)"
            | TPointer p ->
              begin
                let sigma sym =
                  match V.of_symbol sym with
                  | Some v when K.mem_transform v path ->
                    K.get_transform v path
                  | _ -> Ctx.mk_const sym
                in
                let phi =
                  Ctx.mk_and [
                    Ctx.mk_leq (Ctx.mk_real QQ.zero) p.ptr_pos;
                    Ctx.mk_lt p.ptr_pos p.ptr_width
                  ]
                in
                let phi = Syntax.substitute_const Ctx.context sigma phi in

                let path_condition =
                  Ctx.mk_and [K.guard path; Ctx.mk_not phi]
                  |> ArkSimplify.simplify_terms ark
                in
                dump_goal (Def.get_location def) path_condition;
                match Abstract.is_sat Ctx.context path_condition with
                | `Sat -> Report.log_error (Def.get_location def) msg
                | `Unsat -> Report.log_safe ()
                | `Unknown ->
                  logf ~level:`warn "Z3 inconclusive";
                  Report.log_error (Def.get_location def) msg
              end
          end
        | Assert (phi, msg) -> begin
            let phi = tr_bexpr phi in
            let sigma sym =
              match V.of_symbol sym with
              | Some v when K.mem_transform v path ->
                K.get_transform v path
              | _ -> Ctx.mk_const sym
            in
            let phi = Syntax.substitute_const Ctx.context sigma phi in
            let path_condition =
              Ctx.mk_and [K.guard path; Ctx.mk_not phi]
              |> ArkSimplify.simplify_terms ark
            in
            logf "Path condition:@\n%a" (Syntax.pp_smtlib2 Ctx.context) path_condition;
            dump_goal (Def.get_location def) path_condition;
            begin match Abstract.is_sat Ctx.context path_condition with
              | `Sat -> Report.log_error (Def.get_location def) msg
              | `Unsat -> Report.log_safe ()
              | `Unknown ->
                logf ~level:`warn "Z3 inconclusive";
                Report.log_error (Def.get_location def) msg
            end
          end
        | _ -> ()
      in
      A.single_src_restrict query is_assert check_assert;
      Report.print_errors ();
      Report.print_safe ();
    end
  | _ -> assert false

let resource_bound_analysis file =
  match file.entry_points with
  | [main] -> begin
      let rg = Interproc.make_recgraph file in
      let rg =
        if !forward_inv_gen
        then Log.phase "Forward invariant generation" decorate rg
        else rg
      in

      let local _ v = not (Var.is_global (var_of_value v)) in
      let query = A.mk_query rg weight local main in
      let cost =
        let open CfgIr in
        let file = get_gfile () in
        let is_cost v = (Varinfo.show v) = "__cost" in
        try
          VVal (Var.mk (List.find is_cost file.vars))
        with Not_found ->
          Log.fatalf "Could not find __cost variable"
      in
      let cost_symbol = V.symbol_of cost in
      let exists x =
        match V.of_symbol x with
        | Some v -> Var.is_global (var_of_value v)
        | None -> false
      in

      A.HT.iter (fun procedure summary ->
          if K.mem_transform cost summary then begin
            logf ~level:`always "Procedure: %a" Varinfo.pp procedure;
            (* replace cost with 0, add constraint cost = rhs *)
            let guard =
              let subst x =
                if x = cost_symbol then
                  Ctx.mk_real QQ.zero
                else
                  Ctx.mk_const x
              in
              let rhs =
                Syntax.substitute_const ark subst (K.get_transform cost summary)
              in
              Ctx.mk_and [Syntax.substitute_const ark subst (K.guard summary);
                          Ctx.mk_eq (Ctx.mk_const cost_symbol) rhs ]
            in
            let (lower, upper) =
              Abstract.symbolic_bounds ~exists ark guard cost_symbol
            in
            begin match lower with
              | Some lower ->
                logf ~level:`always "%a <= cost" (Syntax.Term.pp ark) lower
              | None -> ()
            end;
            begin match upper with
              | Some upper ->
                logf ~level:`always "cost <= %a" (Syntax.Term.pp ark) upper
              | None -> ()
            end
          end else
            logf ~level:`always "Procedure %a has zero cost" Varinfo.pp procedure)
        (A.get_summaries query)
    end
  | _ -> assert false

let _ =
  CmdLine.register_pass
    ("-cra", analyze, " Compositional recurrence analysis");
  CmdLine.register_pass
    ("-rba", resource_bound_analysis, " Resource bound analysis")
  (*
  CmdLine.register_config
    ("-z3-timeout",
     Arg.Set_int ArkZ3.opt_timeout,
     " Set Z3 solver timeout (milliseconds)");
*)

open Core
open Apak
open Srk
open CfgIr
open BatPervasives

module RG = Interproc.RG
module WG = WeightedGraph
module TLLRF = TerminationLLRF
module TDTA = TerminationDTA
module TM = Termination
module G = RG.G
module Ctx = Syntax.MakeSimplifyingContext ()
module Int = SrkUtil.Int
let srk = Ctx.context

include Log.Make(struct let name = "cra" end)

let forward_inv_gen = ref true
let forward_pred_abs = ref false
let dump_goals = ref false
let monotone = ref false
let nb_goals = ref 0
let termination_exp = ref true
let termination_llrf = ref true
let termination_dta = ref true
let termination_phase_analysis = ref true
let precondition = ref false
let termination_attractor = ref true

let dump_goal loc path_condition =
  if !dump_goals then begin
    let filename =
      Format.sprintf "%s%d-line%d.smt2"
        (Filename.chop_extension (Filename.basename loc.Cil.file))
        (!nb_goals)
        loc.Cil.line
    in
    let chan = Stdlib.open_out filename in
    let formatter = Format.formatter_of_out_channel chan in
    logf ~level:`always "Writing goal formula to %s" filename;
    Syntax.pp_smtlib2 srk formatter path_condition;
    Format.pp_print_newline formatter ();
    Stdlib.close_out chan;
    incr nb_goals
  end

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
  type t = value [@@deriving ord]
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
    let show = SrkUtil.mk_show pp
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

  let is_global = Var.is_global % var_of_value
end

module K = struct
  include Transition.Make(Ctx)(V)

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

let typ_has_offsets typ = match resolve_type typ with
  | Pointer _ | Func _ | Dynamic -> true
  | _ -> false

let is_int_array typ = match resolve_type typ with
  | Array (Concrete (Int _), _) -> true
  | _ -> false

let nondet_const name typ = Ctx.mk_const (Ctx.mk_symbol ~name typ)


let rec tr_expr expr =
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
    | OBoolExpr b -> TInt (Ctx.mk_ite (tr_bexpr b) (Ctx.mk_real (QQ.of_int 1)) (Ctx.mk_real (QQ.of_int 0)))
      (*if (Bexpr.equal b Bexpr.ktrue) then TInt (Ctx.mk_real (QQ.of_int 1)) else TInt (Ctx.mk_real (QQ.of_int 0))*)
    | OAccessPath ap -> TInt (nondet_const "tr" (tr_typ (AP.get_type ap)))
    | OConstant _ -> TInt (nondet_const "tr" `TyInt)
  in
  Aexpr.fold alg expr
and  tr_expr_val expr = match tr_expr expr with
  | TInt x -> x
  | TPointer x -> x.ptr_val
and tr_bexpr bexpr =
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

(* Populate table mapping variables to the offsets of that variable that
   appear in the program.  Must be called before calling weight *)
let offset_table = Varinfo.HT.create 991
let get_offsets v =
  try Varinfo.HT.find offset_table v
  with Not_found -> Int.Set.empty

let populate_offset_table file =
  let add_offset (v, offset) =
    match offset with
    | OffsetUnknown -> ()
    | OffsetNone -> ()
    | OffsetFixed k ->
      Varinfo.HT.modify_def Int.Set.empty v (Int.Set.add k) offset_table
  in
  let rec aexpr e = match e with
    | Cast (_, e) | UnaryOp (_, e, _) -> aexpr e
    | BinaryOp (e1, _, e2, _) -> aexpr e1; aexpr e2
    | AddrOf a | AccessPath a -> ap a
    | BoolExpr b -> bexpr b
    | Havoc _ | Constant _ -> ()
  and ap a = match a with
    | Variable v -> add_offset v
    | Deref e -> aexpr e
  and bexpr b = match b with
    | And (b1, b2) | Or (b1, b2) -> bexpr b1; bexpr b2
    | Atom (_, e1, e2) -> aexpr e1; aexpr e2
  in
  file |> CfgIr.iter_defs (fun def ->
      match def.dkind with
      | Assign (v, e) -> add_offset v; aexpr e
      | Store (a, e) -> ap a; aexpr e;
      | Call (lhs, a, args) ->
        begin match lhs with
          | Some v -> add_offset v
          | None -> ();
        end;
        aexpr a;
        List.iter aexpr args;
      | Assume b -> bexpr b
      | Initial -> ()
      | Assert (b, _) -> bexpr b
      | AssertMemSafe (a, _) -> aexpr a
      | Return (Some a) -> aexpr a
      | Return None -> ()
      | Builtin (Alloc (v, a, _)) -> add_offset v; aexpr a
      | Builtin (Free a) -> aexpr a
      | Builtin (Fork (lhs, a, args)) ->
        begin match lhs with
          | Some v -> add_offset v
          | None -> ();
        end;
        aexpr a;
        List.iter aexpr args
      | Builtin (Acquire a) | Builtin (Release a) -> aexpr a
      | Builtin AtomicEnd | Builtin AtomicBegin | Builtin Exit -> ())

let rec record_assign (lhs : varinfo) loff rhs roff fields =
  fields |> List.map (fun { fityp; fioffset; _ } ->
      match resolve_type fityp with
      | Record { rfields; _ } ->
        record_assign lhs (loff+fioffset) rhs (roff+fioffset) rfields
      | Pointer _ | Func _ | Dynamic ->
        let lhs = (lhs, OffsetFixed (loff + fioffset)) in
        begin match tr_expr (AccessPath (Variable (rhs, OffsetFixed roff))) with
          | TPointer rhs ->
            BatList.reduce K.mul [
              K.assign (VVal lhs) rhs.ptr_val;
              K.assign (VPos lhs) rhs.ptr_pos;
              K.assign (VWidth lhs) rhs.ptr_width;
            ]
          | TInt tint -> begin
              BatList.reduce K.mul [
                K.assign (VVal lhs) tint;
                K.assign (VPos lhs) (nondet_const "type_err" `TyInt);
                K.assign (VWidth lhs) (nondet_const "type_err" `TyInt)
              ]
            end
        end
      | _ ->
        let lhs = (lhs, OffsetFixed (loff+fioffset)) in
        let rhs = tr_expr_val (AccessPath (Variable (rhs, OffsetFixed (fioffset+roff)))) in
        K.assign (VVal lhs) rhs)
  |> BatList.reduce K.mul

let weight def =
  let open K in
  match def.dkind with
  | Assume phi | Assert (phi, _) -> K.assume (tr_bexpr phi)
  | Assign (lhs, rhs) ->
    let lhs_typ = resolve_type (Var.get_type lhs) in
    let rhs_typ = resolve_type (Aexpr.get_type rhs) in
    begin match lhs_typ, rhs_typ with
      | Record { rfields; _ }, _ | _, Record { rfields; _ } ->
        let lhs, loff = match lhs with
          | (lhs, OffsetFixed k) -> (lhs, k)
          | (lhs, OffsetNone) -> (lhs, 0)
          | _ -> invalid_arg "Unsupported record assignment"
        in
        begin match rhs with
          | AccessPath (Variable (v, OffsetFixed k)) ->
            record_assign lhs loff v k rfields
          | AccessPath (Variable (v, OffsetNone)) ->
            record_assign lhs loff v 0 rfields
          | _ -> invalid_arg "Unsupported record assignment"
        end
      | Pointer _, _ | Func _, _ | Dynamic, _ ->
        begin match tr_expr rhs with
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
        end
      | _, _ -> K.assign (VVal lhs) (tr_expr_val rhs)
    end
  | Store (lhs, rhs) ->
    (* Havoc all the variables lhs could point to *)
    let open PointerAnalysis in
    let rhs_val =
      match tr_expr rhs with
      | TPointer rhs -> rhs.ptr_val
      | TInt tint -> tint
    in
    let add_target memloc tr = match memloc with
      | (MAddr v, offset) when is_int_array (Varinfo.get_type v) ->
        begin
          match offset with
          | OffsetUnknown ->
            Int.Set.fold (fun offset tr ->
                K.add tr (K.assign (VVal (v, OffsetFixed offset)) rhs_val))
              (get_offsets v)
              K.one (* weak update *)
            |> K.mul tr
          | _ ->
            K.mul tr (K.assign (VVal (v,offset)) rhs_val)
        end
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
  | Initial | AssertMemSafe (_, _) | Return None -> one
  | _ ->
    Log.errorf "No translation for definition: %a" Def.pp def;
    assert false

type 'a label = 'a TransitionSystem.label =
  | Weight of 'a
  | Call of int * int
[@@deriving ord]

type klabel = K.t label [@@deriving ord]

module TS = TransitionSystem.Make(Ctx)(V)(K)

module TransitionDom = struct
  type weight = K.t
  type abstract_weight = K.t
  let concretize x = x
  let abstract x = x
  let equal = K.equal
  let widen = K.widen
end


module MonotoneDom = struct
  open Syntax
  module Sign = Abstract.Sign
  module SymbolSet = Syntax.Symbol.Set
  type weight = K.t
  module VS = Linear.QQVectorSpace
  type abstract_weight = (symbol * symbol) list * Ctx.t Sign.t * VS.t
  let man = Polka.manager_alloc_equalities ()

  (* Map a list of transition symbols to an affine coordinate system
     for those symbols.  *)
  let coordinates_of tr_symbols =
    let enum =
      (List.fold_left (fun syms (x, x') ->
           SymbolSet.add x (SymbolSet.add x' syms))
         SymbolSet.empty
         tr_symbols
       |> SymbolSet.enum)
      /@ mk_const srk
    in
    BatEnum.push enum (mk_one srk);
    BatArray.of_enum enum

  let abstract tr =
    let tr_symbols, formula = K.to_transition_formula tr in
    let coordinates = coordinates_of tr_symbols in
    let aff =
      Abstract.vanishing_space srk formula coordinates
    in
    let signs =
      let deltas =
        List.fold_left (fun deltas (x, x') ->
            (mk_sub srk (mk_const srk x') (mk_const srk x))::deltas)
          []
          tr_symbols
      in
      let vars = BatArray.to_list coordinates in
      Sign.abstract srk formula (vars@deltas)
    in
    (tr_symbols, signs, aff)

  let concretize (tr_symbols, signs, aff) =
    let transform =
      List.fold_left (fun assign (x,x') ->
          match V.of_symbol x with
          | Some v -> (v, mk_const srk x')::assign
          | None -> assert false)
        []
        tr_symbols
    in
    let coordinates = coordinates_of tr_symbols in
    let affine_guard =
      let zero = mk_zero srk in
      List.map
        (fun vec ->
          Linear.term_of_vec srk (fun dim -> coordinates.(dim)) vec
          |> mk_eq srk zero)
        aff
      |> mk_and srk
    in
    let guard =
      mk_and srk [Sign.formula_of srk signs;
                  affine_guard]
    in
    K.construct guard transform

  let equal (tr_symbols1, signs1, aff1) (tr_symbols2, signs2, aff2) =
    let pre_symbols tr_symbols =
      List.fold_left (fun pre (x,_) ->
          SymbolSet.add x pre)
        SymbolSet.empty
        tr_symbols
    in
    SymbolSet.equal (pre_symbols tr_symbols1) (pre_symbols tr_symbols2)
    && Abstract.Sign.equal signs1 signs2
    && VS.equal aff1 aff2

  let widen _ y = y
end

(* Weight-labeled graph module suitable for ocamlgraph *)
module TSG = struct
  type t = TS.t

  module V = struct
    include SrkUtil.Int
    type label = int
    let label x = x
    let create x = x
  end

  module E = struct
    type label = klabel
    type vertex = int
    type t = int * klabel * int [@@deriving ord]
    let src (x, _, _) = x
    let dst (_, _, x) = x
    let label (_, x, _) = x
    let create x y z = (x, y, z)
  end

  let iter_edges_e = WG.iter_edges
  let iter_vertex = WG.iter_vertex
  let iter_succ f tg v =
    WG.U.iter_succ f (WG.forget_weights tg) v
  let fold_pred_e = WG.fold_pred_e
end

module TSDisplay = ExtGraph.Display.MakeLabeled
    (TSG)
    (SrkUtil.Int)
    (struct
      type t = klabel
      let pp formatter w = match w with
        | Weight w -> K.pp formatter w
        | Call (s,t) -> Format.fprintf formatter "call(%d, %d)" s t
      (* let show = SrkUtil.mk_show pp *)
    end)

module SA = Abstract.MakeAbstractRSY(Ctx)

let decorate_transition_system predicates ts entry =
  let module AbsDom =
    TS.ProductIncr
      (TS.ProductIncr(TS.LiftIncr(SA.Sign))(TS.LiftIncr(SA.AffineRelation)))
      (TS.LiftIncr(SA.PredicateAbs(struct let universe = predicates end)))
  in
  let inv = TS.forward_invariants (module AbsDom) ts entry in
  let member varset sym =
    match V.of_symbol sym with
    | Some v -> TS.VarSet.mem v varset
    | None -> false
  in
  TS.loop_headers_live ts
  |> List.fold_left (fun ts (v, live) ->
      let fresh_id = (Def.mk (Assume Bexpr.ktrue)).did in
      let invariant = AbsDom.formula_of (AbsDom.exists (member live) (inv v)) in
      logf "Found invariant at %d:@;%a" v (Syntax.Formula.pp srk) invariant;
      WG.split_vertex ts v (Weight (K.assume invariant)) fresh_id)
    ts

let make_transition_system rg =
  let call_edge block =
    Call ((RG.block_entry rg block).did, (RG.block_exit rg block).did)
  in
  let assertions = ref SrkUtil.Int.Map.empty in
  let add_assert v e =
    assertions := SrkUtil.Int.Map.add v e (!assertions)
  in
  let ts =
    BatEnum.fold (fun ts (block, graph) ->
        let tg =
          RG.G.fold_vertex (fun def tg ->
              let tg = WG.add_vertex tg def.did in
              let label =
                match def.dkind with
                | Call (None, AddrOf (Variable (func, OffsetNone)), []) ->
                  call_edge func
                | Assert (phi, msg) ->
                  let condition = tr_bexpr phi in
                  add_assert def.did (condition, Def.get_location def, msg);
                  Weight (K.assume condition)
                | AssertMemSafe (expr, msg) ->
                  let condition =
                    match tr_expr expr with
                    | TInt _ -> Ctx.mk_false
                    | TPointer p ->
                      Ctx.mk_and [
                        Ctx.mk_leq (Ctx.mk_real QQ.zero) p.ptr_pos;
                        Ctx.mk_lt p.ptr_pos p.ptr_width
                      ]
                  in
                  add_assert def.did (condition, Def.get_location def, msg);
                  Weight (K.assume condition)
                | _ -> Weight (weight def)
              in
              RG.G.fold_succ
                (fun succ tg -> WG.add_edge tg def.did label succ.did)
                graph def
                tg)
            graph
            TS.empty
        in
        let predicates =
          if !forward_pred_abs then
            RG.G.fold_vertex (fun def predicates ->
                match def.dkind  with
                | Assume phi when Bexpr.equal phi Bexpr.ktrue ->
                  predicates
                | Assert (phi, _) | Assume phi ->
                  Syntax.Expr.Set.add (tr_bexpr phi) predicates
                | _ ->
                  predicates)
              graph
              Syntax.Expr.Set.empty
            |> Syntax.Expr.Set.enum
            |> BatList.of_enum
          else
            []
        in

        let entry = (RG.block_entry rg block).did in
        let exit = (RG.block_exit rg block).did in
        let point_of_interest v =
          v = entry || v = exit || SrkUtil.Int.Map.mem v (!assertions)
        in
        let tg = TS.simplify point_of_interest tg in
        let tg = TS.remove_temporaries tg in
        let tg =
          if !forward_inv_gen then
            Log.phase "Forward invariant generation"
              (decorate_transition_system predicates tg) entry
          else
            tg
        in
        WG.fold_edges (fun (src, label, tgt) ts ->
            match label with
            | Weight w -> WG.add_edge ts src (Weight w) tgt
            | Call (s,t) -> WG.add_edge ts src (Call (s,t)) tgt)
          tg
          (WG.fold_vertex (fun v ts ->
               WG.add_vertex ts v)
              tg
              ts))
      TS.empty
      (RG.bodies rg)
  in
  (ts, !assertions)

let mk_query ts entry =
  TS.mk_query ts entry
    (if !monotone then
       (module MonotoneDom)
     else
       (module TransitionDom))

let analyze file =
  populate_offset_table file;
  match file.entry_points with
  | [main] -> begin
      let rg = Interproc.make_recgraph file in
      let entry = (RG.block_entry rg main).did in
      let (ts, assertions) = make_transition_system rg in

      (*TSDisplay.display ts;*)
      let query = mk_query ts entry in
      assertions |> SrkUtil.Int.Map.iter (fun v (phi, loc, msg) ->
          let path = TS.path_weight query v in
          let sigma sym =
            match V.of_symbol sym with
            | Some v when K.mem_transform v path ->
              K.get_transform v path
            | _ -> Ctx.mk_const sym
          in
          let phi = Syntax.substitute_const Ctx.context sigma phi in
          let path_condition =
            Ctx.mk_and [K.guard path; Ctx.mk_not phi]
            |> SrkSimplify.simplify_terms srk
          in
          logf "Path condition:@\n%a"
            (Syntax.pp_smtlib2 Ctx.context) path_condition;
          dump_goal loc path_condition;
          match Wedge.is_sat Ctx.context path_condition with
          | `Sat -> Report.log_error loc msg
          | `Unsat -> Report.log_safe ()
          | `Unknown ->
            logf ~level:`warn "Z3 inconclusive";
            Report.log_error loc msg);

      Report.print_errors ();
      Report.print_safe ();
    end
  | _ -> assert false

module TermMemo = Memo.Make(struct
                      type t = (Ctx.t,Syntax.typ_fo) Syntax.expr
                      let hash = Syntax.Expr.hash
                      let equal = Syntax.Expr.equal
                    end)

let purify_floor =
  let open Syntax in
  let fresh_sym = TermMemo.memo (fun _ -> mk_const srk (mk_symbol srk `TyInt)) in
  let rewriter expr =
    match destruct srk expr with
    | `Unop (`Floor, _) ->
       if Symbol.Set.for_all (fun s -> typ_symbol srk s == `TyInt) (symbols expr) then
         expr
       else
         fresh_sym expr
    | _ -> expr
  in
  rewrite srk ~up:rewriter

let preimage transition formula =
  let open Syntax in
  let transition = K.linearize transition in
  let fresh_skolem =
    Memo.memo (fun sym ->
        let name = show_symbol srk sym in
        let typ = typ_symbol srk sym in
        mk_const srk (mk_symbol srk ~name typ))
  in
  let subst sym =
    match V.of_symbol sym with
    | Some var ->
       if K.mem_transform var transition then
         K.get_transform var transition
       else
         mk_const srk sym
    | None -> fresh_skolem sym
  in
  mk_and srk [purify_floor (K.guard transition);
              substitute_const srk subst formula]

let formula_with_attractor_region formula x_xp =
  logf "Starting attractor region analysis";
  let xp_leq_x_terms = BatList.fold_left (fun l (x, xp) -> 
      let open Syntax in (mk_leq srk (mk_const srk xp) (mk_const srk x), mk_const srk xp, mk_const srk x) :: l) [] x_xp 
  in
  let lower_bounds = BatList.map (fun (xp_leq_x_term, xp, x) -> 
      match SrkZ3.optimize_box srk (Syntax.mk_and srk [formula; xp_leq_x_term]) [xp] with
      | `Sat l ->  let h = BatList.hd l in (Interval.lower h, x)
      | _ -> (None, x)
    ) 
      xp_leq_x_terms in 
  let x_leq_xp_terms = BatList.fold_left (fun l (x, xp) -> 
      let open Syntax in (mk_leq srk (mk_const srk x) (mk_const srk xp), mk_const srk xp, mk_const srk x) :: l) [] x_xp 
  in
  let upper_bounds = BatList.map (fun (x_leq_xp_term, xp, x) -> 
      match SrkZ3.optimize_box srk (Syntax.mk_and srk [formula; x_leq_xp_term]) [xp] with
      | `Sat l -> let h = BatList.hd l in (Interval.upper h, x)
      | _ -> (None, x)
    ) 
      x_leq_xp_terms 
  in
  let lb_x_ub = BatList.map2 (fun lb ub -> 
      let open Syntax in
      match lb, ub with 
      | (Some a, x), (Some b, y) -> [mk_leq srk (mk_real srk a) x; mk_leq srk y (mk_real srk b)] 
      | (Some a, x), _ -> [mk_leq srk (mk_real srk a) x]
      | _, (Some b, x) -> [mk_leq srk x (mk_real srk b)]
      | _ -> []
    ) 
      lower_bounds 
      upper_bounds
  in
  let formula'' = Syntax.mk_and srk (formula :: BatList.flatten lb_x_ub) in
  logf "Formula with attractor regions:\n%a\n" (Syntax.Formula.pp srk) formula'';
  formula''

let omega_algebra =  function
  | `Omega transition ->
     (** over-approximate possibly non-terminating conditions for a transition *)
     begin
       let open Syntax in
       let x_xp, formula = K.to_transition_formula transition in
       let formula =
          purify_floor (Nonlinear.linearize srk formula)
       in
       let exists =
         let post_symbols =
           List.fold_left
             (fun set (_, sym') -> Syntax.Symbol.Set.add sym' set)
             Syntax.Symbol.Set.empty
             x_xp
         in
         fun x ->
         match V.of_symbol x with
         | Some _ -> true
         | None -> Syntax.Symbol.Set.mem x post_symbols
       in
       let formula = 
        if !termination_attractor then 
          formula_with_attractor_region formula x_xp 
        else formula 
       in
       let nonterm formula =
         if !termination_llrf
            && (let result, _ = TLLRF.compute_swf srk exists x_xp formula in result = TLLRF.ProvedToTerminate)
         then
           Syntax.mk_false srk
         else
           let dta =
             if !termination_dta then
               [TDTA.compute_swf_via_DTA srk exists x_xp formula]
             else []
           in
           let exp =
             if !termination_exp then
               let mp =
                 Syntax.mk_not srk
                   (TerminationExp.mp (module Iteration.LinearRecurrenceInequation) srk exists x_xp formula)
               in
               let dta_entails_mp =
                 (* if DTA |= mp, DTA /\ MP simplifies to DTA *)
                 Syntax.mk_forall_consts
                   srk
                   (fun _ -> false)
                   (Syntax.mk_or srk [mk_not srk (mk_and srk dta); mp])
               in
               match Quantifier.simsat srk dta_entails_mp with
               | `Sat -> []
               | _ -> [mp]
             else []
           in
           let result =
             Syntax.mk_and srk (dta@exp)
           in
           match Quantifier.simsat srk result with
           | `Unsat -> mk_false srk
           | _ -> result
       in
       let phase_mp =
         if !termination_phase_analysis then begin
             let predicates =
               (* Use variable directions & signs as candidate invariants *)
               List.concat_map (fun (x,x') ->
                   let x = mk_const srk x in
                   let x' = mk_const srk x' in
                   [mk_lt srk x x';
                    mk_lt srk x' x;
                    mk_leq srk (mk_zero srk) x;
                    mk_leq srk x (mk_zero srk);
                    mk_eq srk x x'])
                 x_xp
             in
             let phased_nonterm =
              let cells = 
               Iteration.invariant_partition ~exists srk x_xp predicates formula
              in
                Format.printf "Number of cells: %d\n" (List.length cells);
              cells |> List.iteri (fun i phase -> Format.printf "Cell %d: %a\n" i (Expr.pp srk) phase);
              cells
               |> List.map (fun phase ->
                      nonterm (Syntax.mk_and srk [formula; phase]))
               |> Syntax.mk_or srk
             in
             [preimage (K.star transition) phased_nonterm]
           end else []
       in
       let pre =
         let fresh_skolem =
           Memo.memo (fun sym ->
               let name = show_symbol srk sym in
               let typ = typ_symbol srk sym in
               mk_const srk (mk_symbol srk ~name typ))
         in
         let subst sym =
           match V.of_symbol sym with
           | Some _ -> mk_const srk sym
           | None -> fresh_skolem sym
         in
         substitute_const srk subst formula
       in
       Syntax.mk_and srk (pre::(nonterm formula)::phase_mp)
     end
  | `Add (cond1, cond2) ->
     (** combining possibly non-terminating conditions for multiple paths *)
     Syntax.mk_or srk [cond1; cond2]
  | `Mul (transition, state) ->
     (** propagate state formula through a transition *)
     preimage transition state

(* Raise universal quantifiers to top-level.  *)
let lift_universals srk phi =
  let open Syntax in
  let phi = rewrite srk ~down:(nnf_rewriter srk) phi in
  let rec quantify_universals (nb, phi) =
    if nb > 0 then
      quantify_universals (nb - 1, mk_forall srk `TyInt phi)
    else
      phi
  in
  let alg = function
    | `Tru -> (0, mk_true srk)
    | `Fls -> (0, mk_false srk)
    | `Atom (`Eq, x, y) -> (0, mk_eq srk x y)
    | `Atom (`Lt, x, y) -> (0, mk_lt srk x y)
    | `Atom (`Leq, x, y) -> (0, mk_leq srk x y)
    | `And conjuncts ->
       let max_nb = List.fold_left max 0 (List.map fst conjuncts) in
       let shift_conjuncts =
         conjuncts |> List.map (fun (nb,phi) ->
                     let shift = max_nb - nb in
                     substitute srk (fun i -> mk_var srk (i + shift) `TyInt) phi)
       in
       (max_nb, mk_and srk shift_conjuncts)
    | `Or disjuncts ->
       let max_nb = List.fold_left max 0 (List.map fst disjuncts) in
       if max_nb == 0 then
         (0, mk_or srk (List.map snd disjuncts))
       else
         (* Introduce a Skolem constant to distribute universals over disjunction:
            (forall x. F(x)) \/ (forall x. G(x))
            is equisatisfiable with
            exists c. forall x. (F(x) /\ c = 0) \/ (G(x) /\ c = 1) *)
         let sk = mk_const srk (mk_symbol srk ~name:"choice" `TyInt) in
         let shift_disjuncts =
           disjuncts |> BatList.mapi (fun idx (nb,phi) ->
                            let shift = max_nb - nb in
                            mk_and srk
                              [substitute srk (fun i -> mk_var srk (i + shift) `TyInt) phi;
                               mk_eq srk sk (mk_int srk idx)])
         in
         (max_nb, mk_or srk shift_disjuncts)

    | `Quantify (`Exists, name, typ, qphi) ->
       (0, mk_exists srk ~name typ (quantify_universals qphi))
    | `Quantify (`Forall, _, `TyInt, (nb_universals, phi)) ->
       (nb_universals + 1, phi)
    | `Quantify (`Forall, name, typ, qphi) ->
       (0, mk_forall srk ~name typ (quantify_universals qphi))
    | `Not (_, _) -> assert false
    | `Proposition (`Var i) -> (0, mk_var srk i `TyBool)
    | `Proposition (`App (p, args)) -> (0, mk_app srk p args)
    | `Ite (cond, bthen, belse) ->
       (0, mk_ite srk
             (quantify_universals cond)
             (quantify_universals bthen)
             (quantify_universals belse))
  in
  quantify_universals (Formula.eval srk alg phi)

let prove_termination_main file =
  populate_offset_table file;
  match file.entry_points with
  | [main] -> begin
      let rg = Interproc.make_recgraph file in
      let entry = (RG.block_entry rg main).did in
      let (ts1, _) = make_transition_system rg in
      if !CmdLine.display_graphs then
        TSDisplay.display ts1;
      let query = mk_query ts1 entry in
      let omega_paths_sum =
        TS.omega_path_weight query omega_algebra
        |> lift_universals srk
        |> SrkSimplify.simplify_terms srk
      in
      match Quantifier.simsat srk omega_paths_sum with
      | `Sat -> 
         Format.printf "Cannot prove that program always terminates\n";
         if !precondition then
           (* TODO: need to eliminate universal quantifiers first quantifiers first! *)
           let simplified =
             omega_paths_sum
             |> Nonlinear.linearize srk
             |> Quantifier.mbp srk (fun sym ->
                    match V.of_symbol sym with
                    | Some x -> V.is_global x
                    | _ -> false)
             |> Syntax.mk_not srk
           in
           Format.printf "Sufficient terminating conditions:\n%a\n"
             (Syntax.Formula.pp srk)
             simplified
      | `Unsat -> Format.printf "Program always terminates\n"
      | `Unknown -> Format.printf "Unknown analysis result\n"
    end
  | _ -> failwith "Cannot find main function within the C source file"

let resource_bound_analysis file =
  populate_offset_table file;
  match file.entry_points with
  | [main] -> begin
      let rg = Interproc.make_recgraph file in
      let (ts, _) = make_transition_system rg in
      let entry = (RG.block_entry rg main).did in
      let query = mk_query ts entry in
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
      RG.blocks rg |> BatEnum.iter (fun procedure ->
          let entry = (RG.block_entry rg procedure).did in
          let exit = (RG.block_exit rg procedure).did in
          let summary = WG.RecGraph.call_weight query (entry, exit) in
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
                Syntax.substitute_const srk subst (K.get_transform cost summary)
              in
              let simplify =
                SrkSimplify.simplify_terms_rewriter srk
                % Nonlinear.simplify_terms_rewriter srk
              in
              Ctx.mk_and [Syntax.substitute_const srk subst (K.guard summary);
                          Ctx.mk_eq (Ctx.mk_const cost_symbol) rhs ]
              |> Syntax.rewrite srk ~up:simplify
            in
            match Wedge.symbolic_bounds_formula ~exists srk guard cost_symbol with
            | `Sat (lower, upper) ->
              begin match lower with
                | Some lower ->
                  logf ~level:`always "%a <= cost" (Syntax.Term.pp srk) lower;
                  logf ~level:`always "%a is o(%a)"
                    Varinfo.pp procedure
                    BigO.pp (BigO.of_term srk lower)
                | None -> ()
              end;
              begin match upper with
                | Some upper ->
                  logf ~level:`always "cost <= %a" (Syntax.Term.pp srk) upper;
                  logf ~level:`always "%a is O(%a)"
                  Varinfo.pp procedure
                  BigO.pp (BigO.of_term srk upper)
                | None -> ()
              end
            | `Unsat ->
              logf ~level:`always "%a is infeasible"
                Varinfo.pp procedure
          end else
            logf ~level:`always "Procedure %a has zero cost" Varinfo.pp procedure)
    end
  | _ -> assert false

let _ =
  CmdLine.register_config
    ("-cra-no-forward-inv",
     Arg.Clear forward_inv_gen,
     " Turn off forward invariant generation");
  CmdLine.register_config
    ("-cra-pred-abs",
     Arg.Clear forward_pred_abs,
     " Turn on predicate abstraction in forward invariant generation");
  CmdLine.register_config
    ("-cra-split-loops",
     Arg.Unit (fun () ->
         if !monotone then
           K.domain := (module Iteration.InvariantDirection(val !K.domain))
         else
           K.domain := (module Iteration.Split(val !K.domain))),
     " Turn on loop splitting");
  CmdLine.register_config
    ("-cra-prsd",
     Arg.Unit (fun () ->
         let open Iteration in
         let open SolvablePolynomial in
         K.domain := (module ProductWedge(SolvablePolynomialPeriodicRational)(WedgeGuard))),
     " Use periodic rational spectral decomposition");
  CmdLine.register_config
    ("-cra-vas",
     Arg.Unit (fun () ->
         let open Iteration in
         if !monotone then
           K.domain := (module Product
                                 (Product(Vas.Monotone)(PolyhedronGuard))
                                 (LinearRecurrenceInequation))
         else
           K.domain := (module Product
                                 (Product(Vas)(PolyhedronGuard))
                                 (LinearRecurrenceInequation))),
     " Use VAS abstraction");
  CmdLine.register_config
    ("-cra-vass",
     Arg.Unit (fun () ->
         let open Iteration in
         K.domain := (module Product(Product(LinearRecurrenceInequation)(PolyhedronGuard))(Vass))),
     " Use VASS abstraction");
  CmdLine.register_config
    ("-dump-goals",
     Arg.Set dump_goals,
     " Output goal assertions in SMTLIB2 format");
  CmdLine.register_config
    ("-monotone",
     Arg.Unit (fun () ->
         let open Iteration in
         monotone := true;
         K.domain := (module Product(LinearRecurrenceInequation)(PolyhedronGuard))),
     " Disable non-monotone analysis features");
  CmdLine.register_config
    ("-termination-no-exp",
     Arg.Clear termination_exp,
     " Disable exp-based termination analysis");
  CmdLine.register_config
    ("-termination-no-llrf",
     Arg.Clear termination_llrf,
     " Disable LLRF-based termination analysis");
  CmdLine.register_config
    ("-termination-no-dta",
     Arg.Clear termination_dta,
     " Disable DTA-based termination analysis");
  CmdLine.register_config
    ("-termination-no-phase",
     Arg.Clear termination_phase_analysis,
     " Disable phase-based termination analysis");
  CmdLine.register_config
     ("-termination-no-attractor",
      Arg.Clear termination_attractor,
      " Disable attractor region computation for LLRF");
  CmdLine.register_config
    ("-precondition",
     Arg.Clear precondition,
     " Synthesize mortal preconditions")

let _ =
  CmdLine.register_pass
    ("-cra", analyze, " Compositional recurrence analysis");
  CmdLine.register_pass
    ("-termination", prove_termination_main, " Proof of termination");
  CmdLine.register_pass
    ("-rba", resource_bound_analysis, " Resource bound analysis")

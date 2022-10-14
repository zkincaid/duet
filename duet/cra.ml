open Core
open Srk
open CfgIr
open BatPervasives

module RG = Interproc.RG
module WG = WeightedGraph
module TLLRF = TerminationLLRF
module TDTA = TerminationDTA
module G = RG.G
module Ctx = Syntax.MakeSimplifyingContext ()
module Int = SrkUtil.Int
module TF = TransitionFormula

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
let termination_prenex = ref true

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
  { ptr_val : Ctx.arith_term;
    ptr_pos : Ctx.arith_term;
    ptr_width : Ctx.arith_term }

type term =
  | TInt of Ctx.arith_term
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
    let tf = TF.linearize srk (K.to_transition_formula tr) in
    let coordinates = coordinates_of (TF.symbols tf) in
    let aff =
      Abstract.vanishing_space srk (TF.formula tf) coordinates
    in
    let signs =
      let deltas =
        List.fold_left (fun deltas (x, x') ->
            (mk_sub srk (mk_const srk x') (mk_const srk x))::deltas)
          []
          (TF.symbols tf)
      in
      let vars = BatArray.to_list coordinates in
      Sign.abstract srk (TF.formula tf) (vars@deltas)
    in
    (TF.symbols tf, signs, aff)

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

let make_transition_system (simplify: bool) rg =
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
        let tg = if simplify then TS.simplify point_of_interest tg else tg in
        let tg = if simplify then TS.remove_temporaries tg else tg in
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

(** Useful definitions for SMT-based analyses: McMillan's assertion-checking algorithm + concolic execution *)

module IntMap = BatMap.Make(Int)
module DQ = BatDeque
module ARR = Batteries.DynArray 
type cfg_t = K.t label WG.t
type idq_t = int BatDeque.t 
exception Mexception of string 
let mk_true () = Syntax.mk_true Ctx.context
let mk_false () = Syntax.mk_false Ctx.context 
let mk_query ts entry = TS.mk_query ts entry (if !monotone then (module MonotoneDom) else (module TransitionDom))
let mypp_weights s l = List.iteri (fun i f -> logf ~level:`always "%s(%i): \n%a" s i K.pp f) l
let mypp_formula s l = 
  List.iteri (fun i f -> logf ~level:`always "%s(%i): \n%a" s i (Syntax.pp_expr_unnumbered Ctx.context) @@ f) l



(* Convert assertion checking problem to vertex reachability problem. *)
let make_ts_assertions_unreachable (ts : cfg_t) assertions = 
  let largest = ref (WG.fold_vertex (fun v max -> if v > max then v else max) ts 0) in 
  let pts = ref ts in 
  let new_vertices = ref [] in 
  assertions |> SrkUtil.Int.Map.iter (
    fun v (phi, _, _) -> 
      (* For each assertion, create new vertex after the assertion state 
       * with edge into the vertex being the negated condition. *)
      let u = !largest + 1 in 
      largest := (!largest) + 1; 
      pts := WG.add_vertex !pts u ;
      pts := WG.add_edge !pts v (Weight (K.assume (Ctx.mk_not phi))) u ;
      let s = Printf.sprintf " Adding assertion node %d -> %d for label " v u in 
      mypp_formula s [ Ctx.mk_not phi ] ; 
      new_vertices := u :: !new_vertices 
  ); !pts, !new_vertices
  
(** Algebraic formulation of McMillan's algorithm. *)
module McMillanChecker = struct 

  (** type definitions fo McMillan checker. *)
  let logging = false (* enable for logging *)

  (* context of McMillan-Checker. *)
  type mc_context = {
      mode: mc_mode;
      ts: cfg_t;
      entry: int;
      err_loc: int;
      worklist: int DQ.t ref;
      execlist: int DQ.t ref;
      vtxcnt: int ref;
      ptt: ltree ref;
    }
  (* mode of McMillan's algorithm: plain, or CRA-fueled concolic mode *)
  and mc_mode = 
      | PlainMcMillan 
      | ConcolicMcMillan
  (** abstract reachability tree *)
  and ltree = {
    graph : cfg_t;
    entry : int;
    cfg_vertex : int ARR.t;
    parents : int ARR.t;
    labels : (Ctx.t Syntax.formula) ARR.t;
    covers : int IntMap.t ref;       
    (* also maintain reverse map for each y, storing (x, y) that are in cover. *)
    reverse_covers : (int list) IntMap.t ref;
    children : int list ARR.t;
    precedent_nodes : (int list) IntMap.t ref;
    models : (Ctx.t Interpretation.interpretation) IntMap.t;
    solver: Ctx.t Srk.Smt.Solver.t; (** persistent solver state object, prevents Z3 from allocating per SMT call *)
  }
  (* result of McMillan's algorithm *)
  and mc_result = 
    | McProvenSafe
    | McProvenUnsafe
    | McError
  (* state of McMillan's algorithm *)
  and mc_state = 
    | McContinue
    | McErrorReached
    | McWellLabeled
  (** some helper functions that operate on the context *)

  let mk_ltree (g: cfg_t) (entry: int) = 
    ref {
      graph = g;
      entry = entry;
      cfg_vertex = ARR.create ();
      parents = ARR.create ();
      labels = ARR.create ();
      covers = ref IntMap.empty;
      reverse_covers = ref IntMap.empty;
      children = ARR.create ();
      precedent_nodes = ref IntMap.empty;
      models = IntMap.empty;
      solver = Smt.mk_solver Ctx.context
    }

  let mk_mc_context (mode: mc_mode) (ts: cfg_t) (entry: int) (err_loc: int) = 
    ref {
      mode = mode; 
      ts = ts; 
      entry = entry;
      err_loc = err_loc;
      worklist = ref DQ.empty;
      execlist = ref DQ.empty;
      vtxcnt = ref 0;
      ptt = mk_ltree ts entry;
    }

  (** some helper methods *)

    (*  [i %>> q]: add i to front of worklist q  *)
  let (%>>)  (i : int) (q : idq_t) = DQ.cons i q 
  
  (*  [t %^ i]: get parent of node i in tree t.  *)
  let (%^) (t : ltree) (i : int) = ARR.get t.parents i 

  (*  [t %-> i]: get CFG vertex mapped by node i in tree t. *)
  let (%->) (t : ltree) (i : int) = ARR.get t.cfg_vertex i 

  (* [ew t u v] returns the CFG edge weight of edge (u, v) for vertices u, v in the CFG. *) 
  let ew (t : ltree) u v = match WG.edge_weight t.graph u v with  Weight w -> w  | Call _ -> failwith "call unimplemented"    
  
  (* [t %-*> u] returns a list of edge weights that form the path condition from root of t to tree node u.  *)
  let rec (%-*>) (t: ltree) (u : int) = 
    if u == 0 then [ ]
    else let rec (%<*-) (t : ltree) (u : int) =
     match t %^ u with 
      | 0 -> [ ew t (t %-> 0) (t %-> u) ]  
      | v -> ew t (t %-> v) (t %-> u) :: (t %<*- v) in 
      let ews = List.rev (t %<*- u) in
      ews 

  (* [tree_path t u] returns list of tree nodes that form the corrsp. tree path from root of t to tree node u *)
  let tree_path t u = 
    let rec tree_path_rev t u = 
      match u with 
      | 0 -> [ 0 ]
      | x -> x :: (tree_path_rev t (t %^ u)) 
    in List.rev @@ tree_path_rev t u

  (* [children t v] returns children of tree node v in tree t. *)
  let children (t : ltree) v = 
    ARR.get t.children v 

  (* [descendants t v] returns descendants of tree node v in tree t in DFS order. *)
  let rec descendants (t : ltree) v = 
    let v_children = children t v in 
    v :: (List.fold_left (fun l ch -> (descendants t ch) @ l) [] v_children)

  (* return leaves of subtree rooted at v. *)  
  let rec leaves (t: ltree) v = 
    let chs = children t v in 
    if List.length chs == 0 then [ v ]
    else 
      List.fold_left (fun child_leaves ch -> leaves t ch @ child_leaves) [] chs

  (* is a vertex in tree a leaf? *)
  let rec is_leaf (t: ltree) v = 
    let chs = children t v in 
      List.length chs == 0

  (* [label t v] returns the node label of tree node v in tree t. *)
  let label (t : ltree) v = ARR.get t.labels v
  
  (* [get_precedent_nodes t v] retrieves a sequence of precedent nodes of tree node vin preorder in tree t. *)
  let get_precedent_nodes t v = 
    (* The list is stored in tree structure in reverse, so we reverse it to get preorder. *)
    let cfg_vertex = t %-> v in 
    let postordered_precedents = IntMap.find_default [] cfg_vertex !(t.precedent_nodes) in 
    List.rev postordered_precedents 

  (* Interpolate the path (entry) -> (t %-> src) -> (sink). If fail, then get model. *)
  let interpolate_or_get_model (t : ltree) (src : int) (sink : int) = 
    let query = mk_query t.graph (t %-> src) in 
    let post_path_summary = TS.path_weight query sink |> K.guard in
    let initial_path_weights = t %-*> src in 
    K.interpolate_or_concrete_model initial_path_weights post_path_summary 
  
  (** retrieves an abstract model *)
  let get_abstract_model ?(solver=Smt.mk_solver Ctx.context) 
        pre_formula post_pre_symbols 
        (src : int) (sink : int) (graph : cfg_t) = 
    let query = mk_query graph src in 
    let path = TS.path_weight query sink in 
    let pre_formula_symbols = Syntax.symbols pre_formula |> MonotoneDom.SymbolSet.elements in 
    match Smt.get_concrete_model Ctx.context ~solver:(solver) pre_formula_symbols pre_formula with 
      | `Sat itp ->
        let m = Interpretation.enum itp in 
        let itp' = BatEnum.fold (fun itp' (symb, v) -> 
          let pre_symb = List.assoc symb post_pre_symbols in 
          Interpretation.add pre_symb v itp' ) (Interpretation.empty Ctx.context) m in 
          K.get_post_model itp' path               
      | `Unknown -> None 
      | `Unsat -> None

  let get_initial_abstract_model ?(solver=Smt.mk_solver Ctx.context) (src : int) (sink : int) (graph : cfg_t) = 
    let query = mk_query graph src in 
    let path = TS.path_weight query sink in 
    let path_condition = K.guard path in 
    let path_condition_symbols = Syntax.symbols path_condition |> MonotoneDom.SymbolSet.elements in 
      Smt.get_concrete_model Ctx.context ~solver:(solver) path_condition_symbols path_condition 

  
  (** Core procedures of McMillan's algorithm *)

  (* Add new tree leaf mapping to CFG vertex v and with parent tree node p. *)
  let add_tree_vertex (ctx: mc_context) ?model (v: WG.vertex) (p: int) = 
    (* sequentially add v to the lists, indexed by !vtxcnt *)
    ARR.add !(ctx.ptt).cfg_vertex v;
    ARR.add !(ctx.ptt).parents p;
    ARR.add !(ctx.ptt).labels (mk_true ());
    ARR.add !(ctx.ptt).children [];
    (* set children of parent to be !vtxcnt :: children. *)
    ARR.set !(ctx.ptt).children p (!(ctx.vtxcnt) :: (children !(ctx.ptt) p)); 
    (* Add v to precedent_nodes. *)
    let precedent_nodes = IntMap.find_default [] v !(!(ctx.ptt).precedent_nodes) in 
    !(ctx.ptt).precedent_nodes := IntMap.add v (!(ctx.vtxcnt) :: precedent_nodes) !(!(ctx.ptt).precedent_nodes);
    (* Push it onto the worklist and increment vertex counter. *)
    match model with 
    | Some model -> 
      (* putting vertex v (will be assigned tree node !ctx.vtxcnt) on execlist with model... *)
      ctx.execlist := !(ctx.vtxcnt) %>> !(ctx.execlist);
      ctx.ptt := {!(ctx.ptt) with models = IntMap.add !(ctx.vtxcnt) model !(ctx.ptt).models};
      ctx.vtxcnt := !(ctx.vtxcnt) + 1
    | None -> (** frontier nodes are nodes with no interpretations attached to them, pushed to worklist *)
      ctx.worklist := !(ctx.vtxcnt) %>> !(ctx.worklist); 
      ctx.vtxcnt := !(ctx.vtxcnt) + 1

  (* expand leaf node v. If in concolic mode, 
      for every out-neighbor y of v, first try deriving a post-state model of v-> y, if successful, put it
        on the concolic execution worklist. Otherwise, it is a frontier node, and put it on the 
        mcmillan worklist. *)
  let mc_expand (ctx: mc_context) v = 
    let vg = !(ctx.ptt) %-> v in 
    match ctx.mode with 
    | PlainMcMillan ->
      WG.iter_succ_e (fun (_, _, y) ->  
        add_tree_vertex ctx y v;
        ) !(ctx.ptt).graph vg  
    | ConcolicMcMillan ->
      begin 
        (* visit out neighbors of v *)
        begin match IntMap.find_opt v !(ctx.ptt).models with 
        | Some m ->
          WG.iter_succ_e (fun (_, weight, y) -> 
            let weight = match weight with Weight w -> w | Call _ -> failwith "cannot handle call" in 
            begin match K.get_post_model m weight with 
            | Some y_model -> add_tree_vertex ctx ~model:y_model y v 
            | None -> add_tree_vertex ctx y v 
            end
          ) !(ctx.ptt).graph vg
        | None -> 
          failwith @@ Printf.sprintf "trying to expand from node %d(%d) without labelled model " v (!(ctx.ptt) %-> v)
        end
      end 
  
  (* refine the label of each tree node u along path from tree root to v. *)
  let mc_refine_with_interpolants (ctx: mc_context) path interpolants = 
    (*Printf.printf "length of interpolants: %d\n" (List.length interpolants);
    Printf.printf "length of path condition: %d\n" (List.length path_condition);*)
    List.iter2 (fun u interpolant -> 
      let u_label = ARR.get !(ctx.ptt).labels u in 
      let u_label' = Syntax.mk_and Ctx.context [ u_label ; interpolant ] in 
      if logging then Printf.printf "[relabelling %d] to label: \n" u;
      if logging then mypp_formula "" [ u_label' ];
      ARR.set !(ctx.ptt).labels u u_label';
      (* remove ( * -> u) in covering relation. *)
      begin match IntMap.find_opt u !(!(ctx.ptt).reverse_covers) with 
      | None -> () 
      | Some l ->
        (* remove covers (List.iter (fun x -> Printf.printf " (%d->%d)" x u) l *)
        let u_coverers  = List.fold_left (fun coverers x -> 
          (* test if label(x) --> new label(u)*)
          let x_label = ARR.get !(ctx.ptt).labels x in 
          let u_label = ARR.get !(ctx.ptt).labels u in
          begin match Smt.entails Ctx.context (x_label) (u_label) with
          | `No | `Unknown -> 
            (* remove (x, u) from covering. *)
            if logging then Printf.printf "   refine: removing cover (%d->%d)\n" x u;
            !(ctx.ptt).covers := IntMap.remove x !(!(ctx.ptt).covers);
            (* add x's subtree leaves back to the worklist. *)
            let x_leaves = leaves !(ctx.ptt) x in 
              List.iter (fun x_leaf -> 
                if logging then Printf.printf "         refine: adding %d back to worklist \n" x_leaf;
                ctx.worklist := x_leaf %>> !(ctx.worklist)) x_leaves;
            ctx.ptt := {!(ctx.ptt) with models = IntMap.remove x !(ctx.ptt).models };
            l
          | `Yes ->
            if logging then begin 
              Printf.printf "    refine: cover (x %d-> u %d) still holds\n" x u;
              mypp_formula " x label: " [x_label];
              mypp_formula " u label: " [u_label]
            end;
          x :: coverers (* unchanged. *) 
          end
          ) [] l in 
            !(ctx.ptt).reverse_covers := IntMap.add u u_coverers !(!(ctx.ptt).reverse_covers)
      end
    ) path ( (K.one |> K.to_transition_formula |> TransitionFormula.formula) :: interpolants) 

  (* verify interpolant sequence is ok *)
  let verify_consecution_condition (interpolants: Ctx.t Srk.Syntax.formula list) (transitions: K.t list) = 
    let interpolants = (mk_true ()) :: interpolants in 
      let rec oneRest (i: Ctx.t Srk.Syntax.formula) (tr: K.t) i_rest tr_rest = 
        if logging then Printf.printf "verify_consecution_condition: verifying: \n";
        if logging then mypp_formula "interpolant: " [ i ];
        if logging then mypp_weights "transition: " [ tr ];
        begin match i_rest with 
        | [] -> failwith "ERROR in verify_consecution_condition: interpolants length does not match path condition length"
        | i' :: i_rest' -> 
            (* consecution: i /\ tr |= i' *)
            begin match K.valid_triple i [tr] i' with 
              | `Invalid | `Unknown -> 
                mypp_formula "bad interpolant: " [i; i'];
                failwith "ERROR in verify_consecution_condition: found non-consecutive interpolant, shown above"
              | `Valid -> 
                begin match tr_rest with 
                | [] -> 
                  if i_rest' <> [] then failwith "ERROR: interpolant length does not match transitions length\n";
                  begin match Smt.entails Ctx.context i' (mk_false()) with 
                  | `No | `Unknown -> failwith "ERROR: last interpolant does not imply false"
                  | `Yes -> ()
                  end
                | tr' :: tr_rest' -> 
                  oneRest i' tr' i_rest' tr_rest'
                end
            end
        end
      in 
        match interpolants with 
        | [] -> ()
        | i :: i_rest -> 
          begin match transitions with 
          | [] -> if i_rest <> [] then failwith "ERROR: transitions length and interpolants length do not match"
          | tr :: tr_rest -> oneRest i tr i_rest tr_rest 
          end

  (* refine path to node v. Returns false if unable to refine. *)
  let mc_refine (ctx: mc_context) (v: int) = 
    let path_condition = !(ctx.ptt) %-*> v in 
    let path = tree_path !(ctx.ptt) v in 
      match ctx.mode with 
      | PlainMcMillan -> 
        begin 
        match K.interpolate path_condition (Ctx.mk_false) with 
        | `Invalid | `Unknown -> 
          if logging then Printf.printf " *********************** REFINEMENT FAILED *************************\n"; false 
        | `Valid interpolants ->
          if logging then begin 
            Printf.printf "  refine: interpolant sequence for tree vertex %d: -----------\n" v;
            Printf.printf " original formula: ";
            mypp_weights "" path_condition;
            Printf.printf "--------------------------------------------------------------\n";
            mypp_formula "" interpolants;
            Printf.printf "--------------------------------------------------------------\n";
          end;
          (* verify_consecution_condition interpolants path_condition; *)
          mc_refine_with_interpolants ctx path interpolants;
          true  
        end 
        | ConcolicMcMillan -> 
        begin 
          match interpolate_or_get_model !(ctx.ptt) v ctx.err_loc with 
          `Invalid v_model -> 
            if logging then Printf.printf "Unable to refine but got model\n";
            ctx.ptt := {!(ctx.ptt) with models = IntMap.add v v_model !(ctx.ptt).models };
            false 
          | `Unknown -> failwith ""
          | `Valid interpolants -> 
            mc_refine_with_interpolants ctx path interpolants; 
            true 
        end

  (* Adds (v -> w) to covering relation if possible and returns true, false otherwise. *)
  (* note that (v, w) in covering if stateLabel(v) IMPLIES stateLabel(w) *)
  let mc_cover (ctx: mc_context) v w = 
    let v_label = ARR.get !(ctx.ptt).labels v in 
    let w_label = ARR.get !(ctx.ptt).labels w in
    if (!(ctx.ptt) %-> v) <> (!(ctx.ptt) %-> w) then 
      failwith @@ Printf.sprintf "error: %d->%d but %d->%d\n" v (!(ctx.ptt) %-> v) w (!(ctx.ptt) %-> w)
    else 
      if logging then Printf.printf "cover: %d->%d and %d->%d\n" v (!(ctx.ptt) %-> v) w (!(ctx.ptt) %-> w);
    match Smt.entails Ctx.context v_label w_label with 
    | `Yes -> 
      if logging then begin 
        Printf.printf "   cover success (v=%d, w=%d). \n" v w;
        mypp_formula "        v label " [v_label];
        mypp_formula "        w label "  [w_label]
      end;
      let reverse_covers_w = IntMap.find_default [] w !(!(ctx.ptt).reverse_covers) in 
        !(ctx.ptt).covers := IntMap.add v w !(!(ctx.ptt).covers);
        !(ctx.ptt).reverse_covers := IntMap.add w (v :: reverse_covers_w) !(!(ctx.ptt).reverse_covers);
        true
    | `No | `Unknown -> false    

  let mc_close (ctx: mc_context) (v : int) = 
    (* Visits precedents of v in tree and attempts to derive covering relations[].
      A _precedent_ of v in tree is any vertex u<v such that u, v map to the same CFG locations. *)
    let precedents = get_precedent_nodes !(ctx.ptt) v in
    (* Printf.printf "precedents of node %d : " v; List.iter (fun x -> Printf.printf " %d " x) precedents ; Printf.printf "\n";*)
    (* Fold from first node in preorder to the right. If covering succeeds, do not continue covering. *) 
    let result = List.fold_right (fun w status ->
      if status || w == v || w > v (* preorder constraint *) then status
      else begin 
        (* try to "cover v" by deciding if v --> w. If so, no need to further explore v. *)
        let cover_success = mc_cover ctx v w in 
        if cover_success then begin
          (* remove, for each descendant of v, nodes that are sinks of covers. *)
          let v_descendants = descendants !(ctx.ptt) v in 
            List.iter (fun y -> 
              (* Find relations (x,y) in covering relation where y is descendant of v. *)
              if y <> v then 
              begin 
                (* xs = {x | x -> y} *)
                let xs = IntMap.find_default [] y !(!(ctx.ptt).reverse_covers) in 
                (* Iterate through and remove pairs (x, y) from covering relation. *)
                (* Step 1: Remove (x |-> y) from !ptt.covers. *)
                List.iter (fun x -> !(ctx.ptt).covers := IntMap.remove x !(!(ctx.ptt).covers)) xs;
                (* Step 2: Remove (y |-> xs) from !pthit.reverse_covers. *)
                !(ctx.ptt).reverse_covers := IntMap.remove y !(!(ctx.ptt).reverse_covers);
                (* Step 3: add xs to worklist. *)
                List.iter (fun x ->
                  (* add x's subtree leaves back to the worklist. *)
                  let x_leaves = leaves !(ctx.ptt) x in 
                    List.iter (fun x_leaf -> 
                      if logging then Printf.printf "         close: adding %d back to worklist \n" x_leaf;
                      ctx.worklist := x_leaf %>> !(ctx.worklist)) x_leaves;
                  ctx.ptt := {!(ctx.ptt) with models = IntMap.remove x !(ctx.ptt).models } ) xs
              end) v_descendants
        end; cover_success
      end) precedents false in result 

  (* Checks if tree node v is covered. It is covered if its ancestors or it is in covering relation. *)
  let rec mc_is_covered (ctx: mc_context) v = 
    match IntMap.find_opt v !(!(ctx.ptt).covers) with 
    | None -> 
      if v == 0 then false
      else mc_is_covered ctx ((!(ctx.ptt)) %^ v)
    | Some u -> 
      if logging then Printf.printf "  | covered by %d\n" u;
      true 
  
  let tree_printer_get_name (ctx: mc_context) i = 
    match IntMap.find_opt i !(!(ctx.ptt).covers) with 
    | None ->  Printf.sprintf "%d(%d)" i (!(ctx.ptt) %-> i)
    | Some j -> Printf.sprintf "[%d(%d)]->%d" i (!(ctx.ptt) %->i) j

  let print_worklist (ctx: mc_context) = 
    Printf.printf "["; DQ.iter (fun x -> Printf.printf "%d " x) !(ctx.worklist); Printf.printf "]\n"

  let single_plain_mcmillan_round (ctx: mc_context) : mc_state = 
    match DQ.front !(ctx.worklist) with (* use DQ.rear if want BFS *) 
      | Some (u, w) (* (w, u) if use DQ.front *) ->          
        if logging then begin 
          Printf.printf " +----------------- ART ----------------+\n";
          let string_of_art = 
            Tree_printer.to_string 
              ~line_prefix:"* " 
              ~get_name:(tree_printer_get_name ctx) 
              ~get_children:(children !(ctx.ptt)) 0
            in Printf.printf "%s" string_of_art; 
          Printf.printf " +----------------- ART ----------------+\n";
          print_worklist ctx;
          Printf.printf " visit %d\n" u;
          mypp_formula "label: " [ARR.get !(ctx.ptt).labels u]; 
        end;
        ctx.worklist := w;
        (* Fetched tree node u from work list. First attempt to close it. *)
        if not (mc_is_covered ctx u) then begin
          if logging then Printf.printf " uncovered. try close\n";
          begin match mc_close ctx u with 
            | true -> (* Close succeeded. No need to further explore it. *)
              if logging then Printf.printf "Close succeeded.\n"; 
              (* ctx.worklist := u %>> !(ctx.worklist); *)
              McContinue 
            | false -> (* u is uncovered. *)
              if ((!(ctx.ptt)) %-> u) == ctx.err_loc then 
                begin match mc_refine ctx u with 
                  | true -> 
                    if logging then Printf.printf " refinement result: SUCCESS\n";
                    (* for every node along path of refinement try close *)
                    let path = tree_path !(ctx.ptt) u in 
                      List.iter (fun x -> let _ = mc_close ctx x in ()) path;
                      (* ctx.worklist := u %>> !(ctx.worklist); *)
                      McContinue
                  | false -> 
                    if logging then Printf.printf " refinement result: FAILURE\n";
                    McErrorReached
                end 
              else begin 
                if logging then Printf.printf " expanding...\n";
                mc_expand ctx u;
                McContinue
              end
          end end
        else begin if logging then Printf.printf "  | covered \n"; McContinue end
        | None -> failwith ""

  let verify_well_labelled_tree (t: ltree) = 
    let rec aux v =
      let children = ARR.get t.children v in 
      (*mypp_formula (Printf.sprintf "visiting %d, label: " v) [ ARR.get t.labels v ];*)
      match children with 
      | [] (* leaf node *) -> 
        begin match IntMap.find_opt v !(t.covers) with 
          | None -> 
            Printf.printf "!!! found uncovered leaf: %d\n" v;
            WG.fold_succ_e (fun (x, _, y) acc ->
              Printf.printf "  ERROR ERROR ERROR: mapped cfg vertex %d has out-neighbor %d\n" x y; 
              false 
            ) t.graph (ARR.get t.cfg_vertex v) true
          | Some _ -> true 
        end 
      | _ -> 
        begin match IntMap.find_opt v !(t.covers) with 
        | None -> 
          Printf.printf "node %d uncovered\n" v;
          List.fold_left (fun acc u -> (aux u) && acc) true children 
        | Some u -> 
          Printf.printf "node %d covered by %d\n" v u;
          true 
        end 
    in  aux 0

  let check_covering_welformedness (t: ltree) = 
    Printf.printf "checking welformedness of covering relations\n";
    IntMap.iter (fun dst covered_from -> 
      List.iter (fun src -> 
        Printf.printf "checking if (%d, %d) in covering\n" src dst;
        match IntMap.find_opt src !(t.covers) with 
        | Some dst' -> if dst' <> dst then failwith @@ Printf.sprintf "ERROR: (%d, %d) in covering\n" src dst'
        | None -> failwith "ERROR: not in covering"
      ) covered_from
    ) !(t.reverse_covers);
    Printf.printf "performing a reverse check\n";
    IntMap.iter (fun src dst -> 
      match IntMap.find_opt dst !(t.reverse_covers) with 
      | Some reverse_covers ->
        begin match List.mem src reverse_covers with 
        | false -> failwith @@ Printf.sprintf "ERROR: (%d, %d) in t.covers but %d not in %d's reverse_covers\n" src dst src dst
        | true -> ()
        end
      | None -> failwith @@ Printf.sprintf "ERROR: (%d, %d) in t.covers but no list found in reverse_covers\n" src dst
    ) !(t.covers)

  let plain_mcmillan_execute (ctx: mc_context) : mc_result = 
    let continue = ref true in
    let state = ref McContinue in begin
      while DQ.size !(ctx.worklist) > 0 && !continue do 
        begin 
          match single_plain_mcmillan_round ctx with 
          | McContinue -> continue := true; state := McContinue
          | McErrorReached -> 
            if logging then Printf.printf "  not continueing any further --- error reached\n";
            continue := false; state := McErrorReached
          | McWellLabeled -> continue := false; state := McWellLabeled
        end
      done;
      if logging then 
        begin 
        Printf.printf " +++++++++++++++++++++++++++++++++ Final ART +++++++++++++++++++++++++++++ \n";
        let string_of_art = 
            Tree_printer.to_string 
              ~line_prefix:"* " 
              ~get_name:(tree_printer_get_name ctx) 
              ~get_children:(children !(ctx.ptt)) 0
          in Printf.printf "%s" string_of_art
      end;
      match !state with 
      | McErrorReached -> McProvenUnsafe
      | McContinue -> 
      
        Printf.printf "execution saturated\n"; 
        begin match verify_well_labelled_tree !(ctx.ptt) with 
        | false -> failwith "ERROR: well-labelled check failed"
        | true -> check_covering_welformedness !(ctx.ptt) end;
        McProvenSafe
      | _ -> McProvenSafe
    end

  let concolic_mcmillan_execute (ctx: mc_context) : mc_result = 
    let continue = ref true in 
    let state = ref McContinue in
      while !continue && (DQ.size !(ctx.worklist) > 0 || DQ.size !(ctx.execlist) > 0) do
        if logging then Printf.printf " continuing...\n";
        if DQ.size !(ctx.execlist) > 0 then begin 
          match DQ.front !(ctx.execlist) with 
          | Some (u, w) -> 
            if logging then begin 
              Printf.printf " +----------------- ART ----------------+\n";
              let string_of_art = 
                Tree_printer.to_string 
                  ~line_prefix:"* " 
                  ~get_name:(tree_printer_get_name ctx) 
                  ~get_children:(children !(ctx.ptt)) 0
                in Printf.printf "%s" string_of_art; 
              Printf.printf " +----------------- ART ----------------+\n";
              Printf.printf " visit %d (%d)\n" u (!(ctx.ptt) %-> u);
            end;
            if (!(ctx.ptt) %-> u) = ctx.err_loc then 
              begin continue := false; state := McErrorReached end
            else begin
              ctx.execlist := w;
              if logging then begin 
                Printf.printf "model of %d: \n" u;
                Interpretation.pp Format.std_formatter (IntMap.find u !(ctx.ptt).models) 
              end;
              mc_expand ctx u 
            end
          | None -> failwith "" (* cannot happen *)
        end else begin 
          match DQ.front !(ctx.worklist) with 
          | Some (u, w) -> 
            if logging then begin 
              Printf.printf " +----------------- ART ----------------+\n";
              let string_of_art = Tree_printer.to_string ~line_prefix:"* " ~get_name:(tree_printer_get_name ctx) ~get_children:(children !(ctx.ptt)) 0
                in Printf.printf "%s" string_of_art; 
                Printf.printf " +----------------- ART ----------------+\n";
                Printf.printf " visit frontier %d (%d)\n" u (!(ctx.ptt) %-> u);
            end;
            ctx.worklist := w;
            (* Fetched tree node u from work list. First attempt to close it. *)
            if not (mc_is_covered ctx u) then begin
              if logging then Printf.printf " uncovered. try close\n";
              begin match mc_close ctx u with 
                | true -> (* Close succeeded. No need to further explore it. *)
                  if logging then Printf.printf "Close succeeded.\n"; ()
                | false -> (* u is uncovered. *)
                  if true (* ((!ptt) %-> u) == err_loc *) then 
                    begin 
                      continue := mc_refine ctx u;
                      if (!continue) == false then 
                        begin 
                          ctx.execlist := u %>> !(ctx.execlist)  (* put u onto execlist since it now has a model. *)
                        end;
                      continue := true;
                    (* for every node along path of refinement try close *)
                    let path = tree_path !(ctx.ptt) u in 
                      List.iter (fun x -> let _ = mc_close ctx x in ()) path 
                    end 
                  else begin 
                    if logging then Printf.printf " expanding...\n";
                    mc_expand ctx u
                  end
            end end
          | None -> failwith "" (* cannot happen *)
        end
      done; 
      match !state with 
      | McErrorReached -> McProvenUnsafe
      | _ -> McProvenSafe


  let mc_exec (mode: mc_mode) (ts : cfg_t) (entry : int) (err_loc : int) : mc_result = 
    (**
    * Set up data structures used by the algorithm: worklist, 
    * vtxcnt (keeps track of largest unused vertex number in tree), 
    * ptt is a pointer to the reachability tree.
    *)
  (* mode: 1 -> concolic McMillan; 0 -> plain McMillan *)
    let ctx = mk_mc_context mode ts entry err_loc in 
      !ctx.worklist := begin
        match mode with 
        | PlainMcMillan -> (0 %>> DQ.empty)
        | ConcolicMcMillan -> DQ.empty
      end;
      !ctx.execlist := begin
        match mode with 
        | PlainMcMillan -> DQ.empty 
        | ConcolicMcMillan -> 0 %>> DQ.empty
      end;
      !ctx.vtxcnt := 1;
      !ctx.ptt := { 
          !(!ctx.ptt) with 
          graph = ts; 
          entry = entry; 
          cfg_vertex = ARR.singleton entry ; 
          parents = ARR.singleton (-1) ;
          labels = ARR.singleton (mk_true ());
          covers = ref IntMap.empty;
          reverse_covers = ref IntMap.empty; (* reverse_covers[y] returns all x such that (x,y) is in the cover. *)
          children = ARR.singleton [] ;
          precedent_nodes = ref IntMap.empty; (* precedent_nodes[v] stores all tree nodes mapping to CFG vertex v. Used in mc_close. *)
          models = IntMap.empty
      };
      match mode with 
        | PlainMcMillan -> 
          Printf.printf "executing plain mcmillan\n..."; 
          plain_mcmillan_execute (!ctx)
        | ConcolicMcMillan -> 
          Printf.printf "getting initial abstract model...\n";
          begin match get_initial_abstract_model ~solver:!(!ctx.ptt).solver entry err_loc ts with 
          | `Sat m -> 
            Printf.printf "good. continuing...\n";
            !ctx.ptt := {!(!ctx.ptt) with models = IntMap.add 0 m !(!ctx.ptt).models}; 
            concolic_mcmillan_execute (!ctx)
          | _ -> 
            Printf.printf "Proven safe by path summary.\n"; 
            McProvenSafe
          end


  end


(**
  Directed algebraic concolic executor guided by path summaries in CRA
 *)
module Executor = struct 
  (** context and state information of the concolic executor. *)
  type exec_context = {
    ts: cfg_t; (** underlying transition system (control-flow graph) *)
    entry: int; (** entry vertex of the transition system *)
    err_loc: int; (** error location of the transtion system *)
    solver: Ctx.t Srk.Smt.Solver.t; (** persistent solver state object, prevents Z3 from allocating per SMT call *)
    worklist: int DQ.t ref; (** worklist of the solver, implemented as front-to-back deque. *)
    ptt: mtree ref; (** past explored paths tree. *)
    unsafe: bool ref; (** whether the assertion-violation state is reached. If unsafe==true, then found counterexample. *)
    vtxcnt: int ref;
  }
  (* set of paths explored by concolic executor. *)
  and mtree = {
    graph : cfg_t;
    entry : int;
    cfg_vertex : int ARR.t;
    parents : int ARR.t; 
    model : Ctx.t Interpretation.interpretation IntMap.t;
  }
  (* executor state *)
  and executor_state = 
    | Continue 
    | ProvenUnsafe
    | ProvenSafe
  (* result of an execution *)
  and execution_result = 
    | ExecutorResultSafe
    | ExecutorResultUnsafe
    | ExecutorResultUnknown

  (* make a reference to an empty mtree. *)
  let mk_mtree_ptr (ts: cfg_t) (entry: int) = ref { 
      graph = ts; 
      entry = entry; 
      cfg_vertex = ARR.singleton entry ; 
      parents = ARR.singleton (-1) ;
      model  = IntMap.empty (* IntMap.singleton 0 initial_model *) }
  
  (* make an execution context *)
  let mk_context (ts: cfg_t) (entry: int) (err_loc: int) : exec_context = 
    { ts = ts;
      entry = entry; 
      err_loc = err_loc; 
      solver = Smt.mk_solver Ctx.context;
      worklist = ref DQ.empty;
      unsafe = ref false;
      ptt = mk_mtree_ptr ts entry;
      vtxcnt = ref 0; }

  (** some miscellaneous helper operators *)

  (* shove an element into front of an int deque *)
  let (%>>) (i : int)  (q : idq_t) = DQ.cons i q

  (* get parent of a node in mtree *)
  let (%^) (t : mtree) (i : int) = ARR.get t.parents i 

  (* get cfg vertex mapped by mtree node *)
  let (%->) (t : mtree) (i : int) = ARR.get t.cfg_vertex i 

  (* get edge weight in CFG of (t%->u, t%->v) in mtree t. *)
  let ew (t : mtree) u v = match WG.edge_weight t.graph u v with  Weight w -> w  | Call _ -> failwith "call unimplemented" 


  (* get path weight sequence in CFG mapped by tree path 0---->u in mtree t *)
  let rec (%-*>) (t: mtree) (u : int) : K.t list = 
    if u == 0 then [ ]
    else let rec (%<*-) (t : mtree) (u : int) =
     match t %^ u with 
      | 0 -> [ ew t (t %-> 0) (t %-> u) ] 
      | v -> ew t (t %-> v) (t %-> u) :: (t %<*- v) in 
      List.rev (t %<*- u)

  (* out neighbors of a vertex u in cfg g. *)
  let get_out_neighbors (g : cfg_t) (u : int) = 
    WG.fold_succ_e (fun (x, weight, y) l -> 
      if x <> u then failwith "will not happen" 
      else (weight, y) :: l) g u [] 
  
  (* retrieve the initial path-to-error abstract model between source and err loc in CFG. *)
  let get_initial_abstract_model ?(solver=Smt.mk_solver Ctx.context) (src : int) (sink : int) (graph : cfg_t) = 
    let query = mk_query graph src in 
    let path = TS.path_weight query sink in 
    let path_condition = K.guard path in 
    let path_condition_symbols = Syntax.symbols path_condition |> MonotoneDom.SymbolSet.elements in 
      Smt.get_concrete_model Ctx.context ~solver:(solver) path_condition_symbols path_condition 

  (* retrieve abstract model from some intermediate CFG vertex v --> err_loc, provided with pre-condition to vertex v. *)
  let get_abstract_model ?(solver=Smt.mk_solver Ctx.context) pre_condition (src : int) (sink : int) (graph : cfg_t) = 
    let query = mk_query graph src in 
    let post_condition = TS.path_weight query sink |> K.guard |> K.assume in 
    let condition = K.mul pre_condition post_condition in 
    let condition_tf = K.to_transition_formula condition in 
    let post_pre_symbols = List.fold_right (fun (x, y) l -> (y, x) :: l) (TransitionFormula.symbols condition_tf) [] in 
    let condition_formula = TransitionFormula.formula condition_tf in 
    let condition_symbols = Syntax.symbols condition_formula |> MonotoneDom.SymbolSet.elements in 
    match Smt.get_concrete_model Ctx.context ~solver:(solver) condition_symbols condition_formula with 
      | `Sat itp ->
        logf ~level:`always "Interpretation: %a\n" Interpretation.pp itp ;
        let m = Interpretation.enum itp in 
        let itp' = BatEnum.fold (fun itp' (symb, v) -> 
          let pre_symb = List.assoc symb post_pre_symbols in 
          Interpretation.add pre_symb v itp' ) (Interpretation.empty Ctx.context) m in 
          logf ~level:`always "InterpretationPRIME: %a\n" Interpretation.pp itp'; 
          Some itp'
      | `Unknown -> None 
      | `Unsat -> None

  (** concolic execution procedure subroutines *)

  (* do execution loop for a single iterate *)
  let execute_single_round (ctx: exec_context) : executor_state =
    if !(ctx.unsafe) then begin
      ProvenUnsafe 
    end
    else begin 
      begin match DQ.front !(ctx.worklist) with 
        | Some (tx, w') -> 
          let x = ARR.get !(ctx.ptt).cfg_vertex tx in
          ctx.worklist := w'; (* Pop x off front of list. *)
          if x == ctx.err_loc then begin 
            ctx.unsafe := true;
            ProvenUnsafe
          end else 
            let x_model = IntMap.find tx !(ctx.ptt).model in 
            let x_out_neighbors = get_out_neighbors !(ctx.ptt).graph x in 
              List.iter (fun (weight, y) -> 
                let weight = match weight with Weight w -> w | Call _ -> failwith "cannot handle call" in 
                Smt.Solver.reset ctx.solver;
                begin match K.get_post_model ~solver:(ctx.solver) x_model weight with 
                | Some y_model ->   
                      ARR.add !(ctx.ptt).cfg_vertex y;
                      ARR.add !(ctx.ptt).parents tx;
                      ctx.ptt := {!(ctx.ptt) with model = IntMap.add !(ctx.vtxcnt) y_model !(ctx.ptt).model};
                      ctx.worklist := !(ctx.vtxcnt) %>> !(ctx.worklist);
                      ctx.vtxcnt := !(ctx.vtxcnt) + 1 
                | None ->
              let _ = get_out_neighbors !(ctx.ptt).graph y in 
                  try begin 
                    let pre_condition = !(ctx.ptt) %-*> y in 
                    let pre_condition = 
                      match pre_condition with 
                      | a :: t -> List.fold_right (fun x y -> K.mul y x) t a
                      | [] -> K.one 
                    in 
                    Smt.Solver.reset ctx.solver;
                    match get_abstract_model ~solver:(ctx.solver) pre_condition y ctx.err_loc !(ctx.ptt).graph with 
                      | Some y_model ->
                        ARR.add !(ctx.ptt).cfg_vertex y; 
                        ARR.add !(ctx.ptt).parents tx;
                        ctx.ptt := {!(ctx.ptt) with model = IntMap.add !(ctx.vtxcnt) y_model !(ctx.ptt).model};
                        ctx.worklist := !(ctx.vtxcnt) %>> !(ctx.worklist);
                        ctx.vtxcnt := !(ctx.vtxcnt) + 1; () ;
                      | _ -> () 
                      end with _ -> ()
                end
                ) x_out_neighbors;
                (* Can safely remove current node from the tree. *) 
                ctx.ptt := {!(ctx.ptt) with model = IntMap.remove tx !(ctx.ptt).model };
                Continue
        | None -> failwith "cannot happen" 
        end
      end


  (* entry to concolic execution procedure *)
  let go (ctx: exec_context) : execution_result = 
    begin match get_initial_abstract_model ~solver:(ctx.solver) ctx.entry  ctx.err_loc ctx.ts with 
    | `Sat initial_model ->
        begin
        (* (re-)initialize executor state to put first vertex on worklist. *)
          ctx.worklist := (0 %>> DQ.empty);
          ctx.vtxcnt := 1;
          ctx.ptt := {!(ctx.ptt) with model = (IntMap.singleton 0 initial_model) };
          ctx.unsafe := false;
          let post_state = ref Continue in 
            while (DQ.size !(ctx.worklist) > 0) (*&& not !unsafe*) do 
              post_state := execute_single_round ctx 
            done;
            begin match !post_state with 
            | Continue -> ExecutorResultUnknown 
            | ProvenSafe -> ExecutorResultSafe 
            | ProvenUnsafe -> ExecutorResultUnsafe
            end
        end
    | `Unsat -> 
      ExecutorResultSafe 
    | `Unknown -> 
      ExecutorResultUnknown
    end
  end (* end of Executor module *)


module BM = BatMap.Make(Int)

let test_interpolate_path (g : cfg_t) (entry : int) (err_loc : int) = 
  let parents = ref BM.empty in 
  let weights = ref BM.empty in 
  let rec gatherDFS v err_loc p = 
    Printf.printf "gatherDFS: visiting node %d\n" v ; 
    parents := BM.add v p !parents;
    if v == err_loc then ()
    else
      WG.iter_succ_e (fun (_, weight, y) -> 
        (* If y is unvisited, then visit it. *)
        match BM.find_opt y !parents with 
        | None -> 
          let weight = match weight with | Call _ -> failwith "" | Weight w -> w in 
          weights := BM.add y weight !weights;
          gatherDFS y err_loc v
        | Some _ -> ()
        ) g v
  in 
  let rec getPathCond u = 
    Printf.printf "Path node %d, parent %d\n" u (BM.find u !parents);
    if u = entry then begin Printf.printf "returning...\n" ; [] end
    else begin
      let u_weight = BM.find u !weights in 
      u_weight :: (getPathCond @@ BM.find u !parents) end
    in 
      parents := BM.add entry (-1) !parents;
      gatherDFS entry err_loc (-1);
      let path_cond = getPathCond err_loc in 
      let path_cond = List.rev path_cond in 
      Printf.printf "...Got path condition\n";
      mypp_weights "Path condition is: " path_cond;
      let interpolants = K.interpolate [ K.zero ] (mk_false ()) in 
      match interpolants with 
      | `Invalid -> Printf.printf " --- invalid\n"
      | `Unknown -> Printf.printf "  --- unknown\n"
      | `Valid interpolants ->
        mypp_formula " *** Interpolants: " interpolants 


let analyze_concolic file = 
  populate_offset_table file;
  match file.entry_points with
  | [main] -> begin
      let rg = Interproc.make_recgraph file in
      let entry = (RG.block_entry rg main).did in
      let (ts, assertions) = make_transition_system true rg in
      let ts, new_vertices = make_ts_assertions_unreachable ts assertions in 
      TSDisplay.display ts;
      Printf.printf "\nentry: %d\n" entry; 
      List.iter (fun err_loc ->
        let ectx = Executor.mk_context ts entry err_loc in 
          match Executor.go ectx with 
          | Executor.ExecutorResultSafe -> 
            Printf.printf "assertion@%d: safe\n" err_loc
          | Executor.ExecutorResultUnsafe ->
            Printf.printf "assertion%d: unsafe\n" err_loc
          | Executor.ExecutorResultUnknown -> 
            Printf.printf "assertion%d: unknown\n" err_loc
        ) new_vertices 
      end
  | _ -> assert false

(* driver for plain mcmillan *)
let analyze_plain_mcl file = 
  populate_offset_table file;
  match file.entry_points with
  | [main] -> begin

      let rg = Interproc.make_recgraph file in
      let entry = (RG.block_entry rg main).did in
      let (ts, assertions) = make_transition_system true rg in
      let ts, new_vertices = make_ts_assertions_unreachable ts assertions in 
      TSDisplay.display ts;
      Printf.printf "\nentry: %d\n" entry; 
     (* List.iter (fun err_loc -> 
        Printf.printf "Processing erro %d-----------------------------\n" err_loc;
        test_interpolate_path ts entry err_loc 
        ) new_vertices*)
      List.iter (fun err_loc ->
        Printf.printf "testing reachability of location %d\n" err_loc ; 
        Printf.printf "------------------------------\n";
        match McMillanChecker.mc_exec McMillanChecker.PlainMcMillan ts entry err_loc with 
        | McMillanChecker.McProvenSafe -> Printf.printf "  proven safe\n"
        | McMillanChecker.McProvenUnsafe -> Printf.printf "  proven unsafe\n"
        | McMillanChecker.McError -> Printf.printf "  mcmillan error\n";
        Printf.printf "------------------------------\n"
        ) new_vertices 
      end
  | _ -> assert false

(* driver for concolic mcmillan *)
let analyze_concolic_mcl file = 
  populate_offset_table file;
  match file.entry_points with
  | [main] -> begin

      let rg = Interproc.make_recgraph file in
      let entry = (RG.block_entry rg main).did in
      let (ts, assertions) = make_transition_system true rg in
      let ts, new_vertices = make_ts_assertions_unreachable ts assertions in 
      TSDisplay.display ts;
      Printf.printf "\nentry: %d\n" entry; 
     (* List.iter (fun err_loc -> 
        Printf.printf "Processing erro %d-----------------------------\n" err_loc;
        test_interpolate_path ts entry err_loc 
        ) new_vertices*)
      List.iter (fun err_loc ->
        Printf.printf "testing reachability of location %d\n" err_loc ; 
        Printf.printf "------------------------------\n";
        match McMillanChecker.mc_exec McMillanChecker.ConcolicMcMillan ts entry err_loc with 
        | McMillanChecker.McProvenSafe -> Printf.printf "  proven safe\n";
        | McMillanChecker.McProvenUnsafe -> Printf.printf "  proven unsafe\n";
        | McMillanChecker.McError -> Printf.printf "  mcmillan error\n";
        Printf.printf "------------------------------\n"
        ) new_vertices 
      end
  | _ -> assert false

(** dump simplified CFG before doing model checking / CRA / concolic execution *)
let dump_cfg simplify file = 
  populate_offset_table file;
  match file.entry_points with 
  | [main] ->
    begin 
      let rg = Interproc.make_recgraph file in 
      let entry = (RG.block_entry rg main).did in 
      let (ts, assertions) = make_transition_system simplify rg in 
      let ts, _ = make_ts_assertions_unreachable ts assertions in 
      TSDisplay.display ts
    end
  | _ -> assert false




let analyze file =
  populate_offset_table file;
  match file.entry_points with
  | [main] -> begin
      let rg = Interproc.make_recgraph file in
      let entry = (RG.block_entry rg main).did in
      let (ts, assertions) = make_transition_system true rg in

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
  mk_and srk [SrkSimplify.eliminate_floor srk (K.guard transition);
              substitute_const srk subst formula]

(* Attractor region analysis *)
let attractor_regions tf =
  let open Syntax in
  let formula = TF.formula tf in
  let attractors =
    BatList.fold_left (fun xs (x, x') ->
        let (x, x') = mk_const srk x, mk_const srk x' in
        let lo =
          let nonincreasing = mk_and srk [formula; mk_leq srk x' x] in
          match SrkZ3.optimize_box srk (mk_and srk [formula; nonincreasing]) [x'] with
          | `Sat [ivl] ->
             (match Interval.lower ivl with
              | Some lo -> [mk_leq srk (mk_real srk lo) x]
              | None -> [])
          | _ -> []
        in
        let hi =
          let nondecreasing = mk_and srk [formula; mk_leq srk x x'] in
          match SrkZ3.optimize_box srk (mk_and srk [formula; nondecreasing]) [x'] with
          | `Sat [ivl] ->
             (match Interval.upper ivl with
              | Some hi -> [mk_leq srk x (mk_real srk hi)]
              | None -> [])
          | _ -> []
        in
        (lo@hi@xs))
      []
      (TF.symbols tf)
  in
  TF.map_formula (fun _ -> mk_and srk (formula::attractors)) tf


let omega_algebra = function
  | `Omega transition ->
     (** over-approximate possibly non-terminating conditions for a transition *)
     begin
       let open Syntax in
       let tf =
         TF.map_formula
           (fun phi -> SrkSimplify.eliminate_floor srk (Nonlinear.linearize srk phi))
           (K.to_transition_formula transition)
       in
       let nonterm tf =
         let pre =
           let fresh_skolem =
             Memo.memo (fun sym -> mk_const srk (dup_symbol srk sym))
           in
           let subst sym =
             match V.of_symbol sym with
             | Some _ -> mk_const srk sym
             | None -> fresh_skolem sym
           in
           substitute_const srk subst (TF.formula tf)
         in
         let llrf, has_llrf =
           if !termination_llrf then
             if TLLRF.has_llrf srk tf then
               [Syntax.mk_false srk], true
             else if !termination_attractor
                     && TLLRF.has_llrf srk (attractor_regions tf) then
               [Syntax.mk_false srk], true
             else
               [pre], false
           else
             (* If LLRF is disabled, default to pre *)
             [pre], false
         in
         let dta =
           (* If LLRF succeeds, then we do not try dta *)
           if (not has_llrf) && !termination_dta then
             [mk_not srk (TDTA.mp srk tf)]
           else []
         in
         let exp =
           if (not has_llrf) && !termination_exp then
             let mp =
               Syntax.mk_not srk
                 (TerminationExp.mp (module Iteration.LossyTranslation) srk tf)
             in
             let dta_entails_mp =
               (* if DTA |= mp, DTA /\ MP simplifies to DTA *)
               Syntax.mk_forall_consts
                 srk
                 (fun _ -> false)
                 (Syntax.mk_if srk (mk_and srk dta) mp)
             in
             match Quantifier.simsat srk dta_entails_mp with
             | `Sat -> []
             | _ -> [mp]
           else []
         in
         let result =
           Syntax.mk_and srk (llrf@dta@exp)
         in
         let file = get_gfile () in
         if !dump_goals
            && result <> (Syntax.mk_true srk)
            && result <> (Syntax.mk_false srk) then begin
             let filename =
               Format.sprintf "%s-%d-term.smt2"
                 (Filename.chop_extension (Filename.basename file.filename))
                 (!nb_goals)
          in
          let chan = Stdlib.open_out filename in
          let formatter = Format.formatter_of_out_channel chan in
          logf ~level:`always "Writing goal formula to %s" filename;
          Syntax.pp_smtlib2 srk formatter result;
          Format.pp_print_newline formatter ();
          Stdlib.close_out chan;
          incr nb_goals
           end;
         match Quantifier.simsat srk result with
         | `Unsat -> mk_false srk
         | _ -> result
       in
       if !termination_phase_analysis then begin
           let predicates =
             (* Use variable directions & signs as candidate invariants *)
             List.map (fun (x,x') ->
                 let x = mk_const srk x in
                 let x' = mk_const srk x' in
                 [mk_lt srk x x';
                  mk_lt srk x' x;
                  mk_eq srk x x'])
               (TF.symbols tf)
             |> List.concat
           in
           Iteration.phase_mp srk predicates tf nonterm
         end else
         nonterm tf
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
    | `Atom (`Arith (`Eq, x, y)) -> (0, mk_eq srk x y)
    | `Atom (`Arith (`Lt, x, y)) -> (0, mk_lt srk x y)
    | `Atom (`Arith (`Leq, x, y)) -> (0, mk_leq srk x y)
    | `Atom (`ArrEq (a, b)) -> (0, mk_arr_eq srk a b)
    | `And conjuncts ->
       let max_nb = List.fold_left max 0 (List.map fst conjuncts) in
       let shift_conjuncts =
         conjuncts |> List.map (fun (nb,phi) ->
                     let shift = max_nb - nb in
                     substitute srk (fun (i, typ) -> mk_var srk (i + shift) typ) phi)
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
                              [substitute srk (fun (i, typ) -> mk_var srk (i + shift) typ) phi;
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
      let (ts, _) = make_transition_system true rg in
      if !CmdLine.display_graphs then
        TSDisplay.display ts;
      let query = mk_query ts entry in
      let omega_paths_sum =
        TS.omega_path_weight query omega_algebra
        |> (if !termination_prenex
            then lift_universals srk
            else fun x -> x)
        |> SrkSimplify.simplify_terms srk
      in
      if !dump_goals
         && omega_paths_sum <> (Syntax.mk_true srk)
         && omega_paths_sum <> (Syntax.mk_false srk) then begin
          let filename =
            Format.sprintf "%s-%d-term.smt2"
              (Filename.chop_extension (Filename.basename file.filename))
              (!nb_goals)
          in
          let chan = Stdlib.open_out filename in
          let formatter = Format.formatter_of_out_channel chan in
          logf ~level:`always "Writing goal formula to %s" filename;
          Syntax.pp_smtlib2 srk formatter omega_paths_sum;
          Format.pp_print_newline formatter ();
          Stdlib.close_out chan
        end;
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
      let (ts, _) = make_transition_system true rg in
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
                  logf ~level:`always "%a <= cost" (Syntax.ArithTerm.pp srk) lower;
                  logf ~level:`always "%a is o(%a)"
                    Varinfo.pp procedure
                    BigO.pp (BigO.of_arith_term srk lower)
                | None -> ()
              end;
              begin match upper with
                | Some upper ->
                  logf ~level:`always "cost <= %a" (Syntax.ArithTerm.pp srk) upper;
                  logf ~level:`always "%a is O(%a)"
                  Varinfo.pp procedure
                  BigO.pp (BigO.of_arith_term srk upper)
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
                                 (LossyTranslation))
         else
           K.domain := (module Product
                                 (Product(Vas)(PolyhedronGuard))
                                 (LossyTranslation))),
     " Use VAS abstraction");
  CmdLine.register_config
    ("-cra-vass",
     Arg.Unit (fun () ->
         let open Iteration in
         K.domain := (module Product(Product(LossyTranslation)(PolyhedronGuard))(Vass))),
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
         K.domain := (module Product(LossyTranslation)(PolyhedronGuard))),
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
     ("-termination-no-prenex",
      Arg.Clear termination_prenex,
      " Disable prenex conversion");
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
    ("-rba", resource_bound_analysis, " Resource bound analysis");
  CmdLine.register_pass 
    ("-concolic", analyze_concolic, " Concolic executor");
  CmdLine.register_pass 
    ("-mcl-plain", analyze_plain_mcl, " Plain McMillan");
  CmdLine.register_pass 
    ("-mcl-concolic", analyze_concolic_mcl, " Combined McMillan+Concolic execution algorithm");
  CmdLine.register_pass
    ("-dump-simplified-cfg", dump_cfg true, " Dump simplified control-flow-graph before analysis");
  CmdLine.register_pass
    ("-dump-unsimplified-cfg", dump_cfg false, " Dump unsimplified control-flow-graph of the input program")

open Core
open Apak
open Srk
open CfgIr
open BatPervasives

module RG = Interproc.RG
module WG = WeightedGraph
module G = RG.G
module Ctx = Srk.Syntax.MakeSimplifyingContext ()
module Int = SrkUtil.Int

let srk = Ctx.context

include Log.Make(struct let name = "cra" end)

let forward_inv_gen = ref true
let dump_goals = ref false
let prsd = ref false
let cra_refine = ref false
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
    Syntax.pp_smtlib2 srk formatter path_condition;
    Format.pp_print_newline formatter ();
    Pervasives.close_out chan;
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


module IterDomain = struct
  open Iteration
  open SolvablePolynomial
  module SPOne = SumWedge (SolvablePolynomial) (SolvablePolynomialOne) ()
  module SPG = ProductWedge (SPOne) (WedgeGuard)
  module SPPeriodicRational = Sum (SPG) (PresburgerGuard) ()
  module LinRec = Product (LinearRecurrenceInequation) (PolyhedronGuard)
  module D = Sum(SPPeriodicRational)(LinRec)()
  module SPSplit = Sum(D) (Split(D)) ()
  include SPSplit
end

module MakeTransition (V : Transition.Var) = struct
  include Transition.Make(Ctx)(V)

  module I = Iter(Iteration.MakeDomain(IterDomain))

  let star x = Log.time "cra:star" I.star x

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

module K = struct
  module Tr = MakeTransition(V)
  include Tr


  module CRARefinement = Refinement.DomainRefinement
      (struct
        include Tr
        let star = I.star

        (*let star x = Log.time "refine" I.star x*)

        let equal a b = ((Wedge.is_sat srk (guard a)) == `Unsat)
      end)

  let refine_star x = 
    let nnf_guard = Syntax.rewrite srk ~down:(Syntax.nnf_rewriter srk) (guard x) in
    (*Format.eprintf "  Top-level formula:  %a  \n" (Syntax.Formula.pp srk) nnf_guard;*)
    let to_dnf form = 
      match form with
      | `And top_and_list ->
        let dnf_form_no_labels = (* list list list *)
          List.map
            (fun top_and_child ->
              match Syntax.Formula.destruct srk top_and_child with
              | `Or or_list ->
                List.map
                  (fun or_child ->
                    match Syntax.destruct srk or_child with
                    | `And leaf -> leaf
                    | _ -> [or_child]
                  ) or_list
              | `And and_list -> [and_list]
              | _ -> [[top_and_child]]
            ) top_and_list
          in
        let cartesian_prod =
          let cartesian a b = List.concat (List.map (fun e1 -> List.map (fun e2 -> (e1 @ e2)) b) a) in 
          List.fold_left cartesian ([([])])
          in
        let distributed_list = cartesian_prod dnf_form_no_labels in (* list list *)
        Syntax.mk_or srk (List.map (Syntax.mk_and srk) distributed_list)
      | `Or dnf_list ->
        Syntax.mk_or srk
          (List.concat
            (List.map
              (fun or_of_ands ->
                match Syntax.Formula.destruct srk or_of_ands with
                | `Or list_of_ands -> list_of_ands
                | _ -> [or_of_ands]
              ) dnf_list
            )
          )
      | `Tru -> Syntax.mk_true srk
      | `Fls -> Syntax.mk_false srk
      | `Not x -> Syntax.mk_not srk x
      | `Quantify (`Exists, str, typ, x) -> Syntax.mk_exists srk ~name:str typ x
      | `Quantify (`Forall, str, typ, x) -> Syntax.mk_forall srk ~name:str typ x
      | `Atom (`Eq, left, right) -> Syntax.mk_eq srk left right
      | `Atom (`Leq, left, right) -> Syntax.mk_leq srk left right
      | `Atom (`Lt, left, right) -> Syntax.mk_lt srk left right
      | _ -> failwith "Don't support Prop, Ite"
    in
    let dnf_guard = Syntax.Formula.eval_memo srk to_dnf nnf_guard in
    let (guard_dis, one_dis) = 
      (match Syntax.Formula.destruct srk dnf_guard with
      | `Or disjuncts -> (disjuncts, false)
      | _ -> ([dnf_guard], true)
      )
      in
    (*Format.eprintf " UnsimpGuard dnf size : %d\n Formula:  %a\n%!" (List.length guard_dis) (Syntax.Formula.pp srk) dnf_guard;*)
    if one_dis then I.star x
    else
      let rec build_dnf needed_dis disjuncts =
        match disjuncts with
        | [] -> (needed_dis, false)
        | new_dis :: tl -> 
          let cur_dnf = Syntax.mk_or srk needed_dis in
          (match Smt.entails srk (guard x) cur_dnf with
          | `Yes -> (needed_dis, false)
          | `Unknown -> ([], true)
          | `No ->
            (match Smt.entails srk cur_dnf new_dis with
            | `Yes -> build_dnf [new_dis] tl
            | `Unknown -> ([], true)
            | `No ->
              (match Smt.entails srk new_dis cur_dnf with
              | `Yes -> build_dnf needed_dis tl
              | `Unknown -> ([], true)
              | `No -> build_dnf (new_dis :: needed_dis) tl)
            )
          ) 
        in
      let (needed_dis, bailed) = build_dnf [] guard_dis in
      if bailed then 
        I.star x
      else (
        (*Format.eprintf " SimpGuard dnf size : %d\n Formula:  %a\n%!" (List.length needed_dis) (Syntax.Formula.pp srk) (Syntax.mk_or srk needed_dis);*)
        let x_tr = BatEnum.fold (fun acc a -> a :: acc) [] (transform x) in
        let x_dnf = List.map (fun disjunct -> construct disjunct x_tr) needed_dis in
        if (List.length x_dnf) = 1 then I.star (List.hd x_dnf)
        else
          let result = CRARefinement.refinement x_dnf in
          result)    

  let to_dnf x =
    let open Syntax in
    let guard =
      rewrite srk
        ~down:(nnf_rewriter srk)
        ~up:(Nonlinear.uninterpret_rewriter srk)
        (guard x)
    in
    let x_tr = BatEnum.fold (fun acc a -> a :: acc) [] (transform x) in
    let solver = Smt.mk_solver srk in
    let rhs_symbols =
      BatEnum.fold (fun rhs_symbols (_, t) ->
          Symbol.Set.union rhs_symbols (symbols t))
        Symbol.Set.empty
        (transform x)
    in
    let project x =
      match V.of_symbol x with
      | Some _ -> true
      | None -> Symbol.Set.mem x rhs_symbols
    in
    Smt.Solver.add solver [guard];
    let rec split disjuncts =
      match Smt.Solver.get_model solver with
      | `Unknown -> [x]
      | `Unsat ->
        BatList.filter_map (fun guard ->
            let interp_guard = Nonlinear.interpret srk guard in
            if Wedge.is_sat srk interp_guard = `Unsat then
              None
            else
              Some (construct interp_guard x_tr))
          disjuncts
      | `Sat m ->
        let disjunct =
          match Interpretation.select_implicant m guard with
          | Some implicant ->
            let cs = CoordinateSystem.mk_empty srk in
            Polyhedron.of_implicant ~admit:true cs implicant
            |> Polyhedron.try_fourier_motzkin cs project
            |> Polyhedron.implicant_of cs
            |> mk_and srk
          | None -> assert false
        in
        Smt.Solver.add solver [mk_not srk disjunct];
        split (disjunct::disjuncts)
    in
    split []

  let refine_star x =
    (* let x_dnf = to_dnf x in *)
    let x_dnf = Log.time "cra:to_dnf" to_dnf x in
    if (List.length x_dnf) = 1 then I.star (List.hd x_dnf)
    else CRARefinement.refinement x_dnf

  let star x = 
    if (!cra_refine) then 
      Log.time "cra:refine_star" refine_star x
    else 
      Log.time "cra:star" I.star x

  let project = exists V.is_global
end

module RK = struct
  module S = BatSet.Make(K)
  type t = S.t

  let k_leq x y =
    let eq_transform (x,t) (x',t') =
      V.equal x x' && Syntax.Term.equal t t'
    in
    BatEnum.equal eq_transform (K.transform x) (K.transform y)
    && Smt.equiv srk
      (Nonlinear.uninterpret srk (K.guard x))
      (Nonlinear.uninterpret srk (K.guard y)) = `Yes

  let antichain k =
    let rec go = function
      | [] -> []
      | [x] -> [x]
      | (x::xs) ->
        let xs = go xs in
        if List.exists (k_leq x) xs then
          xs
        else
          x::(List.filter (fun y -> not (k_leq y x)) xs)
    in
    let is_consistent x =
      Smt.is_sat srk (Nonlinear.uninterpret srk (K.guard x)) != `Unsat
    in
    S.of_list (go (List.filter is_consistent (S.elements k)))

  let antichain k = Log.time "cra:refine_antichain" antichain k

  let one = S.singleton K.one

  let zero = S.empty

  let add x y = antichain (S.union x y)

  let mul x y =
    BatEnum.fold (fun s x ->
        BatEnum.fold (fun s y ->
            S.add (K.mul x y) s)
          s
          (S.enum y))
      S.empty
      (S.enum x)
    |> antichain

  let star x =
    match S.elements x with
    | [] -> one
    | [x] -> S.singleton (K.star x)
    | xs -> S.singleton (K.CRARefinement.refinement xs)

  let star x = Log.time "cra:refine_star_RK" star x

  let lower s = S.fold K.add s K.zero
  let lift = S.singleton
  (*let lift_dnf x = S.of_list (K.to_dnf x)*)
  let lift_dnf x = S.of_list (Log.time "cra:to_dnf" K.to_dnf x)
  let project = S.map K.project

  let equal x y =
    S.cardinal x = S.cardinal y
    && List.for_all2 K.equal (S.elements x) (S.elements y)

  let widen x y =
    if S.is_empty x then y
    else lift (K.widen (lower x) (lower y))
end

module RefinedTS = struct
  include WeightedGraph.MakeRecGraph(RK)
  let of_transition_system ts =
    let wg =
      WeightedGraph.fold_vertex (fun v wg ->
          WeightedGraph.add_vertex wg v)
        ts
        empty
    in
    WeightedGraph.fold_edges (fun (u, label, v) wg ->
        let label' =
          let open WeightedGraph in
          match label with
          | Call (x, y) -> Call (x, y)
          | Weight tr -> Weight (RK.lift_dnf tr)
        in
        WeightedGraph.add_edge wg u label' v)
      ts
      wg

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
      | Builtin (PrintBounds v) -> add_offset v
      | Builtin AtomicEnd | Builtin AtomicBegin | Builtin Exit -> ())

let rec record_assign (lhs : varinfo) loff rhs roff fields =
  fields |> List.map (fun { fityp; fioffset } ->
      match resolve_type fityp with
      | Record { rfields } ->
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
  | Assume phi -> K.assume (tr_bexpr phi)
  | Assign (lhs, rhs) ->
    let lhs_typ = resolve_type (Var.get_type lhs) in
    let rhs_typ = resolve_type (Aexpr.get_type rhs) in
    begin match lhs_typ, rhs_typ with
      | Record { rfields }, _ | _, Record { rfields } ->
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
    let rhs_val, rhs_pos, rhs_width =
      match tr_expr rhs with
      | TPointer rhs -> rhs.ptr_val, rhs.ptr_pos, rhs.ptr_width
      | TInt tint -> tint, (nondet_const "type_err" `TyInt), (nondet_const "type_err" `TyInt)
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
  | Initial | Assert (_, _) | AssertMemSafe (_, _) | Return None
  | Builtin (PrintBounds _) -> one
  | _ ->
    Log.errorf "No translation for definition: %a" Def.pp def;
    assert false

type 'a label = 'a WeightedGraph.label =
  | Weight of 'a
  | Call of int * int
[@@deriving ord]

type klabel = K.t label [@@deriving ord]

module TS = TransitionSystem.Make(Ctx)(V)(K)

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
      open WeightedGraph
      type t = klabel
      let pp formatter w = match w with
        | Weight w -> K.pp formatter w
        | Call (s,t) -> Format.fprintf formatter "call(%d, %d)" s t
      let show = SrkUtil.mk_show pp
    end)

let decorate_transition_system predicates ts entry =
  TS.forward_invariants_pa predicates ts entry
  |> List.fold_left (fun ts (v, invariant) ->
      let fresh_id = (Def.mk (Assume Bexpr.ktrue)).did in
      WG.split_vertex ts v (Weight (K.assume invariant)) fresh_id)
    ts

let make_transition_system rg =
  let call_edge block =
    Call ((RG.block_entry rg block).did, (RG.block_exit rg block).did)
  in
  let assertions = ref SrkUtil.Int.Map.empty in
  let print_hulls = ref SrkUtil.Int.Set.empty in
  let add_assert v e =
    assertions := SrkUtil.Int.Map.add v e (!assertions)
  in
  let add_print_hull v =
    print_hulls := SrkUtil.Int.Set.add v (!print_hulls)
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
                | Builtin (PrintBounds _) ->
                  add_print_hull def.did;
                  Weight K.one
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
        in

        let entry = (RG.block_entry rg block).did in
        let exit = (RG.block_exit rg block).did in
        let point_of_interest v =
          v = entry || v = exit
          || SrkUtil.Int.Map.mem v (!assertions)
          || SrkUtil.Int.Set.mem v (!print_hulls)
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

let analyze file =
  populate_offset_table file;
  match file.entry_points with
  | [main] -> begin
      let rg = Interproc.make_recgraph file in
      let entry = (RG.block_entry rg main).did in
      let (ts, assertions) = make_transition_system rg in

      (*      TSDisplay.display ts;*)

      if !cra_refine then
        begin
          let rts = RefinedTS.of_transition_system ts in
          let query = RefinedTS.mk_query rts in
          assertions |> SrkUtil.Int.Map.iter (fun v (phi, loc, msg) ->
              let path =
                RK.lower (RefinedTS.path_weight query entry v)
              in
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
                Report.log_error loc msg)
        end
      else
        begin
          let query = TS.mk_query ts in
          assertions |> SrkUtil.Int.Map.iter (fun v (phi, loc, msg) ->
              let path = TS.path_weight query entry v in
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
                Report.log_error loc msg)
        end;

      Report.print_errors ();
      Report.print_safe ();
    end
  | _ -> assert false

let resource_bound_analysis file =
  populate_offset_table file;
  match file.entry_points with
  | [main] -> begin
      let rg = Interproc.make_recgraph file in
      let (ts, _) = make_transition_system rg in
      let query = TS.mk_query ts in
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
          let summary = TS.path_weight query entry exit in
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
              Ctx.mk_and [Syntax.substitute_const srk subst (K.guard summary);
                          Ctx.mk_eq (Ctx.mk_const cost_symbol) rhs ]
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
    ("-cra-split-loops",
     Arg.Clear IterDomain.SPSplit.abstract_left,
     " Turn on loop splitting");
  CmdLine.register_config
    ("-cra-no-matrix",
     Arg.Clear IterDomain.SPOne.abstract_left,
     " Turn off matrix recurrences");
  CmdLine.register_config
    ("-cra-prsd",
     Arg.Clear IterDomain.SPPeriodicRational.abstract_left,
     " Use periodic rational spectral decomposition");
  CmdLine.register_config
<<<<<<< HEAD
    ("-cra-refine",
     Arg.Set cra_refine,
     " Turn on graph refinement");
  CmdLine.register_config
    ("-cra-lin-rec",
     Arg.Clear IterDomain.D.abstract_left,
     " Linear recurrence inequations");
=======
    ("-cra-prsd-pg",
     Arg.Clear IterDomain.SPPRG.abstract_left,
     " Use periodic rational spectral decomposition w/ Presburger guard");
>>>>>>> Newton-ark2
  CmdLine.register_config
    ("-dump-goals",
     Arg.Set dump_goals,
     " Output goal assertions in SMTLIB2 format")

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

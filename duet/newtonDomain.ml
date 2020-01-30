open Core
open Apak
open Srk
open BatPervasives

include Log.Make(struct let name = "newton" end)

module Ctx = Cra.Ctx
module V = Cra.V
module VMemo = Memo.Make(V)
module VMap = BatMap.Make(V)    

let srk = Ctx.context

(*******************************************************************************
 * Newtonian Program Analysis via Tensor product
 ******************************************************************************)
type value = Cra.value =
  | VVal of Var.t
  | VPos of Var.t
  | VWidth of Var.t

module K = struct
  include Cra.MakeTransition(V)

  let project tr =
    let is_global v = Var.is_global (Cra.var_of_value v) in
    exists is_global tr

  (* Transpose a transition formula (intuitively, swap the primed and unprimed
     variables). *)
  let transpose tr =
    (* The transform of the transpose is obtained by mapping each variable in
       tr's transform to a fresh Skolem constant, which will represent the
       value of that variable in the pre-state.  (After the transform, a
       variable which appears in the RHS of a transform or a guard refers to
       the post-state). *)
    let rev_transform =
      transform tr
      /@ (fun (v, _) ->
          let name = "fresh_" ^ (V.show v) in
          (v, Ctx.mk_const (Ctx.mk_symbol ~name (V.typ v))))
      |> BatList.of_enum
      |> parallel_assign
    in

    (* Replace every variable in tr's transform with its Skolem constant *)
    let substitution sym = match V.of_symbol sym with
      | Some v when mem_transform v rev_transform -> get_transform v rev_transform
      | _ -> Ctx.mk_const sym
    in

    (* Apply substitution to the guard & conjoin with equations from tr's
       transform *)
    let guard =
      let transform_equations =
        transform tr
        /@ (fun (v, rhs) ->
            Ctx.mk_eq
              (Ctx.mk_const (V.symbol_of v))
              (Syntax.substitute_const srk substitution rhs))
        |> BatList.of_enum
      in
      let guard = Syntax.substitute_const srk substitution (guard tr) in
      Ctx.mk_and (guard::transform_equations)
    in
    construct guard (BatList.of_enum (transform rev_transform))

  let top_local block =
    let open CfgIr in
    let file = get_gfile () in
    let func = lookup_function block file in
    (BatEnum.append
       (BatEnum.append (BatList.enum func.formals) (BatList.enum func.locals))
       (BatList.enum file.vars))
    /@ (fun vi ->
        let v = VVal (Var.mk vi) in
        assign v (Ctx.mk_const (Ctx.mk_symbol ~name:"havoc" (V.typ v))))
    |> BatEnum.reduce mul
    
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
end


module type Domain = sig
  type t
  type iter
  val mul : t -> t -> t
  val add : t -> t -> t
  val one : t
  val zero : t
  val star : t -> t
  val alpha : t -> iter
  val closure : iter -> t
  val star : t -> t
  val equal : iter -> iter -> bool
  val widen : iter -> iter -> iter
  val iter_pp : Format.formatter -> iter -> unit
  val show : t -> string
  val transpose : t -> t
  val project : t -> t
  val pp : Format.formatter -> t -> unit
  val guard : t -> Cra.Ctx.t Srk.Syntax.formula
  val assume : Cra.Ctx.t Srk.Syntax.formula -> t
  val compare : t -> t -> int
end

module RK = struct
  module S = BatSet.Make(K)
  type t = S.t
  type iter = S.t

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

  module CRARefinement = Refinement.DomainRefinement
    (struct
      include K
      let equal a b = ((Wedge.is_sat srk (K.guard a)) == `Unsat)
    end)

  let star x =
    match S.elements x with
    | [] -> one
    | [x] -> S.singleton (K.star x)
    | xs -> S.singleton (CRARefinement.refinement xs)

  let star x = Log.time "cra:refine_star_RK" star x

  let lower s = S.fold K.add s K.zero
  let lift = S.singleton
  (*let lift_dnf x = S.of_list (K.to_dnf x)*)
  let lift_dnf x = S.of_list (Log.time "cra:to_dnf" K.to_dnf x)
  let project = S.map K.project

  let equal x y = K.I.equal (K.I.alpha (lower x)) (K.I.alpha (lower y))
    (*S.cardinal x = S.cardinal y
    && List.for_all2 K.equal (S.elements x) (S.elements y)*)

  let widen x y =
    if S.is_empty x then y
    else lift (K.widen (lower x) (lower y))

  let pp form x = K.pp form (lower x)

  let iter_pp form x = K.I.pp form (K.I.alpha (lower x))

  let transpose = S.map K.transpose

  let alpha x = x

  let closure x = star x

  let show x = K.show (lower x)

  let guard x = K.guard (lower x)

  let assume x = lift (K.assume x)

  let compare x y = K.compare (lower x) (lower y)
end

let var_of_value = function
  | VVal v | VPos v | VWidth v -> v
let map_value f = function
  | VVal v -> VVal (f v)
  | VPos v -> VPos (f v)
  | VWidth v -> VWidth (f v)

type ptr_term =
  { ptr_val : Ctx.term;
    ptr_pos : Ctx.term;
    ptr_width : Ctx.term }

type cterm =
  | TInt of Ctx.term
  | TPointer of ptr_term

let tr_typ = Cra.tr_typ

let int_binop op left right =
  let open K in
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

let tr_expr expr =
  let open K in
  let alg = function
    | OHavoc typ -> TInt (Ctx.mk_const (Ctx.mk_symbol ~name:"havoc" (tr_typ typ)))
    | OConstant (CInt (k, _)) -> TInt (Ctx.mk_real (QQ.of_int k))
    | OConstant (CFloat (k, _)) -> TInt (Ctx.mk_real (QQ.of_float k))
    | OConstant (CString str) ->
      TPointer { ptr_val = Ctx.mk_const (Ctx.mk_symbol ~name:"tr" `TyInt);
                 ptr_width = Ctx.mk_real (QQ.of_int (String.length str));
                 ptr_pos = Ctx.mk_real QQ.zero }
    | OConstant (CChar k) -> TInt (Ctx.mk_real (QQ.of_int (int_of_char k)))
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
      TPointer { ptr_val = Ctx.mk_const (Ctx.mk_symbol ~name:"tr" `TyInt);
                 ptr_width = Ctx.mk_real QQ.one;
                 ptr_pos = Ctx.mk_real QQ.zero }

    (* No real translations for anything else -- just return a free var "tr"
       (which just acts like a havoc). *)
    | OUnaryOp (_, _, typ) ->
      TInt (Ctx.mk_const (Ctx.mk_symbol ~name:"tr" (tr_typ typ)))
    | OBoolExpr _ ->
      (* TODO: should be bool *)
      TInt (Ctx.mk_const (Ctx.mk_symbol ~name:"tr" `TyInt))
    | OAccessPath ap ->
      TInt (Ctx.mk_const (Ctx.mk_symbol ~name:"tr" (tr_typ (AP.get_type ap))))
  in
  Aexpr.fold alg expr

let tr_expr_val expr = match tr_expr expr with
  | TInt x -> x
  | TPointer x -> x.ptr_val

let tr_bexpr bexpr =
  let open K in
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
  | Assume phi -> assume (tr_bexpr phi)
  | Assign (lhs, rhs) ->
    if typ_has_offsets (Var.get_type lhs) then begin
      match tr_expr rhs with
      | TPointer rhs ->
        BatList.reduce mul [
          assign (VVal lhs) rhs.ptr_val;
          assign (VPos lhs) rhs.ptr_pos;
          assign (VWidth lhs) rhs.ptr_width;
        ]
      | TInt tint -> begin
          (match Var.get_type lhs, rhs with
           | (_, Havoc _) | (Concrete Dynamic, _) -> ()
           | _ -> Log.errorf "Ill-typed pointer assignment: %a" Def.pp def);
          parallel_assign [
            (VVal lhs, tint);
            (VPos lhs, Ctx.mk_const (Ctx.mk_symbol ~name:"type_err" `TyInt));
            (VWidth lhs, Ctx.mk_const (Ctx.mk_symbol ~name:"type_err" `TyInt))
          ]
        end
    end else assign (VVal lhs) (tr_expr_val rhs)
  | Store (lhs, _) ->
    (* Havoc all the variables lhs could point to *)
    let name = "store" in
    let open PointerAnalysis in
    let add_target memloc tr = match memloc with
      | (MAddr v, offset) ->
        if typ_has_offsets (Var.get_type (v,offset)) then begin
          mul
            tr
            (parallel_assign [
                (VVal (v,offset), Ctx.mk_const (Ctx.mk_symbol ~name `TyInt));
                (VPos (v,offset), Ctx.mk_const (Ctx.mk_symbol ~name `TyInt));
                (VWidth (v,offset), Ctx.mk_const (Ctx.mk_symbol ~name `TyInt))
              ])
        end else begin
          mul
            tr
            (assign (VVal (v,offset)) (Ctx.mk_const (Ctx.mk_symbol ~name `TyInt)))
        end
      | _, _ -> tr
    in
    MemLoc.Set.fold add_target (resolve_ap lhs) one
  | Builtin Exit -> zero
  | Builtin (Alloc (v, size, _)) ->
    parallel_assign [
      (VVal v, Ctx.mk_const (Ctx.mk_symbol ~name:"alloc" `TyInt));
      (VWidth v, (tr_expr_val size));
      (VPos v, Ctx.mk_real QQ.zero)
    ]
  | Builtin AtomicBegin | Builtin AtomicEnd
  | Builtin (Acquire _) | Builtin (Release _)
  | Builtin (Free _)
  | Initial | Assert (_, _) | AssertMemSafe (_, _) | Return None -> one
  | _ ->
    Log.errorf "No translation for definition: %a" Def.pp def;
    assert false

(* Tensored vocabulary *)
type vv = Left of V.t | Right of V.t
          [@@deriving show,ord]

module VV = struct
  module I = struct
    type t = vv [@@deriving show,ord]
    let equal x y = compare x y = 0

    let hash = function
      | Left v -> Hashtbl.hash (v, 0)
      | Right v -> Hashtbl.hash (v, 1)
  end
  include I
  module VVHT = Hashtbl.Make(I)

  let sym_to_var = Hashtbl.create 991
  let var_to_sym = VVHT.create 991

  let lower = function
    | Left v -> v
    | Right v -> v

  let left v = Left v
  let right v = Right v

  let typ v = V.typ (lower v)

  let symbol_of var =
    if VVHT.mem var_to_sym var then
      VVHT.find var_to_sym var
    else begin
      let sym = Ctx.mk_symbol ~name:(show var) (typ var) in
      VVHT.add var_to_sym var sym;
      Hashtbl.add sym_to_var sym var;
      sym
    end

  let of_symbol sym =
    if Hashtbl.mem sym_to_var sym then
      Some (Hashtbl.find sym_to_var sym)
    else
      None
end

(* Tensored transition formula *)
module KK = struct
  module Voc = V
  module VocMap = Map.Make(Voc)
  include Cra.MakeTransition(VV)


  (* Detensor-transpose local variables and remove them from the footprint *)
  let project tr =
    (* For every *local* variable v, identify Left v (representing the
       post-state of the left) and Right v (representing the pre-state of the
       right) by substituting [Left v -> Right v] *)
    let substitution sym = match VV.of_symbol sym with
      | Some (Left v) when not (Var.is_global (Cra.var_of_value v)) ->
        Ctx.mk_const (VV.symbol_of (Right v))
      | _ -> Ctx.mk_const sym
    in
    let transform =
      transform tr
      /@ (fun (v, rhs) ->
          (v, Syntax.substitute_const srk substitution rhs))
      |> BatList.of_enum
    in
    let guard = Syntax.substitute_const srk substitution (guard tr) in
    construct guard transform

    (* Remove local variables from the footprint *)
    |> exists (Var.is_global % Cra.var_of_value % VV.lower)

  let top_local block =
    let open CfgIr in
    let file = get_gfile () in
    let func = lookup_function block file in
    (BatEnum.append
       (BatEnum.append (BatList.enum func.formals) (BatList.enum func.locals))
       (BatList.enum file.vars))
    /@ (fun vi ->
        let vl = Left (Cra.VVal (Var.mk vi)) in
        let vr = Right (Cra.VVal (Var.mk vi)) in
        parallel_assign [
          (vl, Ctx.mk_const (Ctx.mk_symbol ~name:"havoc" (VV.typ vl)));
          (vr, Ctx.mk_const (Ctx.mk_symbol ~name:"havoc" (VV.typ vr)))
        ])
    |> BatEnum.reduce mul

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
      match VV.of_symbol x with
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

end

module type TDomain = sig
  type t
  type iter
  val mul : t -> t -> t
  val add : t -> t -> t
  val one : t
  val zero : t
  val star : t -> t
  val alpha : t -> iter
  val closure : iter -> t
  val star : t -> t
  val equal : iter -> iter -> bool
  val widen : iter -> iter -> iter
  val iter_pp : Format.formatter -> iter -> unit
  val show : t -> string
  val project : t -> t
  val pp : Format.formatter -> t -> unit
  val guard : t -> Cra.Ctx.t Srk.Syntax.formula
end

module RKK = struct
  module S = BatSet.Make(KK)
  type t = S.t
  type iter = S.t

  let k_leq x y =
    let eq_transform (x,t) (x',t') =
      VV.equal x x' && Syntax.Term.equal t t'
    in
    BatEnum.equal eq_transform (KK.transform x) (KK.transform y)
    && Smt.equiv srk
      (Nonlinear.uninterpret srk (KK.guard x))
      (Nonlinear.uninterpret srk (KK.guard y)) = `Yes

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
      Smt.is_sat srk (Nonlinear.uninterpret srk (KK.guard x)) != `Unsat
    in
    S.of_list (go (List.filter is_consistent (S.elements k)))

  let antichain k = Log.time "cra:refine_antichain" antichain k

  let one = S.singleton KK.one

  let zero = S.empty

  let add x y = antichain (S.union x y)

  let mul x y =
    BatEnum.fold (fun s x ->
        BatEnum.fold (fun s y ->
            S.add (KK.mul x y) s)
          s
          (S.enum y))
      S.empty
      (S.enum x)
    |> antichain

  module CRARefinement = Refinement.DomainRefinement
    (struct
      include KK
      let equal a b = ((Wedge.is_sat srk (KK.guard a)) == `Unsat)
    end)

  let star x =
    match S.elements x with
    | [] -> one
    | [x] -> S.singleton (KK.star x)
    | xs -> S.singleton (CRARefinement.refinement xs)

  let star x = Log.time "cra:refine_star_RK" star x

  let lower s = S.fold KK.add s KK.zero
  let lift = S.singleton
  (*let lift_dnf x = S.of_list (K.to_dnf x)*)
  let lift_dnf x = S.of_list (Log.time "cra:to_dnf" KK.to_dnf x)
  let project = S.map KK.project

  let equal x y = KK.I.equal (KK.I.alpha (lower x)) (KK.I.alpha (lower y))

    (*S.cardinal x = S.cardinal y
    && List.for_all2 KK.equal (S.elements x) (S.elements y)*)

  let widen x y =
    if S.is_empty x then y
    else lift (KK.widen (lower x) (lower y))

  let pp form x = KK.pp form (lower x)

  let iter_pp form x = KK.I.pp form (KK.I.alpha (lower x))

  let alpha x = x

  let closure x = star x

  let show x = KK.show (lower x)

  let guard x = KK.guard (lower x)
end

let inject_left expr =
  let substitution sym =
    match V.of_symbol sym with
    | Some v -> Ctx.mk_const (VV.symbol_of (Left v))
    | None -> Ctx.mk_const sym
  in
  Syntax.substitute_const srk substitution expr

let inject_right expr =
  let substitution sym =
    match V.of_symbol sym with
    | Some v -> Ctx.mk_const (VV.symbol_of (Right v))
    | None -> Ctx.mk_const sym
  in
  Syntax.substitute_const srk substitution expr

let tensor tr_left tr_right =
  (* Combined left & right transform *)
  let transform =
    BatEnum.append
      (K.transform tr_left
       /@ (fun (v, rhs) -> (Left v, inject_left rhs)))
      (K.transform tr_right
       /@ (fun (v, rhs) -> (Right v, inject_right rhs)))
    |> BatList.of_enum
  in
  let guard =
    Ctx.mk_and [inject_left (K.guard tr_left);
                inject_right (K.guard tr_right)]
  in
  KK.construct guard transform
 
let detensor_transpose tensored_tr =
  (* For [Left v -> rhs] in tensor_tr's transform, create a fresh Skolem
     constant skolem_v.  Store the mapping [v -> skolem_v] in substitution_map,
     and store the pair (v, rhs) in the list pre_state_eqs. *)
  let (substitution_map, pre_state_eqs) =
    let fresh_skolem v =
      let name = "fresh_" ^ (V.show v) in
      Ctx.mk_const (Ctx.mk_symbol ~name (V.typ v))
    in
    BatEnum.fold (fun (substitution_map, pre_state_eqs) (v, rhs) ->
        match v with
        | Right _ -> (substitution_map, pre_state_eqs)
        | Left v ->
          let skolem_v = fresh_skolem v in
          let substitution_map = VMap.add v skolem_v substitution_map in
          (substitution_map,
           (Ctx.mk_eq (Ctx.mk_const (V.symbol_of v)) rhs)::pre_state_eqs))
      (VMap.empty, [])
      (KK.transform tensored_tr)
  in

  (* For every variable v, identify Left v (representing the post-state of the
     left) and Right v (representing the pre-state of the right) by
     substituting the same term term_v for both Left v and Right v.  term_v is
     defined to be v if v was not written on the left, and skolem_v if it
     was. *)
  let lower =
    let merge sym = match VV.of_symbol sym with
      | Some (Left v) | Some (Right v) when VMap.mem v substitution_map ->
        VMap.find v substitution_map
      | Some (Left v) | Some (Right v) -> Ctx.mk_const (V.symbol_of v)
      | _ -> Ctx.mk_const sym
    in
    fun x -> Syntax.substitute_const srk merge x
  in
  (* substitution_map already has all the assignments that come from the left.
     Add to substition map all the right assignments, possibly overwriting the
     left assignments. *)
  let transform =
    BatEnum.fold (fun transform (v, rhs) ->
        match v with
        | Left _ -> transform
        | Right v -> VMap.add v (lower rhs) transform)
      substitution_map
      (KK.transform tensored_tr)
  in

  (* Lower the guard into the untensored vocabulary and conjoin the equations
     for the Skolem constants. *)
  let guard =
    Ctx.mk_and ((lower (KK.guard tensored_tr))::pre_state_eqs)
  in
  K.construct
    guard
    (VMap.enum transform |> BatList.of_enum)

let print_var_bounds formatter cost tr func =
  let open Format in
  let module Symbol = Syntax.Symbol in
  let cost_symbol = Ctx.mk_symbol `TyReal in
  let exists x =
    x = cost_symbol || match V.of_symbol x with
    | Some v -> Var.is_global (var_of_value v)
    | None -> false
  in
  let guard =
    let rhs =
      if K.mem_transform cost tr then
        K.get_transform cost tr
      else
        Ctx.mk_const (V.symbol_of cost)
    in
    Ctx.mk_and [K.guard tr;
                Ctx.mk_eq (Ctx.mk_const cost_symbol) rhs ]
  in
  let param_map =
    BatList.fold_lefti (fun map i formal ->
        let param = PointerAnalysis.get_param i in
        let pval = V.symbol_of (VVal param) in
        let pwidth = V.symbol_of (VWidth param) in
        let ppos = V.symbol_of (VWidth param) in
        let fval = Ctx.mk_const (V.symbol_of (VVal (Var.mk formal))) in
        let fwidth = Ctx.mk_const (V.symbol_of (VWidth (Var.mk formal))) in
        let fpos = Ctx.mk_const (V.symbol_of (VPos (Var.mk formal))) in
        map
        |> Symbol.Map.add pval fval
        |> Symbol.Map.add pwidth fwidth
        |> Symbol.Map.add ppos fpos)
      Symbol.Map.empty
      func.CfgIr.formals
  in
  let pre_cost_zero =
    let cost_symbol = V.symbol_of cost in
    Syntax.substitute_const srk (fun sym ->
        if sym = cost_symbol then
          Ctx.mk_real QQ.zero
        else
          Ctx.mk_const sym)
  in
  match Wedge.symbolic_bounds_formula ~exists srk guard cost_symbol with
  | `Sat (lower, upper) ->
    begin match lower with
      | Some lower ->
        let lower = Syntax.substitute_map srk param_map lower in
        fprintf formatter "%a <= %a@\n" 
          (Syntax.pp_expr_unnumbered srk) lower V.pp cost;

        fprintf formatter "%a is o(%a)@\n"
          V.pp cost
          BigO.pp (BigO.of_term srk (pre_cost_zero lower))

      | None -> ()
    end;
    begin match upper with
      | Some upper ->
        let upper = Syntax.substitute_map srk param_map upper in
        fprintf formatter "%a <= %a@\n" 
          V.pp cost (Syntax.pp_expr_unnumbered srk) upper;
        
        fprintf formatter "%a is O(%a)@\n"
          V.pp cost
          BigO.pp (BigO.of_term srk (pre_cost_zero upper))

      | None -> ()
    end
  | `Unsat ->
    fprintf formatter "unreachable@\n"


module type ICRADomain = sig
  type t
  type tt
  type iter
  type iter_t

  val mul : t -> t -> t
  val t_mul : tt -> tt -> tt

  val add : t -> t -> t
  val t_add : tt -> tt -> tt

  val one : unit -> t
  val t_one : unit -> tt

  val zero : unit -> t
  val t_zero : unit -> tt

  val star : t -> t
  val t_star : tt -> tt

  val alpha : t -> iter
  val t_alpha : tt -> iter_t

  val closure : iter -> t
  val t_closure : iter_t -> tt

  val equal : iter -> iter -> bool
  val t_equal : iter_t -> iter_t -> bool

  val widen : iter -> iter -> iter
  val t_widen : iter_t -> iter_t -> iter_t

  val show : t -> string
  val t_show : tt -> string

  val transpose : t -> t
  val tensor : t -> t -> tt
  val detensor_transpose : tt -> t

  val project : t -> t
  val t_project : tt -> tt

  val guard : t -> Cra.Ctx.t Srk.Syntax.formula
  val t_guard : tt -> Cra.Ctx.t Srk.Syntax.formula

  val pp : Format.formatter -> t -> unit
  val t_pp : Format.formatter -> tt -> unit

  val iter_pp : Format.formatter -> iter -> unit
  val t_iter_pp : Format.formatter -> iter_t -> unit

  val assume : Cra.Ctx.t Srk.Syntax.formula -> t

  val compare : t -> t -> int

  val make_transition : t -> K.t
end

module MakeICRADomain (D : Domain)(DD: TDomain)(T : sig val tensor : D.t -> D.t -> DD.t val detensor_transpose : DD.t -> D.t end) = struct
  type t = D.t
  type tt = DD.t
  type iter = D.iter
  type iter_t = DD.iter

  let mul = D.mul
  let t_mul = DD.mul

  let add = D.add
  let t_add = DD.add

  let one () = D.one
  let t_one () = DD.one

  let zero () = D.zero
  let t_zero () = DD.zero

  let star = D.star
  let t_star = DD.star

  let alpha = D.alpha
  let t_alpha = DD.alpha

  let closure = D.closure
  let t_closure = DD.closure
   
  let equal = D.equal
  let t_equal = DD.equal

  let widen = D.widen
  let t_widen = DD.widen

  let show = D.show
  let t_show = DD.show
  
  let transpose = D.transpose

  let project = D.project
  let t_project = DD.project

  let tensor = T.tensor
  let detensor_transpose = T.detensor_transpose

  let guard = D.guard
  let t_guard = DD.guard

  let pp = D.pp
  let t_pp = DD.pp

  let iter_pp = D.iter_pp
  let t_iter_pp = DD.iter_pp

  let assume = D.assume

  let compare = D.compare
end

module Sum (A : ICRADomain)(B : ICRADomain) : (sig include ICRADomain val use_left : bool ref val make_left : A.t -> t val make_right : B.t -> t val make_transition : t -> K.t end)= struct
  type t = Left of A.t | Right of B.t 
  type tt = Left_tt of A.tt | Right_tt of B.tt
  type iter = Left_iter of A.iter | Right_iter of B.iter
  type iter_t = Left_iter_tt of A.iter_t | Right_iter_tt of B.iter_t

  let use_left = ref true

  let make_left x = Left x
  let make_right x = Right x

  let fmap a_fun b_fun = 
    fun a -> match a with 
    | Left x -> Left (a_fun x)
    | Right x -> Right (b_fun x)

  let fmap_tt a_fun b_fun = 
    fun a -> match a with 
    | Left_tt x -> Left_tt (a_fun x)
    | Right_tt x -> Right_tt (b_fun x)

  let bi_fmap a_fun b_fun = 
    fun a b -> match (a, b) with 
    | (Left x, Left y) -> Left (a_fun x y) 
    | (Right x, Right y) -> Right (b_fun x y)
    | _ -> invalid_arg "Invalid Argument"

  let bi_fmap_tt a_fun b_fun = 
    fun a b -> match (a, b) with 
    | (Left_tt x, Left_tt y) -> Left_tt (a_fun x y) 
    | (Right_tt x, Right_tt y) -> Right_tt (b_fun x y)
    | _ -> invalid_arg "Invalid Argument"

  let bi_fmap_iter a_fun b_fun = 
    fun a b -> match (a, b) with 
    | (Left_iter x, Left_iter y) -> Left_iter (a_fun x y) 
    | (Right_iter x, Right_iter y) -> Right_iter (b_fun x y)
    | _ -> invalid_arg "Invalid Argument"

  let bi_fmap_iter_tt a_fun b_fun = 
    fun a b -> match (a, b) with 
    | (Left_iter_tt x, Left_iter_tt y) -> Left_iter_tt (a_fun x y) 
    | (Right_iter_tt x, Right_iter_tt y) -> Right_iter_tt (b_fun x y)
    | _ -> invalid_arg "Invalid Argument"

  let mul = bi_fmap A.mul B.mul
  let t_mul = bi_fmap_tt A.t_mul B.t_mul

  let add = bi_fmap A.add B.add
  let t_add = bi_fmap_tt A.t_add B.t_add

  let one () = if !use_left then Left (A.one ()) else Right (B.one ())
  let t_one () = if !use_left then Left_tt (A.t_one ()) else Right_tt (B.t_one ())

  let zero () = if !use_left then Left (A.zero ()) else Right (B.zero ())
  let t_zero () = if !use_left then Left_tt (A.t_zero ()) else Right_tt (B.t_zero ())

  let star = fmap A.star B.star
  let t_star = fmap_tt A.t_star B.t_star

  let alpha = function
    | Left x -> Left_iter (A.alpha x)
    | Right x -> Right_iter (B.alpha x)
  
  let t_alpha = function
    | Left_tt x -> Left_iter_tt (A.t_alpha x)
    | Right_tt x -> Right_iter_tt (B.t_alpha x)

  let closure = function
    | Left_iter x -> Left (A.closure x)
    | Right_iter x -> Right (B.closure x)

  let t_closure = function
    | Left_iter_tt x -> Left_tt (A.t_closure x)
    | Right_iter_tt x -> Right_tt (B.t_closure x)
   
  let equal = 
    fun a b ->
    match (a, b) with
    | (Left_iter x, Left_iter y) -> A.equal x y
    | (Right_iter x, Right_iter y) -> B.equal x y
    | _ -> invalid_arg "Invalid Argument"

  let t_equal = 
    fun a b ->
    match (a, b) with
    | (Left_iter_tt x, Left_iter_tt y) -> A.t_equal x y
    | (Right_iter_tt x, Right_iter_tt y) -> B.t_equal x y
    | _ -> invalid_arg "Invalid Argument"

  let widen = bi_fmap_iter A.widen B.widen
  let t_widen = bi_fmap_iter_tt A.t_widen B.t_widen

  let show = function
    | Left x -> A.show x
    | Right x -> B.show x

  let t_show = function
    | Left_tt x -> A.t_show x
    | Right_tt x -> B.t_show x
  
  let transpose = fmap A.transpose B.transpose

  let tensor = 
    fun a b ->
    match (a, b) with
    | (Left x, Left y) -> Left_tt (A.tensor x y)
    | (Right x, Right y) -> Right_tt (B.tensor x y)
    | _ -> invalid_arg "Invalid Argument"

  let detensor_transpose =
    fun a ->
    match a with
    | Left_tt x -> Left (A.detensor_transpose x)
    | Right_tt x -> Right (B.detensor_transpose x)

  let project = fmap A.project B.project
  let t_project = fmap_tt A.t_project B.t_project

  let guard =
    fun a ->
    match a with
    | Left x -> A.guard x
    | Right x -> B.guard x

  let t_guard =
    fun a ->
    match a with
    | Left_tt x -> A.t_guard x
    | Right_tt x -> B.t_guard x

  let pp form a =
    match a with
    | Left x -> A.pp form x
    | Right x -> B.pp form x

  let t_pp form a =
    match a with
    | Left_tt x -> A.t_pp form x
    | Right_tt x -> B.t_pp form x

  let iter_pp form a =
    match a with
    | Left_iter x -> A.iter_pp form x
    | Right_iter x -> B.iter_pp form x

  let t_iter_pp form a =
    match a with
    | Left_iter_tt x -> A.t_iter_pp form x
    | Right_iter_tt x -> B.t_iter_pp form x

  let assume x =
    if !use_left then make_left (A.assume x)
    else make_right (B.assume x)

  let compare a b =
    match (a, b) with
    | (Left x, Left y) -> A.compare x y
    | (Right x, Right y) -> B.compare x y
    | _ -> invalid_arg "Invalid Argument"

  let make_transition a = 
    match a with
    | Left x -> A.make_transition x
    | Right x -> B.make_transition x
end

module ICRA = MakeICRADomain
  ( struct
    type t = K.t
    type iter = K.I.iter
    let mul = K.mul
    let add = K.add
    let one = K.one
    let zero = K.zero
    let star = K.I.star
    let alpha = K.I.alpha
    let widen = K.I.widen
    let equal = K.I.equal
    let closure = K.I.closure
    let project = K.project
    let transpose = K.transpose
    let show = K.show
    let guard = K.guard
    let pp = K.pp
    let iter_pp = K.I.pp
    let assume = K.assume
    let compare = K.compare
  end )
  ( struct
    type t = KK.t
    type iter = KK.I.iter
    let mul = KK.mul
    let add = KK.add
    let one  = KK.one
    let zero = KK.zero
    let star = KK.I.star
    let alpha = KK.I.alpha
    let widen = KK.I.widen
    let equal = KK.I.equal
    let closure = KK.I.closure
    let project = KK.project
    let show = KK.show
    let guard = KK.guard
    let pp = KK.pp
    let iter_pp = KK.I.pp
  end )
  (
    struct
      let tensor = tensor
      let detensor_transpose = detensor_transpose
    end
  )

module RefinedICRA = MakeICRADomain(RK)(RKK)
  (struct 
    let tensor = fun x y ->
    RK.S.fold
      (fun a s ->
        RKK.S.union
          (RK.S.fold
            (fun b s1 -> RKK.S.add (tensor a b) s1)
            y
            RKK.S.empty
          )
          s
      )
      x
      RKK.S.empty
    
    let detensor_transpose = fun x -> RK.S.of_enum (BatEnum.map detensor_transpose (RKK.S.enum x))
  end)

module ICRASum = Sum(struct include ICRA let make_transition = identity end)(struct include RefinedICRA let make_transition = RK.lower end)


let _ =
  CmdLine.register_config
    ("-cra-refine",
      Arg.Clear ICRASum.use_left,
      " Turn on loop refinement");
  CmdLine.register_config
    ("-cra-refine-full",
    Arg.Unit (fun () -> ICRASum.use_left := false; RK.CRARefinement.refine_full := true; RKK.CRARefinement.refine_full := true),
    " Turn on unrestricted loop refinement")

let () =

  Callback.register "compose_callback" ICRASum.mul;
  Callback.register "tensorCompose_callback" ICRASum.t_mul;

  Callback.register "union_callback" ICRASum.add;
  Callback.register "tensorUnion_callback" ICRASum.t_add;

  Callback.register "one_callback" (fun () -> ICRASum.one ());
  Callback.register "tensorOne_callback" (fun () -> ICRASum.t_one ());

  Callback.register "zero_callback" (fun () -> ICRASum.zero ());
  Callback.register "tensorZero_callback" (fun () -> ICRASum.t_zero ());

  Callback.register "star_callback" ICRASum.star;
  Callback.register "tensorStar_callback" ICRASum.t_star;
  Callback.register "alpha_hat_callback" ICRASum.alpha;
  Callback.register "tensor_alpha_hat_callback" ICRASum.t_alpha;
  Callback.register "abstract_star_callback" ICRASum.closure;
  Callback.register "tensor_abstract_star_callback" ICRASum.t_closure;

  Callback.register "abstract_equiv_callback" ICRASum.equal;
  Callback.register "tensor_abstract_equiv_callback" ICRASum.t_equal;

  Callback.register "abstract_widen_callback" ICRASum.widen;
  Callback.register "tensor_abstract_widen_callback" ICRASum.t_widen;

  Callback.register "print_callback" ICRASum.show;
  Callback.register "tensoredPrint_callback" ICRASum.t_show;

  Callback.register "transpose_callback" ICRASum.transpose;
  Callback.register "tensor_callback" ICRASum.tensor;
  Callback.register "detensorTranspose_callback" ICRASum.detensor_transpose;

  Callback.register "merge_callback" ICRASum.project;
  Callback.register "tensorMerge_callback" ICRASum.t_project;

  Callback.register "eq_callback" (fun x y -> ICRASum.compare x y = 0);

  Callback.register "is_sat_callback" (fun tr ->
      Wedge.is_sat srk (ICRASum.guard tr) != `Unsat);

  Callback.register "get_global_var" (fun name ->
      let open CfgIr in
      let file = get_gfile() in
      (BatList.enum file.vars)
      |> BatEnum.find_map (fun v ->
          if (Varinfo.show v) = name then
            Some (Varinfo.get_id v)
          else
            None));

  Callback.register "print_robust_callback" (fun indent tr ->
      SrkUtil.mk_show (fun formatter tr ->
          Format.pp_open_vbox formatter indent;
          Format.pp_print_break formatter 0 0;
          Format.fprintf formatter "%a" ICRASum.pp tr;
          Format.pp_close_box formatter ()) tr);
  Callback.register "tensor_print_robust_callback" (fun indent tr ->
      SrkUtil.mk_show (fun formatter tr ->
          Format.pp_open_vbox formatter indent;
          Format.pp_print_break formatter 0 0;
          Format.fprintf formatter "%a" ICRASum.t_pp tr;
          Format.pp_close_box formatter ()) tr);

  Callback.register "print_indent_callback" (fun indent tr ->
      SrkUtil.mk_show (fun formatter tr ->
          Format.pp_open_vbox formatter indent;
          Format.pp_print_break formatter 0 0;
          Format.fprintf formatter "%a" ICRASum.pp tr;
          Format.pp_close_box formatter ()) tr);
  Callback.register "tensor_print_indent_callback" (fun indent tr ->
      SrkUtil.mk_show (fun formatter tr ->
          Format.pp_open_vbox formatter indent;
          Format.pp_print_break formatter 0 0;
          Format.fprintf formatter "%a" ICRASum.t_pp tr;
          Format.pp_close_box formatter ()) tr);

  Callback.register "print_abstract_callback" (fun indent abstract ->
     SrkUtil.mk_show (fun formatter abstract ->
          Format.pp_open_vbox formatter indent;
          Format.pp_print_break formatter 0 0;
          Format.fprintf formatter "%a" ICRASum.iter_pp abstract;
          Format.pp_close_box formatter ())
       abstract);
  Callback.register "tensor_print_abstract_callback" (fun indent abstract ->
     SrkUtil.mk_show (fun formatter abstract ->
          Format.pp_open_vbox formatter indent;
          Format.pp_print_break formatter 0 0;
          Format.fprintf formatter "%a" ICRASum.t_iter_pp abstract;
          Format.pp_close_box formatter ())
       abstract);

  Callback.register "print_var_bounds_callback" (fun indent varid tr func_name ->
      let tick_var = ref None in
      let func = CfgIr.lookup_function_name func_name (CfgIr.get_gfile()) in
      CfgIr.iter_vars (fun v ->
          if Varinfo.get_id v = varid then
            tick_var := Some (VVal (Var.mk v))
        ) (CfgIr.get_gfile());
      match !tick_var with
      | None -> Log.fatalf "Variable id %d not recognized" varid
      | Some tick_var  ->
        SrkUtil.mk_show (fun formatter (tick_var, tr) ->
            Format.pp_open_vbox formatter indent;
            Format.pp_print_break formatter 0 0;
            print_var_bounds formatter tick_var (ICRASum.make_transition tr) func;
            Format.pp_close_box formatter ()) (tick_var, tr));

  Callback.register "simplify_callback" (fun tr -> tr);
  Callback.register "tensorSimplify_callback" (fun tr -> tr);

  Callback.register "normalize_callback" (fun _ -> assert false);
  Callback.register "equiv_callback" (fun _ _ -> assert false);
  Callback.register "tensorEquiv_callback" (fun _ _ -> assert false);

  Callback.register "print_formula_callback" (Syntax.Formula.show srk);
  Callback.register "tensor_print_formula_callback" (Syntax.Formula.show srk);

  Callback.register "is_sat_linear_callback" (fun tr -> assert false);

  Callback.register "print_smtlib" (fun tr ->
      SrkUtil.mk_show (fun formatter tr ->
          Syntax.pp_smtlib2 srk formatter (ICRASum.guard tr)
        ) tr);
  Callback.register "tensor_print_smtlib" (fun tr ->
      SrkUtil.mk_show (fun formatter tr ->
          Syntax.pp_smtlib2 srk formatter (ICRASum.t_guard tr)
        ) tr);

  Callback.register "top_callback" (fun () ->
      let open CfgIr in
      let file = get_gfile() in
      K.havoc (List.map (fun vi -> Cra.VVal (Var.mk vi)) file.vars));

  Callback.register "print_stats" Log.print_stats

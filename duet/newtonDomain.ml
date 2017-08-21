open Core
open Apak
open Ark
open BatPervasives

include Log.Make(struct let name = "newton" end)

module Ctx = Cra.Ctx
module V = Cra.V
module VMemo = Memo.Make(V)
module VMap = BatMap.Make(V)    

let ark = Ctx.context

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
              (Syntax.substitute_const ark substitution rhs))
        |> BatList.of_enum
      in
      let guard = Syntax.substitute_const ark substitution (guard tr) in
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
          (v, Syntax.substitute_const ark substitution rhs))
      |> BatList.of_enum
    in
    let guard = Syntax.substitute_const ark substitution (guard tr) in
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
end

let inject_left expr =
  let substitution sym =
    match V.of_symbol sym with
    | Some v -> Ctx.mk_const (VV.symbol_of (Left v))
    | None -> Ctx.mk_const sym
  in
  Syntax.substitute_const ark substitution expr

let inject_right expr =
  let substitution sym =
    match V.of_symbol sym with
    | Some v -> Ctx.mk_const (VV.symbol_of (Right v))
    | None -> Ctx.mk_const sym
  in
  Syntax.substitute_const ark substitution expr

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
    fun x -> Syntax.substitute_const ark merge x
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

let print_var_bounds formatter cost tr =
  let open Format in
  let cost_symbol = V.symbol_of cost in
  let exists x =
    x = cost_symbol || match V.of_symbol x with
    | Some v -> Var.is_global (var_of_value v)
    | None -> false
  in
  let guard =
    let subst x =
      if x = cost_symbol then
        Ctx.mk_real QQ.zero
      else
        Ctx.mk_const x
    in
    let rhs =
      Syntax.substitute_const ark subst (K.get_transform cost tr)
    in
    Ctx.mk_and [Syntax.substitute_const ark subst (K.guard tr);
                Ctx.mk_eq (Ctx.mk_const cost_symbol) rhs ]
  in
  match Wedge.symbolic_bounds_formula ~exists ark guard cost_symbol with
  | `Sat (lower, upper) ->
    begin match lower with
      | Some lower ->
        fprintf formatter "%a <= %a@\n" (Syntax.Term.pp ark) lower V.pp cost;
        fprintf formatter "%a is o(%a)@\n"
          V.pp cost
          BigO.pp (BigO.of_term ark lower)

      | None -> ()
    end;
    begin match upper with
      | Some upper ->
        fprintf formatter "%a <= %a@\n" V.pp cost (Syntax.Term.pp ark) upper;
        fprintf formatter "%a is O(%a)@\n"
          V.pp cost
          BigO.pp (BigO.of_term ark upper)

      | None -> ()
    end
  | `Unsat ->
    fprintf formatter "unreachable@\n"

let () =
  Callback.register "compose_callback" K.mul;
  Callback.register "tensorCompose_callback" KK.mul;

  Callback.register "union_callback" K.add;
  Callback.register "tensorUnion_callback" KK.add;

  Callback.register "one_callback" (fun () -> K.one);
  Callback.register "tensorOne_callback" (fun () -> KK.one);

  Callback.register "zero_callback" (fun () -> K.zero);
  Callback.register "tensorZero_callback" (fun () -> KK.zero);

  Callback.register "star_callback" K.star;
  Callback.register "tensorStar_callback" KK.star;
  Callback.register "alpha_hat_callback" K.I.alpha;
  Callback.register "tensor_alpha_hat_callback" KK.I.alpha;
  Callback.register "abstract_star_callback" K.I.closure;
  Callback.register "tensor_abstract_star_callback" KK.I.closure;

  Callback.register "abstract_equiv_callback" K.I.equal;
  Callback.register "tensor_abstract_equiv_callback" KK.I.equal;

  Callback.register "abstract_widen_callback" K.I.widen;
  Callback.register "tensor_abstract_widen_callback" KK.I.widen;

  Callback.register "print_callback" K.show;
  Callback.register "tensoredPrint_callback" KK.show;

  Callback.register "transpose_callback" K.transpose;
  Callback.register "tensor_callback" tensor;
  Callback.register "detensorTranspose_callback" detensor_transpose;

  Callback.register "merge_callback" K.project;
  Callback.register "tensorMerge_callback" KK.project;

  Callback.register "eq_callback" (fun x y -> K.compare x y = 0);

  Callback.register "is_sat_callback" (fun tr ->
      Wedge.is_sat ark (K.guard tr) != `Unsat);

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
      ArkUtil.mk_show (fun formatter tr ->
          Format.pp_open_vbox formatter indent;
          Format.pp_print_break formatter 0 0;
          Format.fprintf formatter "%a" K.pp tr;
          Format.pp_close_box formatter ()) tr);
  Callback.register "tensor_print_robust_callback" (fun indent tr ->
      ArkUtil.mk_show (fun formatter tr ->
          Format.pp_open_vbox formatter indent;
          Format.pp_print_break formatter 0 0;
          Format.fprintf formatter "%a" KK.pp tr;
          Format.pp_close_box formatter ()) tr);

  Callback.register "print_indent_callback" (fun indent tr ->
      ArkUtil.mk_show (fun formatter tr ->
          Format.pp_open_vbox formatter indent;
          Format.pp_print_break formatter 0 0;
          Format.fprintf formatter "%a" K.pp tr;
          Format.pp_close_box formatter ()) tr);
  Callback.register "tensor_print_indent_callback" (fun indent tr ->
      ArkUtil.mk_show (fun formatter tr ->
          Format.pp_open_vbox formatter indent;
          Format.pp_print_break formatter 0 0;
          Format.fprintf formatter "%a" KK.pp tr;
          Format.pp_close_box formatter ()) tr);

  Callback.register "print_abstract_callback" (fun indent abstract ->
     ArkUtil.mk_show (fun formatter abstract ->
          Format.pp_open_vbox formatter indent;
          Format.pp_print_break formatter 0 0;
          Format.fprintf formatter "%a" K.I.pp abstract;
          Format.pp_close_box formatter ())
       abstract);
  Callback.register "tensor_print_abstract_callback" (fun indent abstract ->
     ArkUtil.mk_show (fun formatter abstract ->
          Format.pp_open_vbox formatter indent;
          Format.pp_print_break formatter 0 0;
          Format.fprintf formatter "%a" KK.I.pp abstract;
          Format.pp_close_box formatter ())
       abstract);

  Callback.register "print_var_bounds_callback" (fun indent varid tr ->
      let tick_var =
        let p (v, _) = match v with
          | VVal v -> (Var.get_id v) = varid
          | _ -> false
        in
        try
          Some (fst (BatEnum.find p (K.transform tr)))
        with Not_found -> None
      in
      match tick_var with
      | None -> "No bounds"
      | Some tick_var ->
        ArkUtil.mk_show (fun formatter (tick_var, tr) ->
            Format.pp_open_vbox formatter indent;
            Format.pp_print_break formatter 0 0;
            print_var_bounds formatter tick_var tr;
            Format.pp_close_box formatter ()) (tick_var, tr));

  Callback.register "simplify_callback" (fun tr -> tr);
  Callback.register "tensorSimplify_callback" (fun tr -> tr);

  Callback.register "normalize_callback" (fun _ -> assert false);
  Callback.register "equiv_callback" (fun _ _ -> assert false);
  Callback.register "tensorEquiv_callback" (fun _ _ -> assert false);

  Callback.register "print_formula_callback" (Syntax.Formula.show ark);
  Callback.register "tensor_print_formula_callback" (Syntax.Formula.show ark);

  Callback.register "is_sat_linear_callback" (fun tr -> assert false);

  Callback.register "print_smtlib" (fun tr ->
      ArkUtil.mk_show (fun formatter tr ->
          Syntax.pp_smtlib2 ark formatter (K.guard tr)
        ) tr);
  Callback.register "tensor_print_smtlib" (fun tr ->
      ArkUtil.mk_show (fun formatter tr ->
          Syntax.pp_smtlib2 ark formatter (KK.guard tr)
        ) tr);

  Callback.register "top_callback" (fun () ->
      let open CfgIr in
      let file = get_gfile() in
      K.havoc (List.map (fun vi -> Cra.VVal (Var.mk vi)) file.vars))

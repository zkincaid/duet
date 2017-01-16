open Core
open Apak
open Ark
open CfgIr
open BatPervasives
open ArkPervasives
open Pathexp

module RG = Interproc.RG
module G = RG.G

include Log.Make(struct let name = "cra" end)

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
          let open Pa in
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
  | _ -> TyInt

type value =
  | VVal of Var.t
  | VPos of Var.t
  | VWidth of Var.t
        deriving (Compare)

let var_of_value = function
  | VVal v | VPos v | VWidth v -> v
let map_value f = function
  | VVal v -> VVal (f v)
  | VPos v -> VPos (f v)
  | VWidth v -> VWidth (f v)

module V = struct

  module I = struct
    type t = value deriving (Compare)
    include Putil.MakeFmt(struct
        type a = t
        let format formatter = function
          | VVal v -> Var.format formatter v
          | VWidth v -> Format.fprintf formatter "%a@@width" Var.format v
          | VPos v -> Format.fprintf formatter "%a@@pos" Var.format v
      end)
    let compare = Compare_t.compare
    let show = Show_t.show
    let format = Show_t.format
    let equal x y = compare x y = 0
    let hash = function
      | VVal v -> Hashtbl.hash (Var.hash v, 0)
      | VPos v -> Hashtbl.hash (Var.hash v, 1)
      | VWidth v -> Hashtbl.hash (Var.hash v, 2)
  end
  include I

  let prime = map_value (flip Var.subscript 1)

  module E = Enumeration.Make(I)
  let enum = E.empty ()
  let of_smt sym = match Smt.symbol_refine sym with
    | Smt.Symbol_int id -> E.from_int enum id
    | Smt.Symbol_string _ -> assert false
  let typ v = tr_typ (Var.get_type (var_of_value v))
  let to_smt v =
    let id = E.to_int enum v in
    match typ v with
    | TyInt -> Smt.mk_int_const (Smt.mk_int_symbol id)
    | TyReal -> Smt.mk_real_const (Smt.mk_int_symbol id)
  let tag = E.to_int enum
end


module K = struct
  module Voc = V
  include Transition.Make(V)

  (* Enable/disable loop splitting during for star computation  *)
  let opt_split_loops = ref false

  let exists p tr =
    Log.time "Existential quantification" (exists p) tr

  module FormulaSet = Putil.Set.Make(F)

  (* Split loops using the atomic predicates that (1) appear in the guard of
     the loop body and (2) are expressed over pre-state variables, and then
     compute star *)
  let star_split tr =
    let tr = linearize tr in
    let alg = function
      | OAnd (xs, ys) | OOr (xs, ys) -> FormulaSet.union xs ys
      | OAtom atom ->
        begin match atom with
          | LeqZ t when VSet.is_empty (term_free_tmp_vars t) ->
            FormulaSet.singleton (F.leqz t)
          | LtZ t when VSet.is_empty (term_free_tmp_vars t) ->
            FormulaSet.singleton (F.ltz t)
          | EqZ t when VSet.is_empty (term_free_tmp_vars t) ->
            FormulaSet.singleton (F.eqz t)
          | _ -> FormulaSet.empty
        end
    in
    let star tr = Log.time "cra:base-star" star tr in
    let predicates =
      FormulaSet.fold (fun phi predicates ->
          if FormulaSet.mem (F.negate phi) predicates then
            predicates
          else
            FormulaSet.add phi predicates)
        (F.eval alg tr.guard)
        FormulaSet.empty
      |> FormulaSet.elements
    in
    let s = new Smt.solver in
    let postify =
      F.subst (fun v -> match V.lower v with
          | Some pv ->
            if M.mem pv tr.transform then
              T.var (V.mk_var (Voc.prime pv))
            else
              T.var v
          | None -> assert false)
    in
    s#assrt (F.to_smt (to_formula tr));
    match s#check () with
    | Smt.Unsat -> one
    | Smt.Undef -> assert false
    | Smt.Sat -> begin
        let sat_modulo_tr phi =
          s#push ();
          s#assrt phi;
          let res = s#check () in
          s#pop ();
          res
        in
        let is_split_predicate phi =
          (sat_modulo_tr (F.to_smt phi) = Smt.Sat)
          && (sat_modulo_tr (Smt.mk_not (F.to_smt phi)) = Smt.Sat)
        in
        let split_loops =
          predicates |> BatList.filter_map (fun phi ->
              if Log.time "is_split_predicate" is_split_predicate phi
              then begin
                let assume_phi = assume phi in
                let assume_not_phi = assume (F.negate phi) in
                let phi_tr = mul assume_phi tr in
                let not_phi_tr = mul assume_not_phi tr in
                let phi_inv = (* unsat <=> phi is a loop invariant *)
                  Smt.mk_and [F.to_smt phi;
                              F.to_smt (postify (F.negate phi))]
                in
                let not_phi_inv = (* unsat <=> !phi is a loop invariant *)
                  Smt.mk_and [Smt.mk_not (F.to_smt phi);
                              F.to_smt (postify phi)]
                in
                if sat_modulo_tr phi_inv = Smt.Unsat then
                  if sat_modulo_tr not_phi_inv = Smt.Unsat then
                    (logf "Splitting on predicate: %a" F.format phi;
                     Some (add (star not_phi_tr) (star phi_tr)))
                  else
                    (logf "Splitting on predicate: %a" F.format phi;
                     Some (mul (star not_phi_tr) (star phi_tr)))
                else if sat_modulo_tr not_phi_inv = Smt.Unsat then
                  (logf "Splitting on predicate: %a" F.format phi;
                   Some (mul (star phi_tr) (star not_phi_tr)))
                else
                  None
              end else
                None)
        in
        match split_loops with
        | [] -> star tr
        | (x::xs) -> List.fold_left meet x xs
      end
  (* tree-style split predicates *)
        (*
        let rec go predicates tr =
          match predicates with
          | [] -> Log.time "cra:base-star" star tr
          | (phi::predicates) when is_split_predicate phi ->
            logf "Splitting on predicate: %a" F.format phi;
            let assume_phi = assume phi in
            let assume_not_phi = assume (F.negate phi) in
            let phi_tr = mul assume_phi tr in
            let not_phi_tr = mul assume_not_phi tr in
            if not (F.is_sat (mul phi_tr assume_not_phi).guard) then
              mul (go predicates not_phi_tr) (go predicates phi_tr)
            else if not (F.is_sat (mul not_phi_tr assume_phi).guard) then
              mul (go predicates phi_tr) (go predicates not_phi_tr)
            else
              go predicates tr
          | (_::predicates) -> go predicates tr
        in
        go predicates tr
      end
*)
  let star tr =
    if !opt_split_loops then
      Log.time "cra:split-star" star_split tr
    else
      Log.time "cra:base-star" star tr

(*
  let simplify tr = tr

  let add x y =
    if equal x zero then y
    else if equal y zero then x
    else Log.time "cra:add" (add (simplify x)) (simplify y)

  let mul x y =
    if equal x zero || equal y zero then zero
    else if equal x one then y
    else if equal y one then x
    else simplify (Log.time "cra:mul" (mul x) y)
*)

  let widen x y = Log.time "cra:widen" (widen x) y
end
module A = Interproc.MakePathExpr(K)

(* Linearization as a simplifier *)
let linearize _ = K.F.linearize (fun () -> K.V.mk_tmp "nonlin" TyInt)

type ptr_term =
  { ptr_val : K.T.t;
    ptr_pos : K.T.t;
    ptr_width : K.T.t }

type term =
  | TInt of K.T.t
  | TPointer of ptr_term

let int_binop op left right =
  let open K in
  match op with
  | Add -> T.add left right
  | Minus -> T.sub left right
  | Mult -> T.mul left right
  | Div -> T.idiv left right
  | Mod ->
    begin match T.to_const right with
      | Some _ -> T.modulo left right
      | None -> T.var (V.mk_tmp "havoc" TyInt)
    end
  | _ -> T.var (V.mk_tmp "havoc" TyInt)

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
    | OHavoc typ -> TInt (T.var (V.mk_tmp "havoc" (tr_typ typ)))
    | OConstant (CInt (k, _)) -> TInt (T.int (ZZ.of_int k))
    | OConstant (CFloat (k, _)) -> TInt (T.const (QQ.of_float k))
    | OConstant (CString str) ->
      TPointer { ptr_val = T.var (V.mk_tmp "tr" TyInt);
                 ptr_width = T.int (ZZ.of_int (String.length str));
                 ptr_pos = T.zero }
    | OCast (_, expr) -> expr
    | OBinaryOp (a, op, b, _) -> term_binop op a b

    | OUnaryOp (Neg, TInt a, _) -> TInt (T.neg a)
    | OUnaryOp (Neg, TPointer a, _) -> TInt (T.neg a.ptr_val)
    | OAccessPath (Variable v) ->
      if typ_has_offsets (Var.get_type v) then
        TPointer { ptr_val = T.var (V.mk_var (VVal v));
                   ptr_width = T.var (V.mk_var (VWidth v));
                   ptr_pos = T.var (V.mk_var (VPos v)) }
      else TInt (T.var (V.mk_var (VVal v)))

    | OAddrOf _ ->
      (* Todo: width and pos aren't correct. *)
      TPointer { ptr_val = T.var (V.mk_tmp "tr" TyInt);
                 ptr_width = T.one;
                 ptr_pos = T.zero }

    (* No real translations for anything else -- just return a free var "tr"
       (which just acts like a havoc). *)
    | OUnaryOp (_, _, typ) -> TInt (T.var (V.mk_tmp "tr" (tr_typ typ)))
    | OBoolExpr _ -> TInt (T.var (V.mk_int_tmp "tr"))
    | OAccessPath ap -> TInt (T.var (V.mk_tmp "tr" (tr_typ (AP.get_type ap))))
    | OConstant _ -> TInt (T.var (V.mk_int_tmp "tr"))
  in
  Expr.fold alg expr


let tr_expr_val expr = match tr_expr expr with
  | TInt x -> x
  | TPointer x -> x.ptr_val

let tr_bexpr bexpr =
  let open K in
  let alg = function
    | Core.OAnd (a, b) -> F.conj a b
    | Core.OOr (a, b) -> F.disj a b
    | Core.OAtom (pred, x, y) ->
      let x = tr_expr_val x in
      let y = tr_expr_val y in
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
           | _ -> Log.errorf "Ill-typed pointer assignment on line %d: %a"
                    (Def.get_location def).Cil.line
                    Def.format def);
          BatList.reduce K.mul [
            K.assign (VVal lhs) tint;
            K.assign (VPos lhs) (T.var (V.mk_tmp "type_err" TyInt));
            K.assign (VWidth lhs) (T.var (V.mk_tmp "type_err" TyInt))
          ]
        end
    end else K.assign (VVal lhs) (tr_expr_val rhs)
  | Store (lhs, _) ->
    (* Havoc all the variables lhs could point to *)
    let open Pa in
    let add_target memloc tr = match memloc with
      | (MAddr v, offset) ->
        if typ_has_offsets (Var.get_type (v,offset)) then begin
          BatList.reduce K.mul [
            tr;
            K.assign (VVal (v,offset)) (T.var (V.mk_tmp "store" TyInt));
            K.assign (VPos (v,offset)) (T.var (V.mk_tmp "store" TyInt));
            K.assign (VWidth (v,offset)) (T.var (V.mk_tmp "store" TyInt))
          ]
        end else begin
          K.mul tr (K.assign (VVal (v,offset)) (T.var (V.mk_tmp "store" TyInt)))
        end
      | _, _ -> tr
    in
    MemLoc.Set.fold add_target (resolve_ap lhs) one
  | Builtin Exit -> zero
  | Builtin (Alloc (v, size, _)) ->
    BatList.reduce K.mul [
      K.assign (VVal v) (T.var (V.mk_tmp "alloc" TyInt));
      K.assign (VWidth v) (tr_expr_val size);
      K.assign (VPos v) T.zero
    ]
  | Builtin AtomicBegin | Builtin AtomicEnd
  | Builtin (Acquire _) | Builtin (Release _)
  | Builtin (Free _)
  | Initial | Assert (_, _) | AssertMemSafe (_, _) | Return None
  | Builtin (PrintBounds _) -> one
  | _ ->
    Log.errorf "No translation for definition: %a" Def.format def;
    assert false

let forward_inv_gen = ref false
let set_qe = function
  | "lme" -> K.F.opt_qe_strategy := K.F.qe_lme
  | "cover" -> K.F.opt_qe_strategy := K.F.qe_cover
  | "z3" -> K.F.opt_qe_strategy := K.F.qe_z3
  | "trivial" -> K.F.opt_qe_strategy := K.F.qe_trivial
  | s -> Log.errorf "Unrecognized QE strategy: `%s`" s; assert false

let abstract_guard man p phi =
  K.F.of_abstract (K.F.abstract man ~exists:(Some p) phi)

let set_guard s =
  if s = "none" then K.opt_loop_guard := None else
    let guard = match s with
      | "qe" -> K.F.exists
      | "box" -> abstract_guard (Box.manager_of_box (Box.manager_alloc ()))
      | "oct" -> abstract_guard (Oct.manager_of_oct (Oct.manager_alloc ()))
      | "polka" ->
        abstract_guard (Polka.manager_of_polka (Polka.manager_alloc_loose ()))
      | _ ->
        Log.errorf "Unrecognized option for -cra-guard: `%s'" s;
        assert false
    in
    K.opt_loop_guard := Some guard

let _ =
  CmdLine.register_config
    ("-cra-forward-inv",
     Arg.Set forward_inv_gen,
     " Forward invariant generation");
  CmdLine.register_config
    ("-cra-unroll-loop",
     Arg.Set K.opt_unroll_loop,
     " Unroll loops");
  CmdLine.register_config
    ("-cra-rec-ineq",
     Arg.Set K.opt_recurrence_ineq,
     " Solve simple recurrence inequations");
  CmdLine.register_config
    ("-cra-no-polyrec",
     Arg.Clear K.opt_polyrec,
     " Turn off polyhedral recurrences");
  CmdLine.register_config
    ("-cra-guard",
     Arg.String set_guard,
     " Turn off loop guards");
  CmdLine.register_config
    ("-cra-split-loops",
     Arg.Set K.opt_split_loops,
     " Turn on loop splitting");
  CmdLine.register_config
    ("-qe",
     Arg.String set_qe,
     " Set default quantifier elimination strategy (lme,cover,z3)")


let print_var_bounds formatter (tick_var, tr) =
  let tick_var = VVal tick_var in
  let sigma v =
    match K.V.lower v with
    | Some pv ->
      if V.equal pv tick_var then K.T.zero else K.T.var v
    | None -> K.T.var v
  in
  let pre_vars =
    K.VarSet.remove tick_var (K.formula_free_program_vars tr.K.guard)
  in

  (* Create & define synthetic dimensions *)
  let synthetic_dimensions = BatEnum.empty () in
  let synthetic_definitions = BatEnum.empty () in
  let ite_eq t cond bthen belse =
    K.F.disj
      (K.F.conj cond (K.F.eq t bthen))
      (K.F.conj (K.F.negate cond) (K.F.eq t belse))
  in
  pre_vars |> K.VarSet.iter (fun v ->
      let zero_to_x = K.V.mk_tmp ("[0," ^ (V.show v) ^ "]") TyReal in
      let zero_to_x_term = K.T.var zero_to_x in
      let v_term = K.T.var (K.V.mk_var v) in
      BatEnum.push synthetic_dimensions zero_to_x;
      BatEnum.push synthetic_definitions
        (ite_eq zero_to_x_term (K.F.geq v_term K.T.zero) v_term K.T.zero));
  ApakEnum.cartesian_product
    (K.VarSet.enum pre_vars)
    (K.VarSet.enum pre_vars)
  |> BatEnum.iter (fun (x, y) ->
      let xt = K.T.var (K.V.mk_var x) in
      let yt = K.T.var (K.V.mk_var y) in
      if not (V.equal x y) then begin
        let x_to_y =
          K.V.mk_tmp ("[" ^ (V.show x) ^ "," ^ (V.show y) ^ "]") TyReal
        in
        BatEnum.push synthetic_dimensions x_to_y;
        BatEnum.push synthetic_definitions
          (ite_eq (K.T.var x_to_y) (K.F.lt xt yt) (K.T.sub yt xt) K.T.zero)
      end;
      let x_times_y =
        K.V.mk_tmp ("(" ^ (V.show x) ^ "*" ^ (V.show y) ^ ")") TyReal
      in
      BatEnum.push synthetic_dimensions x_times_y;
      BatEnum.push synthetic_definitions
        (K.F.eq (K.T.var x_times_y) (K.T.mul xt yt)));

  let synth_dimensions = K.VSet.of_enum synthetic_dimensions in
  let defs = K.F.big_conj synthetic_definitions in
  let man = NumDomain.polka_loose_manager () in
  let phi =
    K.F.conj
      (K.F.conj (K.F.subst sigma tr.K.guard) defs)
      (K.F.eq
         (K.T.var (K.V.mk_var tick_var))
         (K.T.subst sigma (K.M.find tick_var tr.K.transform)))
  in
  Log.errorf "%a" K.F.format phi;
  let hull =
    K.F.conj
      (K.F.conj (K.F.subst sigma tr.K.guard) defs)
      (K.F.eq
         (K.T.var (K.V.mk_var tick_var))
         (K.T.subst sigma (K.M.find tick_var tr.K.transform)))
    |> K.F.linearize (fun () -> K.V.mk_tmp "nonlin" TyInt)
    |> K.F.abstract ~exists:(Some (fun v -> K.VSet.mem v synth_dimensions
                                            || K.V.lower v != None))
                                    (*|| K.V.equal v (K.V.mk_var tick_var)))*) man
  in
  let tick_dim = AVar (K.V.mk_var tick_var) in
  let print_tcons tcons =
    let open Apron in
    let open Tcons0 in
    match K.T.to_linterm (K.T.of_apron hull.K.T.D.env tcons.texpr0) with
    | None -> ()
    | Some t ->
      let (a, t) = K.T.Linterm.pivot tick_dim t in
      if QQ.equal a QQ.zero then
        ()
      else begin
        let bound =
          K.T.Linterm.scalar_mul (QQ.negate (QQ.inverse a)) t
          |> K.T.of_linterm
        in
        match tcons.typ with
        | EQ ->
          Format.fprintf formatter "%a = %a@;"
            V.format tick_var
            K.T.format bound
        | SUPEQ when QQ.lt QQ.zero a ->
          Format.fprintf formatter "%a >= %a@;"
            V.format tick_var
            K.T.format bound
        | SUPEQ when QQ.lt a QQ.zero ->
          Format.fprintf formatter "%a <= %a@;"
            V.format tick_var
            K.T.format bound
        | _ -> ()
      end
  in
  BatArray.iter
    print_tcons
    (Apron.Abstract0.to_tcons_array man hull.K.F.T.D.prop)

let analyze file =
  match file.entry_points with
  | [main] -> begin
      let rg = Interproc.make_recgraph file in
      let rg =
        if !forward_inv_gen
        then Log.phase "Forward invariant generation" decorate rg
        else rg
      in

      (*    BatEnum.iter (Interproc.RGD.display % snd) (RG.bodies rg);*)

      let local func_name =
        if defined_function func_name (get_gfile()) then begin
          let func = lookup_function func_name (get_gfile()) in
          let vars =
            Varinfo.Set.remove (return_var func_name)
              (Varinfo.Set.of_enum
                 (BatEnum.append
                    (BatList.enum func.formals)
                    (BatList.enum func.locals)))
          in
          fun x -> (Varinfo.Set.mem (fst (var_of_value x)) vars)
        end else (fun _ -> false)
      in
      let query = A.mk_query rg weight local main in
      let is_assert def = match def.dkind with
        | Assert (_, _) | AssertMemSafe _ -> true
        | _             -> false
      in
      let s = new Smt.solver in
      let check_assert def path =
        match def.dkind with
        | AssertMemSafe (expr, msg) -> begin
            match tr_expr expr with
            | TInt _ ->
              Report.log_error (Def.get_location def) "Memory safety (type error)"
            | TPointer p ->
              begin
                let sigma v = match K.V.lower v with
                  | None -> K.T.var v
                  | Some v ->
                    try K.M.find v path.K.transform
                    with Not_found -> K.T.var (K.V.mk_var v)
                in
                let phi =
                  K.F.conj
                    (K.F.geq p.ptr_pos K.T.zero)
                    (K.F.lt p.ptr_pos p.ptr_width)
                in
                let phi = K.F.subst sigma phi in

                let mk_tmp () = K.V.mk_tmp "nonlin" TyInt in
                let path_condition =
                  K.F.conj (K.to_formula path) (K.F.negate phi)
                in

                s#push ();
                s#assrt (K.F.to_smt path_condition);
                let checked =
                  try
                    begin match Log.time "Assertion checking" s#check () with
                      | Smt.Unsat -> (Report.log_safe (); true)
                      | Smt.Sat -> (Report.log_error (Def.get_location def) msg; true)
                      | Smt.Undef -> false
                    end
                  with Z3.Error _ -> false
                in
                if (not checked) && not (K.F.is_linear path_condition) then begin
                  Log.errorf "Z3 inconclusive; trying to linearize";
                  s#pop ();
                  s#push ();
                  s#assrt (K.F.to_smt (K.F.linearize mk_tmp path_condition));
                  begin match Log.time "Assertion checking" s#check () with
                    | Smt.Unsat -> Report.log_safe ()
                    | Smt.Sat -> Report.log_error (Def.get_location def) msg
                    | Smt.Undef -> Report.log_error (Def.get_location def) msg
                  end
                end;
                s#pop ();
              end
          end
        | Assert (phi, msg) -> begin
            s#push ();

            let phi = tr_bexpr phi in
            let sigma v = match K.V.lower v with
              | None -> K.T.var v
              | Some v ->
                try K.M.find v path.K.transform
                with Not_found -> K.T.var (K.V.mk_var v)
            in
            let phi = K.F.subst sigma phi in
            let mk_tmp () = K.V.mk_tmp "nonlin" TyInt in
            let path_condition = K.F.conj (K.to_formula path) (K.F.negate phi) in
            logf "Path condition:@\n%a" K.format path;
            s#assrt (K.F.to_smt path_condition);
            let checked =
              try
                begin match Log.time "Assertion checking" s#check () with
                  | Smt.Unsat -> (Report.log_safe (); true)
                  | Smt.Sat -> (Report.log_error (Def.get_location def) msg; true)
                  | Smt.Undef -> false
                end
              with Z3.Error _ -> false
            in

            if (not checked) && not (K.F.is_linear path_condition) then begin
              Log.errorf "Z3 inconclusive; trying to linearize";
              s#pop ();
              s#push ();
              s#assrt (K.F.to_smt (K.F.linearize mk_tmp path_condition));
              begin match Log.time "Assertion checking" s#check () with
                | Smt.Unsat -> Report.log_safe ()
                | Smt.Sat -> Report.log_error (Def.get_location def) msg
                | Smt.Undef -> Report.log_error (Def.get_location def) msg
              end
            end;
            s#pop ()
          end
        | _ -> ()
      in
      A.single_src_restrict query is_assert check_assert;
      Report.print_errors ();
      Report.print_safe ();
      if !CmdLine.show_stats then begin
        K.T.log_stats `always;
        K.F.log_stats `always
      end
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
      let local func_name =
        if defined_function func_name (get_gfile()) then begin
          let func = lookup_function func_name (get_gfile()) in
          let vars =
            Varinfo.Set.remove (return_var func_name)
              (Varinfo.Set.of_enum
                 (BatEnum.append
                    (BatList.enum func.formals)
                    (BatList.enum func.locals)))
          in
          fun x -> (Varinfo.Set.mem (fst (var_of_value x)) vars)
        end else (fun _ -> false)
      in
      let query = A.mk_query rg weight local main in
      RG.blocks rg |> BatEnum.iter (fun block ->
          Format.printf "Resource bounds for %a:@\n" Varinfo.format block;
          let summary = A.get_summary query block in
          let tick_var =
            let p v = V.show v = "__cost" in
            try
              Some (BatEnum.find p (K.M.keys summary.K.transform))
            with Not_found -> None
          in
          match tick_var with
          | Some (VVal tick_var) ->
            Format.printf "@[<v 0>%a@]@\n@\n" print_var_bounds (tick_var, summary)
          | _ -> Format.printf "No bounds for tick@\n"
        )
    end
  | _ -> assert false

let _ =
  let open K in
  opt_higher_recurrence := true;
  opt_disjunctive_recurrence_eq := false;
  set_guard "polka";
  opt_recurrence_ineq := false;
  opt_unroll_loop := false;
  opt_polyrec := true;
  F.opt_qe_strategy := (fun p phi -> F.qe_lme p (F.qe_partial p phi));
  F.opt_linearize_strategy := F.linearize_opt;
  F.opt_simplify_strategy := []

let _ =
  CmdLine.register_pass
    ("-cra", analyze, " Compositional recurrence analysis");
  CmdLine.register_pass
    ("-rba", resource_bound_analysis, " Resource bound analysis");
  CmdLine.register_config
    ("-z3-timeout",
     Arg.Set_int Ark.Smt.opt_timeout,
     " Set Z3 solver timeout (milliseconds)");
  CmdLine.register_config
    ("-cra-abstraction-timeout",
     Arg.Set_float Ark.Formula.abstraction_timeout,
     " Time limit for symbolic abstraction");

open Apak
open BatPervasives
open Core
open Ark
open Ark.Syntax
open Pa

include Log.Make(struct let name = "proofspace" end)

let tr_typ typ =
  match resolve_type typ with
  | Int _   -> TyInt
  | Float _ -> TyReal
  | Pointer _ -> TyInt
  | Enum _ -> TyInt
  | Array _ -> TyInt
  | Dynamic -> TyReal
  | _ -> TyInt

module PInt = Putil.PInt

module IV = struct
  module I = struct
    type t = Var.t * int [@@deriving ord]

    let pp formatter (var, i) =
      if Var.is_shared var then Var.pp formatter var
      else Format.fprintf formatter "%a[#%d]" Var.pp var i

    let equal x y = compare x y = 0
    let hash (v, i) = Hashtbl.hash (Var.hash v, i)
  end
  include I
  let typ = tr_typ % Var.get_type % fst
  let subscript (v, i) ss = (Var.subscript v ss, i)
end

module Ctx = struct
  module C = Syntax.Make(IV)()
  include C
  include Smt.MakeSolver(C)(struct let opts = [] end)()
end

let loc = Var.mk (Varinfo.mk_local "@" (Concrete (Int unknown_width)))

module VarSet = BatSet.Make(IV)

module P = struct
  include Ctx.Formula
  let conjuncts phi =
    match destruct phi with
    | `And conjuncts -> BatList.enum conjuncts
    | `Tru -> BatEnum.empty ()
    | _ -> BatEnum.singleton phi
  let big_conj enum = Ctx.mk_and (BatList.of_enum enum)
  let big_disj enum = Ctx.mk_or (BatList.of_enum enum)
  let constants phi =
    Ctx.Formula.fold_constants
      (fun i s ->
         match Ctx.const_of_symbol i with
         | Some v -> VarSet.add v s
         | None -> s)
      phi
      VarSet.empty
end

let program_var v = Ctx.mk_const (Ctx.symbol_of_const v)

module PA = PredicateAutomata.Make(Def)(struct
    include P
    let pp formatter p = Format.fprintf formatter "{%a}" pp p
  end)

(* Determine the arity of a predicate (i.e., the number of distinct threads
   whose local variables appear in the predicate).  This function assumes
   that expressions are "normal" in the sense that thread id's have been
   renamed to occupy an initial segment of the naturals. *)
let arity phi =
  let f m (v, idx) =
    if Var.is_shared v then m else max m idx
  in
  BatEnum.fold f 0 (VarSet.enum (P.constants phi))

let add_stable pa phi =
  let program_vars = P.constants phi in
  let arity = arity phi in
  let stable =
    PaFormula.mk_atom
      phi
      (BatList.of_enum ((1 -- arity) /@ (fun i -> PaFormula.Var i)))
  in
  PA.alphabet pa |> BatEnum.iter (fun def ->
      let open PaFormula in
      let rhs =
        match def.dkind with
        | Assign (v, expr) ->
          if Var.is_shared v && VarSet.mem (v, 0) program_vars then
            mk_false
          else
            (1 -- arity) |> BatEnum.fold (fun rhs i ->
                if VarSet.mem (v, i) program_vars then
                  mk_and rhs (mk_neq (Var 0) (Var i))
                else
                  rhs)
              stable
        | _ -> stable
      in
      PA.add_transition pa phi def rhs)

(* Subscripting *)
type ss =
  { ssglobal : int Var.Map.t;
    sslocal : (int Var.Map.t) PInt.Map.t }

let ss_init =
  { ssglobal = Var.Map.empty;
    sslocal = PInt.Map.empty }

let subscript ss i =
  let lookup map x =
    try Var.Map.find x map
    with Not_found -> 0
  in
  let local =
    try PInt.Map.find i ss.sslocal
    with Not_found -> Var.Map.empty
  in
  fun x ->
    if Var.is_shared x then IV.subscript (x,0) (lookup ss.ssglobal x)
    else IV.subscript (x,i) (lookup local x)

let subscript_incr ss i x =
  let lookup map x =
    try Var.Map.find x map
    with Not_found -> 0
  in
  if Var.is_shared x then
    { ss with ssglobal = Var.Map.add x (1+lookup ss.ssglobal x) ss.ssglobal }
  else
    let local =
      try PInt.Map.find i ss.sslocal
      with Not_found -> Var.Map.empty
    in
    let sub = 1 + lookup local x in
    { ss with sslocal = PInt.Map.add i (Var.Map.add x sub local) ss.sslocal }

let gensym =
  let n = ref (-1) in
  fun () -> incr n; !n

let subscript_expr ss i =
  let subscript = subscript ss i in
  let alg = function
    | OHavoc typ -> Ctx.mk_var (gensym ()) (tr_typ typ)
    | OConstant (CInt (k, _)) -> Ctx.mk_real (QQ.of_int k)
    | OConstant (CFloat (k, _)) -> Ctx.mk_real (QQ.of_float k)
    | OCast (_, expr) -> expr
    | OBinaryOp (a, Add, b, _) -> Ctx.mk_add [a; b]
    | OBinaryOp (a, Mult, b, _) -> Ctx.mk_mul [a; b]
    | OBinaryOp (a, Minus, b, _) -> Ctx.mk_sub a b

    | OUnaryOp (Neg, a, _) -> Ctx.mk_neg a

    | OAccessPath (Variable v) -> program_var (subscript v)

    (* No real translations for anything else -- just return a free var "tr"
       (which just acts like a havoc). *)
    | OBinaryOp (a, _, b, typ) -> Ctx.mk_var (gensym ()) (tr_typ typ)
    | OUnaryOp (_, _, typ) -> Ctx.mk_var (gensym ()) (tr_typ typ)
    | OBoolExpr _ -> Ctx.mk_var (gensym ()) TyInt
    | OAccessPath ap -> Ctx.mk_var (gensym ()) (tr_typ (AP.get_type ap))
    | OConstant _ -> Ctx.mk_var (gensym ()) TyInt
    | OAddrOf _ -> Ctx.mk_var (gensym ()) TyInt
  in
  Expr.fold alg

let unsubscript =
  let sigma sym = program_var (fst (Ctx.const_of_symbol_exn sym), 0) in
  P.substitute_const sigma

let subscript_bexpr ss i bexpr =
  let subscript = subscript_expr ss i in
  let alg = function
    | Core.OAnd (a, b) -> Ctx.mk_and [a; b]
    | Core.OOr (a, b) -> Ctx.mk_or [a; b]
    | Core.OAtom (pred, x, y) ->
      let x = subscript x in
      let y = subscript y in
      begin
        match pred with
        | Lt -> Ctx.mk_lt x y
        | Le -> Ctx.mk_leq x y
        | Eq -> Ctx.mk_eq x y
        | Ne -> Ctx.mk_not (Ctx.mk_eq x y)
      end
  in
  P.existential_closure (Bexpr.fold alg bexpr)

let generalize_atom phi =
  let subst = BatDynArray.make 10 in
  let rev_subst = BatHashtbl.create 31 in
  let generalize i =
    try BatHashtbl.find rev_subst i
    with Not_found -> begin
        let id = BatDynArray.length subst in
        BatHashtbl.add rev_subst i id;
        BatDynArray.add subst i;
        id
      end
  in
  let sigma v =
    let (v, tid) = Ctx.const_of_symbol_exn v in
    let iv =
      if Var.is_shared v then (v, tid) else (v, 1 + generalize tid)
    in
    program_var (IV.subscript iv 0)
  in
  let gen_phi = P.substitute_const sigma phi in
  (gen_phi, BatDynArray.to_list subst)

let generalize i phi psi =
  let subst = BatDynArray.make 10 in
  let rev_subst = BatHashtbl.create 31 in
  BatDynArray.add subst i;

  let generalize i =
    try BatHashtbl.find rev_subst i
    with Not_found -> begin
        let id = BatDynArray.length subst in
        BatHashtbl.add rev_subst i id;
        BatDynArray.add subst i;
        id
      end
  in
  let sigma v =
    let (v, tid) = Ctx.const_of_symbol_exn v in
    let iv =
      if Var.is_shared v then (v, tid) else (v, generalize tid)
    in
    program_var (IV.subscript iv 0)
  in
  let gen_phi = P.substitute_const sigma phi in
  let f psi =
    let (gen_psi, args) = generalize_atom psi in
    PaFormula.mk_atom
      gen_psi
      (List.map (fun i -> PaFormula.Var (generalize i)) args)
  in
  let mk_eq ((i,j), (k,l)) =
    let open PaFormula in
    if i = k then
      mk_eq (Var j) (Var l)
    else
      mk_neq (Var j) (Var l)
  in
  BatHashtbl.add rev_subst i 0;
  let rhs =
    let props = BatList.of_enum (BatEnum.map f (P.conjuncts psi)) in
    let vars = BatHashtbl.enum rev_subst in
    PaFormula.big_conj
      (BatEnum.append
         (BatList.enum props)
         (ApakEnum.distinct_pairs vars /@ mk_eq))
  in
  (subst, gen_phi, rhs)

let generalize i phi psi =
  try generalize i phi psi
  with _ -> assert false

(* Given a trace <a_0 : i_0> ... <a_n : i_n>, produces the sequence
   (a_0, i_0, phi_0) ... (a_n, i_n, phi_n)
   where the sequence of phis is the SSA form of the trace.
*)
let trace_formulae trace =
  let f (ss, rest) (def, i) = match def.dkind with
    | Assume phi -> (ss, (i, def, subscript_bexpr ss i phi)::rest)
    | Assign (v, expr) ->
      let rhs = subscript_expr ss i expr in
      let ss' = subscript_incr ss i v in
      let assign =
        Ctx.mk_eq (program_var (subscript ss' i v)) rhs
        |> P.existential_closure
      in
      (ss', (i, def, assign)::rest)
    | _ -> (ss, (i, def, Ctx.mk_true)::rest)
  in
  List.rev (snd (List.fold_left f (ss_init, []) trace))

let construct ipa trace =
  let rec go post = function
    | ((i, tr, phi)::rest) ->
      let phis = BatList.map (fun (_,_,phi) -> phi) rest in
      let a = Ctx.mk_and phis in
      let b = Ctx.mk_and [phi; Ctx.mk_not post] in
      let itp = match Ctx.interpolate_seq [a; b] with
        | `Unsat [itp] -> itp
        | _ ->
          Log.fatalf "Failed to interpolate! %a / %a" P.pp a P.pp b
      in
      if P.compare (unsubscript post) (unsubscript itp) = 0 then begin
        Log.logf "Skipping transition: [#%d] %a" i Def.pp tr;
        let (_, lhs, rhs) = generalize i post itp in
        PA.add_transition ipa lhs tr rhs;
        go itp rest
      end else begin
        BatEnum.iter (flip go rest) (P.conjuncts itp);
        let (_, lhs, rhs) = generalize i post itp in
        add_stable ipa lhs;
        Log.logf
          "Added PA transition:@\n @[{%a}(%a)@]@\n --( [#0] %a )-->@\n @[%a@]"
          P.pp lhs
          (ApakEnum.pp_print_enum Format.pp_print_int) (1 -- arity lhs)
          Def.pp tr
          PA.pp_formula rhs;
        PA.add_transition ipa lhs tr rhs
      end

    | [] -> assert false
  in
  go Ctx.mk_false (List.rev (trace_formulae trace))
let construct ipa trace =
  Log.time "PA construction" (construct ipa) trace

module PHT = Hashtbl.Make(P)
module PSet = BatSet.Make(P)

let program_automaton file rg =
  let open Interproc in
  let main = match file.CfgIr.entry_points with
    | [x] -> x
    | _   -> failwith "PA: No support for multiple entry points"
  in

  (* Map each control location to a unique monadic predicate symbol *)
  let loc_pred def =
    Ctx.mk_eq (program_var (loc,1)) (Ctx.mk_real (QQ.of_int def.did))
  in

  (* Nullary error predicate: asserts are replaced with guarded transitions to
     error. *)
  let err = loc_pred (Def.mk (Assume Bexpr.ktrue)) in

  (* Unary atomic predicate for implementing atomic sections. *)
  let atomic = loc_pred (Def.mk (Assume Bexpr.ktrue)) in

  (* Nullary loc predicate ensures that whenever a new thread executes a
     command its program counter is instantiated properly. *)
  let loc = Ctx.mk_true in

  (* Transitions to the error state *)
  let err_tr =
    let module M = Memo.Make(Def) in
    M.memo (fun def ->
        match def.dkind with
        | Assert (phi, _) ->
          Def.mk ~loc:(Def.get_location def) (Assume (Bexpr.negate phi))
        | _ -> assert false)
  in
  (* Thread creation transitions *)
  let init_tr =
    let module M = Memo.Make(Varinfo) in
    M.memo (fun thread -> Def.mk Initial)
  in

  let is_assert def =
    match def.dkind with
    | Assert (_, _) -> true
    | _ -> false
  in
  let sigma =
    let sigma = ref [] in
    RG.vertices rg |> BatEnum.iter (fun (_, def) ->
        sigma := def::(!sigma);
        if is_assert def then sigma := (err_tr def)::(!sigma)
      );
    RG.blocks rg |> BatEnum.iter (fun thread ->
        if not (Varinfo.equal thread main) then
          sigma := (init_tr thread)::(!sigma)
      );
    !sigma
  in

  let initial_formula =
    PaFormula.mk_and (PaFormula.mk_atom loc []) (PaFormula.mk_atom err [])
  in
  let pa =
    PA.make sigma [loc; loc_pred (RG.block_entry rg main)] initial_formula
  in

  BatEnum.iter (fun (thread, body) ->
      let open PaFormula in
      RG.G.iter_edges (fun u v ->
          (* delta(tgt(sigma)(i),sigma:j) = (i = j) *)
          PA.add_transition pa (loc_pred v) u (mk_eq (Var 0) (Var 1))
        ) body;

      RG.G.iter_vertex (fun u ->
          begin match u.dkind with
          | Builtin AtomicEnd ->
            PA.add_transition pa loc u
              (* delta(loc, sigma:i) = loc /\ src(sigma)(i) /\ atomic(i) *)
              (mk_and
                 (mk_and (mk_atom loc []) (mk_atom atomic [Var 0]))
                 (mk_atom (loc_pred u) [Var 0]));
          | _ ->
            (* delta(loc, sigma:i) = loc /\ src(sigma)(i) *)
            PA.add_transition pa loc u (mk_and
                                          (mk_atom loc [])
                                          (mk_atom (loc_pred u) [Var 0]))
          end;
            
          begin match u.dkind with
            | Builtin AtomicBegin -> PA.add_transition pa atomic u mk_true
            | _ -> 
              PA.add_transition pa atomic u
                (mk_and (mk_eq (Var 0) (Var 1)) (mk_atom atomic [Var 1]))
          end;

          match u.dkind with
          | Assert (_, _) ->
            (* Guarded transition to the error state *)
            PA.add_transition pa err (err_tr u) mk_true;

            (* delta(loc, sigma:i) = loc /\ src(sigma)(i) *)
            PA.add_transition
              pa
              loc
              (err_tr u)
              (mk_and (mk_atom loc []) (mk_atom (loc_pred u) [Var 0]))

          | Builtin (Fork (_, expr, _)) ->
            (* delta(init-t(i), fork(t):j) = true *)
            let func = match Expr.strip_casts expr with
              | AddrOf (Variable (func, OffsetFixed 0)) -> func
              | _ -> assert false
            in
            let init = loc_pred (init_tr func) in
            PA.add_transition pa init u mk_true
          | _ -> ()
        ) body;

      if not (Varinfo.equal thread main) then begin
        let entry = loc_pred (RG.block_entry rg thread) in
        let init = init_tr thread in
        PA.add_transition pa loc init (mk_atom loc []);
        PA.add_transition pa entry init (mk_and
                                           (mk_eq (Var 0) (Var 1))
                                           (mk_atom (loc_pred init) [Var 0]))
      end
    ) (RG.bodies rg);

  (* delta(u(i), v:j) = u(i) /\ i != j *)
  RG.vertices rg |> BatEnum.iter (fun (ublk, u) ->
      let open PaFormula in
      let u = loc_pred u in
      let rhs = mk_and (mk_atom u [Var 1]) (mk_neq (Var 0) (Var 1)) in

      RG.vertices rg |> BatEnum.iter (fun (vblk, v) ->
          (* only one copy of main is running *)
          if not (Varinfo.equal ublk main) || not (Varinfo.equal vblk main) then
            PA.add_transition pa u v rhs);
      RG.blocks rg |> BatEnum.iter (fun thread ->
          if not (Varinfo.equal thread main) then
            PA.add_transition pa u (init_tr thread) rhs));

  pa

let verify file =
  let open PA in
  let rg = Interproc.remove_skip (Interproc.make_recgraph file) in
  let program_pa = program_automaton file rg in
  let pf =
    PA.make
      (BatList.of_enum (PA.alphabet program_pa))
      []
      (PaFormula.mk_atom Ctx.mk_false [])
  in

  let check pf = PA.empty (PA.intersect program_pa (PA.negate pf)) in
  let number_cex = ref 0 in
  let print_info () =
    logf ~level:`info "  PA predicates: %d"
      (BatEnum.count (PA.vocabulary pf));
    logf ~level:`info "  Spurious counter-examples: %d " !number_cex;
  in
  let rec loop () =
    match check pf with
    | Some trace ->
      logf ~attributes:[`Bold] "@\nFound error trace (%d):" (!number_cex);
      List.iter (fun (def, id) ->
          logf "  [#%d] %a" id Def.pp def
        ) trace;
      logf ""; (* newline *)
      let trace_formula =
        BatList.enum (trace_formulae trace)
        /@ (fun (_,_,phi) -> phi) |> P.big_conj
      in
      begin
        match Ctx.is_sat trace_formula with
        | `Sat ->
          log ~level:`always ~attributes:[`Bold;`Red]
            "Verification result: Unsafe";
          print_info ();
          logf ~level:`info ~attributes:[`Bold] "  Error trace:";
          List.iter (fun (def, id) ->
              logf ~level:`info "    [#%d] %a" id Def.pp def
            ) trace
        | `Unsat ->
          construct pf trace;
          incr number_cex;
          loop ()
        | `Unknown ->
          log ~level:`always ~attributes:[`Bold;`Red]
            "Verification result: Unknown";
          print_info ();
          logf ~level:`info ~attributes:[`Bold] "  Could not verify trace:";
          List.iter (fun (def, id) ->
              logf ~level:`info "    [#%d] %a" id Def.pp def
            ) trace
      end
    | None ->
      log ~level:`always ~attributes:[`Bold;`Green]
        "Verification result: Safe";
      print_info ()
  in
  loop ()

let _ =
  CmdLine.register_pass
    ("-proofspace", verify, " Proof space")

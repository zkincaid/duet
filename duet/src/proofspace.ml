open Apak
open BatPervasives
open Core
open Ark
open Ark.Syntax

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
  module C = Syntax.Make(IV)
  include C
  include Smt.MakeSolver(C)(struct let opts = [] end)
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
      (fun i s -> VarSet.add (Ctx.const_of_symbol i) s)
      phi
      VarSet.empty
end

let program_var v = Ctx.mk_const (Ctx.symbol_of_const v)

module PA = PredicateAutomata.Make(Def)(P)

let stable phi args def k =
  let program_vars = P.constants phi in
  match def.dkind with
  | Assign (v, expr) ->
    let p (v', k') =
      Var.equal loc v'
      || (Var.equal v v' && (Var.is_shared v || List.nth args (k' - 1) = k))
    in
    not (VarSet.exists p program_vars)
  | _ ->
    not (VarSet.exists (fun (v, _) -> Var.equal loc v) program_vars)

(* Determine the arity of a predicate (i.e., the number of distinct threads
   whose local variables appear in the predicate).  This function assumes
   that expressions are "normal" in the sense that thread id's have been
   renamed to occupy an initial segment of the naturals. *)
let arity phi =
  let f m (v, id) =
    if Var.is_shared v then max m id else m
  in
  1 + (BatEnum.fold f (-1) (VarSet.enum (P.constants phi)))

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
  let sigma v = program_var (fst (Ctx.const_of_symbol v), 0) in
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
    let (v, tid) = Ctx.const_of_symbol v in
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
    let (v, tid) = Ctx.const_of_symbol v in
    let iv =
      if Var.is_shared v then (v, tid) else (v, generalize tid)
    in
    program_var (IV.subscript iv 0)
  in
  let gen_phi = P.substitute_const sigma phi in
  BatHashtbl.add rev_subst i 0;
  let f psi =
    let (gen_psi, args) = generalize_atom psi in
    PA.Atom (gen_psi, List.map generalize args)
  in
  let mk_eq ((i,j), (k,l)) = if i = k then PA.Eq (j,l) else PA.Neq (j,l) in

  let rhs =
    PA.big_conj
      (BatEnum.append
         (BatEnum.map f (P.conjuncts psi))
         (ApakEnum.distinct_pairs (BatHashtbl.enum rev_subst) /@ mk_eq))
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
  let f (def, i) (ss, rest) = match def.dkind with
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
  snd (List.fold_right f trace (ss_init, []))

let construct ipa trace =
  let rec go post = function
    | ((i, tr, phi)::rest) ->
      let phis = BatList.map (fun (_,_,phi) -> phi) rest in
      let a = Ctx.mk_and phis in
      let b = Ctx.mk_and [phi; Ctx.mk_not post] in
      let itp = match Ctx.interpolate_seq [a; b] with
        | `Unsat [itp] ->
          (Log.logf ~level:`trace "Found interpolant!@\n%a / %a: %a"
             P.pp a P.pp b P.pp itp;
           assert (Ctx.implies a itp);
           assert (Ctx.is_sat (Ctx.mk_and [itp; b]) = `Unsat);
           itp)
        | _ ->
          Log.fatalf "Failed to interpolate! %a / %a" P.pp a P.pp b
      in
      if P.compare (unsubscript post) (unsubscript itp) = 0 then begin
        Log.logf "Skipping transition: [#%d] %a" i Def.pp tr;
        go itp rest
      end else begin
        BatEnum.iter (flip go rest) (P.conjuncts itp);
        let (_, lhs, rhs) = generalize i post itp in

        Log.logf
          "Added PA transition:@\n @[%a@]@\n --( [#0] %a )-->@\n @[%a@]"
          P.pp lhs
          Def.pp tr
          PA.pp_formula rhs;
        PA.add_transition ipa lhs tr rhs
      end

    | [] -> assert false
  in
  go Ctx.mk_false (trace_formulae trace)
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

  let sigma = ref [] in
  let preds = ref PSet.empty in
  let add_pred p = preds := PSet.add p (!preds) in
  let main_locs = ref PSet.empty in

  (* Map each control location to a unique predicate symbol *)
  let loc_pred def =
    Ctx.mk_eq (program_var (loc,1)) (Ctx.mk_real (QQ.of_int def.did))
  in

  (* Map control locations to their successors *)
  let next = PHT.create 991 in
  let add_next u v =
    let u,v = loc_pred u, loc_pred v in
    try PHT.replace next u (PSet.add v (PHT.find next u))
    with Not_found -> PHT.add next u (PSet.singleton v)
  in
  let get_next v =
    try PHT.find next v
    with Not_found -> PSet.empty
  in

  (* Each thread gets a new initial vertex.  If some thread is in the
     initial location, the only transition that can be executed is a fork
     which spawns that thread. *)
  let thread_init = PHT.create 31 in
  let add_thread_init thread =
    let init = Def.mk Initial in
    let entry = RG.block_entry rg thread in
    sigma := init::(!sigma);
    add_pred (loc_pred init);
    add_next init entry;
    PHT.add thread_init (loc_pred init) thread
  in

  (* Error location; must replace asserts with guarded transitions to
     error. *)
  let err = Def.mk (Assume Bexpr.ktrue) in
  add_pred (loc_pred err);

  (* Transitions to the error state *)
  let err_tr = Def.HT.create 61 in
  let add_err_tr def phi =
    let guard =
      Def.mk ~loc:(Def.get_location def) (Assume (Bexpr.negate phi))
    in
    sigma := guard::(!sigma);
    Def.HT.add err_tr guard (loc_pred def)
  in

  let delta (p, args) (a,i) =
    match args with
    | [] -> (* loc *)
      if Def.HT.mem err_tr a
      then PA.And (PA.Atom (p, []),
                   PA.Atom (Def.HT.find err_tr a, [i]))
      else PA.And (PA.Atom (p, []),
                   PA.Atom (loc_pred a, [i]))
    | [j] ->
      if PHT.mem thread_init p then begin
        match a.dkind with
        | Builtin (Fork (_, expr, _)) ->
          let func = match Expr.strip_casts expr with
            | AddrOf (Variable (func, OffsetFixed 0)) -> func
            | _ -> assert false
          in
          if Varinfo.equal (PHT.find thread_init p) func && i != j
          then PA.True
          else PA.False
        | _ -> PA.False
      end else
      if P.equal p (loc_pred err) && Def.HT.mem err_tr a then
        if i = j then PA.Atom (Def.HT.find err_tr a, [i])
        else PA.False
      else if i = j && PSet.mem p (get_next (loc_pred a)) then PA.True
      else if i != j && not (PSet.mem (loc_pred a) (!main_locs))
      then PA.Atom (p, args)
      else PA.False
    | _ -> assert false
  in

  (* loc predicate ensure that whenever a new thread executes a command its
     program counter is instantiated properly. *)
  let loc = Ctx.mk_true in
  add_pred loc;

  BatEnum.iter (fun (thread, body) ->
      RG.G.iter_edges (fun u v -> add_next u v) body;
      RG.G.iter_vertex (fun u ->
          sigma := u::(!sigma);
          add_pred (loc_pred u);
          match u.dkind with
          | Assert (phi, _) -> add_err_tr u phi
          | _ -> ()
        ) body;
      if not (Varinfo.equal thread main) then add_thread_init thread
    ) (RG.bodies rg);
  RG.G.iter_vertex (fun d ->
      main_locs := PSet.add (loc_pred d) (!main_locs)
    ) (RG.block_body rg main);
  let accept =
    let entry = RG.block_entry rg main in
    (fun p -> P.equal (loc_pred entry) p || P.equal loc p)
  in
  { PA.abs_delta = delta;
    PA.abs_sigma = !sigma;
    PA.abs_predicates = !preds;
    PA.abs_accepting = accept;
    PA.abs_initial = PA.And (PA.Atom (loc_pred err, [0]), PA.Atom (loc, [])) }

let verify file =
  let open PA in
  let rg = Interproc.make_recgraph file in
  let program_pa = program_automaton file rg in
  let pf =
    PA.make program_pa.abs_sigma (fun _ -> false) (Atom (Ctx.mk_false, []))
  in
  let abstract_pf pf =
    let open PA in
    let delta (p,args) (a,i) =
      if stable p args a i
      then Or (Atom (p, args), next pf (p,args) (a,i))
      else next pf (p,args) (a,i)
    in
    { abs_predicates = PSet.add Ctx.mk_false (predicates pf);
      abs_delta = delta;
      abs_sigma = pf.sigma;
      abs_accepting = pf.accepting;
      abs_initial = pf.initial
    }
  in
  let check pf =
    abs_empty (abs_intersect program_pa (abs_negate (abstract_pf pf)))
    (* (mk_abstract pf)))*)
  in
  let number_cex = ref 0 in
  let print_info () =
    logf ~level:`info "  PA transitions: %d"
      (BatEnum.count (PA.enum_delta pf));
    logf ~level:`info "  Spurious counter-examples: %d " !number_cex;
  in
  let rec loop () =
    match check pf with
    | Some trace ->
      logf ~attributes:[`Bold] "@\nFound error trace (%d):" (!number_cex);
      List.iter (fun (def, id) ->
          logf "  [#%d] %a" id Def.pp def
        ) (List.rev trace);
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

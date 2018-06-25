(** BDD-based points-to and escape analysis.  The analysis is:
    - Inclusion based
    - Context insensitive
    - Speculatively field sensitive
*)

open Core
open CfgIr
open Srk
open Apak
open Datalog
open PointerAnalysis


(* Enumerations for converting to/from integers for datalog *******************)
module DefEnum = Enumeration.Make(Def)
module VarEnum = Enumeration.Make(Var)
module MemBaseEnum = Enumeration.Make(MemBase)
module FieldEnum = Enumeration.Make(Offset)

let def_enum = DefEnum.empty ()
let id_of_def = DefEnum.to_int def_enum
let def_of_id = DefEnum.from_int def_enum

let var_enum = VarEnum.empty ()
let id_of_var = VarEnum.to_int var_enum
let var_of_id = VarEnum.from_int var_enum

let field_enum = FieldEnum.empty ()
let id_of_field = FieldEnum.to_int field_enum
let field_of_id = FieldEnum.from_int field_enum

let membase_enum = MemBaseEnum.empty ()
let id_of_membase = MemBaseEnum.to_int membase_enum
let membase_of_id = MemBaseEnum.from_int membase_enum

let type_enum = FieldEnum.empty ()
let id_of_type = FieldEnum.to_int type_enum
let type_of_id = FieldEnum.from_int type_enum

type context =
  { file : CfgIr.file;
    assign : MemBase.t * Offset.t * MemBase.t * Offset.t * Offset.t -> unit;
    load : MemBase.t * Offset.t * MemBase.t * Offset.t * Offset.t -> unit;
    store : MemBase.t * Offset.t * Offset.t * MemBase.t * Offset.t -> unit;
    alloc : MemBase.t * Offset.t * MemBase.t * Offset.t -> unit;
    new_tmp : unit -> MemBase.t;
    mutable indirect_calls : (Var.t option * aexpr * aexpr list) list }

let mk_context file d =
  (* x.of1 := y.of2 + of3 *)
  let e_assign =
    d#input_tuples "assign" [("H",0);("F",0);("H",1);("F",1);("F",2)]
  in
  let e_assign (x, of1, y, of2, of3) =
    e_assign [id_of_membase x; id_of_field of1;
              id_of_membase y; id_of_field of2; id_of_field of3]
  in

  (* x.of1 := *(y.of2 + of3) *)
  let e_load =
    d#input_tuples "load" [("H",0);("F",0);("H",1);("F",1);("F",2)]
  in
  let e_load (x, of1, y, of2, of3) =
    e_load [id_of_membase x; id_of_field of1;
            id_of_membase y; id_of_field of2; id_of_field of3]
  in

  (* *(x.of1 + of2) := y.of3 *)
  let e_store =
    d#input_tuples "store" [("H",0);("F",0);("F",1);("H",1);("F",2)]
  in
  let e_store (x, of1, of2, y, of3) =
    e_store [id_of_membase x; id_of_field of1; id_of_field of2;
             id_of_membase y; id_of_field of3]
  in

  (* x.of1 = alloc(...), x.of1 = &y, or x.of1 = "string_constant" *)
  let e_alloc =
    d#input_tuples "alloc" [("H",0);("F",0);("H",1);("F",1)]
  in
  let e_alloc (x, of1, loc, of2) =
    e_alloc [id_of_membase x; id_of_field of1;
             id_of_membase loc; id_of_field of2]
  in

  let max_tmp = ref 0 in
  let new_tmp () =
    let mem = MTmp (!max_tmp) in
    incr max_tmp;
    mem
  in

  { file = file;
    assign = e_assign;
    load = e_load;
    store = e_store;
    alloc = e_alloc;
    new_tmp = new_tmp;
    indirect_calls = [] }

let emit_program d =
  let emit = d#emit in
  let tuple x = "(" ^ (String.concat "," x) ^ ")" in
  let binary_relation name (x,y) = name ^ (tuple [x;y]) in
  let ternary_relation name (x,y,z) = name ^ (tuple [x;y;z]) in
  let quaternary_relation name (w,x,y,z) = name ^ (tuple [w;x;y;z]) in
  let quinary_relation name (v,w,x,y,z) = name ^ (tuple [v;w;x;y;z]) in
  let (<--) x y = emit (x ^ " :- " ^ y ^ ".") in
  let (&&&) x y = x ^ "," ^ y in

  (* input relations *)
  let alloc = quaternary_relation "alloc" in
  let assign = quinary_relation "assign" in
  let store = quinary_relation "store" in
  let load = quinary_relation "load" in

  (* computed relations *)
  let resolveField = binary_relation "resolveField" in
  let cat = ternary_relation "cat" in
  let pointsTo = quaternary_relation "pointsTo" in

  (* variables *)
  let x = "x" in
  let y = "y" in
  let f = "f" in
  let fx = "fx" in
  let fy = "fy" in
  let h = "h" in
  let f1 = "f1" in
  let f2 = "f2" in
  let f3 = "f3" in
  let f4 = "f4" in
  let hf = "hf" in
  let hx = "hx" in
  let hy = "hy" in
  let hyf = "hyf" in
  let ff = "ff" in

  (* constants *)
  let none = string_of_int (id_of_field (OffsetFixed 0)) in
  let unknown = string_of_int (id_of_field OffsetUnknown) in

  emit (pointsTo("a:H", "b:F", "c:H", "d:F") ^ " outputtuples");
  emit (resolveField("a:F", "b:F"));
  emit (cat("a:F", "b:F", "c:F"));

  cat (none, x, y) <-- "x = y";
  cat (x, none, y) <-- "x = y";
  cat (x, y, unknown) <-- (("x != " ^ none) &&& ("y != " ^ none));

  resolveField(x, y) <-- "x = y";
  emit (resolveField("_", unknown) ^ ".");
  emit (resolveField(unknown, "_") ^ ".");

  (* x.fx := y.f1 + f2 *)
  pointsTo(x, ff, h, f) <-- (assign(x, fx, y, f1, f2)
                             &&& pointsTo(y, f1, h, hf)
                             &&& resolveField(fx, ff)
                             &&& cat(hf, f2, f));

  (* *(x.f1 + f2) := y.fy *)
  pointsTo(hx, ff, h, f) <-- (store(x, f1, f2, y, fy)
                              &&& pointsTo(x, f1, hx, f3)
                              &&& cat(f3, f2, f4)
                              &&& resolveField(f4, ff)
                              &&& pointsTo(y, fy, h, f));

  (* x.fx := *(y.f1 + f2) *)
  pointsTo(x, ff, h, f) <-- (load(x, fx, y, f1, f2)
                             &&& pointsTo(y, f1, hy, f3)
                             &&& cat (f3, f2, hyf)
                             &&& pointsTo(hy, hyf, h, f)
                             &&& resolveField(fx, ff));

  (* x.fx := alloc (...) + f / &y + f / "const_str" + f *)
  pointsTo(x, ff, y, f) <-- (alloc(x, fx, y, f)
                             &&& resolveField (fx, ff))

(* ap is on the lhs of an assignment; return a memory location such that
   assigning to that location approximates assigning to ap *)
let get_lhs ctx ap =
  let simple_lhs = simplify_ap ap in
  if SimpleAP.Set.cardinal simple_lhs = 1 then begin
    match SimpleAP.Set.choose simple_lhs with
    | Lvl0 (var, offset) -> (MAddr var, offset)
    | Lvl1 ((var, of1), of2) ->
      let tmp = ctx.new_tmp () in
      ctx.store (MAddr var, of1, of2, tmp, OffsetFixed 0);
      (tmp, OffsetFixed 0)
  end else begin
    let tmp = ctx.new_tmp () in
    let add = function
      | Lvl0 (var, of1) ->
        ctx.assign (MAddr var, of1, tmp, OffsetFixed 0, OffsetFixed 0)
      | Lvl1 ((var, of1), of2) ->
        ctx.store (MAddr var, of1, of2, tmp, OffsetFixed 0)
    in
    SimpleAP.Set.iter add simple_lhs;
    (tmp, OffsetFixed 0)
  end

let emit_assign ctx lhs rhs =
  let assign (x, of1) = function
    | (RAp (Lvl0 (y, of2)), of3) -> ctx.assign (x,of1,MAddr y,of2,of3)
    | (RAp (Lvl1 ((y, of2), of3)), OffsetFixed 0) ->
      ctx.load (x, of1, MAddr y, of2, of3)
    | (RAp (Lvl1 ((y, of2), of3)), of4) ->
      let tmp = ctx.new_tmp () in
      ctx.load (tmp, OffsetFixed 0, MAddr y, of2, of3);
      ctx.assign (x, of1, tmp, OffsetFixed 0, of4)
    | (RAddr v, of2) -> ctx.alloc (x, of1, MAddr v, of2)
    | (RStr str, of2) -> ctx.alloc (x, of1, MStr str, of2)
  in
  match simplify_expr rhs with
  | VConst _ -> ()
  | VRhs set -> SimpleRhs.Set.iter (assign (get_lhs ctx lhs)) set

let emit_call ctx (lhs, v, args) =
  if defined_function v ctx.file then begin
    let func = lookup_function v ctx.file in
    let f formal actual = emit_assign ctx (Variable (Var.mk formal)) actual in
    let rec go formals actuals = match formals, actuals with
      | (formal::frest, actual::arest) ->
        f formal actual; go frest arest
      | _ -> () (* todo! *)
    in
    go func.formals args;
    match lhs with
    | Some var ->
      emit_assign ctx
        (Variable var)
        (AccessPath (Variable (Var.mk (return_var v))))
    | None    -> ()
  end else () (* Undefined function *)

let emit_structure ctx file =
  let get_lhs = get_lhs ctx in

  let assign_aexpr = emit_assign ctx in
  let vdef func def = match def.dkind with
    | Store (lhs, rhs) -> assign_aexpr lhs rhs
    | Assign (var, rhs) -> assign_aexpr (Variable var) rhs
    | Builtin (Alloc (lhs, _, _)) ->
      (* todo: this can be simplified now that lhs is a variable *)
      let (var, of1) = get_lhs (Variable lhs) in
      ctx.alloc (var, of1, MAlloc def, OffsetFixed 0)

    | Call (lhs, aexpr, args) ->
      begin match Aexpr.strip_casts aexpr with
        | AddrOf (Variable (v, OffsetFixed 0)) -> (* Direct call *)
          emit_call ctx (lhs, v, args)
        | _ -> (* Indirect call *)
          ctx.indirect_calls <- (lhs, aexpr, args)::ctx.indirect_calls
      end

    | Builtin (Fork (_, aexpr, args)) ->
      begin match Aexpr.strip_casts aexpr with
        | AddrOf (Variable (v, OffsetFixed 0)) -> (* Direct fork *)
          emit_call ctx (None, v, args)
        | _ -> (* Indirect fork *)
          ctx.indirect_calls <- (None, aexpr, args)::ctx.indirect_calls
      end

    | Return (Some x) -> assign_aexpr (Variable (Var.mk (return_var func))) x
    | _ -> ()
  in
  let vdef func def =
    try vdef func def
    with Higher_ap simple_rhs ->
      let loc = Def.get_location def in
      Log.errorf "Higher-level AP: `%a'@\n  Found on: %s:%d"
        SimpleRhs.pp simple_rhs
        loc.Cil.file
        loc.Cil.line
  in
  CfgIr.iter_func_defs vdef file

let simple_ap_points_to pt ap =
  let points_to memloc =
    let memloc =
      if FieldEnum.in_enum field_enum (snd memloc) then memloc
      else (fst memloc, OffsetUnknown)
    in
    try MemLoc.HT.find pt memloc
    with Not_found -> MemLoc.Set.empty
  in
  match ap with
  | Lvl0 (var, of1) -> points_to (MAddr var, of1)
  | Lvl1 ((var, of1), of2) -> begin
      let add (mem, offset) =
        MemLoc.Set.union (points_to (mem, Offset.add offset of2))
      in
      MemLoc.Set.fold add (points_to (MAddr var, of1)) MemLoc.Set.empty
    end

let ap_points_to pt ap =
  try
    let add sap set = MemLoc.Set.union (simple_ap_points_to pt sap) set in
    SimpleAP.Set.fold add (simplify_ap ap) MemLoc.Set.empty
  with Higher_ap simple_rhs ->
    Log.fatalf "Higher-level AP: `%a'" SimpleRhs.pp simple_rhs

let aexpr_points_to pt aexpr =
  try
    match simplify_expr aexpr with
    | VConst _ -> MemLoc.Set.empty
    | VRhs rhs ->
      let add rhs set =
        match rhs with
        | (RAp ap, offset) ->
          let add memloc =
            MemLoc.Set.add (fst memloc, Offset.add (snd memloc) offset)
          in
          MemLoc.Set.fold add (simple_ap_points_to pt ap) set
        | (RAddr v, offset) -> MemLoc.Set.add (MAddr v, offset) set
        | (RStr str, offset) -> MemLoc.Set.add (MStr str, offset) set
      in
      SimpleRhs.Set.fold add rhs MemLoc.Set.empty
  with Higher_ap simple_rhs ->
    Log.fatalf "Higher-level AP: `%a'" SimpleRhs.pp simple_rhs

let resolve_call pt aexpr =
  let targets = match Aexpr.strip_casts aexpr with
    | AccessPath (Deref x) -> aexpr_points_to pt x
    | AddrOf _ -> aexpr_points_to pt aexpr
    | AccessPath (Variable _) -> aexpr_points_to pt aexpr
    | aexpr ->
      Log.errorf "Couldn't resolve call to `%a'" Aexpr.pp aexpr;
      assert false
  in
  let add_call x set = match x with
    | (MAddr v, OffsetFixed 0) -> Varinfo.Set.add v set
    | _ -> set (* No functions on the heap *)
  in
  MemLoc.Set.fold add_call targets Varinfo.Set.empty

let solve_impl file d =
  let ht = MemLoc.HT.create 1024 in
  let ctx = mk_context file d in
  let build d =
    let getm m offset = (membase_of_id m, field_of_id offset) in
    let add_pt src tgt =
      try MemLoc.HT.replace ht src (MemLoc.Set.add tgt (MemLoc.HT.find ht src))
      with Not_found -> MemLoc.HT.add ht src (MemLoc.Set.singleton tgt)
    in
    let add = function
      | [v;vo;m;mo] ->
        (* bddbddb can produce out-of-range tuples.  Just ignore them. *)
        (try begin
           match getm v vo, getm m mo with
           (* skip temporary mem locs *)
           | ((MTmp _,_), _) | (_, (MTmp _,_)) -> ()
           | (x, y) -> add_pt x y
         end with Enumeration.Not_in_enumeration _ -> ())
      | _ -> assert false
    in
    d#iter_tuples add "pointsTo"
  in
  let rec fix targets =
    let changed = ref false in
    let f (lhs, func, args) old_targets =
      let targets = resolve_call ht func in
      let new_targets = Varinfo.Set.diff targets old_targets in
      if Varinfo.Set.cardinal new_targets != 0 then begin
        changed := true;
        Varinfo.Set.iter
          (fun tgt -> emit_call ctx (lhs, tgt, args))
          new_targets
      end;
      targets
    in
    d#run ();
    build d;
    let new_targets = List.map2 f ctx.indirect_calls targets in
    if !changed then fix new_targets
  in
  d#new_domain "F";
  d#new_domain "H";

  emit_structure ctx file;
  emit_program d; (* populates ctx.indirect_calls *)

  d#ensure_domain_capacity "F" (FieldEnum.size field_enum);
  d#ensure_domain_capacity "H" (MemBaseEnum.size membase_enum);

  fix (List.map (fun _ -> Varinfo.Set.empty) ctx.indirect_calls);

  ht

let solve file =
  Putil.with_temp_dir
    "bddpa"
    (fun dir ->
       Log.phase "Pointer analysis"
         (solve_impl file) (new Datalog.monolithicSolver dir "bddpa"))

class pa file =
  object(self)
    inherit ptr_anal file
    val instance = solve file
    method ap_points_to = ap_points_to instance
    method expr_points_to = aexpr_points_to instance
    method iter f = MemLoc.HT.iter f instance
  end

let initialize file =
  let p = new pa file in
  set_pa (p :> ptr_anal);
  p

(** Build a hash table mapping each allocation site to the set of memory
    locations associated with it.  This includes all field offsets of the
    memory that can possibly be accessed.  *)
let build_accessed pa file =
  let accessed = Def.HT.create 512 in
  let add_access def memloc =
    try
      let set = MemLoc.Set.add memloc (Def.HT.find accessed def) in
      Def.HT.replace accessed def set
    with Not_found -> Def.HT.add accessed def (MemLoc.Set.singleton memloc)
  in
  let add_access memloc = match memloc with
    | (MAlloc site, _) -> add_access site memloc
    | _ -> ()
  in
  let add_ap ap = MemLoc.Set.iter add_access (pa#resolve_ap ap) in
  let add_def def = AP.Set.iter add_ap (Def.get_uses def) in
  CfgIr.iter_defs add_def file;
  accessed

let _ =
  let go file = ((new pa file) :> ptr_anal) in
  set_init go

let _ =
  let go file =
    let check def = match def.dkind with
      | Assert (Or (Atom (Lt, p, q),
                    Atom (Lt, q0, p0)), msg)
        when Aexpr.equal p p0 && Aexpr.equal q q0 ->
        let memloc_is_alias x y =
          if (snd x) = OffsetUnknown || (snd y) = OffsetUnknown
          then MemBase.equal (fst x) (fst y)
          else MemLoc.equal x y
        in
        let p_pt = PointerAnalysis.expr_points_to p in
        let may_eq =
          MemLoc.Set.exists
            (fun x -> MemLoc.Set.exists (memloc_is_alias x) p_pt)
            (PointerAnalysis.expr_points_to q)
        in
        if may_eq then
          Report.log_error (Def.get_location def) ("Assertion failed: " ^ msg)
        else
          Report.log_safe ()
      | _ -> ()
    in
    let points_to = initialize file in
    let pp_memloc_set set =
      String.concat ", "
        (BatList.sort
           Pervasives.compare
           (BatList.map MemLoc.show (MemLoc.Set.elements set)))
    in
    let pp_pointsto memloc set =
      (MemLoc.show memloc) ^ " -> {" ^ (pp_memloc_set set) ^ "}"
    in
    let pt = ref [] in
    let print memloc set =
      pt := (pp_pointsto memloc set)::(!pt)
    in
    points_to#iter print;
    Log.log "Pointer analysis results:";
    List.iter Log.log (BatList.sort Pervasives.compare (!pt));

    CfgIr.iter_defs check file;
    Report.print_errors ();
    Report.print_safe ()
  in

  CmdLine.register_pass
    ("-pa",
     go,
     " Check pointer disequality assertions with pointer analysis")

let _ =
  let go file =
    ignore(initialize file);
    simplify_calls file;
    Inline.inline_file file;
  in
  CmdLine.register_pass ("-inline", go, " Inline and simplify function calls")

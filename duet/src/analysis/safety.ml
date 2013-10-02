open Core
open CfgIr
open Apak

let assert_before cfg v cond msg =
  let assrt = Def.mk ~loc:(Def.get_location v) (Assert (cond, msg)) in
    insert_pre assrt v cfg

let aps_referenced def =
  let lhs_aps = match def.dkind with
    | Store (lhs, _) -> AP.accessed lhs
    | Call (Some lhs, _, _)
    | Builtin (Fork (Some lhs, _, _))
    | Builtin (Alloc (lhs, _, _))
    | Assign (lhs, _) -> AP.Set.singleton (Variable lhs)

    | Call (None, _, _)
    | Builtin (Fork (None, _, _))
    | Assume _ | Initial | Assert _ | AssertMemSafe _ | Return _
    | Builtin (Free _)
    | Builtin (Acquire _) | Builtin (Release _)
    | Builtin AtomicBegin | Builtin AtomicEnd
    | Builtin Exit -> AP.Set.empty
  in
    AP.Set.union lhs_aps (Def.get_accessed def)

let add_array_bounds file =
  let check_func func =
    let vertices = Cfg.fold_vertex (fun v vs -> v::vs) func.cfg [] in
    let examine_vertex def =
      let f apx = match apx with
        | Deref expr ->
	  let loc = Def.get_location def in
	  let msg =
	    "memory safe: " ^ (Expr.show (Expr.strip_all_casts expr)) in
          let d = Def.mk ~loc:loc (AssertMemSafe (expr, msg)) in
          insert_pre d def func.cfg
        | _ -> ()
      in
      AP.Set.iter f (Def.get_accessed def);
      begin match def.dkind with
      | Store (ap, _) -> f ap
      | _ -> ()
      end

    in
    List.iter examine_vertex vertices
  in
  List.iter check_func file.funcs

(** Null assertions transformation. For each dereference assert that NULL
  * is not being dereferenced *)
let add_null_pointer_derefs file =
  let null_ne expr =
    (Ne, Cast (Concrete (Int IInt), expr), Constant (CInt (0, IInt)))
  in
  let check_func func =
    let vertices = Cfg.fold_vertex (fun v vs -> v::vs) func.cfg [] in
    let examine_vertex def =
      let f apx = match apx with
        | Deref expr ->
	    let loc = Def.get_location def in
	    let msg =
	      "nonnull: " ^ (Expr.show (Expr.strip_all_casts expr))
	    in
            let d = Def.mk ~loc:loc (Assert (Atom (null_ne expr), msg)) in
              insert_pre d def func.cfg
        | _ -> ()
      in
        AP.Set.iter f (Def.get_accessed def)
    in
      List.iter examine_vertex vertices
  in
    List.iter check_func file.funcs

let _ =
  CmdLine.register_pass
    ("-check-null",
     add_null_pointer_derefs,
     " Check for null pointer dereferences");
  CmdLine.register_pass
    ("-check-array-bounds",
     add_array_bounds,
     " Check for out-of-bounds array accesses")

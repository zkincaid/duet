open Apak
open Core

module DefHT = struct
  type t = def
  module Compare_t = struct
    type a = t
    let compare x y = Pervasives.compare x.did y.did
  end
  let compare = Compare_t.compare
  include Putil.MakeFmt(struct
    type a = t
    let format = format_def
  end)
  let equal x y = x.did = y.did
  let hash x = x.did
end
include DefHT

let dk_get_defs defkind = match defkind with
  | Assign (lhs, _) -> AP.Set.singleton (Variable lhs)
  | Store (lhs, _) -> AP.Set.singleton lhs
  | Call (Some lhs, _, _) -> AP.Set.singleton (Variable lhs)
  | Call (None, _, _) -> AP.Set.empty
  | Assume expr -> Bexpr.get_uses expr
  | Assert (expr, _) -> Bexpr.get_uses expr
  | AssertMemSafe (expr, _) -> Expr.get_uses expr
  | Initial -> AP.Set.empty
  | Return _ -> AP.Set.empty
  | Builtin (Alloc (lhs, _, _)) -> AP.Set.singleton (Variable lhs)
  | Builtin (Fork (Some lhs, _, _)) -> AP.Set.singleton (Variable lhs)
  | Builtin (Fork (None, _, _)) -> AP.Set.empty
  | Builtin (Free _) -> AP.Set.empty
  | Builtin (Acquire _) | Builtin (Release _) -> AP.Set.empty
  | Builtin AtomicBegin | Builtin AtomicEnd -> AP.Set.empty
  | Builtin Exit -> AP.Set.empty

let dk_assigned_var = function
  | Assign (v, _)
  | Store (Variable v, _)
  | Call (Some v, _, _)
  | Builtin (Alloc (v, _, _))
  | Builtin (Fork (Some v, _, _)) -> Some v

  | Store _ | Assume _ | Assert _ | Initial | Return _
  | Call (_, _, _) | AssertMemSafe _ | Builtin (Free _)
  | Builtin (Fork (None, _, _))
  | Builtin (Acquire _) | Builtin (Release _)
  | Builtin AtomicBegin | Builtin AtomicEnd
  | Builtin Exit ->
      None

let rec lhs_accessed = function
  | Variable v -> AP.Set.empty
  | Deref expr -> Expr.accessed expr

let dk_get_accessed = function
  | Assign (_, rhs) -> Expr.accessed rhs
  | Store (ap, rhs) ->
      AP.Set.union (lhs_accessed ap) (Expr.accessed rhs)
  | Call (_, callee, args) | Builtin (Fork (_, callee, args)) -> 
      let f rest expr = AP.Set.union (Expr.accessed expr) rest in
      List.fold_left f (Expr.accessed callee) args
  | Assume bexpr | Assert (bexpr, _) -> Bexpr.accessed bexpr
  | AssertMemSafe (expr, _) -> Expr.accessed expr
  | Initial -> AP.Set.empty
  | Return (Some expr) -> Expr.accessed expr
  | Return None -> AP.Set.empty
  | Builtin (Alloc (_, expr, _)) -> Expr.accessed expr
  | Builtin (Free expr) -> Expr.accessed expr
  | Builtin (Acquire expr) | Builtin (Release expr) -> Expr.accessed expr
  | Builtin AtomicBegin | Builtin AtomicEnd -> AP.Set.empty
  | Builtin Exit -> AP.Set.empty

let lhs_free_vars = function
  | Variable v -> Var.Set.singleton v
  | ap -> AP.free_vars ap

let dk_free_vars = function
  | Assign (var, rhs) -> Var.Set.add var (Expr.free_vars rhs)
  | Store (ap, rhs) ->
      Var.Set.union (lhs_free_vars ap) (Expr.free_vars rhs)
  | Call (lhs, callee, args) ->
      let f rest exp = Var.Set.union (Expr.free_vars exp) rest in
      let accessed = List.fold_left f (Expr.free_vars callee) args in
	begin match lhs with
	  | Some v -> Var.Set.add v accessed
	  | None -> accessed
	end
  | Assume bexpr | Assert (bexpr, _) -> Bexpr.free_vars bexpr
  | AssertMemSafe (expr, _) -> Expr.free_vars expr
  | Initial -> Var.Set.empty
  | Return (Some expr) -> Expr.free_vars expr
  | Return None -> Var.Set.empty
  | Builtin (Alloc (lhs, expr, _)) ->
      Var.Set.add lhs (Expr.free_vars expr)
  | Builtin (Fork (Some lhs, _, _)) -> Var.Set.singleton lhs
  | Builtin (Fork (None, _, _)) -> Var.Set.empty
  | Builtin (Free expr) -> Expr.free_vars expr
  | Builtin (Acquire expr) | Builtin (Release expr) -> Expr.free_vars expr
  | Builtin AtomicBegin | Builtin AtomicEnd -> Var.Set.empty
  | Builtin Exit -> Var.Set.empty

let exprlist_uses =
  let f l e = AP.Set.union (Expr.get_uses e) l in
    List.fold_left f AP.Set.empty

let rec dk_get_uses = function
  | Assign (_, expr) -> Expr.get_uses expr
  | Store (_, expr) -> Expr.get_uses expr
  | Call (_, func, args) -> exprlist_uses (func::args)
  | Assume expr -> Bexpr.get_uses expr
  | Initial -> AP.Set.empty
  | Assert (expr, _) -> Bexpr.get_uses expr
  | AssertMemSafe (expr, _) -> Expr.get_uses expr
  | Return None -> AP.Set.empty
  | Return (Some expr) -> Expr.get_uses expr
  | Builtin (Alloc (_, expr, _)) -> Expr.get_uses expr
  | Builtin (Free expr) -> Expr.get_uses expr
  | Builtin (Fork (_, func, args)) -> exprlist_uses (func::args)
  | Builtin (Acquire expr) -> Expr.get_uses expr
  | Builtin (Release expr) -> Expr.get_uses expr
  | Builtin AtomicBegin | Builtin AtomicEnd -> AP.Set.empty
  | Builtin Exit -> AP.Set.empty

(** Gets the access_path of definitions *)
let get_defs def = dk_get_defs def.dkind

let get_uses def = dk_get_uses def.dkind

let get_accessed def = dk_get_accessed def.dkind

let free_vars def = dk_free_vars def.dkind
let assigned_var def = dk_assigned_var def.dkind

module Set = Putil.Set.Make(DefHT)
module Map = BatMap.Make(DefHT)
module HT = Hashtbl.Make(DefHT)

let initial = mk_def unknown_loc Initial

let clone def = mk_def (location_of_def def) def.dkind

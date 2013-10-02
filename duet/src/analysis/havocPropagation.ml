(** Havoc propagation *)
open Core
open Expr
open CfgIr
open Apak

let replace_havoc_ap hv = function
  | AccessPath ap ->
      if AP.Set.mem ap hv then Havoc (AP.get_type ap)
      else (AccessPath ap)
  | expr -> expr
let replace_havoc_expr hv expr =
  Expr.simplify (Expr.subst_expr (replace_havoc_ap hv) expr)

module HP = struct
  include Lattice.LiftSubset(AP.Set)
  let name = "Havoc propagation"
  let transfer def havoc_vars =
    let is_havoc_expr e =
      match replace_havoc_expr havoc_vars e with
	| Havoc _ -> true
	| _ -> false
    in
      match def.dkind with
	| Store (ap, expr) ->
	    if is_havoc_expr expr then AP.Set.add ap havoc_vars
	    else AP.Set.remove ap havoc_vars
	| Assign (var, expr) ->
	  let ap = Variable var in
	  if is_havoc_expr expr then AP.Set.add ap havoc_vars
	  else AP.Set.remove ap havoc_vars
	| Assume bexpr -> AP.Set.diff havoc_vars (Bexpr.get_uses bexpr)
	| Initial -> havoc_vars (* todo - should be universe *)
	| Assert (bexpr, _) -> AP.Set.diff havoc_vars (Bexpr.get_uses bexpr)
	| _ -> havoc_vars
  let widen = join
  let bottom = AP.Set.empty
end

module HavocProp = Solve.MakeForwardCfgSolver(HP)

let havoc_prop file =
  let add_vars s v =
    let f v = AP.Set.add (Variable v) in
    Var.Set.fold f (get_offsets v) s
  in
  let initial = List.fold_left add_vars AP.Set.empty file.vars in
  let mk_init thread hv =
    let hv = List.fold_left add_vars hv thread.locals in
    List.fold_left add_vars hv thread.formals
  in
  let transform (def, hv) =
    match def.dkind with
    | Assign (var, expr) ->
      def.dkind <- Assign (var, replace_havoc_expr hv expr)
    | Store (ap, expr) ->
      def.dkind <- Store (ap, replace_havoc_expr hv expr)
    | _ -> ()
  in
  let f res = BatEnum.iter transform (HavocProp.enum_input res) in
  HavocProp.file_analysis file f initial mk_init

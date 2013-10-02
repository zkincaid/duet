(*pp camlp4find deriving.syntax *)

(** Representation of sparse integer affine expressions *)

open Core
open Apak

module LinExpr = Monoid.FunctionSpace.Ordered.Make(Var)(Monoid.ZPlus)
include Semilattice.Bounded

module AExpr = struct
  type t = LinExpr.t * int deriving (Compare)
  let compare = Compare_t.compare
  include Putil.MakeFmt(struct
    type a = t
    let format formatter (lin, c) =
      let pp formatter (var, coeff) =
	if coeff = 1 then Var.format formatter var
	else if coeff = -1 then Format.fprintf formatter "-%a" Var.format var
	else Format.fprintf formatter "%d%a" coeff Var.format var 
      in
      Format.fprintf formatter "@[%a@ +@ %d@]"
	(Putil.format_enum pp ~left:"" ~sep:" + " ~right:"") (LinExpr.enum lin)
	c
  end)
  let equal x y = compare x y = 0

  let scalar_mul k (lin, c) =
    if k = 1 then (lin, c)
    else (LinExpr.map_cod (fun coeff -> k*coeff) lin, k*c)
  let negate = scalar_mul (-1)
  let plus (lin0, c0) (lin1, c1) = (LinExpr.mul lin0 lin1, c0 + c1)
  let minus ar1 ar2 = plus ar1 (negate ar2)
  let const k = (LinExpr.unit, k)
  let var v = (LinExpr.add v 1 LinExpr.unit, 0)
  let subst sub (lin, c) =
    let f var coeff rest =
      let expr = sub var in
	plus (scalar_mul coeff expr) rest
    in
      LinExpr.fold f lin (const c)
  let const_of (lin, c) =
    if LinExpr.equal lin LinExpr.unit then Some c else None
  let of_expr =
    let f = function
      | OHavoc _ -> None
      | OConstant (CInt (k, _)) -> Some (const k)
      | OConstant _ -> None
      | OCast (_, aexpr) -> aexpr
      | OBinaryOp (Some left, Add, Some right, _) -> Some (plus left right)
      | OBinaryOp (Some left, Minus, Some right, _) -> Some (minus left right)
      | OBinaryOp (Some left, op, Some right, _) -> begin
	  match op, const_of left, const_of right with
	    | (_, Some k0, Some k1) -> Some (const (Expr.eval_binop op k0 k1))
	    | (Mult, Some k, _) -> Some (scalar_mul k right)
	    | (Mult, _, Some k) -> Some (scalar_mul k right)
	    | (_, _, _) -> None
	end
      | OBinaryOp (_, _, _, _) -> None
      | OUnaryOp (Neg, Some expr, _) -> Some (negate expr)
      | OUnaryOp (_, _, _) -> None
      | OAccessPath (Variable v) -> Some (var v)
      | OAccessPath _ -> None
      | OBoolExpr _ -> None
      | OAddrOf _ -> None
    in
      fold_expr_only f
end

(** Affine Boolean expressions.  An affine aexpr represents the inequation
    aexpr < 0. *)
module ABExpr = struct
  include Putil.Set.Make(AExpr)
  let lt a b = singleton (AExpr.minus a b)
  let gt a b = singleton (AExpr.minus b a)
  let le a b = singleton (AExpr.minus a (AExpr.plus b (AExpr.const 1)))
  let ge a b = singleton (AExpr.minus b (AExpr.plus a (AExpr.const 1)))
  let conj = union
  let disj = inter
  let eq a b = conj (le a b) (ge a b)
end

module FlatAExpr = struct
  include Semilattice.Bounded.Ordered.Flat(AExpr)
  let lift f = function
    | Top -> Top
    | Value x -> Value (f x)
  let lift_bin f x y = match x, y with
    | (Top, _) | (_, Top) -> Top
    | (Value x, Value y)  -> Value (f x y)
  let plus = lift_bin AExpr.plus
  let const k = Value (AExpr.const k)
  let var v = Value (AExpr.var v)
  let scalar_mul k = lift (AExpr.scalar_mul k)
  let subst sub = function
    | Top -> Top
    | Value (lin, c) ->
	let f var coeff rest =
	  let expr = sub var in
	    plus (scalar_mul coeff expr) rest
	in
	  LinExpr.fold f lin (const c)
  let of_expr expr = match AExpr.of_expr expr with
    | Some x -> Value x
    | None   -> Top
end
module AState = Semilattice.Ordered.FunctionSpace.Make(Var)(FlatAExpr)

type astate =
    { state : AState.t;
      footprint : Var.Set.t }
      deriving (Compare)

module SState = struct
  type t = astate deriving (Compare)

  let mk_subst st v =
    if Var.Set.mem v st.footprint then AState.eval st.state v
    else FlatAExpr.var v

  let one = { footprint = Var.Set.empty;
	      state = AState.const Top }
    
  let mul x y =
    let footprint = Var.Set.union x.footprint y.footprint in
    let x_sub = mk_subst x in
    let f v st =
      let value =
	if Var.Set.mem v y.footprint
	then FlatAExpr.subst x_sub (AState.eval y.state v)
	else x_sub v
      in
	AState.update v value st
    in
      { state = Var.Set.fold f footprint (AState.const Top);
	footprint = footprint }

  let plus x y =
    let footprint = Var.Set.union x.footprint y.footprint in
    let x_sub = mk_subst x in
    let y_sub = mk_subst y in
    let f v st =
      let value =
	if FlatAExpr.equal (x_sub v) (y_sub v) then x_sub v
	else Top
      in
	AState.update v value st
    in
      { state = Var.Set.fold f footprint (AState.const Top);
	footprint = footprint }

  let exists p x =
    let footprint = Var.Set.filter p x.footprint in
    let set_value v st = AState.update v (AState.eval x.state v) st in
      { footprint = footprint;
	state = Var.Set.fold set_value footprint (AState.const Top) }
end

(* Variable dependence graph *)
module DG = struct
  type t = astate
  module V = Var
  let iter_vertex f st = Var.Set.iter f st.footprint
  let iter_succ f st v =
    match AState.eval st.state v with
      | Top -> ()
      | Value (lin, _) ->
	  let g v coeff () = f v in
	    LinExpr.fold g lin ()
end
module Scc = Graph.Components.Make(DG)

type expr_type =
  | NonRec of AExpr.t   (* v = expr, where no v in expr is in footprint *)
  | PlusConst of int    (* v = v + k *)
  | Rec                 (* otherwise *)

let type_map st =
  let sub = SState.mk_subst st in
  let add_scc map = function
    | [v] -> begin match sub v with
	| Top -> Var.Map.add v Rec map
	| Value (lin, c) ->
	    if LinExpr.equal lin (LinExpr.add v 1 LinExpr.unit)
	    then Var.Map.add v (PlusConst c) map
	    else (try ignore (LinExpr.find v lin); Var.Map.add v Rec map
		  with Not_found -> Var.Map.add v (NonRec (lin, c)) map)
      end
    | vs -> List.fold_left (fun map v -> Var.Map.add v Rec map) map vs
  in
    List.fold_left add_scc Var.Map.empty (Scc.scc_list st)

type kill =
    { base : AExpr.t;
      step : int;
      high : AExpr.t }
(*
module K = struct
  let 
end
*)

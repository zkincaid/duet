open Core
open Apak

let format_expr = Core.format_expr
let format_bexpr = Core.format_bexpr
let show_expr = Core.show_expr
let show_bexpr = Core.show_bexpr
let expr_compare = Core.expr_compare
let bexpr_compare = Core.bexpr_compare
let expr_equal a b = expr_compare a b = 0
let bexpr_equal a b = bexpr_compare a b = 0

let eval_binop op i j = match op with
  | Add    -> i + j
  | Minus  -> i - j
  | Mult   -> i * j
  | Div    -> i / j
  | Mod    -> i mod j
  | ShiftL -> i lsl j
  | ShiftR -> i lsr j
  | BXor   -> i lxor j
  | BAnd   -> i land j
  | BOr    -> i lor j

let get_type_expr = Core.expr_type

(** Iterate over an expression and all its subexpressions in top-down order *)
let rec iter_expr f g e =
  f e;
  match e with
    | Havoc _ -> ()
    | Cast (t, expr) ->  iter_expr f g expr
    | BinaryOp (e1, b, e2, t) -> iter_expr f g e1; iter_expr f g e2
    | UnaryOp (u, expr, t) -> iter_expr f g expr
    | Constant _ -> ()
    | AccessPath _ -> ()
    | BoolExpr e -> iter_bexpr f g e
    | AddrOf _ -> ()
and iter_bexpr f g e =
  g e;
  match e with
    | And (a, b)     -> iter_bexpr f g a; iter_bexpr f g b
    | Or (a, b)      -> iter_bexpr f g a; iter_bexpr f g b
    | Atom (_, a, b) -> iter_expr f g a; iter_expr f g b

let expr_of_int x = Constant (CInt (x, IInt))
let expr_zero = expr_of_int 0
let expr_one = expr_of_int 1
let expr_null typ = Cast (typ, expr_zero)

let expr_apply apply_ap f = function
  | OHavoc typ -> f (Havoc typ)
  | OConstant c -> f (Constant c)
  | OCast (typ, expr) -> f (Cast (typ, expr))
  | OBinaryOp (a, op, b, typ) -> f (BinaryOp (a, op, b, typ))
  | OUnaryOp (op, a, typ) -> f (UnaryOp (op, a, typ))
  | OBoolExpr b -> f (BoolExpr b)
  | OAccessPath ap -> f (AccessPath (apply_ap ap))
  | OAddrOf ap -> f (AddrOf (apply_ap ap))
let bexpr_apply f = function
  | OAtom (pred, a, b) -> f (Atom (pred, a, b))
  | OAnd (a, b) -> f (And (a, b))
  | OOr (a, b) -> f (Or (a, b))

let expr_identity f_ap = function
  | OHavoc typ -> Havoc typ
  | OConstant c -> Constant c
  | OCast (typ, expr) -> Cast (typ, expr)
  | OBinaryOp (a, op, b, typ) -> BinaryOp (a, op, b, typ)
  | OUnaryOp (op, a, typ) -> UnaryOp (op, a, typ)
  | OBoolExpr b -> BoolExpr b
  | OAccessPath ap -> AccessPath (f_ap ap)
  | OAddrOf ap -> AddrOf (f_ap ap)
let bexpr_identity = function
  | OAtom (pred, a, b) -> Atom (pred, a, b)
  | OAnd (a, b) -> And (a, b)
  | OOr (a, b) -> Or (a, b)

let expr_partial_identity f_ap = function
  | OHavoc typ -> Some (Havoc typ)
  | OConstant c -> Some (Constant c)
  | OCast (typ, Some expr) -> Some (Cast (typ, expr))
  | OCast (_, _) -> None
  | OBinaryOp (Some left, op, Some right, typ) ->
      Some (BinaryOp (left, op, right, typ))
  | OBinaryOp (_, _, _, _) -> None
  | OUnaryOp (op, Some a, typ) -> Some (UnaryOp (op, a, typ))
  | OUnaryOp (_, _, _) -> None
  | OBoolExpr (Some bexpr) -> Some (BoolExpr bexpr)
  | OBoolExpr None -> None
  | OAccessPath ap -> begin match f_ap ap with
      | Some ap -> Some (AccessPath ap)
      | None    -> None
    end
  | OAddrOf ap -> begin match f_ap ap with
      | Some ap -> Some (AddrOf ap)
      | None    -> None
    end
let bexpr_partial_identity = function
  | OAtom (pred, Some left, Some right) -> Some (Atom (pred, left, right))
  | OAtom (_, _, _) -> None
  | OAnd (Some left, Some right) -> Some (And (left, right))
  | OAnd (_, _) -> None
  | OOr (Some left, Some right) -> Some (Or (left, right))
  | OOr (_, _) -> None

type bexpr_val = BTrue | BFalse | BHavoc | BNone

module Expr = struct
  type t = expr
  module Compare_t = struct
    type a = t
    let compare = expr_compare
  end
  let compare = expr_compare
  include Putil.MakeFmt(struct
    type a = t
    let format = format_expr
  end)
end
module SumOfProducts = Monoid.FunctionSpace.Make(Expr)(Monoid.ZPlus)

let sop_of_exp exp = (0, SumOfProducts.add exp 1 SumOfProducts.unit)
let add_sop (a, sop_a) (b, sop_b) = (a+b, SumOfProducts.mul sop_a sop_b)
let mult_const k (a, sop) = (k*a, SumOfProducts.map_cod (fun x -> x*k) sop)
let from_sop (a, sop) =
  let typ = Concrete (Int IInt) in
  let add lhs = function
    | Constant (CInt (0, IInt)) -> lhs
    | rhs -> BinaryOp (lhs, Add, rhs, typ)
  in
  let add_factor exp k rest =
    if k = 0 then rest
    else if k = 1 then add exp rest
    else add (BinaryOp (Constant (CInt (k, IInt)), Mult, exp, typ)) rest
  in
    SumOfProducts.fold add_factor sop (Constant (CInt (a, IInt)))

let rec sop = function
  | Constant (CInt (c, _)) -> (c, SumOfProducts.unit)
  | BinaryOp (lhs, Add, rhs, _) -> add_sop (sop lhs) (sop rhs)
  | BinaryOp (lhs, Minus, rhs, _) ->
      add_sop (sop lhs) (mult_const (-1) (sop rhs))
  | BinaryOp (Constant (CInt (k, _)), Mult, exp, _) -> mult_const k (sop exp)
  | BinaryOp (exp, Mult, Constant (CInt (k, _)), _) -> mult_const k (sop exp)
  | UnaryOp (Neg, exp, _) -> mult_const (-1) (sop exp)
  | BinaryOp (lhs, op, rhs, typ) ->
      begin
	match (normalize_exp lhs, normalize_exp rhs) with
	  | (Constant (CInt (i, _)), Constant (CInt (j, _))) ->
	      (eval_binop op i j, SumOfProducts.unit)
	  | (lhs_norm, rhs_norm) ->
	      sop_of_exp (BinaryOp (lhs_norm, op, rhs_norm, typ))
      end
  | UnaryOp (op, exp, typ) ->
      begin
	match normalize_exp exp with
	  | Constant (CInt (i, _)) ->
	      let result = match op with
		| Neg  -> failwith "unreachable" (* matched earlier *)
		| BNot -> lnot i
	      in
		(result, SumOfProducts.unit)
	  | exp_norm -> sop_of_exp (UnaryOp (op, exp_norm, typ))
      end
  | exp -> sop_of_exp exp
and normalize_exp x = from_sop (sop x)

let normalize x = x

let (simplify_expr, simplify_bexpr) =
  let constant_bexpr bexpr =
    if bexpr_equal bexpr bexpr_true then BTrue
    else if bexpr_equal bexpr bexpr_false then BFalse
    else if bexpr_equal bexpr bexpr_havoc then BHavoc
    else BNone
  in
  let f = function
    | OConstant (CInt (i, ik)) -> Constant (CInt (i, ik))
    | OConstant x -> Constant x
    | OCast (typ, e) -> Cast (typ, e)
    | OBinaryOp (Constant (CInt (i, ik)), op, Constant (CInt (j, jk)), typ) ->
	(match op with
	   | Add -> Constant (CInt (i + j, ik))
	   | Minus -> Constant (CInt (i - j, ik))
	   | Mult -> Constant (CInt (i * j, ik))
	   | Div -> Constant (CInt (i / j, ik))
	   | Mod -> Constant (CInt (i mod j, ik))
	   | ShiftL -> Constant (CInt (i lsl j, ik))
	   | ShiftR -> Constant (CInt (i lsr j, ik))
	   | BXor -> Constant (CInt (i lxor j, ik))
	   | BAnd -> Constant (CInt (i land j, ik))
	   | BOr -> Constant (CInt (i lor j, ik)))
    | OBinaryOp (left, op, right, typ) -> BinaryOp (left, op, right, typ)
    | OUnaryOp (op, Constant (CInt (i, ik)), typ) ->
	(match op with
	   | Neg -> Constant (CInt (0 - i, ik))
	   | BNot -> Constant (CInt (lnot i, ik)))
    | OUnaryOp (op, expr, typ) -> UnaryOp (op, expr, typ)
    | OAccessPath ap -> AccessPath ap
    | OBoolExpr expr ->
	(match constant_bexpr expr with
	   | BTrue -> Constant (CInt (1, IBool))
	   | BFalse -> Constant (CInt (0, IBool))
	   | BHavoc -> Havoc (Concrete (Int IBool))
	   | BNone -> BoolExpr expr)
    | OHavoc typ -> Havoc typ
    | OAddrOf ap -> AddrOf ap
  in
  let g = function
    | OOr (a, b) ->
	(match (constant_bexpr a, constant_bexpr b) with
	   | (BTrue, _) -> bexpr_true
	   | (_, BTrue) -> bexpr_true
	   | (BFalse, _) -> b
	   | (_, BFalse) -> a
	   | _ -> if bexpr_equal a b then a else Or (a, b))
    | OAnd (a, b) ->
	(match (constant_bexpr a, constant_bexpr b) with
	   | (BFalse, _) -> bexpr_false
	   | (_, BFalse) -> bexpr_false
	   | (BTrue, _) -> b
	   | (_, BTrue) -> a
	   | _ -> if bexpr_equal a b then a else And (a, b))
    | OAtom (Eq, Havoc _, _) -> bexpr_havoc
    | OAtom (Eq, _, Havoc _) -> bexpr_havoc
    | OAtom (Ne, Havoc _, _) -> bexpr_havoc
    | OAtom (Ne, _, Havoc _) -> bexpr_havoc
    | OAtom (pred, Constant (CInt (i, _)), Constant (CInt (j, _))) ->
	let tr_bool b = if b then bexpr_true else bexpr_false in
	  (match pred with
	     | Lt -> tr_bool (i < j)
	     | Le -> tr_bool (i <= j)
	     | Eq -> tr_bool (i = j)
	     | Ne -> tr_bool (i != j))
    | OAtom (pred, a, b) -> Atom (pred, a, b)
  in
    (fold_expr f g, fold_bexpr f g)

let bexpr_dnf bexpr =
  let f = function
    | OAnd (x, y) ->
      let enum = Putil.cartesian_product (BatList.enum x) (BatList.enum y) in
      BatEnum.fold (fun r (x, y) -> (x @ y)::r) [] enum
    | OOr (x, y) -> x@y
    | OAtom (p, a, b) -> [[Atom (p,a,b)]]
  in
  let dnf_list = fold_bexpr_only f bexpr in
  let construct_minterm = BatList.reduce (fun x y -> And (x, y)) in
  let minterms = List.map construct_minterm dnf_list in
    BatList.reduce (fun x y -> Or (x, y)) minterms

let constant_bexpr bexpr =
  let bexpr = simplify_bexpr bexpr in
    if bexpr_equal bexpr bexpr_true then Some true
    else if bexpr_equal bexpr bexpr_false then Some false
    else None

let is_constant_bexpr bexpr =
  match constant_bexpr bexpr with
    | Some _ -> true
    | None -> false

(* An access path is used by an expression if it is read, but is not a
   subexpression of another access path.  If a value is provided for every
   used access path, then that expression can be evaluated. *)
let uses_expr_alg expr_uses = function
  | OAccessPath x -> AP.Set.singleton x
  | OAddrOf (Deref x) -> expr_uses x
  | OHavoc _ | OConstant _ | OAddrOf _ -> AP.Set.empty
  | OUnaryOp (_, uses, _) | OCast (_, uses) | OBoolExpr uses -> uses
  | OBinaryOp (use1, _, use2, _) -> AP.Set.union use1 use2
let uses_bexpr_alg = function
  | OAtom (_, left, right) | OAnd (left, right) | OOr (left, right) ->
      AP.Set.union left right

let rec get_uses_expr expr =
  fold_expr (uses_expr_alg get_uses_expr) uses_bexpr_alg expr
let get_uses_bexpr = fold_bexpr (uses_expr_alg get_uses_expr) uses_bexpr_alg

(* A variable is free in an expression if it occurs in that expression. *)
let free_vars_expr_alg free_vars_ap = function
  | OHavoc _ | OConstant _ -> Var.Set.empty
  | OAddrOf ap | OAccessPath ap -> free_vars_ap ap
  | OUnaryOp (_, uses, _) | OCast (_, uses) | OBoolExpr uses -> uses
  | OBinaryOp (use1, _, use2, _) -> Var.Set.union use1 use2
let free_vars_bexpr_alg = function
  | OAtom (_, left, right) | OAnd (left, right) | OOr (left, right) ->
      Var.Set.union left right

let rec free_vars_expr expr =
  fold_expr (free_vars_expr_alg free_vars_ap) free_vars_bexpr_alg expr
and free_vars_bexpr bexpr =
  fold_bexpr (free_vars_expr_alg free_vars_ap) free_vars_bexpr_alg bexpr
and free_vars_ap = function
  | Variable v -> Var.Set.singleton v
  | Deref expr -> free_vars_expr expr

(* An access path is accessed by an expression if it is read in the concrete
   execution of that expression.  *)
let rec accessed_expr = function
  | Havoc _ | Constant _ -> AP.Set.empty
  | Cast (_, expr) -> accessed_expr expr
  | BinaryOp (left, _, right, _) ->
      AP.Set.union (accessed_expr left) (accessed_expr right)
  | UnaryOp (_, expr, _) -> accessed_expr expr
  | AccessPath ap -> AP.Set.add ap (accessed_ap ap)
  | BoolExpr bexpr -> accessed_bexpr bexpr
  | AddrOf (Deref expr) -> accessed_expr expr
  | AddrOf (Variable _) -> AP.Set.empty
and accessed_bexpr = function
  | Atom (_, left, right) ->
      AP.Set.union (accessed_expr left) (accessed_expr right)
  | And (left, right) | Or (left, right) ->
      AP.Set.union (accessed_bexpr left) (accessed_bexpr right)
and accessed_ap ap =
  AP.Set.add ap (match ap with
		   | Deref expr -> accessed_expr expr
		   | Variable _ -> AP.Set.empty)

(** {0 Substitution functions}  *)

(** Substitute an access path within an expression *)
let rec subst_ap_expr f =
  fold_expr (expr_identity (subst_ap_ap f)) bexpr_identity

(** Substitute an access path within a Boolean expression *)
and subst_ap_bexpr f =
  fold_bexpr (expr_identity (subst_ap_ap f)) bexpr_identity

(** Substitute an access path within an access path *)
and subst_ap_ap f = function
  | Variable _ as var -> f var
  | Deref expr -> f (Deref (subst_ap_expr f expr))

(** Substitute an expression within an expression *)
let rec subst_expr_expr f =
  fold_expr (expr_apply (subst_expr_ap f) f) bexpr_identity

(** Substitute an expression within a Boolean expression *)
and subst_expr_bexpr f =
  fold_bexpr (expr_apply (subst_expr_ap f) f) bexpr_identity

(** Substitute an expression within an access path *)
and subst_expr_ap f = function
  | Deref expr -> Deref (subst_expr_expr f expr)
  | Variable _ as var -> var

let rec subst_var_expr f =
  fold_expr (expr_identity (subst_var_ap f)) bexpr_identity

(** Substitute a variable within a Boolean expression *)
and subst_var_bexpr f =
  fold_bexpr (expr_identity (subst_var_ap f)) bexpr_identity

(** Substitute a variable within an access path *)
and subst_var_ap f = function
  | Variable var -> Variable (f var)
  | Deref expr -> Deref (subst_var_expr f expr)


let rec psubst_var_expr f =
  fold_expr (expr_partial_identity (psubst_var_ap f)) bexpr_partial_identity

(** Partial substitution of a variable within a Boolean expression *)
and psubst_var_bexpr f =
  fold_bexpr (expr_partial_identity (psubst_var_ap f)) bexpr_partial_identity

(** Partial substitution of a variable within an access path *)
and psubst_var_ap f = function
  | Variable var -> begin match f var with
      | Some var -> Some (Variable var)
      | None     -> None
    end
  | Deref expr -> begin match psubst_var_expr f expr with
      | Some expr -> Some (Deref expr)
      | None      -> None
    end

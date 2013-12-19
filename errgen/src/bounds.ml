(*pp camlp4find deriving.syntax *)

open Ast
open Apak
open Ark
open ArkPervasives
open BatPervasives

module StrVar = struct
  include Putil.PString
  let prime x = x ^ "^"
  let to_smt x = Smt.real_var x
  let of_smt sym = match Smt.symbol_refine sym with
    | Z3.Symbol_string str -> str
    | Z3.Symbol_int _ -> assert false
  let typ _ = TyReal
end

module K = Transition.Make(StrVar) (* Transition PKA *)

let _ =
  K.opt_higher_recurrence := false;
  K.opt_disjunctive_recurrence_eq := false;
  K.opt_recurrence_ineq := true;
  K.opt_unroll_loop := false;
  K.opt_loop_guard := true

module F = K.F (* Formulae *)
module T = K.T (* Terms *)
module V = K.V
module D = T.D

let var = T.var % K.V.mk_var

let rec tr_aexp = function
  | Real_const k -> T.const k
  | Sum_exp (s, t) -> T.add (tr_aexp s) (tr_aexp t)
  | Diff_exp (s, t) -> T.sub (tr_aexp s) (tr_aexp t)
  | Mult_exp (s, t) -> T.mul (tr_aexp s) (tr_aexp t)
  | Var_exp v -> var v
  | Unneg_exp t -> T.neg (tr_aexp t)
  | Havoc_aexp -> T.var (K.V.mk_tmp "havoc" TyReal)

let to_aexp =
  let alg = function
  | OVar v ->
    begin match V.lower v with
    | Some var -> Var_exp var
    | None -> assert false
    end
  | OConst k -> Real_const k
  | OAdd (x, y) -> Sum_exp (x, y)
  | OMul (x, y) -> Mult_exp (x, y)
  | ODiv (_, _) | OFloor _ -> assert false
  in
  T.eval alg

let rec tr_bexp = function
  | Bool_const true -> F.top
  | Bool_const false -> F.bottom
  | Eq_exp (s, t) -> F.eq (tr_aexp s) (tr_aexp t)
  | Ne_exp (s, t) -> F.negate (F.eq (tr_aexp s) (tr_aexp t))
  | Gt_exp (s, t) -> F.gt (tr_aexp s) (tr_aexp t)
  | Lt_exp (s, t) -> F.lt (tr_aexp s) (tr_aexp t)
  | Ge_exp (s, t) -> F.geq (tr_aexp s) (tr_aexp t)
  | Le_exp (s, t) -> F.leq (tr_aexp s) (tr_aexp t)
  | And_exp (phi, psi) -> F.conj (tr_bexp phi) (tr_bexp psi)
  | Or_exp (phi, psi) -> F.disj (tr_bexp phi) (tr_bexp psi)
  | Not_exp phi -> F.negate (tr_bexp phi)
  | Havoc_bexp -> F.leqz (T.var (K.V.mk_tmp "havoc" TyReal))

let to_bexp =
  let alg = function
    | OOr (phi, psi) -> Or_exp (phi, psi)
    | OAnd (phi, psi) -> And_exp (phi, psi)
    | OLeqZ t -> Le_exp (to_aexp t, Real_const QQ.zero)
    | OEqZ t -> Eq_exp (to_aexp t, Real_const QQ.zero)
    | OLtZ t -> Lt_exp (to_aexp t, Real_const QQ.zero)
  in
  F.eval alg

let rec eval = function
  | Skip -> K.one 
  | Assign (v, t) -> K.assign v (tr_aexp t)
  | Seq (x, y) -> K.mul (eval x) (eval y)
  | Ite (cond, bthen, belse) ->
    let cond = tr_bexp cond in
    K.add
      (K.mul (K.assume cond) (eval bthen))
      (K.mul (K.assume (F.negate cond)) (eval belse))
  | While (cond, body, _) ->
    let cond = tr_bexp cond in
    K.mul
      (K.star (K.mul (K.assume cond) (eval body)))
      (K.assume (F.negate cond))
  | Assert phi -> K.assume (tr_bexp phi)
  | Print _ -> K.one
  | Assume phi -> K.assume (tr_bexp phi)

let rec add_bounds path_to = function
  | Skip -> (Skip, path_to)
  | Assign (v, t) -> (Assign (v, t), K.mul path_to (K.assign v (tr_aexp t)))
  | Seq (x, y) ->
    let (x, to_y) = add_bounds path_to x in
    let (y, to_end) = add_bounds to_y y in
    (Seq (x, y), to_end)
  | Ite (cond, bthen, belse) ->
    let tr_cond = tr_bexp cond in
    let (bthen, then_path) =
      add_bounds (K.mul path_to (K.assume tr_cond)) bthen
    in
    let (belse, else_path) =
      add_bounds (K.mul path_to (K.assume (F.negate tr_cond))) belse
    in
    (Ite (cond, bthen, belse), K.add then_path else_path)
  | While (cond, body, residual) ->
    let tr_cond = tr_bexp cond in
    let loop = K.star (K.mul (K.assume tr_cond) (eval body)) in
    let to_loop = K.mul path_to loop in

    let to_body = K.mul to_loop (K.assume tr_cond) in
    let (body, _) = add_bounds to_body body in
    let inv =
      let phi =
	F.linearize
	  (fun () -> V.mk_tmp "nonlin" TyReal)
	  (K.to_formula to_body)
      in
      let vars =
	BatList.of_enum (K.M.keys to_body.K.transform
			 /@ (T.var % V.mk_var % StrVar.prime))
      in
      let bounds = F.symbolic_abstract vars phi in
      let to_formula (v, (lower, upper)) =
	let v = T.var (V.mk_var v) in
	let lo = match lower with
	  | Some b -> F.leq (T.const b) v
	  | None -> F.top
	in
	let hi = match upper with
	  | Some b -> F.leq v (T.const b)
	  | None -> F.top
	in
	F.conj lo hi
      in
      let e =
	BatEnum.combine (K.M.keys to_body.K.transform, BatList.enum bounds)
      in
      BatEnum.fold F.conj F.top (e /@ to_formula)
    in
    (While (cond, Seq (Assume (to_bexp inv), body), residual),
     K.mul to_loop (K.assume (F.negate tr_cond)))
  | Assert phi ->
(*
    let path_through = K.mul path_to (K.assume (tr_bexp phi)) in
    if not (F.equiv (K.to_formula path_to) (K.to_formula path_through))
    then begin
      Log.errorf "Could not generate error program: guess failed!";
      assert false
    end;
*)
    (Assert phi, path_to)
  | Print t -> (Print t, path_to)
  | Assume phi -> (Assume phi, K.mul path_to (K.assume (tr_bexp phi)))

let forward_bounds man stmt =
  let assume c pre = F.abstract_assume man pre (tr_bexp c) in
  let rec go stmt pre = match stmt with
    | Print _
    | Skip -> (stmt, pre)
    | Assign (v, exp) ->
      (stmt, F.abstract_assign man pre (V.mk_var v) (tr_aexp exp))
    | Seq (s0, s1) ->
      let (s0, mid) = go s0 pre in
      let (s1, post) = go s1 mid in
      (Seq (s0,s1), post)
    | Ite (c, bthen, belse) ->
      let (then_prop, else_prop) = (assume c pre, assume (Not_exp c) pre) in
      if D.is_bottom then_prop then begin
	let (belse, post_else) = go belse else_prop in
	(Seq (Assume (Not_exp c), belse), post_else)
      end else if D.is_bottom else_prop then begin
	let (bthen, post_then) = go bthen then_prop in
	(Seq (Assume c, bthen), post_then)
      end else begin
	let (bthen, post_then) = go bthen then_prop in
	let (belse, post_else) = go belse else_prop in
	(Ite (c, bthen, belse), D.join post_then post_else)
      end
    | While (c, body, residual) ->
      let iterations = ref 0 in
      let rec fix prop =
	let (body, next) = go body (assume c prop) in
	if D.leq next prop then begin
	  Log.logf Log.info "Found a fixpoint at iteration %i:\n%a"
	    (!iterations)
	    D.format next;
	  (body, D.join pre next)
	end
	else (incr iterations; fix (D.widen prop next))
      in
      let (body, post) = fix (snd (go body (assume c pre))) in
      (* Project out temporaries *)
      let p x = match V.lower x with
	| Some x -> not (BatString.starts_with x "__")
	| None -> false
      in
      let post = D.exists man p post in
      if D.is_bottom post then begin
	(While (c, Assume (Bool_const false), residual), post)
      end else begin
	let inv = Assume (to_bexp (F.of_abstract (assume c post))) in
	(While (c, Seq (inv, body), residual), assume (Not_exp c) post)
      end
    | Assert c
    | Assume c -> (stmt, assume c pre)
  in
  fst (go stmt (D.top man (D.Env.of_list [])))

let add_bounds (Prog s) =
  let s =
    Log.phase "Forward invariant generation"
      (forward_bounds (Box.manager_alloc ()))
      s
  in
  let (s, _) =
    Log.phase "Invariant generation" (add_bounds K.one) s
  in
  Prog s

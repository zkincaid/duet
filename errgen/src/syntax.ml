open Ast
open Apak
open Ark
open ArkPervasives

let eps_mach = QQ.exp (QQ.of_int 2) (-53)
let eps_0 = QQ.exp (QQ.of_int 2) (-53)

module Var = struct
  type t = string deriving (Compare)
  include Putil.MakeFmt(struct
    type a = t
    let format formatter str = Format.pp_print_string formatter str
  end)
  let compare = Compare_t.compare
  let hash = Hashtbl.hash
  let equal x y = x = y
  let prime x = x ^ "^"
  let to_smt x = Smt.real_var x
  let of_smt sym = match Smt.symbol_refine sym with
    | Smt.Symbol_string str -> str
    | Smt.Symbol_int _ -> assert false
  let typ _ = TyReal
  module E = Enumeration.Make(Putil.PString)
  let enum = E.empty ()
  let tag = E.to_int enum
end

let approxify = primify
let idealify x = x

module K =
  struct
    include Transition.Make(Var) (* Transition PKA *)
    let default = one
  end

module T = K.T
module F = K.F
module V = K.V
module D = T.D

let rec real_aexp = function
  | Real_const k -> T.const k
  | Sum_exp (s, t) -> T.add (real_aexp s) (real_aexp t)
  | Diff_exp (s, t) -> T.sub (real_aexp s) (real_aexp t)
  | Mult_exp (s, t) -> T.mul (real_aexp s) (real_aexp t)
  | Div_exp (s, t) -> T.div (real_aexp s) (real_aexp t)
  | Var_exp v -> T.var (K.V.mk_var v)
  | Unneg_exp t -> T.neg (real_aexp t)
  | Havoc_aexp -> T.var (K.V.mk_tmp "havoc" TyReal)


let rec real_bexp = function
  | Bool_const true -> F.top
  | Bool_const false -> F.bottom
  | Eq_exp (s, t) -> F.eq (real_aexp s) (real_aexp t)
  | Ne_exp (s, t) -> F.negate (F.eq (real_aexp s) (real_aexp t))
  | Gt_exp (s, t) -> F.gt (real_aexp s) (real_aexp t)
  | Lt_exp (s, t) -> F.lt (real_aexp s) (real_aexp t)
  | Ge_exp (s, t) -> F.geq (real_aexp s) (real_aexp t)
  | Le_exp (s, t) -> F.leq (real_aexp s) (real_aexp t)
  | And_exp (phi, psi) -> F.conj (real_bexp phi) (real_bexp psi)
  | Or_exp (phi, psi) -> F.disj (real_bexp phi) (real_bexp psi)
  | Not_exp phi -> F.negate (real_bexp phi)
  | Havoc_bexp -> F.leqz (T.var (K.V.mk_tmp "havoc" TyReal))

let rec float_aexp = function
  | Real_const k -> (T.const (Mpqf.of_float (Mpqf.to_float k)), F.top)
  | Sum_exp (s, t) -> float_binop T.add s t
  | Diff_exp (s, t) -> float_binop T.sub s t
  | Mult_exp (s, t) -> float_binop T.mul s t
  | Div_exp (s, t) -> float_binop T.div s t
  | Var_exp v -> (T.var (K.V.mk_var v), F.top)
  | Unneg_exp t ->
    let (t, t_err) = float_aexp t in
    (T.neg t, t_err)
  | Havoc_aexp -> (T.var (K.V.mk_tmp "havoc" TyReal), F.top)
and float_binop op s t =
  let (s,s_err) = float_aexp s in
  let (t,t_err) = float_aexp t in
  let err = T.var (K.V.mk_tmp "err" TyReal) in
  let term = op s t in
  let err_magnitude = T.mul term (T.const eps_mach) in
  let err_constraint =
    F.disj
      (F.conj
         (F.leq (T.neg err_magnitude) err)
         (F.leq err err_magnitude))
      (F.conj
         (F.leq (T.neg err_magnitude) err)
         (F.leq err (T.neg err_magnitude)))
  in
  (T.add term err, F.conj err_constraint (F.conj s_err t_err))

let rec float_bexp = function
  | Bool_const true -> F.top
  | Bool_const false -> F.bottom
  | Eq_exp (s, t) -> float_bool_binop F.eq s t
  | Gt_exp (s, t) -> float_bool_binop F.gt s t
  | Lt_exp (s, t) -> float_bool_binop F.lt s t
  | Ge_exp (s, t) -> float_bool_binop F.geq s t
  | Le_exp (s, t) -> float_bool_binop F.leq s t
  | And_exp (phi, psi) -> F.conj (float_bexp phi) (float_bexp psi)
  | Or_exp (phi, psi) -> F.disj (float_bexp phi) (float_bexp psi)
  | Havoc_bexp -> F.leqz (T.var (K.V.mk_tmp "havoc" TyReal))
  | Ne_exp _ -> assert false
  | Not_exp _ -> assert false
and float_bool_binop op s t =
  let (s,s_err) = float_aexp s in
  let (t,t_err) = float_aexp t in
  F.conj (op s t) (F.conj s_err t_err)
let float_bexp bexp = float_bexp (nnf bexp)

let float_weight = function
  | Assign (v, rhs) ->
    let (rhs, rhs_err) = float_aexp rhs in
    { K.assign v rhs with K.guard = rhs_err }
  | Assume phi -> K.assume (float_bexp phi)
  | Skip -> K.one
  | Assert _ | Print _ -> K.one

let real_weight = function
  | Assign (v, rhs) -> K.assign v (real_aexp rhs)
  | Assume phi -> K.assume (real_bexp phi)
  | Skip -> K.one
  | Assert _ | Print _ -> K.one

let linearize = F.linearize (fun () -> V.mk_real_tmp "nonlin")

let not_tmp v = V.lower v != None

let guard_ex p phi =
  let vars =
    K.VarSet.elements (K.formula_free_program_vars phi)
  in
  let vars =
    List.filter (fun v -> p (V.mk_var v)) vars
  in
  let templates =
    let is_primed v =
      v.[String.length v - 1] = '''
      || (v.[String.length v - 1] = '^' && v.[String.length v - 2] = ''')
    in
    let unprimed =
      List.filter (fun v -> not (is_primed v)) vars
    in
    let primify v =
      if v.[String.length v - 1] = '^'
      then (String.sub v 0 (String.length v - 1)) ^ "'^"
      else v ^ "'"
    in
    (List.map (fun v -> T.var (V.mk_var v)) vars)
    @ (List.map
         (fun v -> T.sub (T.var (V.mk_var v)) (T.var (V.mk_var (primify v))))
         unprimed)
  in
  F.boxify templates phi

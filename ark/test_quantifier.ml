open OUnit
open Quantifier
open Syntax
open Apak

module Ctx = MakeSimplifyingContext ()
module Infix = Syntax.Infix(Ctx)
let ctx = Ctx.context
let smt_ctx = Smt.mk_context ctx []

let rsym = Ctx.mk_symbol ~name:"r" `TyReal
let ssym = Ctx.mk_symbol ~name:"s" `TyReal

let wsym = Ctx.mk_symbol ~name:"w" `TyInt
let xsym = Ctx.mk_symbol ~name:"x" `TyInt
let ysym = Ctx.mk_symbol ~name:"y" `TyInt
let zsym = Ctx.mk_symbol ~name:"z" `TyInt

let r = mk_const ctx rsym
let s = mk_const ctx ssym

let w = mk_const ctx wsym
let x = mk_const ctx xsym
let y = mk_const ctx ysym
let z = mk_const ctx zsym

let frac num den = Ctx.mk_real (QQ.of_frac num den)
let int k = Ctx.mk_real (QQ.of_int k)

let assert_equal_term s t =
  assert_equal ~printer:(Term.show ctx) s t
let assert_equiv_formula s t =
  assert_equal ~printer:(Formula.show ctx) ~cmp:(smt_ctx#equiv) s t
let assert_equal_qq x y =
  assert_equal ~printer:QQ.show ~cmp:QQ.equal x y

let simsat1 () =
  let phi =
    Ctx.mk_forall ~name:"r" `TyReal
      (Ctx.mk_exists ~name:"s" `TyReal
         (Ctx.mk_lt (Ctx.mk_var 1 `TyReal) (Ctx.mk_var 0 `TyReal)))
  in
  assert_equal `Sat (simsat smt_ctx phi)

let mbp1 () =
  let phi =
    let open Infix in
    let s = Ctx.mk_var 0 `TyReal in
    (Ctx.mk_exists ~name:"s" `TyReal
       (s = r && (s <= (int 0) || r <= (int 1))))
  in
  let psi =
    let open Infix in
    r <= (int 1)
  in
  assert_equiv_formula (qe_mbp smt_ctx phi) psi

let mbp2 () =
  let phi =
    let s = Ctx.mk_var 0 `TyReal in
    Ctx.mk_forall ~name:"s" `TyReal
      (Ctx.mk_leq r (Ctx.mk_ite
                       (Ctx.mk_lt (int 0) s)
                       s
                       (Ctx.mk_neg s)))
  in
  let psi = Ctx.mk_leq r (int 0) in
  assert_equiv_formula (qe_mbp smt_ctx phi) psi

let sim1 () =
  let phi =
    let x = Ctx.mk_var 1 `TyInt in
    let y = Ctx.mk_var 0 `TyInt in
    let open Infix in
    Ctx.mk_exists ~name:"x" `TyInt
      (Ctx.mk_forall ~name:"y" `TyInt
         ((Ctx.mk_not ((y < x) && (x < (int 2))))
          || x = (int 1)))
  in
  assert_bool "sim1" (simsat smt_ctx phi = `Sat)

let sim2 () =
  let phi =
    let x = Ctx.mk_var 1 `TyInt in
    let y = Ctx.mk_var 0 `TyInt in
    let open Infix in
    Ctx.mk_exists ~name:"x" `TyInt
      (Ctx.mk_forall ~name:"y" `TyInt
         (x <= (Ctx.mk_ite ((int 0) < y) y (Ctx.mk_neg y))))
  in
  assert_bool "sim2" (simsat smt_ctx phi = `Sat)

let strategy1 () =
  let phi =
    let open Infix in
    (((int 0) <= x) && (x < y))
    || ((x < (int 0)) && (y < x))
  in
  let qf_prefix = [`Forall, xsym; `Exists, ysym] in
  match winning_strategy smt_ctx qf_prefix phi with
  | `Sat strategy ->
    assert_bool "strategy1" (check_strategy smt_ctx qf_prefix phi strategy)
  | _ -> assert false

let strategy2 () =
  let phi =
    let open Infix in
    (y < w) && (y < x)
    && (w < z) && (x < z)
  in
  let qf_prefix =
    [`Forall, wsym; `Forall, xsym; `Exists, ysym; `Exists, zsym]
  in
  match winning_strategy smt_ctx qf_prefix phi with
  | `Sat strategy ->
    assert_bool "strategy2" (check_strategy smt_ctx qf_prefix phi strategy)
  | _ -> assert false

let suite = "Quantifier" >::: [
    "simsat1" >:: simsat1;
    "mbp1" >:: mbp1;
    "mbp2" >:: mbp2;
    "sim1" >:: sim1;
    "sim2" >:: sim2;
    "strategy1" >:: strategy1;
    "strategy2" >:: strategy2;
  ]

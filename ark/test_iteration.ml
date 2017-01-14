open OUnit
open Abstract
open Syntax
open ArkApron

module Ctx = MakeSimplifyingContext ()
module Infix = Syntax.Infix(Ctx)
let ctx = Ctx.context
let smt_ctx = ArkZ3.mk_context ctx []

let rsym = Ctx.mk_symbol ~name:"r" `TyReal
let ssym = Ctx.mk_symbol ~name:"s" `TyReal

let wsym = Ctx.mk_symbol ~name:"w" `TyInt
let xsym = Ctx.mk_symbol ~name:"x" `TyInt
let ysym = Ctx.mk_symbol ~name:"y" `TyInt
let zsym = Ctx.mk_symbol ~name:"z" `TyInt
let wsym' = Ctx.mk_symbol ~name:"w'" `TyInt
let xsym' = Ctx.mk_symbol ~name:"x'" `TyInt
let ysym' = Ctx.mk_symbol ~name:"y'" `TyInt
let zsym' = Ctx.mk_symbol ~name:"z'" `TyInt

let r = mk_const ctx rsym
let s = mk_const ctx ssym

let w = mk_const ctx wsym
let x = mk_const ctx xsym
let y = mk_const ctx ysym
let z = mk_const ctx zsym
let w' = mk_const ctx wsym'
let x' = mk_const ctx xsym'
let y' = mk_const ctx ysym'
let z' = mk_const ctx zsym'

let frac num den = Ctx.mk_real (QQ.of_frac num den)
let int k = Ctx.mk_real (QQ.of_int k)

let assert_equal_term s t =
  assert_equal ~printer:(Term.show ctx) s t
let assert_equiv_formula s t =
  assert_equal ~printer:(Formula.show ctx) ~cmp:(smt_ctx#equiv) s t
let assert_equal_qq x y =
  assert_equal ~printer:QQ.show ~cmp:QQ.equal x y
let assert_implies phi psi =
  if not (smt_ctx#implies phi psi) then
    assert_failure (Printf.sprintf "%s\ndoes not imply\n%s"
                      (Formula.show ctx phi)
                      (Formula.show ctx psi))

let tr_symbols = [(wsym,wsym');(xsym,xsym');(ysym,ysym');(zsym,zsym')]

let prepost () =
  let phi =
    let open Infix in
    (int 0) <= x && x <= x'
  in
  let closure = Iteration.star ctx phi tr_symbols in
  assert_implies closure (Ctx.mk_leq (int 0) x);
  assert_implies closure (Ctx.mk_leq (int 0) x')

let simple_induction () =
  let phi =
    let open Infix in
    w' = w + (int 1)
    && x' = x + (int 2)
    && y' = y + z
    && z = (int 3)
  in
  let closure = Iteration.star ctx phi tr_symbols in
  let result =
    let open Infix in
    (int 2)*(w' - w) = x' - x
    && (w' - w) + (x' - x) = (y' - y)
  in
  assert_implies closure result

let stratified1 () =
  let tr_symbols = [(xsym,xsym');(ysym,ysym')] in
  let phi =
    let open Infix in
    x' = x + (int 1)
    && y' = y + z
  in
  let closure = Iteration.star ctx phi tr_symbols in
  let result =
    let open Infix in
    z*(x' - x) = (y' - y)
  in
  assert_implies closure result

let stratified2 () =
  let tr_symbols = [(xsym,xsym');(ysym,ysym')] in
  let phi =
    let open Infix in
    x' = x + (int 1)
    && y' = y + x
  in
  let closure =
    let open Infix in
    x = (int 0)
    && y = (int 0)
    && Iteration.star ctx phi tr_symbols
  in
  let result =
    let open Infix in
    (int 2)*y' = x'*(x' - (int 1))
  in
  assert_implies closure result

let suite = "Iteration" >::: [
    "prepost" >:: prepost;
    "simple_induction" >:: simple_induction;
    "stratified1" >:: stratified1;
    "stratified2" >:: stratified2;
  ]

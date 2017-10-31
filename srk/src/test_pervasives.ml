open OUnit
open Syntax

module Ctx = MakeSimplifyingContext ()
module Infix = Syntax.Infix(Ctx)
let srk = Ctx.context
let smt_ctx = SrkZ3.mk_context srk []

let qsym = Ctx.mk_symbol ~name:"q" `TyReal
let rsym = Ctx.mk_symbol ~name:"r" `TyReal
let ssym = Ctx.mk_symbol ~name:"s" `TyReal
let q : 'a term = Ctx.mk_const qsym
let r : 'a term = Ctx.mk_const rsym
let s : 'a term = Ctx.mk_const ssym

let vsym = Ctx.mk_symbol ~name:"v" `TyInt
let wsym = Ctx.mk_symbol ~name:"w" `TyInt
let xsym = Ctx.mk_symbol ~name:"x" `TyInt
let ysym = Ctx.mk_symbol ~name:"y" `TyInt
let zsym = Ctx.mk_symbol ~name:"z" `TyInt
let vsym' = Ctx.mk_symbol ~name:"v'" `TyInt
let wsym' = Ctx.mk_symbol ~name:"w'" `TyInt
let xsym' = Ctx.mk_symbol ~name:"x'" `TyInt
let ysym' = Ctx.mk_symbol ~name:"y'" `TyInt
let zsym' = Ctx.mk_symbol ~name:"z'" `TyInt

let v : 'a term = Ctx.mk_const vsym
let w : 'a term = Ctx.mk_const wsym
let x : 'a term = Ctx.mk_const xsym
let y : 'a term = Ctx.mk_const ysym
let z : 'a term = Ctx.mk_const zsym
let v' : 'a term = Ctx.mk_const vsym'
let w' : 'a term = Ctx.mk_const wsym'
let x' : 'a term = Ctx.mk_const xsym'
let y' : 'a term = Ctx.mk_const ysym'
let z' : 'a term = Ctx.mk_const zsym'

let frac num den = Ctx.mk_real (QQ.of_frac num den)
let int k = Ctx.mk_real (QQ.of_int k)

let assert_equal_term s t =
  assert_equal ~printer:(Term.show srk) s t

let assert_equal_formula s t =
  assert_equal ~printer:(Formula.show srk) s t

let assert_equiv_formula s t =
  assert_equal ~printer:(Formula.show srk) ~cmp:(smt_ctx#equiv) s t

let assert_equal_qq x y =
  assert_equal ~printer:QQ.show ~cmp:QQ.equal x y

let assert_implies phi psi =
  if not (smt_ctx#implies phi psi) then
    assert_failure (Printf.sprintf "%s\ndoes not imply\n%s"
                      (Formula.show srk phi)
                      (Formula.show srk psi))

let assert_not_implies phi psi =
  if smt_ctx#implies phi psi then
    assert_failure (Printf.sprintf "%s\nimplies\n%s"
                      (Formula.show srk phi)
                      (Formula.show srk psi))

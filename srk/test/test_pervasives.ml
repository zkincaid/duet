open Srk
open OUnit
open Syntax
open Linear

module Ctx = MakeSimplifyingContext ()
module Infix = Syntax.Infix(Ctx)
let srk = Ctx.context
let z3 = Z3.mk_context []
let formula_of_z3 = SrkZ3.formula_of_z3 srk
let z3_of_formula = SrkZ3.z3_of_formula srk z3
let term_of_z3 = SrkZ3.term_of_z3 srk
let z3_of_term = SrkZ3.z3_of_term srk z3
let z3_of_arith_term = SrkZ3.z3_of_arith_term srk z3
let z3_of_arr_term = SrkZ3.z3_of_arr_term srk z3


let qsym = Ctx.mk_symbol ~name:"q" `TyReal
let rsym = Ctx.mk_symbol ~name:"r" `TyReal
let ssym = Ctx.mk_symbol ~name:"s" `TyReal
let q : 'a arith_term = Ctx.mk_const qsym
let r : 'a arith_term = Ctx.mk_const rsym
let s : 'a arith_term = Ctx.mk_const ssym

let bsym = Ctx.mk_symbol ~name:"b" `TyBool
let b : 'a formula = Ctx.mk_const bsym

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

let v : 'a arith_term = Ctx.mk_const vsym
let w : 'a arith_term = Ctx.mk_const wsym
let x : 'a arith_term = Ctx.mk_const xsym
let y : 'a arith_term = Ctx.mk_const ysym
let z : 'a arith_term = Ctx.mk_const zsym
let v' : 'a arith_term = Ctx.mk_const vsym'
let w' : 'a arith_term = Ctx.mk_const wsym'
let x' : 'a arith_term = Ctx.mk_const xsym'
let y' : 'a arith_term = Ctx.mk_const ysym'
let z' : 'a arith_term = Ctx.mk_const zsym'

let a1sym = Ctx.mk_symbol ~name:"a1" `TyArr
let a2sym = Ctx.mk_symbol ~name:"a2" `TyArr
let a3sym = Ctx.mk_symbol ~name:"a3" `TyArr
let a1 = Ctx.mk_const a1sym
let a2 = Ctx.mk_const a2sym
let a3 = Ctx.mk_const a3sym

let fsym = Ctx.mk_symbol ~name:"f" (`TyFun ([`TyInt], `TyInt))
let f : Ctx.arith_term -> Ctx.arith_term =
  fun x -> Ctx.mk_app fsym [(x :> (Ctx.t, typ_fo) expr)]

let frac num den = Ctx.mk_real (QQ.of_frac num den)
let int k = Ctx.mk_real (QQ.of_int k)

let mk_vector vec =
  List.fold_left
    (fun vec (i, k) -> QQVector.add_term k i vec)
    QQVector.zero
    (List.mapi (fun i k -> (i, QQ.of_int k)) vec)

let mk_matrix mat =
  List.fold_left
    (fun mat (i, row) -> QQMatrix.add_row i row mat)
    QQMatrix.zero
    (List.mapi (fun i row -> (i, mk_vector row)) mat)

let mk_qqvector vec =
  List.fold_left
    (fun vec (i, k) -> QQVector.add_term k i vec)
    QQVector.zero
    (List.mapi (fun i k -> (i, k)) vec)

let mk_qqmatrix mat =
  List.fold_left
    (fun mat (i, row) -> QQMatrix.add_row i row mat)
    QQMatrix.zero
    (List.mapi (fun i row -> (i, mk_qqvector row)) mat)

let assert_equal_arith_term s t =
  assert_equal ~cmp:ArithTerm.equal ~printer:(ArithTerm.show srk) s t

let assert_equal_term s t =
  assert_equal ~cmp:Term.equal ~printer:(Term.show srk) s t

let assert_equal_formula s t =
  assert_equal ~printer:(Formula.show srk) s t

let assert_equiv_formula s t =
  assert_equal
    ~printer:(Formula.show srk)
    ~cmp:(fun x y -> Smt.equiv srk x y = `Yes) s t

let assert_equiv_quantified_formula s t =
  assert_equal
    ~printer:(Formula.show srk)
    ~cmp:(fun x y -> Quantifier.simsat srk (mk_not srk (mk_iff srk x y)) = `Unsat) s t

let assert_equal_qq x y =
  assert_equal ~printer:QQ.show ~cmp:QQ.equal x y

let assert_equal_qqmatrix x y =
  assert_equal ~cmp:Linear.QQMatrix.equal ~printer:Linear.QQMatrix.show x y

let assert_equal_qqvector x y =
  assert_equal ~cmp:Linear.QQVector.equal ~printer:Linear.QQVector.show x y

let assert_equal_exppoly x y =
  assert_equal ~cmp:ExpPolynomial.equal ~printer:ExpPolynomial.show x y

let assert_equal_up_exppoly x y =
  assert_equal ~cmp:ExpPolynomial.UltPeriodic.equal ~printer:ExpPolynomial.UltPeriodic.show x y

let assert_equal_pathexpr context x y =
  assert_equal ~cmp:(Pathexpr.equiv context) ~printer:Pathexpr.show x y

let assert_implies phi psi =
  if not (Smt.entails srk phi psi = `Yes) then
    assert_failure (Printf.sprintf "%s\ndoes not imply\n%s"
                      (Formula.show srk phi)
                      (Formula.show srk psi))

let assert_not_implies phi psi =
  if (Smt.entails srk phi psi = `Yes) then
    assert_failure (Printf.sprintf "%s\nimplies\n%s"
                      (Formula.show srk phi)
                      (Formula.show srk psi))

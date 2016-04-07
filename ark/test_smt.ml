open OUnit
open Syntax

module Ctx = MakeSimplifyingContext ()
module Infix = Syntax.Infix(Ctx)
let ctx = Ctx.context
let smt_ctx = Smt.mk_context ctx []

let r = Ctx.mk_const (Ctx.mk_symbol ~name:"r" `TyReal)
let s = Ctx.mk_const (Ctx.mk_symbol ~name:"s" `TyReal)

let w = Ctx.mk_const (Ctx.mk_symbol ~name:"w" `TyInt)
let x = Ctx.mk_const (Ctx.mk_symbol ~name:"x" `TyInt)
let y = Ctx.mk_const (Ctx.mk_symbol ~name:"y" `TyInt)
let z = Ctx.mk_const (Ctx.mk_symbol ~name:"z" `TyInt)

let b = Ctx.mk_const (Ctx.mk_symbol ~name:"b" `TyBool)
let f = Ctx.mk_symbol ~name:"f" (`TyFun ([`TyInt; `TyBool], `TyInt))
let p = Ctx.mk_symbol ~name:"p" (`TyFun ([`TyInt; `TyBool], `TyBool))

let frac num den = Ctx.mk_real (QQ.of_frac num den)
let int k = Ctx.mk_real (QQ.of_int k)

let assert_equal_term s t =
  assert_equal ~printer:(Term.show ctx)  s t
let assert_equal_formula s t =
  assert_equal ~printer:(Formula.show ctx) s t

let roundtrip0 () =
  let tru = mk_true ctx in
  let fls = mk_false ctx in
  assert_equal_formula tru (smt_ctx#formula_of (smt_ctx#of_formula tru));
  assert_equal_formula fls (smt_ctx#formula_of (smt_ctx#of_formula fls))

let roundtrip1 () =
  let term =
    let open Infix in
    x * x * x mod (int 10) + (frac 100 3) / (r - z + s)
  in
  assert_equal_term term (smt_ctx#term_of (smt_ctx#of_term term))

let roundtrip2 () =
  let phi =
    let open Infix in
    x <= y && y <= z && x < z
    || x = y && y = z
  in
  assert_equal_formula phi (smt_ctx#formula_of (smt_ctx#of_formula phi))

let roundtrip3 () =
  let phi =
    let open Infix in
    forall ~name:"a" `TyInt
      (forall ~name:"b" `TyInt
         (!((var 0 `TyInt) < (var 1 `TyInt))
          || (exists ~name:"c" `TyReal
                ((var 1 `TyInt) < (var 0 `TyReal)
                 && (var 0 `TyReal) < (var 2 `TyInt)))))
  in
  assert_equal_formula phi (smt_ctx#formula_of (smt_ctx#of_formula phi))

let roundtrip4 () =
  let term =
    let open Infix in
    (Ctx.mk_app f [x; b]) + x
  in
  assert_equal_term term (smt_ctx#term_of (smt_ctx#of_term term))

let is_interpolant phi psi itp =
  (smt_ctx#implies phi itp)
  && smt_ctx#is_sat (mk_and ctx [itp; psi]) = `Unsat

let interpolate1 () =
  let phi =
    let open Infix in
    x = y && (int 0) = x
  in
  let psi =
    let open Infix in
    y = z && z < (int 0)
  in
  (match smt_ctx#interpolate_seq [phi; psi] with
   | `Unsat [itp] ->
     assert_bool "itp(y == x < 0, 0 < z = y)" (is_interpolant phi psi itp)
   | _ -> assert false);
  (match smt_ctx#interpolate_seq [psi; phi] with
   | `Unsat [itp] ->
     assert_bool "itp(0 < z = y, y == x < 0)" (is_interpolant psi phi itp)
   | _ -> assert false)

let interpolate2 () =
  let phi =
    let open Infix in
    x = (int 0) && y = x + (int 1) && y < (int 1)
  in
  let psi = Ctx.mk_true in
  (match smt_ctx#interpolate_seq [phi; psi] with
   | `Unsat [itp] ->
     assert_bool "itp(x = 0 /\\ y = x + 1 /\\ y < 1, true)"
       (is_interpolant phi psi itp)
   | _ -> assert false);
  (match smt_ctx#interpolate_seq [psi; phi] with
   | `Unsat [itp] ->
     assert_bool "itp(true, x = 0 /\\ y = x + 1 /\\ y < 1)"
       (is_interpolant psi phi itp)
   | _ -> assert false)

let interpolate3 () =
  let phi =
    let open Infix in
    x = (int 1) && w = (int 1)
  in
  let psi =
    let open Infix in
    y = x + w && y <= (int 1)
  in
  (match smt_ctx#interpolate_seq [phi; psi] with
   | `Unsat [itp] ->
     assert_bool "itp(x = w = 1, y = x + w <= 1)"
       (is_interpolant phi psi itp)
   | _ -> assert false);
  (match smt_ctx#interpolate_seq [psi; phi] with
   | `Unsat [itp] ->
     assert_bool "itp(y = x + w <= 1, x = w = 1)"
       (is_interpolant psi phi itp)
   | _ -> assert false)


let suite = "SMT" >:::
  [
    "roundtrip0" >:: roundtrip0;
    "roundtrip1" >:: roundtrip1;
    "roundtrip2" >:: roundtrip2;
    "roundtrip3" >:: roundtrip3;
    "roundtrip4" >:: roundtrip4;
    "interpolate1" >:: interpolate1;
    "interpolate2" >:: interpolate2;
    "interpolate3" >:: interpolate3;
  ]

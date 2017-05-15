open OUnit
open Syntax

module Ctx = MakeSimplifyingContext ()
module Infix = Syntax.Infix(Ctx)
let ctx = Ctx.context
let smt_ctx = ArkZ3.mk_context ctx []

let r = Ctx.mk_const (Ctx.mk_symbol ~name:"r" `TyReal)
let s = Ctx.mk_const (Ctx.mk_symbol ~name:"s" `TyReal)

let wsym = Ctx.mk_symbol ~name:"w" `TyInt
let xsym = Ctx.mk_symbol ~name:"x" `TyInt
let ysym = Ctx.mk_symbol ~name:"y" `TyInt
let zsym = Ctx.mk_symbol ~name:"z" `TyInt
let w = Ctx.mk_const wsym
let x = Ctx.mk_const xsym
let y = Ctx.mk_const ysym
let z = Ctx.mk_const zsym

let b = Ctx.mk_const (Ctx.mk_symbol ~name:"b" `TyBool)

let gsym = Ctx.mk_symbol ~name:"g" (`TyFun ([`TyInt; `TyInt], `TyInt))
let g : Ctx.term * Ctx.term -> Ctx.term =
  fun (x, y) -> Ctx.mk_app gsym [x; y]

let fsym = Ctx.mk_symbol ~name:"f" (`TyFun ([`TyInt; `TyBool], `TyInt))
let f : Ctx.term * Ctx.formula -> Ctx.term =
  fun (x, y) -> Ctx.mk_app fsym [(x :> (Ctx.t, typ_fo) expr);
                                 (y :> (Ctx.t, typ_fo) expr)]

let p = Ctx.mk_symbol ~name:"p" (`TyFun ([`TyInt; `TyBool], `TyBool))

let hsym = Ctx.mk_symbol ~name:"h" (`TyFun ([`TyReal; `TyReal], `TyReal))
let h : Ctx.term * Ctx.term -> Ctx.term =
  fun (x, y) -> Ctx.mk_app hsym [x; y]

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
    (f (x, b)) + x
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

let interpretation1 () =
  let phi =
    let open Infix in
    (int 0) = x && x <= y
    && g(x, y) < g(y, x) && g(int 0, int 0) = (int 0)
  in
  match smt_ctx#get_model phi with
  | `Sat m ->
    let interp = Interpretation.of_model ctx m [gsym; xsym; ysym] in
    assert_bool "is_model"
      (Interpretation.evaluate_formula interp phi)
  | _ -> assert false

let implicant1 () =
  let phi =
    let open Infix in
    (int 0) = x
    && x <= f((int 0), (int 1) = y || (int 2)= y)
    && (y <= (int 0) || (x = (int 3)))
  in
  match smt_ctx#get_model phi with
  | `Sat m ->
    let interp = Interpretation.of_model ctx m [fsym; xsym; ysym] in
    begin match Interpretation.select_implicant interp phi with
      | Some implicant ->
        List.iter (fun psi ->
            assert_bool "is_model"
              (Interpretation.evaluate_formula interp psi))
          implicant
      | None -> assert false
    end
  | _ -> assert false

let affine_interp1 () =
  let phi =
    let open Infix in
    h(x, y) = h(y, x)
    && x < y
    && h(x, (int 0)) = x
    && h(y, (int 0)) = y
  in
  match smt_ctx#get_model phi with
  | `Sat m ->
    let interp = Interpretation.of_model ctx m [hsym; xsym; ysym] in
    let has_affine_interp =
      match Interpretation.affine_interpretation interp phi with
      | `Sat _ -> true
      | _ -> false
    in
    assert_bool "has_affine_interp" has_affine_interp
  | _ -> assert false

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
    "interpretation1" >:: interpretation1;
    "implicant1" >:: implicant1;
    "affine_interp1" >:: affine_interp1;
  ]

open OUnit
open Syntax

module F = Formula
module T = Term

let ctx = Syntax.mk_string_context ()
let z3 = new Smt.context []
module S = ImplicitContext(struct
    type t = string * typ
    let context = ctx
  end)

let r = S.const (symbol_of_const ctx ("r", TyReal))
let s = S.const (symbol_of_const ctx ("s", TyReal))
let t = S.const (symbol_of_const ctx ("t", TyReal))

let w = S.const (symbol_of_const ctx ("w", TyInt))
let x = S.const (symbol_of_const ctx ("x", TyInt))
let y = S.const (symbol_of_const ctx ("y", TyInt))
let z = S.const (symbol_of_const ctx ("z", TyInt))

let frac num den = Term.mk_real ctx (QQ.of_frac num den)
let int k = Term.mk_real ctx (QQ.of_int k)

let assert_equal_term s t =
  assert_equal ~printer:(Term.show ctx) s t
let assert_equal_formula s t =
  assert_equal ~printer:(Formula.show ctx) s t

let roundtrip1 () =
  let term =
    let open S in
    x * x * x mod (int 10) + (frac 100 3) / (r - z + s)
  in
  assert_equal_term term (z3#term_of ctx (z3#of_term term))

let roundtrip2 () =
  let phi =
    let open S in
    x <= y && y <= z && x < z
    || x = y && y = z
  in
  assert_equal_formula phi (z3#formula_of ctx (z3#of_formula phi))


let roundtrip3 () =
  let phi =
    let open S in
    forall ~name:"a" TyInt
      (forall ~name:"b" TyInt
         (!((var 0 TyInt) < (var 1 TyInt))
          || (exists ~name:"c" TyReal
                ((var 1 TyInt) < (var 0 TyReal)
                 && (var 0 TyReal) < (var 2 TyInt)))))
  in
  assert_equal_formula phi (z3#formula_of ctx (z3#of_formula phi))

let is_interpolant phi psi itp =
  (Smt.implies z3 phi itp)
  && Smt.is_sat z3 (Formula.mk_and ctx itp psi) = `Unsat

let interpolate1 () =
  let phi =
    let open S in
    x = y && (int 0) = x
  in
  let psi =
    let open S in
    y = z && z < (int 0)
  in
  (match z3#interpolate_seq ctx [phi; psi] with
   | Some [itp] ->
     assert_bool "itp(y == x < 0, 0 < z = y)" (is_interpolant phi psi itp)
   | _ -> assert false);
  (match z3#interpolate_seq ctx [psi; phi] with
   | Some [itp] ->
     assert_bool "itp(0 < z = y, y == x < 0)" (is_interpolant psi phi itp)
   | _ -> assert false)

let interpolate2 () =
  let phi =
    let open S in
    x = (int 0) && y = x + (int 1) && y < (int 1)
  in
  let psi = S.tru in
  (match z3#interpolate_seq ctx [phi; psi] with
   | Some [itp] ->
     assert_bool "itp(x = 0 /\\ y = x + 1 /\\ y < 1, true)"
       (is_interpolant phi psi itp)
   | _ -> assert false);
  (match z3#interpolate_seq ctx [psi; phi] with
   | Some [itp] ->
     assert_bool "itp(true, x = 0 /\\ y = x + 1 /\\ y < 1)"
       (is_interpolant psi phi itp)
   | _ -> assert false)

let interpolate3 () =
  let phi =
    let open S in
    x = (int 1) && w = (int 1)
  in
  let psi =
    let open S in
    y = x + w && y <= (int 1)
  in
  (match z3#interpolate_seq ctx [phi; psi] with
   | Some [itp] ->
     assert_bool "itp(x = w = 1, y = x + w <= 1)"
       (is_interpolant phi psi itp)
   | _ -> assert false);
  (match z3#interpolate_seq ctx [psi; phi] with
   | Some [itp] ->
     assert_bool "itp(y = x + w <= 1, x = w = 1)"
       (is_interpolant psi phi itp)
   | _ -> assert false)


let suite = "SMT" >:::
  [
    "roundtrip1" >:: roundtrip1;
    "roundtrip2" >:: roundtrip2;
    "roundtrip3" >:: roundtrip3;
    "interpolate1" >:: interpolate1;
    "interpolate2" >:: interpolate2;
    "interpolate3" >:: interpolate3;
  ]

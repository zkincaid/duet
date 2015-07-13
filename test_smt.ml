open OUnit
open Syntax

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

let assert_equal_term s t =
  assert_equal ~printer:(Term.show ctx) s t
let assert_equal_formula s t =
  assert_equal ~printer:(Formula.show ctx) s t

let roundtrip1 () =
  let term =
    let open S in
    x * x * x mod (frac 10 1) + (frac 100 3) / (r - z + s)
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

let suite = "SMT" >:::
  [
    "roundtrip1" >:: roundtrip1;
    "roundtrip2" >:: roundtrip2;
    "roundtrip3" >:: roundtrip3;
  ]

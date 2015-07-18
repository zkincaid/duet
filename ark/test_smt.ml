open OUnit
open Syntax

module Ctx = struct
  module C = Syntax.Make(Syntax.TypedString)()
  include C
  include Smt.MakeSolver(C)(struct let opts = [] end)()
end

module Z3 = Smt.MakeZ3(struct let opts = [] end)()
module Z3Of = MakeTranslator(Ctx)(Z3)
module OfZ3 = MakeTranslator(Z3)(Ctx)

module Infix = Syntax.Infix(Ctx)

let r = Ctx.mk_const (Ctx.symbol_of_const ("r", TyReal))
let s = Ctx.mk_const (Ctx.symbol_of_const ("s", TyReal))
let t = Ctx.mk_const (Ctx.symbol_of_const ("t", TyReal))

let w = Ctx.mk_const (Ctx.symbol_of_const ("w", TyInt))
let x = Ctx.mk_const (Ctx.symbol_of_const ("x", TyInt))
let y = Ctx.mk_const (Ctx.symbol_of_const ("y", TyInt))
let z = Ctx.mk_const (Ctx.symbol_of_const ("z", TyInt))

let frac num den = Ctx.mk_real (QQ.of_frac num den)
let int k = Ctx.mk_real (QQ.of_int k)

let assert_equal_term s t =
  assert_equal ~printer:Ctx.Term.show s t
let assert_equal_formula s t =
  assert_equal ~printer:Ctx.Formula.show s t

let roundtrip1 () =
  let term =
    let open Infix in
    x * x * x mod (int 10) + (frac 100 3) / (r - z + s)
  in
  assert_equal_term term (OfZ3.term (Z3Of.term term))

let roundtrip2 () =
  let phi =
    let open Infix in
    x <= y && y <= z && x < z
    || x = y && y = z
  in
  assert_equal_formula phi (OfZ3.formula (Z3Of.formula phi))

let roundtrip3 () =
  let phi =
    let open Infix in
    forall ~name:"a" TyInt
      (forall ~name:"b" TyInt
         (!((var 0 TyInt) < (var 1 TyInt))
          || (exists ~name:"c" TyReal
                ((var 1 TyInt) < (var 0 TyReal)
                 && (var 0 TyReal) < (var 2 TyInt)))))
  in
  assert_equal_formula phi (OfZ3.formula (Z3Of.formula phi))

let is_interpolant phi psi itp =
  (Ctx.implies phi itp)
  && Ctx.is_sat (Ctx.mk_and [itp; psi]) = `Unsat

let interpolate1 () =
  let phi =
    let open Infix in
    x = y && (int 0) = x
  in
  let psi =
    let open Infix in
    y = z && z < (int 0)
  in
  (match Ctx.interpolate_seq [phi; psi] with
   | `Unsat [itp] ->
     assert_bool "itp(y == x < 0, 0 < z = y)" (is_interpolant phi psi itp)
   | _ -> assert false);
  (match Ctx.interpolate_seq [psi; phi] with
   | `Unsat [itp] ->
     assert_bool "itp(0 < z = y, y == x < 0)" (is_interpolant psi phi itp)
   | _ -> assert false)

let interpolate2 () =
  let phi =
    let open Infix in
    x = (int 0) && y = x + (int 1) && y < (int 1)
  in
  let psi = Ctx.mk_true in
  (match Ctx.interpolate_seq [phi; psi] with
   | `Unsat [itp] ->
     assert_bool "itp(x = 0 /\\ y = x + 1 /\\ y < 1, true)"
       (is_interpolant phi psi itp)
   | _ -> assert false);
  (match Ctx.interpolate_seq [psi; phi] with
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
  (match Ctx.interpolate_seq [phi; psi] with
   | `Unsat [itp] ->
     assert_bool "itp(x = w = 1, y = x + w <= 1)"
       (is_interpolant phi psi itp)
   | _ -> assert false);
  (match Ctx.interpolate_seq [psi; phi] with
   | `Unsat [itp] ->
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

open OUnit
open Syntax

module Ctx = Syntax.Make(Syntax.TypedString)()
module Infix = Syntax.Infix(Ctx)

let r = Ctx.mk_const (Ctx.symbol_of_const ("r", `TyReal))
let s = Ctx.mk_const (Ctx.symbol_of_const ("s", `TyReal))
let t = Ctx.mk_const (Ctx.symbol_of_const ("t", `TyReal))

let w = Ctx.mk_const (Ctx.symbol_of_const ("w", `TyInt))
let x = Ctx.mk_const (Ctx.symbol_of_const ("x", `TyInt))
let y = Ctx.mk_const (Ctx.symbol_of_const ("y", `TyInt))
let z = Ctx.mk_const (Ctx.symbol_of_const ("z", `TyInt))

let frac num den = Ctx.mk_real (QQ.of_frac num den)
let int k = Ctx.mk_real (QQ.of_int k)

let assert_equal_term s t =
  assert_equal ~printer:Ctx.Term.show s t
let assert_equal_formula s t =
  assert_equal ~printer:Ctx.Formula.show s t

let substitute () =
  let subst =
    let open Infix in
    function
    | 0 -> x
    | 2 -> (var 0 `TyInt)
    | _ -> raise Not_found
  in
  let phi =
    let open Infix in
    (y = (var 0 `TyInt))
    || (exists `TyInt
          ((y = (var 0 `TyInt) + (var 1 `TyInt))
           && (var 1 `TyInt) < (var 3 `TyInt)))
  in
  let psi =
    let open Infix in
    (y = x)
    || (exists `TyInt
          ((y = (var 0 `TyInt) + x)
           && x < (var 1 `TyInt)))
  in
  assert_equal_formula (Ctx.Formula.substitute subst phi) psi

let existential_closure1 () =
  let phi =
    let open Infix in
    (x = (var 34 `TyInt) || (var 34 `TyInt) < y)
    && (var 35 `TyReal) <= (var 42 `TyReal)
    && (var 42 `TyReal) <= (var 34 `TyInt)
  in
  let psi =
    let open Infix in
    ((x = (var 0 `TyInt) || (var 0 `TyInt) < y)
     && (var 1 `TyReal) <= (var 2 `TyReal)
     && (var 2 `TyReal) <= (var 0 `TyInt))
    |> exists `TyInt
    |> exists `TyReal
    |> exists `TyReal
  in
  assert_equal_formula (Ctx.Formula.existential_closure phi) psi

let existential_closure2 () =
  let phi =
    let open Infix in
    ((var 5 `TyReal) = (var 0 `TyInt) + (int 1))
    && (exists `TyInt
          ((var 0 `TyInt) = (var 6 `TyReal)))
  in
  let psi =
    let open Infix in
    exists `TyReal
      (exists `TyInt
         (((var 1 `TyReal) = (var 0 `TyInt) + (int 1))
          && (exists `TyInt
                ((var 0 `TyInt) = (var 2 `TyReal)))))
  in
  assert_equal_formula (Ctx.Formula.existential_closure phi) psi

let suite = "Syntax" >:::
  [
    "substitute" >:: substitute;
    "existential_closure1" >:: existential_closure1;
    "existential_closure2" >:: existential_closure2;
  ]

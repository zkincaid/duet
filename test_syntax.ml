open OUnit
open Syntax

module Ctx = MakeContext ()
module Infix = Syntax.Infix(Ctx)
let ctx = Ctx.context
let smt_ctx = Smt.mk_context ctx []

let x = Ctx.mk_const (Ctx.mk_symbol ~name:"x" `TyInt)
let y = Ctx.mk_const (Ctx.mk_symbol ~name:"y" `TyInt)

let frac num den = Ctx.mk_real (QQ.of_frac num den)
let int k = Ctx.mk_real (QQ.of_int k)

let assert_equal_term s t =
  assert_equal ~printer:(Term.show ctx) s t
let assert_equal_formula s t =
  assert_equal ~printer:(Formula.show ctx) s t

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
  assert_equal_formula (substitute ctx subst phi) psi

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
  assert_equal_formula (Formula.existential_closure ctx phi) psi

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
  assert_equal_formula (Formula.existential_closure ctx phi) psi

(* This test will fail if the implementation of prenex changes the way that
   unordered quantifiers get ordered (swap var 0 and var 1 in psi). *)
let prenex () =
  let phi =
    let open Infix in
    exists `TyReal
      ((exists `TyReal ((var 0 `TyReal) = (var 1 `TyReal)))
       && (exists `TyReal ((var 0 `TyReal) <= (var 1 `TyReal))))
  in
  let psi =
    let open Infix in
    exists `TyReal
      (exists `TyReal
         (exists `TyReal
            ((var 1 `TyReal) = (var 2 `TyReal)
             && (var 0 `TyReal) <= (var 2 `TyReal))))
  in
  assert_equal_formula (Formula.prenex ctx phi) psi

let suite = "Syntax" >:::
  [
    "substitute" >:: substitute;
    "existential_closure1" >:: existential_closure1;
    "existential_closure2" >:: existential_closure2;
    "prenex" >:: prenex;
  ]

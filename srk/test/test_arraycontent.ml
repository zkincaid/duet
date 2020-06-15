open Srk
open OUnit
open Syntax
open Test_pervasives
open Arraycontent

(* This test will fail if the implementation of prenex changes the way that
   unordered quantifiers get ordered (swap var 0 and var 1 in psi). *)
let tomfa () =
  let phi =
    let open Infix in
    exists `TyInt
      ((forall `TyInt ((var 0 `TyInt) = (var 1 `TyInt)))
      || (exists `TyReal ((var 0 `TyReal) <= (var 1 `TyInt))))
  in
  (*let psi =
    let open Infix in
    exists `TyReal
      (exists `TyReal
         (exists `TyReal
            ((var 1 `TyReal) = (var 2 `TyReal)
             && (var 0 `TyReal) <= (var 2 `TyReal))))
  in*)
  assert_equal_formula (add_prefix srk (to_mfa srk phi)) (mk_false srk)


let pred_test () =
  let phi =
    let open Infix in
    exists `TyInt
      ((forall `TyInt ((var 0 `TyInt) = a((var 0 `TyInt)) && a(x) = a(y)))
      || (exists `TyReal ((var 0 `TyReal) <= (var 1 `TyInt))))
  in
  (*let psi =
    let open Infix in
    exists `TyReal
      (exists `TyReal
         (exists `TyReal
            ((var 1 `TyReal) = (var 2 `TyReal)
             && (var 0 ` <= (var 2 `TyReal))))
  in*)
  let arrsyms = Symbol.Set.add asym (Symbol.Set.empty) in 
  assert_equal_formula (mfa_to_lia srk (to_mfa srk phi) arrsyms) 
    (mk_false srk)




let suite = "ArrayContent" >:::
  [
    "tomfa" >:: tomfa;
    "pred_test" >:: pred_test
  ]

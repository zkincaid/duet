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
      || (exists `TyInt ((var 0 `TyInt) <= (var 1 `TyInt))))
  in
  (*let psi =
    let open Infix in
    exists `TyReal
      (exists `TyReal
         (exists `TyReal
            ((var 1 `TyReal) = (var 2 `TyReal)
             && (var 0 `TyReal) <= (var 2 `TyReal))))
  in*)
  let qf, _, matr = to_mfa srk phi in
  assert_equal_formula (add_prefix srk (qf, matr)) (mk_false srk)


let pred_test () =
  let phi =
    let open Infix in
    exists `TyInt
      ((forall `TyInt ((var 0 `TyInt) = a((var 1 `TyInt)) && a(x) = a(y)))
      || (exists `TyInt ((var 0 `TyInt) <= (var 1 `TyInt))))
  in
  (*let psi =
    let open Infix in
    exists `TyReal
      (exists `TyReal
         (exists `TyReal
            ((var 1 `TyReal) = (var 2 `TyReal)
             && (var 0 ` <= (var 2 `TyReal))))
    in*)
  (*let qpf, bbu, matr = to_mfa srk phi in
  let arruniv, arrother = get_array_syms srk matr bbu in
  let lia = mfa_to_lia srk (qpf, matr) arruniv arrother bbu in *)
  let lia = new_to_mfa srk phi in
  assert_equal_formula lia 
    (mk_false srk)




let suite = "ArrayContent" >:::
  [
    "tomfa" >:: tomfa;
    "pred_test" >:: pred_test
  ]

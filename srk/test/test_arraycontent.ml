open Srk
open OUnit
open Syntax
open Test_pervasives
open Iteration
module A = Arraycontent
module Array_vas = A.Array_analysis(Product(LinearRecurrenceInequation)(PolyhedronGuard))
(*module Array_vas = A.Array_analysis(Product(Product(Vass)(PolyhedronGuard))(LinearRecurrenceInequation))*)

(*
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
*)

let pred_test () =
  let phi =
    let open Infix in
    exists `TyInt
      (exists `TyInt
      ((forall `TyInt (
           exists  `TyInt 
             ((var 0 `TyInt) = a((var 1 `TyInt)) 
              && a((var 2 `TyInt)) = a(y))))
      || (exists `TyInt ((var 0 `TyInt) <= (var 1 `TyInt))))
      && (var 0 `TyInt) = x)
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
  (*1let lia = new_mfa_to_lia srk (new_to_mfa srk phi) in*)
  let lia = A.to_mfa srk phi in
  assert_equal_formula lia 
    (mk_false srk)



let pred_test2 () =
  let phi =
    let open Infix in
    exists `TyInt
      (exists `TyInt
         ((forall `TyInt ( 
              (var 0 `TyInt) = a((var 1 `TyInt)) 
              && a((var 2 `TyInt)) = a(y)))
          || (exists `TyInt ((var 0 `TyInt) <= (var 1 `TyInt))))
       && (var 0 `TyInt) = x)
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
  (*1let lia = new_mfa_to_lia srk (new_to_mfa srk phi) in*)
  let lia = A.to_mfa srk phi in
  assert_equal_formula lia 
    (mk_false srk)

let merge_proj_syms srk trs1 trs2 =
  let f (x, x') (y, y') = 
    mk_eq srk (mk_const srk x) (mk_const srk y), 
    (mk_eq srk (mk_const srk x') (mk_const srk y'))
  in
  let eqs = BatList.map2 f trs1 trs2 in
  let a, b = List.split eqs in
  a @ b


let iter_init () =
  let phi =
    let open Infix in
    x' = x + (int 1) &&
    forall `TyInt (
      (mk_if 
        srk 
        ((var 0 `TyInt) = x)
        (a'(var 0 `TyInt)  = (int 999)))
      &&
      (mk_if 
         srk 
         (!((var 0 `TyInt) = x))
         (a'(var 0 `TyInt)  = a(var 0 `TyInt))))
  in
  let psi =
    let open Infix in
    x' = x + y && (int 0) <= y &&
    forall `TyInt (
      (mk_ite 
        srk 
        ((int 0) < y && x <= (var 0 `TyInt) && (var 0 `TyInt) < x')
        (a'(var 0 `TyInt)  = (int 999))
        (a'(var 0 `TyInt)  = a(var 0 `TyInt)))
      )
  in
  let tr_symbols = [(xsym, xsym'); (asym, asym')] in
  let iter = 
    Array_vas.exp 
      srk 
      tr_symbols
      y
      (Array_vas.abstract srk tr_symbols phi)
  in
  assert (Arraycontent.is_eq_projs srk iter psi [(asym, asym')] = `Yes)


let iter_non_null () =
  let phi =
    let open Infix in
    x' = x + (int 1) &&
    forall `TyInt (
      (mk_if 
        srk 
        ((var 0 `TyInt) = x)
        (a'(var 0 `TyInt)  = a(var 0 `TyInt) && !(a(var 0 `TyInt) = (int 0))))
      &&
      (mk_if 
         srk 
         (!((var 0 `TyInt) = x))
         (a'(var 0 `TyInt)  = a(var 0 `TyInt))))
  in
  let psi =
    let open Infix in
    x' = x + y && (int 0) <= y &&
    forall `TyInt (
      (mk_ite 
        srk 
        ((int 0) < y && x <= (var 0 `TyInt) && (var 0 `TyInt) < x')
        (a'(var 0 `TyInt)  = a(var 0 `TyInt) && !(a(var 0 `TyInt) = (int 0)))
        (a'(var 0 `TyInt)  = a(var 0 `TyInt)))
      )
  in
  let tr_symbols = [(xsym, xsym'); (asym, asym')] in
  let iter = 
    Array_vas.exp 
      srk 
      tr_symbols
      y
      (Array_vas.abstract srk tr_symbols phi)
  in
  assert (Arraycontent.is_eq_projs srk psi iter [(asym, asym')] = `Yes)


(*this currently times out when showing iter -> psi *)
let iter_same () =
  let phi =
    let open Infix in
    x' = x + (int 1) &&
    forall `TyInt (
      (mk_if 
        srk 
        ((var 0 `TyInt) = (int 5))
        (a'(var 0 `TyInt)  = (int 999)))
      &&
      (mk_if 
         srk 
         (!((var 0 `TyInt) = (int 5)))
         (a'(var 0 `TyInt)  = a(var 0 `TyInt))))
  in
  let psi =
    let open Infix in
    x' = x + y && (int 0) <= y &&
    forall `TyInt (
      (mk_if
         srk 
         ((int 0) = y)
         (a'(var 0 `TyInt)  = a(var 0 `TyInt))) &&
      (mk_if
         srk 
         (!((var 0 `TyInt) = (int 5)))
         (a'(var 0 `TyInt)  = a(var 0 `TyInt))) &&
      (mk_if
         srk 
         ((int 0) < y && y < (int 3) && (var 0 `TyInt) = (int 5))
         (a'(var 0 `TyInt)  = (int 999)))
    )
  in
  let tr_symbols = [(xsym, xsym'); (asym, asym')] in
  let iter = 
    Array_vas.exp 
      srk 
      tr_symbols
      y
      (Array_vas.abstract srk tr_symbols phi)
  in
  assert (Arraycontent.is_eq_projs srk iter psi [(asym, asym')] = `Yes)

let suite = "ArrayContent" >:::
  [
    "pred_test2" >:: pred_test2;
    "pred_test" >:: pred_test;
    "iter_init" >:: iter_init;
    "iter_non_null" >:: iter_non_null;
    "iter_same" >:: iter_same
  ]

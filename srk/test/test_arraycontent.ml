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


let iter_test1 () =
  let phi =
    let open Infix in
    x' = x + (int 1) &&
    forall `TyInt (
      (mk_if 
        srk 
        ((var 0 `TyInt) = (int 5))
        (a'(var 0 `TyInt)  = (int 9)))
      &&
      (mk_if 
         srk 
         (!((var 0 `TyInt) = (int 5)))
         (a'(var 0 `TyInt)  = a(var 0 `TyInt))))
  in
  let psi =
    let open Infix in
    x' = x + y &&
    forall `TyInt (
      (mk_ite 
        srk 
        (*(x <= (var 0 `TyInt) && (var 0 `TyInt) < x')*)
        ((int 0) < y && (var 0 `TyInt) = (int 5))
        (a'(var 0 `TyInt)  = ( int 9))
        (((int 0) <= y) && a'(var 0 `TyInt)  = a(var 0 `TyInt)))
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
  let _, _, (trs_iter, proj_iter) = 
    Arraycontent.projection srk iter [(asym, asym')] in
  Log.errorf "testfail4";
  let _, _, (trs_psi, proj_psi) = 
    Arraycontent.projection srk psi [(asym, asym')] in
  Log.errorf "testfail3\n";
  Log.errorf "result of iter is %a" (Formula.pp srk) iter;
  let lia_iter = 
    mk_forall 
      srk 
      `TyInt
      (Arraycontent.mfa_to_lia srk (Arraycontent.to_mfa srk proj_iter)) in
  Log.errorf "testfail2";
  let lia_psi = 
    mk_forall 
      srk 
      `TyInt
      (Arraycontent.mfa_to_lia srk (Arraycontent.to_mfa srk proj_psi)) in
  Log.errorf "testfail1";
  let consistency_syms = merge_proj_syms srk trs_iter trs_psi in
  (*let pre_qf = (mk_if srk (mk_and srk (lia_psi :: consistency_syms))
    (mk_and srk (lia_iter :: consistency_syms)))
  in
  let qf = Arraycontent.mbp_qe srk pre_qf in
  let ass = mk_not srk qf in
  let filename = "/Users/jakesilverman/Documents/duet/duet/HISISTEST.smt2" in
  let chan = Stdlib.open_out filename in
  let formatter = Format.formatter_of_out_channel chan in
  Syntax.pp_smtlib2 srk formatter ass;
  Format.pp_print_newline formatter ();
  Stdlib.close_out chan;*)
  assert_equiv_formula 
    (mk_and srk (lia_iter :: consistency_syms)) 
    (mk_and srk (lia_psi :: consistency_syms))




let suite = "ArrayContent" >:::
  [
    "pred_test2" >:: pred_test2;
    "pred_test" >:: pred_test;
    "iter_test1" >:: iter_test1
  ]

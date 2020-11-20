open Srk
open OUnit
open Syntax
open Test_pervasives
open Iteration
module A = Arraycontent
module T = TransitionFormula
module Array_vas = A.Array_analysis(Product(LinearRecurrenceInequation)(PolyhedronGuard))


let time =
    let t = Sys.time() in
    Log.errorf "Curr time: %fs\n" (t); t

let diff t1 t2 =
    Log.errorf "Execution time: %fs\n" (t2 -. t1)



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
let invert hashtbl =
  let tbl' = Hashtbl.create (Hashtbl.length hashtbl * 4 / 3) in
  Hashtbl.iter (fun a b -> Hashtbl.add tbl' b a) hashtbl;
  tbl'

let assert_equiv_quant_formula s t =
  let equiv_formula =
    mk_or srk [mk_and srk [s; mk_not srk t];
               mk_and srk [mk_not srk s; t]]
  in
  Log.errorf "EQUIV is \n\n %a" (pp_smtlib2 srk) equiv_formula;
    assert_equal
    ~printer:(Formula.show srk)
    ~cmp:(fun _ _ -> Quantifier.simsat srk equiv_formula = `Unsat) s t

let merge_proj_syms srk trs1 trs2 =
  let f (x, x') (y, y') = 
    mk_eq srk (mk_const srk x) (mk_const srk y), 
    (mk_eq srk (mk_const srk x') (mk_const srk y'))
  in
  let eqs = BatList.map2 f trs1 trs2 in
  let a, b = List.split eqs in
  a @ b

let pmfa_to_lia srk pmfa syms = A.mfa_to_lia srk (A.to_mfa srk pmfa) syms



let mk_eq_projs srk phi1 phi2 tr num_trs =
  let j1, map1, phi1_proj = A.projection srk phi1 in
  let j2, map2, phi2_proj = A.projection srk phi2 in
  let map1 = invert map1 in
  let map2 = invert map2 in
  let trs1 = List.map (fun (a, a') -> (Hashtbl.find map1 a, Hashtbl.find map1 a')) tr in
  let trs2 = List.map (fun (a, a') -> (Hashtbl.find map2 a, Hashtbl.find map2 a')) tr in
  let trs1 = (j1, j1) :: trs1 in
  let trs2 = (j2, j2) :: trs2 in


  let phi1_proj_lia = pmfa_to_lia srk phi1_proj ((T.symbols phi1_proj) @ num_trs) in
  to_file srk phi1_proj_lia "/Users/jakesilverman/Documents/duet/duet/projtest.smt2" ; 
  let phi2_proj_lia = pmfa_to_lia srk phi2_proj ((T.symbols phi2_proj) @ num_trs) in
  let consistency_syms = merge_proj_syms srk trs1 trs2 in
  let phi = mk_and srk (phi1_proj_lia :: consistency_syms) in
  let psi = mk_and srk (phi2_proj_lia :: consistency_syms) in
  let all_num_trs = num_trs @ (T.symbols phi1_proj) @ (T.symbols phi2_proj) in
  let tr_syms_flat = List.fold_left (fun acc (sym, sym') -> sym :: sym' :: acc) [] all_num_trs in
  let phi = mk_exists_consts srk (fun sym -> List.mem sym tr_syms_flat) phi in
  let psi = mk_exists_consts srk (fun sym -> List.mem sym tr_syms_flat) psi in
  phi, psi
  (*fst (A.mbp_qe srk phi false), fst (A.mbp_qe srk psi false)*)



let pmfa_to_lia0 () =
  let phi =
    let open Infix in
    x' = x + (int 1) &&
    forall `TyInt (a(var 0 `TyInt) = b(var 0 `TyInt) &&
                   a(x) = (int 99))
  in
  let tf = T.make phi [(asym, bsym); (xsym, xsym')] in
  let j, map, phi_proj = A.projection srk tf in
  let matrix = A.to_mfa srk phi_proj in
  let lia = A.mfa_to_lia srk matrix (T.symbols phi_proj) in
  (*let tr_syms_flat = List.fold_left (fun acc (sym, sym') -> sym :: sym' :: acc) [] new_trs in
  let tr_syms_flat = xsym :: xsym' :: tr_syms_flat in
  let lia = mk_exists_consts srk (fun sym -> List.mem sym tr_syms_flat) lia in
  Log.errorf "LIA is %a\n\n" (Formula.pp srk) lia;*)
  let lia, _ = A.mbp_qe srk lia false in
  let map = invert map in
  let (z, z') = mk_const srk (Hashtbl.find map asym), mk_const srk (Hashtbl.find map bsym) in
  let j = mk_const srk j in
  let lam =
    let open Infix in
    x' = x + (int 1) && z = z' && (z = (int 99) || !(x = j))
  in
  let equiv_formula =
    mk_or srk [(*mk_and srk [lam; mk_not srk lia];*)
               mk_and srk [mk_not srk lam; lia]]
  in
  to_file srk equiv_formula "/Users/jakesilverman/Documents/duet/duet/projtest2.smt2" ; 
  assert_equiv_formula lam lia


(*let pmfa_to_lia1 () =
  let phi =
    let open Infix in
    exists `TyInt (
      exists `TyInt (
        forall `TyInt ( 
          (var 0 `TyInt) = a(var 1 `TyInt) && 
          a(var 2 `TyInt) = a(y)))
      || (exists `TyInt ((var 0 `TyInt) <= (var 1 `TyInt))
      && (var 0 `TyInt) = x))
  in
 (* let psi =
    mk_forall `TyInt (
    )*)
  (*let qpf, bbu, matr = to_mfa srk phi in
  let arruniv, arrother = get_array_syms srk matr bbu in
  let lia = mfa_to_lia srk (qpf, matr) arruniv arrother bbu in *)
  (*1let lia = new_mfa_to_lia srk (new_to_mfa srk phi) in*)
  let lia = A.to_mfa srk phi in
  assert_equal_formula lia 
    (mk_false srk)

*)

(*
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
*)
let merge_proj_syms srk trs1 trs2 =
  let f (x, x') (y, y') = 
    mk_eq srk (mk_const srk x) (mk_const srk y), 
    (mk_eq srk (mk_const srk x') (mk_const srk y'))
  in
  let eqs = BatList.map2 f trs1 trs2 in
  let a, b = List.split eqs in
  a @ b


let iter_init () =
  Log.errorf "ENTER INIT\n"; let t1 = time in
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
  let tf = TransitionFormula.make phi tr_symbols in
  let iter = 
    Array_vas.exp
      srk 
      tr_symbols
      y
      (Array_vas.abstract srk tf)
  in

  let equiv_formula =
    mk_or srk [mk_and srk [iter; mk_not srk psi];
               mk_and srk [mk_not srk iter; psi]]
  in
  to_file srk equiv_formula
    "/Users/jakesilverman/Documents/duet/duet/arrform.smt2";
 
  to_file srk iter
    "/Users/jakesilverman/Documents/duet/duet/iter2.smt2";
 
  let iter = T.make iter [(asym, asym'); (xsym, xsym'); (ysym, ysym)] in
  let psi = T.make psi [(asym, asym'); (xsym, xsym'); (ysym, ysym)] in 
  let phi, psi = mk_eq_projs srk iter psi [(asym, asym')] [(xsym, xsym'); (ysym, ysym)] in
  let equiv_formula =
    mk_or srk [mk_and srk [phi; mk_not srk psi];
               mk_and srk [mk_not srk phi; psi]]
  in
  to_file srk equiv_formula
    "/Users/jakesilverman/Documents/duet/duet/equiv_form.smt2";
  Log.errorf "Pre Simsat Init"; let t2 = time in
  diff t1 t2;
  assert (Quantifier.simsat_forward srk equiv_formula = `Unsat)
  (*assert_equiv_formula phi psi*)
  (*assert false*)
(*
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
  let tf = TransitionFormula.make phi tr_symbols in
  let iter = 
    Array_vas.exp 
      srk 
      tr_symbols
      y
      (Array_vas.abstract srk tf)
  in
  assert (Arraycontent.is_eq_projs srk psi iter [(asym, asym')] [] = `Yes)

*)
(*this currently times out when showing iter -> psi *)
(*let iter_same () =
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
  let tf = TransitionFormula.make phi tr_symbols in
  let iter = 
    Array_vas.exp 
      srk 
      tr_symbols
      y
      (Array_vas.abstract srk tf)
  in
  assert (Arraycontent.is_eq_projs srk iter psi [(asym, asym')] [] = `Yes)
*)
let suite = "ArrayContent" >:::
  [
    "pmfa_to_lia0" >:: pmfa_to_lia0;
    (*"pred_test2" >:: pred_test2;
    "pmfa_to_lia1" >:: pmfa_to_lia1;*)
    "iter_init" >:: iter_init;
    (*"iter_non_null" >:: iter_non_null;
    "iter_same" >:: iter_same*)
  ]

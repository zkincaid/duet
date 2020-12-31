open Srk
open OUnit
open Syntax
open Test_pervasives
open Iteration
module A = Arraycontent
module T = TransitionFormula
module Array_lre = A.Array_analysis(Product(LinearRecurrenceInequation)(PolyhedronGuard))

let invert hashtbl =
  let tbl' = Hashtbl.create (Hashtbl.length hashtbl * 4 / 3) in
  Hashtbl.iter (fun a b -> Hashtbl.add tbl' b a) hashtbl;
  tbl'

let merge_proj_syms srk trs1 trs2 =
  let f (x, x') (y, y') = 
    mk_eq srk (mk_const srk x) (mk_const srk y), 
    (mk_eq srk (mk_const srk x') (mk_const srk y'))
  in
  let eqs = BatList.map2 f trs1 trs2 in
  let a, b = List.split eqs in
  a @ b


  (* Tr symbols in phi and psi must be in same order *)
let mk_eq_projs srk phi psi =
  let _, _, phi_proj = A.projection srk phi in
  let _, _, psi_proj = A.projection srk psi in
  let trs1 = T.symbols phi_proj in
  let trs2 = T.symbols psi_proj in
  let phi_lia = A.pmfa_to_lia srk phi_proj in
  let psi_lia = A.pmfa_to_lia srk psi_proj in
  let consistency_syms = merge_proj_syms srk trs1 trs2 in
  let phi' = mk_and srk ((T.formula phi_lia) :: consistency_syms) in
  let psi' = mk_and srk ((T.formula psi_lia) :: consistency_syms) in
  mk_or srk [mk_and srk [phi'; mk_not srk psi']; mk_and srk [mk_not srk phi'; psi']]



let pmfa_to_lia0 () =
  let phi =
    let open Infix in
    x' = x + (int 1) &&
    a1 = a2 && a1.%[x] = (int 99)
    in
  let phi = Arraycontent.eliminate_stores srk phi in
  let tf = T.make phi [(a1sym, a2sym); (xsym, xsym')] in
  let j, map, phi_proj = A.projection srk tf in
  let lia = T.formula (A.pmfa_to_lia srk phi_proj) in
  let map = invert map in
  let z = mk_const srk (Hashtbl.find map a1sym) in
  let z' = mk_const srk (Hashtbl.find map a2sym) in
  let lam =
    let open Infix in
    x' = x + (int 1) && z = z' && (z = (int 99) || !(x = (mk_const srk j)))
  in
  let equiv = 
    mk_or srk [mk_and srk [lam; mk_not srk lia]; mk_and srk [mk_not srk lam; lia]]
  in
  assert (Smt.is_sat srk equiv  = `Unsat)

let iter_init () =
  let phi =
    let open Infix in
    x' = x + (int 1) &&
    forall `TyInt (
      (mk_if 
        srk 
        ((var 0 `TyInt) = x)
        (a2.%[var 0 `TyInt]  = (int 999)))
      &&
      (mk_if 
         srk 
         (!((var 0 `TyInt) = x))
         (a2.%[var 0 `TyInt]  = a1.%[var 0 `TyInt])))
  in
  let psi =
    let open Infix in
    x' = x + y && (int 0) <= y &&
    forall `TyInt (
      (mk_ite 
        srk 
        ((int 0) < y && x <= (var 0 `TyInt) && (var 0 `TyInt) < x')
        (a2.%[var 0 `TyInt]  = (int 999))
        (a1.%[var 0 `TyInt]  = a2.%[var 0 `TyInt])))
  in
  let tr_symbols = [(xsym, xsym'); (a1sym, a2sym)] in
  let tf = TransitionFormula.make phi tr_symbols in
  let iter = 
    Array_lre.exp
      srk 
      tr_symbols
      y
      (Array_lre.abstract srk tf)
  in
  let iter_tf = T.make iter [(a1sym, a2sym); (xsym, xsym'); (ysym, ysym)] in
  let psi_tf = T.make psi [(a1sym, a2sym); (xsym, xsym'); (ysym, ysym)] in
  let equiv = mk_eq_projs srk iter_tf psi_tf in
  assert (Smt.is_sat srk equiv  = `Unsat)

let iter_init2 () =
  let phi =
    let open Infix in
    x' = x + (int 1) &&
    forall `TyInt (
      (mk_if 
        srk 
        ((var 0 `TyInt) = x)
        (a2.%[var 0 `TyInt]  = a1.%[var 0 `TyInt] + (int 1)))
      &&
      (mk_if 
         srk 
         (!((var 0 `TyInt) = x))
         (a2.%[var 0 `TyInt]  = a1.%[var 0 `TyInt])))
  in
  let psi =
    let open Infix in
    x' = x + y && (int 0) <= y &&
    forall `TyInt (
      (mk_ite 
        srk 
        ((int 0) < y && x <= (var 0 `TyInt) && (var 0 `TyInt) < x')
        (a2.%[var 0 `TyInt]  = a1.%[var 0 `TyInt] + (int 1))
        (a1.%[var 0 `TyInt]  = a2.%[var 0 `TyInt])))
  in
  let tr_symbols = [(xsym, xsym'); (a1sym, a2sym)] in
  let tf = TransitionFormula.make phi tr_symbols in
  let iter = 
    Array_lre.exp
      srk 
      tr_symbols
      y
      (Array_lre.abstract srk tf)
  in
  let iter_tf = T.make iter [(a1sym, a2sym); (xsym, xsym'); (ysym, ysym)] in
  let psi_tf = T.make psi [(a1sym, a2sym); (xsym, xsym'); (ysym, ysym)] in
  let equiv = mk_eq_projs srk iter_tf psi_tf in
  assert (Smt.is_sat srk equiv  = `Unsat)


  (* Currently fails - doesn't appear to be bug but worth examining further *)
let iter_same () =
  let phi =
    let open Infix in
    x' = x + (int 1) &&
    forall `TyInt (
      (mk_if 
        srk 
        ((var 0 `TyInt) = (int 5))
        (a2.%[var 0 `TyInt]  = (int 999)))
      &&
      (mk_if 
         srk 
         (!((var 0 `TyInt) = (int 5)))
         (a2.%[var 0 `TyInt]  = a1.%[var 0 `TyInt])))
  in
  let psi =
    let open Infix in
    x' = x + y && (int 0) <= y &&
    forall `TyInt (
      (mk_ite 
        srk 
        ((int 0) < y && (var 0 `TyInt) = (int 5))
        (a2.%[var 0 `TyInt]  = (int 999))
        (a1.%[var 0 `TyInt]  = a2.%[var 0 `TyInt])))
  in
  let tr_symbols = [(xsym, xsym'); (a1sym, a2sym)] in
  let tf = TransitionFormula.make phi tr_symbols in
  let iter = 
    Array_lre.exp
      srk 
      tr_symbols
      y
      (Array_lre.abstract srk tf)
  in
  let iter_tf = T.make iter [(a1sym, a2sym); (xsym, xsym'); (ysym, ysym)] in
  let psi_tf = T.make psi [(a1sym, a2sym); (xsym, xsym'); (ysym, ysym)] in
  let equiv = mk_eq_projs srk iter_tf psi_tf in
  assert (Smt.is_sat srk equiv  = `Unsat)


(* Fails. Potential bug *)
let iter_non_null () =
  let phi =
    let open Infix in
    x' = x + (int 1) &&
      forall `TyInt (
        (mk_if 
          srk 
          ((var 0 `TyInt) = x)
          (a2.%[var 0 `TyInt]  = a1.%[var 0 `TyInt] && 
          !(a1.%[var 0 `TyInt] = (int 0))))
        &&
        (mk_if 
          srk 
          (!((var 0 `TyInt) = x))
          (a2.%[var 0 `TyInt]  = a1.%[var 0 `TyInt])))
  in
  let psi =
    let open Infix in
    x' = x + y && (int 0) <= y &&
    forall `TyInt (
      (mk_ite 
        srk 
        ((int 0) < y && x <= (var 0 `TyInt) && (var 0 `TyInt) < x')
        (a2.%[var 0 `TyInt]  = a1.%[var 0 `TyInt] && !(a1.%[var 0 `TyInt] = (int 0)))
        (a2.%[var 0 `TyInt]  = a1.%[var 0 `TyInt])))
  in
 let tr_symbols = [(xsym, xsym'); (a1sym, a2sym)] in
 let tf = TransitionFormula.make phi tr_symbols in
 let iter = 
   Array_lre.exp
      srk 
      tr_symbols
      y
      (Array_lre.abstract srk tf)
 in
  let iter_tf = T.make iter [(a1sym, a2sym); (xsym, xsym'); (ysym, ysym)] in
  let psi_tf = T.make psi [(a1sym, a2sym); (xsym, xsym'); (ysym, ysym)] in
  let equiv = mk_eq_projs srk iter_tf psi_tf in
  assert (Smt.is_sat srk equiv  = `Unsat)




let suite = "ArrayContent" >:::
  [
    "pmfa_to_lia0" >:: pmfa_to_lia0;
    (*"pred_test2" >:: pred_test2;
    "pmfa_to_lia1" >:: pmfa_to_lia1;*)
    "iter_init" >:: iter_init;
    "iter_init2" >:: iter_init2;
    (*"iter_same" >:: iter_same*)
    (*"iter_non_null" >:: iter_non_null;*)
  ]

open Srk
open OUnit2
open Syntax
open Iteration
open Arraylift
open Test_pervasives


let noop_eop : 'a exp_op = 
  let f solver _ = Solver.get_formula solver in 
  f

let ksym = Ctx.mk_symbol ~name:"k" `TyInt
let ksym' = Ctx.mk_symbol ~name:"k'" `TyInt
let nsym = Ctx.mk_symbol ~name:"n" `TyInt
let nsym' = Ctx.mk_symbol ~name:"n'" `TyInt
let asym = Ctx.mk_symbol ~name:"a" `TyArr
let asym' = Ctx.mk_symbol ~name:"a'" `TyArr
let bsym = Ctx.mk_symbol ~name:"b" `TyArr
let bsym' = Ctx.mk_symbol ~name:"b'" `TyArr
let dsym = Ctx.mk_symbol ~name:"d" `TyArr
let dsym' = Ctx.mk_symbol ~name:"d'" `TyArr

let k : 'a arith_term = Ctx.mk_const ksym
let k' : 'a arith_term = Ctx.mk_const ksym'
let n : 'a arith_term = Ctx.mk_const nsym
let n' : 'a arith_term = Ctx.mk_const nsym'
let a : 'a arr_term = Ctx.mk_const asym
let a' : 'a arr_term = Ctx.mk_const asym'
let b : 'a arr_term = Ctx.mk_const bsym
let b' : 'a arr_term = Ctx.mk_const bsym'
let d : 'a arr_term = Ctx.mk_const dsym
let d' : 'a arr_term = Ctx.mk_const dsym'

let strlen_test _ctxt = 
  let open Infix in
  let tf = TransitionFormula.make 
    (forall ~name:"i" `TyInt 
    (k' = k + (int 1) && n' = n && a'.%[(var 0 `TyInt)] = a.%[(var 0 `TyInt)] && b'.%[(var 0 `TyInt)] = b.%[(var 0 `TyInt)]
     && ((k = (var 0 `TyInt) && d'.%[(var 0 `TyInt)] = a.%[(var 0 `TyInt)] + b.%[(var 0 `TyInt)]) || 
      (((k < (var 0 `TyInt)) || ((var 0 `TyInt) < k)) && d'.%[(var 0 `TyInt)] = d.%[(var 0 `TyInt)])
    ))) 
    [(asym, asym'); (bsym, bsym'); (ksym, ksym'); (dsym, dsym'); (nsym, nsym')] in 
  let aeop = array_exponentiate srk noop_eop in

  let eop_result = aeop tf k in

  let expected = TransitionFormula.formula tf in 
  assert_equiv_formula (expected) (eop_result)

let subproblem _ctx = 
  let open Infix in
  let tf = TransitionFormula.make 
    (forall ~name:"i" `TyInt 
    (k' = k + (int 1)
     && ((k = (var 0 `TyInt) && d'.%[(var 0 `TyInt)] = (int 1)) || 
      (((k < (var 0 `TyInt)) || ((var 0 `TyInt) < k)) && d'.%[(var 0 `TyInt)] = (int 0))
    ))) 
    [(ksym, ksym'); (dsym, dsym')] in 
  let aeop = array_exponentiate srk noop_eop in

  let eop_result = aeop tf k in

  let expected = TransitionFormula.formula tf in 
  assert_equiv_formula (expected) (eop_result)


let basic_test _ctx = 
  let open Infix in 
  let tf = TransitionFormula.make 
      (forall ~name:"i" `TyInt 
        (a'.%[(var 0 `TyInt)] = a.%[(var 0 `TyInt)] + (int 1))
      ) [(asym, asym')] in
  let aeop = array_exponentiate srk noop_eop in
  let eop_result = aeop tf k in
  let expected = (TransitionFormula.formula tf) in               
  assert_equiv_formula ( expected) ( eop_result)

let unsat_formula _ctx = 
  let open Infix in 
  let f = (forall ~name:"i" `TyInt 
        (a'.%[(var 0 `TyInt)] = a.%[(var 0 `TyInt)] + (int 1) &&
         a'.%[(var 0 `TyInt)] = a.%[(var 0 `TyInt)] + (int 2)
        )) in 
  let f = mk_exists_const srk asym f in 
  let f = mk_exists_const srk asym' f in 
  let pos = rewrite srk ~down:(pos_rewriter srk) f in
  let equi_sat = Arraylift.map_elim srk pos in
  match Quantifier.simsat srk equi_sat with
  | `Sat -> failwith "Unexpected sat result"
  | `Unsat -> ()
  | `Unknown -> failwith "Unknown result from sat solver"

let formula_test _ctx = 
  let open Infix in 
  let loop_summary = ((forall ~name:"j" `TyInt
    (a'.%[(var 0 `TyInt)] = a.%[(var 0 `TyInt)] && 
      b'.%[(var 0 `TyInt)] = b.%[(var 0 `TyInt)] &&
      (((int 0) <= (var 0 `TyInt) && ((var 0 `TyInt) < k') && d'.%[(var 0 `TyInt)] = a.%[(var 0 `TyInt)] + b.%[(var 0 `TyInt)]) || 
      ((var 0 `TyInt) < (int 0) && (k' <= (var 0 `TyInt)) && d'.%[(var 0 `TyInt)] = d.%[(var 0 `TyInt)]))
  )) && 
  (exists ~name:"i" `TyInt (n' = (var 0 `TyInt) && (int 0) <= (var 0 `TyInt) && (var 0 `TyInt) < k'))) in 
  let verification_condition = d'.%[n'] = a.%[n'] + b.%[n'] in 
  
  let combined = mk_and srk [loop_summary; !verification_condition] in 
  let quantified = List.fold_left 
    (fun acc s -> mk_exists_const srk s acc) combined [asym; asym'; bsym; bsym'; dsym; dsym'; ksym; ksym'; nsym; nsym'] in 
  let pos = rewrite srk ~down:(pos_rewriter srk) quantified in 
  let equi_sat = Arraylift.map_elim srk pos in 
  match Quantifier.simsat srk equi_sat with
  | `Sat -> failwith "Unexpected sat result"
  | `Unsat -> ()
  | `Unknown -> failwith "Unknown result from sat solver"

let existential_index_test _ctx = 
  let open Infix in 
  let loop_summary = ((forall ~name:"j" `TyInt
    (a'.%[(var 0 `TyInt)] = a.%[(var 0 `TyInt)] && 
      b'.%[(var 0 `TyInt)] = b.%[(var 0 `TyInt)] &&
      (((int 0) <= (var 0 `TyInt) && ((var 0 `TyInt) < k') && d'.%[(var 0 `TyInt)] = (var 0 `TyInt)) || 
      ((var 0 `TyInt) < (int 0) && (k' <= (var 0 `TyInt)) && d'.%[(var 0 `TyInt)] = d.%[(var 0 `TyInt)]))
  )) && 
  (exists ~name:"i" `TyInt (n' = (var 0 `TyInt) && (int 0) <= (var 0 `TyInt) && (var 0 `TyInt) < k'))) in 
  let error_condition = (exists ~name:"q" `TyInt ((int 0) <= (var 0 `TyInt) && (var 0 `TyInt) < k' && d'.%[(var 0 `TyInt)] = k' + (int 1))) in 
  
  let combined = mk_and srk [loop_summary; error_condition] in 
  let quantified = List.fold_left 
    (fun acc s -> mk_exists_const srk s acc) combined [asym; asym'; bsym; bsym'; dsym; dsym'; ksym; ksym'; nsym; nsym'] in 
  let pos = rewrite srk ~down:(pos_rewriter srk) quantified in 
  let equi_sat = Arraylift.map_elim srk pos in 
  match Quantifier.simsat srk equi_sat with
  | `Sat -> failwith "Unexpected sat result"
  | `Unsat -> ()
  | `Unknown -> failwith "Unknown result from sat solver"

let constant_index_test _ctx = 
  let open Infix in 
  let loop_summary = ((forall ~name:"j" `TyInt
    (a'.%[(var 0 `TyInt)] = a.%[(var 0 `TyInt)] && 
      b'.%[(var 0 `TyInt)] = b.%[(var 0 `TyInt)] &&
      (((int 0) <= (var 0 `TyInt) && ((var 0 `TyInt) < k') && d'.%[(var 0 `TyInt)] = (var 0 `TyInt)) || 
      ((var 0 `TyInt) < (int 0) && (k' <= (var 0 `TyInt)) && d'.%[(var 0 `TyInt)] = d.%[(var 0 `TyInt)]))
  )) && 
  (exists ~name:"i" `TyInt (n' = (var 0 `TyInt) && (int 0) <= (var 0 `TyInt) && (var 0 `TyInt) < k'))) in 
  let error_condition = ((k' < (int 10)) && !(d'.%[(int 10)] = d.%[(int 10)])) in 
  
  let combined = mk_and srk [loop_summary; error_condition] in 
  let quantified = List.fold_left 
    (fun acc s -> mk_exists_const srk s acc) combined [asym; asym'; bsym; bsym'; dsym; dsym'; ksym; ksym'; nsym; nsym'] in 
  let pos = rewrite srk ~down:(pos_rewriter srk) quantified in 
  let equi_sat = Arraylift.map_elim srk pos in 
  match Quantifier.simsat srk equi_sat with
  | `Sat -> failwith "Unexpected sat result"
  | `Unsat -> ()
  | `Unknown -> failwith "Unknown result from sat solver"


  let simple_store_test _ctx = 
    let open Infix in 
    let loop_summary = 
    (forall ~name:"i" `TyInt 
    (b'.%[(var 0 `TyInt)] = (a.%[(int 7)]<- (int 42)).%[var 0 `TyInt]
    )) 
     in
    let error_condition = (forall ~name:"i" `TyInt 
    (!(b'.%[(var 0 `TyInt)] = (int 42))
    )) in 
     let combined = mk_and srk [loop_summary; error_condition] in 
    let quantified = List.fold_left 
      (fun acc s -> mk_exists_const srk s acc) combined [asym; bsym';] in 
    let pos = rewrite srk ~down:(pos_rewriter srk) quantified in 
    let equi_sat = Arraylift.map_elim srk pos in 

    match Quantifier.simsat srk equi_sat with
    | `Sat -> failwith "Unexpected sat result"
    | `Unsat -> ()
    | `Unknown -> failwith "Unknown result from sat solver"




  let store_test _ctx = 
  let open Infix in 
  let loop_summary = 
    (forall ~name:"i" `TyInt 
    (a'.%[(var 0 `TyInt)] = a.%[(var 0 `TyInt)]
     && b'.%[(var 0 `TyInt)] = (a.%[(int 7)]<- (int 42)).%[var 0 `TyInt]
    )) 
     in 
  let error_condition = exists ~name:"j" `TyInt
    (!(b'.%[(var 0 `TyInt)] = a'.%[(var 0 `TyInt)]) && !((var 0 `TyInt) = (int 7))) in

  let combined = mk_and srk [loop_summary; error_condition] in 
  let quantified = List.fold_left 
    (fun acc s -> mk_exists_const srk s acc) combined [asym; asym'; bsym; bsym'] in 
  let pos = rewrite srk ~down:(pos_rewriter srk) quantified in

  let equi_sat = Arraylift.map_elim srk pos in 
  match Quantifier.simsat srk equi_sat with
  | `Sat -> failwith "Unexpected sat result"
  | `Unsat -> ()
  | `Unknown -> failwith "Unknown result from sat solver"
  
let formula_test2 _ctx = 
  let open Infix in 
  let f = (exists ~name:"n" `TyInt
    (exists ~name:"m" `TyInt 
      (exists ~name:"a" `TyArr 
        ((var 1 `TyInt) = (var 2 `TyInt) && !((var 0 `TyArr).%[var 1 `TyInt] = (var 0 `TyArr).%[var 2 `TyInt]))
      ))
  ) in 
  let pos = rewrite srk ~down:(pos_rewriter srk) f in
  let equi_sat = Arraylift.map_elim srk pos in 
  match Quantifier.simsat srk equi_sat with
  | `Sat -> failwith "Unexpected sat result"
  | `Unsat -> ()
  | `Unknown -> failwith "Unknown result from sat solver"

let suite = "Iteration" >::: [
  "strlen_test" >:: strlen_test;
  "subproblem" >:: subproblem;
   "basic_test" >:: basic_test;
  "formula_test" >:: formula_test;
  "existential_index_test" >:: existential_index_test;
  "constant_index_test" >:: constant_index_test;
  "store_test" >:: store_test;
  "simple_store_test" >:: simple_store_test;
  "unsat_formula" >:: unsat_formula; 
  "formula_test2" >:: formula_test2;
]



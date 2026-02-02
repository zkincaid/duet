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
      ((k < (var 0 `TyInt)) || ((var 0 `TyInt) < k)) && d'.%[(var 0 `TyInt)] = d.%[(var 0 `TyInt)]
    ))) 
    [(asym, asym'); (bsym, bsym'); (ksym, ksym'); (dsym, dsym'); (nsym, nsym')] in 
  let aeop = array_exponentiate srk noop_eop in

  let eop_result = aeop tf k in

  let expected = TransitionFormula.formula tf in 
  assert_equal (z3_of_formula expected) (z3_of_formula eop_result)

let basic_test _ctx = 
  let open Infix in 
  let tf = TransitionFormula.make 
      (forall ~name:"i" `TyInt 
        (a'.%[(var 0 `TyInt)] = a.%[(var 0 `TyInt)] + (int 1))
      ) [(asym, asym')] in
  let aeop = array_exponentiate srk noop_eop in
  let eop_result = aeop tf k in
  let expected = TransitionFormula.formula tf in
  assert_equal (z3_of_formula expected) (z3_of_formula eop_result)

let or_test _ctx = 
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
  | `Sat -> print_string "Sat\n"
  | `Unsat -> print_string "Unsat\n"
  | `Unknown -> print_string "Unknown\n"

let qe_investigation _ctx = 
  let open Infix in 
  let tf = TransitionFormula.make
  (forall ~name:"i" `TyInt 
    (
      (((var 1  `TyInt) < (var 0 `TyInt) || (var 0 `TyInt) < (var 1  `TyInt)) && (var 2 `TyInt) = (int 0)) ||
      ((var 1  `TyInt) = (var 0 `TyInt) || (var 0 `TyInt) < (var 1  `TyInt)) && (var 2 `TyInt) = (int 1)
    )) [] in
  print_string (TransitionFormula.show srk tf); print_newline ();
  print_string "eliminating...\n";
  print_string (Formula.show srk (SrkZ3.qe srk (TransitionFormula.formula tf))); print_newline ()

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
  | `Sat -> print_string "Sat\n"
  | `Unsat -> print_string "Unsat\n"
  | `Unknown -> print_string "Unknown\n"


let suite = "Iteration" >::: [
  (* "strlen_test" >:: strlen_test; *)
  (* "basic_test" >:: basic_test; *)
  (* "qe_investigation" >:: qe_investigation; *)
  "formula_test" >:: formula_test;
  (* "or_test" >:: or_test; *)
]
open OUnit
open Test_pervasives

let tr_symbols = [(wsym,wsym');(xsym,xsym');(ysym,ysym');(zsym,zsym')]

module A = LinearSemiautomaton

let ls_abstract1 () =
  let phi =
    let open Infix in
    x' = x + (int 10)
    && y' = (int 0)
    && z' = x + (int 1)
  in
  let ls = A.abstract srk phi tr_symbols in
  assert_equiv_formula phi (A.to_transition_formula srk ls tr_symbols)

let ls_abstract2 () =
  let phi =
    let open Infix in
    x' = x + (int 10)
    && y = (int 0)
    && z' = x + v
  in
  let ls = A.abstract srk phi tr_symbols in
  let phi_abs =
    let open Infix in
    x' = x + (int 10)
    && z' = x + v
  in
  assert_equiv_formula phi_abs (A.to_transition_formula srk ls tr_symbols)

let ls_abstract3 () =
  let phi =
    let open Infix in
    (x' = x + (int 1)
     && (y' = y + (int 2) || y' = x))
  in
  let ls = A.abstract srk phi tr_symbols in
  assert_equiv_formula phi (A.to_transition_formula srk ls tr_symbols)

let ls_abstract4 () =
  let phi =
    let open Infix in
    (x' = x + (int 1) && y' = y + (int 2))
    || (x' = x + (int 2) && z' = z + (int 3))
  in
  let ls = A.abstract srk phi tr_symbols in
  let phi_abs =
    let open Infix in
    x' = x + (int 1) || x' = x + (int 2)
  in
  assert_equiv_formula phi_abs (A.to_transition_formula srk ls tr_symbols)

let ls_abstract5 () =
  let phi =
    let open Infix in
    x' = x + v && w' = (int 0) && y' = v && z' = (int 0)
    || (x' = x && w' + z' = w + z + (int 1) && w' + y' = x)
  in
  let ls = A.abstract srk phi tr_symbols in
  let phi_abs =
    let open Infix in
    (x' = x + v && (w' + z' = (int 0)) && (w' + y' = v)
     || (x' = x && w' + z' = w + z + (int 1) && w' + y' = x))
  in
  assert_equiv_formula phi_abs (A.to_transition_formula srk ls tr_symbols)

let ls_abstract6 () =
  let phi =
    let open Infix in
    x' = x && y' = y + x && z' = z + v
    || y' = y + w && w' = (int 0) && z' = z + v
  in
  let ls = A.abstract srk phi tr_symbols in
  let phi_abs =
    let open Infix in
    z' = z + v
  in
  assert_equiv_formula phi_abs (A.to_transition_formula srk ls tr_symbols)

let suite = "LinearSemiautomaton" >::: [
    "ls_abstract1" >:: ls_abstract1;
    "ls_abstract2" >:: ls_abstract2;
    "ls_abstract3" >:: ls_abstract3;
    "ls_abstract4" >:: ls_abstract4;
    "ls_abstract5" >:: ls_abstract5;
    "ls_abstract6" >:: ls_abstract6
  ]

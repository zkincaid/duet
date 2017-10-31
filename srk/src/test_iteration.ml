open OUnit
open Abstract
open Syntax
open SrkApron
open Test_pervasives

module QQMatrix = Linear.QQMatrix
module WV = struct
  include Iteration.WedgeVector
  let star srk symbols phi = closure (abstract_iter srk symbols phi)
end

let assert_implies_nonlinear phi psi =
  match Wedge.is_sat srk (mk_and srk [phi; mk_not srk psi]) with
  | `Unsat -> ()
  | `Sat | `Unknown ->
    assert_failure (Printf.sprintf "%s\ndoes not imply\n%s"
                      (Formula.show srk phi)
                      (Formula.show srk psi))

let tr_symbols = [(wsym,wsym');(xsym,xsym');(ysym,ysym');(zsym,zsym')]

let prepost () =
  let phi =
    let open Infix in
    (int 0) <= x && x <= x'
  in
  let closure =
    let open Infix in
    !(x = x')
    && WV.star srk phi tr_symbols
  in
  assert_implies closure (Ctx.mk_leq (int 0) x);
  assert_implies closure (Ctx.mk_leq (int 0) x')

let simple_induction () =
  let phi =
    let open Infix in
    w' = w + (int 1)
    && x' = x + (int 2)
    && y' = y + z
    && z = (int 3)
  in
  let closure = WV.star srk phi tr_symbols in
  let result =
    let open Infix in
    (int 2)*(w' - w) = x' - x
    && (w' - w) + (x' - x) = (y' - y)
  in
  assert_implies closure result

let count_by_1 () =
  let tr_symbols = [(xsym,xsym')] in
  let phi =
    let open Infix in
    x' = x + (int 1)
    && x < y
  in
  let closure =
    let open Infix in
    x = (int 0)
    && WV.star srk phi tr_symbols
    && y <= x'
    && (int 0) <= y
  in
  let result =
    let open Infix in
    x' = y
  in
  assert_implies closure result

let count_by_2 () =
  let tr_symbols = [(xsym,xsym')] in
  let phi =
    let open Infix in
    x' = x + (int 2)
    && x < y
  in
  let closure =
    let open Infix in
    x = (int 0)
    && WV.star srk phi tr_symbols
    && y <= x'
    && (int 0) <= y
  in
  let result =
    let open Infix in
    x' = y
  in
  let y_even =
    let open Infix in
    y = (int 2) * z
  in
  assert_not_implies closure result;
  assert_implies (mk_and srk [closure; y_even]) result

let stratified1 () =
  let tr_symbols = [(xsym,xsym');(ysym,ysym')] in
  let phi =
    let open Infix in
    x' = x + (int 1)
    && y' = y + z
  in
  let closure = WV.star srk phi tr_symbols in
  let result =
    let open Infix in
    z*(x' - x) = (y' - y)
  in
  assert_implies closure result

let stratified2 () =
  let tr_symbols = [(xsym,xsym');(ysym,ysym')] in
  let phi =
    let open Infix in
    x' = x + (int 1)
    && y' = y + x
  in
  let closure =
    let open Infix in
    x = (int 0)
    && y = (int 0)
    && WV.star srk phi tr_symbols
  in
  let result =
    let open Infix in
    (int 2)*y' = x'*(x' - (int 1))
  in
  assert_implies closure result

let count_by_k () =
  let tr_symbols = [(xsym,xsym')] in
  let phi =
    let open Infix in
    x' = x + z
    && x < y
  in
  let closure =
    let open Infix in
    x = (int 0)
    && (int 1) <= z
    && WV.star srk phi tr_symbols
    && y <= x'
  in
  let result =
    let open Infix in
    x' <= (int 100) * z
  in
  let z_div_y =
    let open Infix in
    y = (int 100) * z
  in
  assert_not_implies closure result;
  assert_implies (mk_and srk [closure; z_div_y]) result

let ineq1 () =
  let phi =
    let open Infix in
    z' = z + (int 1)
    && ((x' = x + (int 1) && y' = y)
        || (x' = x && y' = y + (int 1)))
  in
  let closure =
    let open Infix in
    x = (int 0)
    && y = (int 0)
    && z = (int 0)
    && WV.star srk phi tr_symbols
  in
  let result =
    let open Infix in
    x' + y' = z'
    && x' <= z'
    && y' <= z'
    && (int 0) <= x'
    && (int 0) <= y'
  in
  assert_implies closure result

let ineq2 () =
  let phi =
    let open Infix in
    x' = x + (int 1)
    && ((y' = y + (int 1) || y' = y + (int 10)))
  in
  let closure =
    let open Infix in
    x = (int 0)
    && y = (int 0)
    && WV.star srk phi tr_symbols
  in
  let result =
    let open Infix in
    x' <= y'
    && y' <= (int 10) * x'
  in
  assert_implies closure result

let stratified_ineq1 () =
  let phi =
    let open Infix in
    x' = x + (int 1)
    && (int 0) <= x
    && ((y' = y + (int 1) || y' = y + x + (int 1)))
  in
  let closure =
    let open Infix in
    x = (int 0)
    && y = (int 0)
    && WV.star srk phi tr_symbols
  in
  let result =
    let open Infix in
    x' <= y'
    && (int 2)*y' <= x'*(x' + (int 1))
    && (int 0) <= x'
  in
  assert_implies closure result

let suite = "Iteration" >::: [
    "prepost" >:: prepost;
    "simple_induction" >:: simple_induction;
    "count_by_1" >:: count_by_1;
    "count_by_2" >:: count_by_2;
    "stratified1" >:: stratified1;
    "stratified2" >:: stratified2;
    (*    "count_by_k" >:: count_by_k;*)
    "ineq1" >:: ineq1;
    "ineq2" >:: ineq2;
    "stratified_ineq1" >:: stratified_ineq1;
  ]

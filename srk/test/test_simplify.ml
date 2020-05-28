open Srk
open OUnit
open Syntax
open Test_pervasives

let simplify_dda1 () =
  let open Infix in
  let phi = x <= (int 0) in
  assert_equal_formula phi (SrkSimplify.simplify_dda srk (phi && phi));
  assert_equal_formula phi (SrkSimplify.simplify_dda srk (phi || phi))

let simplify_dda2 () =
  let open Infix in
  let phi = x < (int 0) || x = (int 0) || (int 0) < x in
  assert_equal_formula (mk_true srk) (SrkSimplify.simplify_dda srk phi)

let simplify_dda3 () =
  let open Infix in
  let phi = x < (int 0) || y < (int 0) in
  assert_equal_formula phi (SrkSimplify.simplify_dda srk (phi && phi));
  assert_equal_formula phi (SrkSimplify.simplify_dda srk (phi || phi))

let suite = "Simplify" >:::
  [
    "simplify_dda1" >:: simplify_dda1;
    "simplify_dda2" >:: simplify_dda2;
    "simplify_dda3" >:: simplify_dda3;
  ]

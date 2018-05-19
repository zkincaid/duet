open OUnit
open Test_pervasives
open Polynomial

let mk_qqx vec =
  List.fold_left
    (fun vec (i, k) -> QQX.add_term k i vec)
    QQX.zero
    (List.mapi (fun i k -> (i, QQ.of_int k)) vec)

module Infix = struct
  let ( + ) = ExpPolynomial.add
  let ( * ) = ExpPolynomial.mul
  let x = ExpPolynomial.of_polynomial (QQX.of_term QQ.one 1)
  let exp n = ExpPolynomial.of_exponential (QQ.of_int n)
  let int n = ExpPolynomial.scalar (QQ.of_int n)
  let frac n m = ExpPolynomial.scalar (QQ.of_frac n m)
  let ( - ) x y = ExpPolynomial.add x (ExpPolynomial.mul (int (-1)) y)
end

let two_to_x = ExpPolynomial.of_exponential (QQ.of_int 2)

let test_sum1 () =
  let sum = ExpPolynomial.summation two_to_x in
  let expected_sum =
    let open Infix in
    (int 2) * (exp 2) + (int (-1))
  in
  assert_equal_exppoly expected_sum sum

let test_sum2 () =
  let f =
    ExpPolynomial.mul
      (ExpPolynomial.of_polynomial (mk_qqx [0; 1]))
      two_to_x
  in
  let sum = ExpPolynomial.summation f in
  let expected_sum =
    let open Infix in
    (int 2) * ((exp 2) * (x + (int (-1))) + (int 1))
  in
  assert_equal_exppoly expected_sum sum

let test_sum3 () =
  let f =
    let open Infix in
    (x*x - x)*(exp 3)
  in
  let sum = ExpPolynomial.summation f in
  let expected_sum =
    let open Infix in
    (ExpPolynomial.scalar (QQ.of_frac 3 4))
    * ((exp 3)*((int 2) * x * x + (int (-4)) * x + (int 3)) + (int (-3)))
  in
  assert_equal_exppoly expected_sum sum

let test_sum4 () =
  let f =
    let open Infix in
    (x*x - x)
  in
  let sum = ExpPolynomial.summation f in
  let expected_sum =
    let open Infix in
    (ExpPolynomial.scalar (QQ.of_frac 1 3))*(x - (int 1))*x*(x + (int 1))
  in
  assert_equal_exppoly expected_sum sum

let test_sum4 () =
  let f =
    let open Infix in
    (x*x - x)
  in
  let sum = ExpPolynomial.summation f in
  let expected_sum =
    let open Infix in
    (ExpPolynomial.scalar (QQ.of_frac 1 3))*(x - (int 1))*x*(x + (int 1))
  in
  assert_equal_exppoly expected_sum sum

let test_sum5 () =
  let f =
    let open Infix in
    x*x*x - x + x*(exp 3) - (exp 2)
  in
  let sum = ExpPolynomial.summation f in
  let expected_sum =
    let open Infix in
    (ExpPolynomial.scalar (QQ.of_frac 1 4))*(
      (x - (int 1))*x*(x + (int 1))*(x + (int 2))
      + (int 6)*(exp 3)*x - (int 3)*(exp 3)
      - (int 8)*(exp 2)
      + (int 7)
    )
  in
  assert_equal_exppoly expected_sum sum

let test_rec1 () =
  let open Infix in
  let sln = ExpPolynomial.solve_rec (QQ.of_int 2) (int 1) in
  let expected_sln =
    (int 2)*(exp 2)-(int 1)
  in
  assert_equal_exppoly expected_sln sln

let test_rec2 () =
  let open Infix in
  let sln = ExpPolynomial.solve_rec (QQ.of_int 2) x in
  let expected_sln =
    (int 2)*(exp 2)-x-(int 2)
  in
  assert_equal_exppoly expected_sln sln

let test_rec3 () =
  let open Infix in
  let sln = ExpPolynomial.solve_rec (QQ.of_int 2) (exp 3) in
  let expected_sln =
    (int 3)*(exp 3)-(int 2)*(exp 2)
  in
  assert_equal_exppoly expected_sln sln

let test_rec4 () =
  let open Infix in
  let sln = ExpPolynomial.solve_rec (QQ.of_int 3) (x*(exp 9) - x) in
  let expected_sln =
    (frac 1 4)*((int 2) * x
                + (int 3)*(exp 9)*((int 2)*x - (int 1)) + (int 3))
  in
  assert_equal_exppoly expected_sln sln


let suite = "ExpPolynomial" >::: [
      "sum1" >:: test_sum1;
      "sum2" >:: test_sum2;
      "sum3" >:: test_sum3;
      "sum4" >:: test_sum4;
      "sum5" >:: test_sum5;
      "test_rec1" >:: test_rec1;
      "test_rec2" >:: test_rec2;
      "test_rec3" >:: test_rec3;
      "test_rec4" >:: test_rec4;
  ]

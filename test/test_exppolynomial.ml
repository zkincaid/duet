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

module UP = ExpPolynomial.UltPeriodic

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

let rec_list lambda xs =
  BatList.fold_lefti (fun (sum,xs) i f ->
      let sum = QQ.add (QQ.mul lambda sum) (ExpPolynomial.eval f i) in
      (sum,sum::xs))
    (QQ.zero,[])
    xs
  |> snd
  |> BatList.rev

let sum_list = rec_list QQ.one

let test_up_sum1 () =
  let f =
    let open Infix in
    UP.make [] [int 1; int 2]
  in
  let sum = UP.summation f in
  let expected_sum =
    let open Infix in
    UP.make [] [(frac 3 2)*x + (int 1); (frac 3 2)*x + (frac 3 2)]
  in
  assert_equal_up_exppoly expected_sum sum
let test_up_sum2 () =
  let f =
    let open Infix in
    UP.make [int 5; int 4; int 0] [int 1; int 2]
  in
  let sum = UP.summation f in
  let expected_sum =
    let open Infix in
    UP.make [int 5; int 9; int 9] [(frac 3 2)*x + (frac 11 2); (frac 3 2)*x + (int 6)]
  in
  assert_equal_up_exppoly expected_sum sum

let test_up_sum3 () =
  let f =
    let open Infix in
    UP.make [] [x; x + int 1]
  in
  let sum = UP.summation f in
  let expected_sum =
    let open Infix in
    UP.make [] [(frac 1 2)*x*x + x; (frac 1 2)*(x*x + (int 2)*x + (int 1))]
  in
  assert_equal_up_exppoly expected_sum sum

let test_up_sum4 () =
  let f =
    let open Infix in
        UP.make [int 1] [x; exp 2]
  in
  let sum = UP.summation f in
  let expected_sum =
    let open Infix in
    UP.make [int 1] [(frac 2 3)*(exp 2) + (frac 1 4)*x*x + (frac 1 2)*x - (frac 1 12);
                     (frac 4 3)*(exp 2) + (frac 1 4)*x*x - (frac 1 3)]
  in
  assert_equal_up_exppoly expected_sum sum
let test_up_sum5 () =
  let f =
    let open Infix in
    UP.make [int 1; int 2] [x; x + (int 1); (int 2)*x]
  in
  let sum = UP.summation f in
  let expected_sum =
    let open Infix in
    UP.make [int 1; int 3] [(frac 1 3) + x + (frac 2 3)*x*x;
                            (int 1) + (frac 2 3)*(x*x + x);
                            (int 1) + (frac 2 3)*x*x + (frac 4 3)*x]
  in
  assert_equal_up_exppoly expected_sum sum

let test_up_rec1 () =
  let f =
    let open Infix in
    UP.make [int 1; int 2; int 1] [x]
  in
  let sln = UP.solve_rec (QQ.of_int 2) f in
  let expected_sln =
    let open Infix in
    UP.make [int 1; int 4; int 9] [(frac 13 4)*(exp 2) - x - (int 2)]
  in
  assert_equal_up_exppoly expected_sln sln

let test_up_rec2 () =
  let f =
    let open Infix in
    UP.make [] [x; (int 2)*x]
  in
  let sln = UP.solve_rec (QQ.of_int 5) f in
  let expected_sln =
    let open Infix in
    UP.make [] [(frac 155 288)*(exp 5) - (frac 11 24)*x - (frac 155 288);
                (frac 155 288)*(exp 5) - (frac 7 24)*x - (frac 115 288)]
  in
  assert_equal_up_exppoly expected_sln sln

let test_up_rec3 () =
  let f =
    let open Infix in
    UP.make [int 1; int 2; int 3] [x; exp 2]
  in
  let sln = UP.solve_rec (QQ.of_int 3) f in
  let expected_sln =
    let open Infix in
    UP.make
      [int 1; int 5; int 18]
      [(exp 3)*(frac 3587 1440) - (frac 6 5)*(exp 2) - (frac 1 8)*x - (frac 9 32);
       (exp 3)*(frac 3587 1440) - (frac 4 5)*(exp 2) - (frac 3 8)*x - (frac 15 32)]
  in
  assert_equal_up_exppoly expected_sln sln

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
      "up_sum1" >:: test_up_sum1;
      "up_sum2" >:: test_up_sum2;
      "up_sum3" >:: test_up_sum3;
      "up_sum4" >:: test_up_sum4;
      "up_sum5" >:: test_up_sum5;
      "up_rec1" >:: test_up_rec1;
      "up_rec2" >:: test_up_rec2;
      "up_rec3" >:: test_up_rec3;
  ]

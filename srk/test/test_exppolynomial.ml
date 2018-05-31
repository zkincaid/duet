open OUnit
open Test_pervasives
open Polynomial
open BatPervasives

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
    (exp 2)-(int 1)
  in
  assert_equal_exppoly expected_sln sln

let test_rec2 () =
  let open Infix in
  let sln = ExpPolynomial.solve_rec (QQ.of_int 2) x in
  let expected_sln =
    (exp 2)-x-(int 1)
  in
  assert_equal_exppoly expected_sln sln

let test_rec3 () =
  let open Infix in
  let sln = ExpPolynomial.solve_rec (QQ.of_int 2) (exp 3) in
  let expected_sln =
    (exp 3) - (exp 2)
  in
  assert_equal_exppoly expected_sln sln

let test_rec4 () =
  let open Infix in
  let sln = ExpPolynomial.solve_rec (QQ.of_int 3) (x*(exp 9) - x) in
  let expected_sln =
    (frac 1 12) * ((int 6) * x
                   + (exp 9)*((int 2)*x - (int 3))
                   + (int 3))
  in
  assert_equal_exppoly expected_sln sln

let rec_list lambda xs =
  BatList.fold_lefti (fun (sum,xs) i x ->
      let total = QQ.add (QQ.mul lambda sum) x in
      (total,total::xs))
    (QQ.zero,[QQ.zero])
    xs
  |> snd
  |> BatList.rev

let sum_list xs =
  BatList.fold_left (fun (sum, xs) x ->
      let sum = QQ.add sum x in
      (sum,sum::xs))
    (QQ.zero,[])
    xs
  |> snd
  |> BatList.rev

let test_up_compose () =
  let f =
    let open Infix in
    UP.make [] [x; x]
  in
  let g =
    let open Infix in
    UP.make
      (List.map QQ.of_int [1;2;3;4])
      [x; (int 1) - x; (int 2)*x]
  in
  let check f a b x =
    assert_equal_qq
      (UP.eval f (a * x + b))
      (UP.eval (UP.compose_left_affine f a b) x)
  in
  check f 1 2 0;
  check f 1 2 1;
  check f 1 3 3;
  check f 2 3 1;
  check f 2 0 10;
  check f 3 0 10;
  check f 3 5 10;
  check g 1 2 0;
  check g 2 2 1;
  check g 2 3 4;
  check g 7 9 10

let test_up_sum1 () =
  let f =
    let open Infix in
    UP.make [] [int 1; int 2]
  in
  let sum = UP.summation f in
  let expected_sum =
    let open Infix in
    UP.make [] [(int 3)*x + (int 1); (int 3)*x + (int 3)]
  in
  assert_equal
    ~printer:([%derive.show: QQ.t list])
    (sum_list (BatList.of_enum ((0--100) /@ (UP.eval f))))
    (BatList.of_enum ((0--100) /@ (UP.eval sum)));
  assert_equal_up_exppoly expected_sum sum

let test_up_sum2 () =
  let f =
    let open Infix in
    UP.make (List.map QQ.of_int [5; 4; 0]) [int 1; int 2]
  in
  let sum = UP.summation f in
  let expected_sum =
    let open Infix in
    UP.make (List.map QQ.of_int [5; 9; 9]) [(int 6) + (int 3)*x; (int 8) + (int 3)*x]
  in
  assert_equal
    ~printer:([%derive.show: QQ.t list])
    (sum_list (BatList.of_enum ((0--100) /@ (UP.eval f))))
    (BatList.of_enum ((0--100) /@ (UP.eval sum)));
  assert_equal_up_exppoly expected_sum sum

let test_up_sum3 () =
  let f =
    let open Infix in
    UP.make [] [(int 2)*x; (int 2)*x + int 1]
  in
  let sum = UP.summation f in
  let expected_sum =
    let open Infix in
    UP.make [] [(int 2)*x*x + x; (int 2)*x*x + (int 3)*x + (int 1)]
  in
  assert_equal
    ~printer:([%derive.show: QQ.t list])
    (sum_list (BatList.of_enum ((0--100) /@ (UP.eval f))))
    (BatList.of_enum ((0--100) /@ (UP.eval sum)));
  assert_equal_up_exppoly expected_sum sum

let test_up_sum4 () =
  let f =
    let open Infix in
    UP.make [QQ.of_int 1] [x; exp 2]
  in
  let sum = UP.summation f in
  assert_equal
    ~printer:([%derive.show: QQ.t list])
    (sum_list (BatList.of_enum ((0--100) /@ (UP.eval f))))
    (BatList.of_enum ((0--100) /@ (UP.eval sum)))

let test_up_sum5 () =
  let f =
    let open Infix in
    UP.make [QQ.of_int 1; QQ.of_int 2] [x; x + (int 1); (int 2)*x]
  in
  let sum = UP.summation f in
  assert_equal
    ~printer:([%derive.show: QQ.t list])
    (sum_list (BatList.of_enum ((0--100) /@ (UP.eval f))))
    (BatList.of_enum ((0--100) /@ (UP.eval sum)))

let test_up_rec1 () =
  let f =
    let open Infix in
    UP.make (List.map QQ.of_int [1; 2; 1]) [x]
  in
  let sln = UP.solve_rec (QQ.of_int 2) f in
  assert_equal
    ~printer:([%derive.show: QQ.t list])
    (rec_list (QQ.of_int 2) (BatList.of_enum ((0--99) /@ (UP.eval f))))
    (BatList.of_enum ((0--100) /@ (UP.eval sln)))

let test_up_rec2 () =
  let f =
    let open Infix in
    UP.make [] [x; (int 2)*x]
  in
  let sln = UP.solve_rec (QQ.of_int 5) f in
  assert_equal
    ~printer:([%derive.show: QQ.t list])
    (rec_list (QQ.of_int 5) (BatList.of_enum ((0--99) /@ (UP.eval f))))
    (BatList.of_enum ((0--100) /@ (UP.eval sln)))

let test_up_rec3 () =
  let f =
    let open Infix in
    UP.make (List.map QQ.of_int [1; 2; 3]) [x; exp 2]
  in
  let sln = UP.solve_rec (QQ.of_int 3) f in
  assert_equal
    ~printer:([%derive.show: QQ.t list])
    (rec_list (QQ.of_int 3) (BatList.of_enum ((0--99) /@ (UP.eval f))))
    (BatList.of_enum ((0--100) /@ (UP.eval sln)))

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
      "up_compose" >:: test_up_compose;
      "up_sum1" >:: test_up_sum1;
      "up_sum2" >:: test_up_sum2;
      "up_sum3" >:: test_up_sum3;
      "up_sum4" >:: test_up_sum4;
      "up_sum5" >:: test_up_sum5;
      "up_rec1" >:: test_up_rec1;
      "up_rec2" >:: test_up_rec2;
      "up_rec3" >:: test_up_rec3;
  ]

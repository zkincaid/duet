open OUnit
open Interval

let assert_equal = assert_equal ~cmp:Interval.equal ~printer:Interval.show

let join_bottom () =
  let x = Interval.make_bounded (QQ.of_int 4) (QQ.of_int 5) in
  let x_left = Interval.join x Interval.bottom in
  let x_right = Interval.join Interval.bottom x in
  assert_equal x x_left;
  assert_equal x x_right

let empty_meet () =
  let x = Interval.make_bounded (QQ.of_int 4) (QQ.of_int 5) in
  let y = Interval.make_bounded (QQ.of_int 10) (QQ.of_int 100) in
  assert_equal (Interval.meet x y) Interval.bottom

let mul1 () =
  let x = Interval.make_bounded (QQ.of_int 1) (QQ.of_int 5) in
  let y = Interval.make_bounded (QQ.of_int (-10)) (QQ.of_int (-2)) in
  assert_equal (Interval.mul x y) (Interval.mul y x);
  assert_equal (Interval.mul x y)
	       (Interval.make_bounded (QQ.of_int (-50)) (QQ.of_int (-2)))


let mul_zero () =
  let x = Interval.make_bounded (QQ.of_int (-10)) (QQ.of_int 1) in
  assert_equal (Interval.mul Interval.zero x) Interval.zero;
  assert_equal (Interval.mul x Interval.zero) Interval.zero

let mul_signs () =
  let neg = Interval.make None (Some (QQ.of_int 0)) in
  let pos = Interval.make (Some (QQ.of_int 0)) None in
  assert_equal pos (Interval.mul neg neg);
  assert_equal pos (Interval.mul pos pos);
  assert_equal neg (Interval.mul pos neg);
  assert_equal neg (Interval.mul neg pos)

let apron_op op typ x y =
  let open Apron.Texpr0 in
  binop op typ Zero
    (cst (Apron.Coeff.Interval (Interval.apron_of x)))
    (cst (Apron.Coeff.Interval (Interval.apron_of y)))
  |> SrkApron.eval_texpr
  |> Interval.of_apron

let suite = "Interval" >:::
  [
    "join_bottom" >:: join_bottom;
    "empty_meet" >:: empty_meet;
    "mul1" >:: mul1;
    "mul_zero" >:: mul_zero;
    "mul_signs" >:: mul_signs;
  ]

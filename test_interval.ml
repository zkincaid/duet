open OUnit
open Interval
open ArkPervasives

let join_bottom () =
  let x = Interval.make_bounded (QQ.of_int 4) (QQ.of_int 5) in
  let x_left = Interval.join x Interval.bottom in
  let x_right = Interval.join Interval.bottom x in
  assert_equal ~cmp:Interval.equal ~printer:Interval.show x x_left;
  assert_equal ~cmp:Interval.equal ~printer:Interval.show x x_right

let empty_meet () =
  let x = Interval.make_bounded (QQ.of_int 4) (QQ.of_int 5) in
  let y = Interval.make_bounded (QQ.of_int 10) (QQ.of_int 100) in
  assert_equal ~cmp:Interval.equal ~printer:Interval.show
	       (Interval.meet x y) Interval.bottom

let mul1 () =
  let x = Interval.make_bounded (QQ.of_int 1) (QQ.of_int 5) in
  let y = Interval.make_bounded (QQ.of_int (-10)) (QQ.of_int (-2)) in
  assert_equal ~cmp:Interval.equal ~printer:Interval.show
	       (Interval.mul x y) (Interval.mul y x);
  assert_equal ~cmp:Interval.equal ~printer:Interval.show
	       (Interval.mul x y)
	       (Interval.make_bounded (QQ.of_int (-50)) (QQ.of_int (-2)))

let suite = "Interval" >:::
  [
    "join_bottom" >:: join_bottom;
    "empty_meet" >:: empty_meet;
    "mul1" >:: empty_meet;
  ]

open OUnit
open Interval
open ArkPervasives

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

let apron_op op typ x y =
  let open Apron in
  Texpr0.binop op typ Texpr0.Zero
    (Texpr0.cst (Coeff.Interval (apron_of x)))
    (Texpr0.cst (Coeff.Interval (apron_of y)))
  |> NumDomain.eval_texpr
  |> of_apron

let apron_mod = apron_op Apron.Texpr0.Mod Apron.Texpr0.Int

let mod1 () =
  let x = Interval.make_bounded (QQ.of_int 1) (QQ.of_int 5) in
  let y = Interval.negate x in
  assert_equal (Interval.modulo x y) (apron_mod x y);
  assert_equal (Interval.modulo y x) (apron_mod y x);
  assert_equal (Interval.modulo x x) (apron_mod x x);
  assert_equal (Interval.modulo y y) (apron_mod y y)

let mod2 () =
  let x = Interval.make_bounded (QQ.of_int (-1)) (QQ.of_int 5) in
  let y = Interval.make (Some (QQ.of_int 1)) None in
  let neg_x = Interval.negate x in
  let neg_y = Interval.negate y in
  (* Apron is overly conservative here *)
  assert_equal (Interval.modulo x y)
    (Interval.make_bounded (QQ.of_int (-1)) (QQ.of_int 5));
  assert_equal (Interval.modulo neg_x neg_y)
    (Interval.make_bounded (QQ.of_int (-5)) (QQ.of_int 1));

  assert_equal (Interval.modulo y x) (apron_mod y x);
  assert_equal (Interval.modulo x x) (apron_mod x x)

(*  assert_equal (Interval.modulo y y) (apron_mod y y)*)

let mod3 () =
  let x = Interval.make_bounded (QQ.of_int 4) (QQ.of_int 5) in
  let y = Interval.make_bounded (QQ.of_int 1) (QQ.of_int 3) in
  let neg_x = Interval.negate x in
  let neg_y = Interval.negate y in
  assert_equal (Interval.modulo x y) (apron_mod x y);
  assert_equal (Interval.modulo y x) (apron_mod y x);
  assert_equal (Interval.modulo neg_x neg_y) (apron_mod neg_x neg_y);
  assert_equal (Interval.modulo neg_y neg_x) (apron_mod neg_y neg_x)


let suite = "Interval" >:::
            [
              "join_bottom" >:: join_bottom;
              "empty_meet" >:: empty_meet;
              "mul1" >:: empty_meet;
              "mod1" >:: mod1;
              "mod2" >:: mod2;
              "mod3" >:: mod3;
            ]

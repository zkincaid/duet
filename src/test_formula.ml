(*pp camlp4find deriving.syntax *)

open Apak
open OUnit
open ArkPervasives
open BatPervasives

module StrVar = struct
  include Putil.PString
  let prime x = x ^ "'"
  let to_smt x = Smt.real_var x
  let of_smt sym = match Smt.symbol_refine sym with
    | Z3.Symbol_string str -> str
    | Z3.Symbol_int _ -> assert false
  let typ _ = TyReal
end
module T = Term.MakeHashconsed(StrVar)
module F = Formula.MakeHashconsed(T)
module FEq = Formula.MakeEq(F)

open T.Syntax
open F.Syntax

let test1 () =
  let x = T.var "x" in
  let y = T.var "y" in
  let phi = (x == y) in
  let eqs = FEq.extract_equalities phi ["x";"y"] in
  Log.log Log.info (Show.show<FEq.AffineTerm.t list> eqs);
  assert_equal (List.length eqs) 1

let test2 () =
  let x = T.var "x" in
  let y = T.var "y" in
  let z = T.var "z" in
  let phi = (x == y || x == z) in
  let eqs = FEq.extract_equalities phi ["x";"y";"z"] in
  Log.log Log.info (Show.show<FEq.AffineTerm.t list> eqs);
  assert_equal (List.length eqs) 0

let test3 () =
  let w = T.var "w" in
  let x = T.var "x" in
  let y = T.var "y" in
  let z = T.var "z" in
  let phi = ((w == x && x == y) || (w == z && z == y)) in
  let eqs = FEq.extract_equalities phi ["w";"x";"y";"z"] in
  Log.log Log.info (Show.show<FEq.AffineTerm.t list> eqs);
  assert_equal (List.length eqs) 1

let test4 () =
  let w = T.var "w" in
  let x = T.var "x" in
  let y = T.var "y" in
  let z = T.var "z" in
  let phi = ((w == x && x == y) || (w == z && z == y)) in
  let eqs = FEq.extract_equalities phi ["x";"y";"z"] in
  Log.log Log.info (Show.show<FEq.AffineTerm.t list> eqs);
  assert_equal (List.length eqs) 0

let test5 () =
  let w = T.var "w" in
  let x = T.var "x" in
  let y = T.var "y" in
  let z = T.var "z" in
  let phi = ((w == x && x == y) || (w == z && z == y)) in
  let eqs = FEq.extract_equalities phi ["w";"y"] in
  Log.log Log.info (Show.show<FEq.AffineTerm.t list> eqs);
  assert_equal (List.length eqs) 1

let test6 () =
  let w = T.var "w" in
  let x = T.var "x" in
  let y = T.var "y" in
  let z = T.var "z" in
  let phi = w >= x && ((w <= x && x == y) || (w == z && z == y)) in
  let eqs = FEq.extract_equalities phi ["w";"y"] in
  Log.log Log.info (Show.show<FEq.AffineTerm.t list> eqs);
  assert_equal (List.length eqs) 1

let test7 () =
  let x = T.var "x" in
  let phi = x == T.one in
  let eqs = FEq.extract_equalities phi ["x"] in
  Log.log Log.info (Show.show<FEq.AffineTerm.t list> eqs);
  assert_equal (List.length eqs) 1

let test8 () =
  let w = T.var "w" in
  let x = T.var "x" in
  let y = T.var "y" in
  let z = T.var "z" in
  let phi =
    w >= x && z <= T.one && ((w <= x && x == y && z == T.one)
			     || (w == z && z == y && z >= T.one))
  in
  let eqs = FEq.extract_equalities phi ["w";"x";"y";"z"] in
  Log.log Log.info (Show.show<FEq.AffineTerm.t list> eqs);
  assert_equal (List.length eqs) 2

let test9 () =
  let x = T.var "x" in
  let y = T.var "y" in
  let z = T.var "z" in
  let phi = F.conj (F.leq x y) (F.leq y z) in
  let psi1 = F.exists_list ["y"] phi in
  let psi2 = F.leq x z in
  assert_equal ~cmp:F.equiv ~printer:F.show psi2 psi1

let test10 () =
  let x = T.var "x" in
  let y = T.var "y" in
  let z = T.var "z" in
  let two = T.const (QQ.of_int 2) in
  let five = T.const (QQ.of_int 5) in
  let phi =
    x <= (two * y) && x >= (y + y) && x < z && x >= z - five in
  let psi1 = F.exists_list ["x"] phi in
  let psi2 = (two * y) < z && (two * y) >= z - five in
  assert_equal ~cmp:F.equiv ~printer:F.show psi2 psi1

let test11 () =
  let w = T.var "w" in
  let x = T.var "x" in
  let y = T.var "y" in
  let z = T.var "z" in
  let phi = w <= x && x <= y && y <= z in
  let psi1 = F.exists_list ["x";"y"] phi in
  let psi2 = w <= z in
  assert_equal ~cmp:F.equiv ~printer:F.show psi2 psi1

let linearize phi =
  let max = ref (-1) in
  let mk () =
    incr max;
    "nonlin" ^ (string_of_int (!max))
  in
  F.linearize mk phi

let assert_implies phi psi =
  if not (F.implies phi psi) then
    assert_failure (Printf.sprintf "%s\ndoes not imply\n%s"
		      (F.show phi)
		      (F.show psi))

let linearize1 () =
  let x = T.var "x" in
  let y = T.var "y" in
  let const = T.const % QQ.of_int in
  let phi =
    linearize (T.zero <= x
	       && x <= (const 1000)
	       && y == x * x
	       && y >= (const 1000000))
  in
  let psi = (x == const 1000) && (y == const 1000000) in
  assert_implies phi psi

let linearize2 () =
  let w = T.var "w" in
  let x = T.var "x" in
  let y = T.var "y" in
  let z = T.var "z" in
  let phi =
    linearize (T.one <= x
	       && x <= T.one
	       && w == T.zero
	       && z == y / x + w * y)
  in
  assert_implies phi (z == y)

let linearize3 () =
  let w = T.var "w" in
  let x = T.var "x" in
  let y = T.var "y" in
  let z = T.var "z" in
  let phi =
    linearize (w <= x
	       && T.zero <= y
	       && w >= T.zero
	       && z == x * y)
  in
  assert_implies phi (z >= T.zero)

(* easier version of linearization5: y * y appears twice, but we when we
   replace nonlinear terms by variables we lose that information. *)
let linearize4 () =
  let x = T.var "x" in
  let y = T.var "y" in
  let z = T.var "z" in
  let phi =
    linearize (x == y * y && z == y * y + T.one)
  in
  assert_implies phi (x < z)

(* to pass this test case, we need linearization to be smart enough to see
   that x = y implies x * x = y * y *)
let linearize5 () =
  let x = T.var "x" in
  let y = T.var "y" in
  let z = T.var "z" in
  let phi =
    linearize (x == y && z == x * x && z == y * y + (T.const (QQ.of_int 1)))
  in
  assert_implies phi F.bottom


let suite = "Formula" >:::
  [
    "test1" >:: test1;
    "test2" >:: test2;
    "test3" >:: test3;
    "test4" >:: test4;
    "test5" >:: test5;
    "test6" >:: test6;
    "test7" >:: test7;
    "test8" >:: test8;
    "test9" >:: test9;
    "test10" >:: test10;
    "test11" >:: test11;
    "linearize1" >:: linearize1;
    "linearize2" >:: linearize2;
    "linearize3" >:: linearize3;
    "linearize4" >:: linearize4;
    "linearize5" >:: linearize5;
  ]

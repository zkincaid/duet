(*pp camlp4find deriving.syntax *)

open Apak
open OUnit
open ArkPervasives

module StrVar = Test_formula.StrVar

module T = Term.MakeHashconsed(StrVar)
module F = Formula.MakeHashconsed(T)
open T.Syntax
open F.Syntax

let man = Polka.manager_alloc_strict ()
let box = Box.manager_alloc ()
module D = F.T.D
module Env = F.T.D.Env

let roundtrip1 () =
  let x = T.var "x" in
  let y = T.var "y" in
  let env = Env.of_enum (BatList.enum ["x"; "y"]) in
  let five = T.const (QQ.of_int 5) in
  let two = T.const (QQ.of_int 2) in
  let t = (x + y) / five + (two * x) in
  let t2 = T.of_apron env (T.to_apron env t) in
  assert_equal ~cmp:T.equal ~printer:T.show t t2

let roundtrip2 () =
  let x = T.var "x" in
  let y = T.var "y" in
  let z = T.var "z" in
  let env = Env.of_enum (BatList.enum ["x"; "y"; "z"]) in
  let five = T.const (QQ.of_int 5) in
  let two = T.const (QQ.of_int 2) in
  let t = T.floor ((x + y) / ((two / five) + z)) + T.one in
  let t2 = T.of_apron env (T.to_apron env t) in
  assert_equal ~cmp:T.equal ~printer:T.show t t2

let abstract1 () =
  let x = T.var "x" in
  let y = T.var "y" in
  let phi = (x == y) || (x < y) in
  let psi1 = F.of_abstract (F.abstract man (x <= y)) in
  let psi2 = F.of_abstract (F.abstract man phi) in
  assert_equal ~cmp:F.equiv ~printer:F.show psi2 psi1

let box () =
  let x = T.var "x" in
  let y = T.var "y" in
  let phi = T.zero <= x && x <= y && y <= T.one in
  let psi = F.of_abstract (F.abstract box phi) in
  let psi2 =
       T.zero <= x && x <= T.one
    && T.zero <= y && y <= T.one
  in
  assert_equal ~cmp:F.equiv ~printer:F.show psi psi2

let env1 () =
  let x = T.var "x" in
  let y = T.var "y" in
  let z = T.var "z" in
  let psi1 = F.of_abstract (D.meet
			      (F.abstract man (x <= y))
			      (F.abstract man (y <= z)))
  in
  let psi2 = F.of_abstract (F.abstract man (x <= y && y <= z)) in
  assert_equal ~cmp:F.equiv ~printer:F.show psi2 psi1

let env2 () =
  let w = T.var "w" in
  let x = T.var "x" in
  let y = T.var "y" in
  let z = T.var "z" in
  let psi1 = F.of_abstract (D.join
			      (F.abstract man (x <= z && w <= x))
			      (F.abstract man (x <= z && y < z)))
  in
  let psi2 = F.of_abstract (F.abstract man (x <= z)) in
  assert_equal ~cmp:F.equiv ~printer:F.show psi2 psi1


let suite = "Numerical" >:::
  [
    "roundtrip1" >:: roundtrip1;
    "roundtrip2" >:: roundtrip2;
    "abstract1" >:: abstract1;
    "box" >:: box;
    "env1" >:: env1;
    "env2" >:: env2;
  ]

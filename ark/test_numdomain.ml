open Apak
open OUnit
open ArkPervasives
open BatPervasives

module StrVar = Test_formula.StrVar

module T = Term.Make(StrVar)
module F = Formula.Make(T)
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

let roundtrip3 () =
  let x = T.var "ix" in
  let env = Env.of_enum (BatList.enum ["ix"]) in
  let five = T.const (QQ.of_int 5) in
  let two = T.const (QQ.of_int 2) in
  let t = T.modulo (x + five) two in
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

let assign1 () =
  let x = T.var "x" in
  let y = T.var "y" in
  let prop = F.abstract man (x == T.zero && y == x + T.one) in
  let post_prop1 = F.abstract man (x == T.one && y == T.one) in
  let post_prop2 = F.abstract_assign man prop "x" y in
  assert_equal ~cmp:D.equal ~printer:D.show post_prop2 post_prop1

let assign2 () =
  let x = T.var "x" in
  let y = T.var "y" in
  let two = T.const (QQ.of_int 2) in
  let prop = F.abstract man (y == T.one) in
  let post_prop1 = F.abstract man (x == two && y == T.one) in
  let post_prop2 = F.abstract_assign man prop "x" (y + y) in
  assert_equal ~cmp:D.equal ~printer:D.show post_prop2 post_prop1

let assign3 () =
  let x = T.var "x" in
  let y = T.var "y" in
  let prop = F.abstract man F.top in
  let post_prop1 = F.abstract man (x == y) in
  let post_prop2 = F.abstract_assign man prop "x" y in
  assert_equal ~cmp:D.equal ~printer:D.show post_prop2 post_prop1

let formula_of_bounds t bounds =
  let f (pred, bound) = match pred with
    | Plt  -> F.lt t bound
    | Pgt  -> F.gt t bound
    | Pleq -> F.leq t bound
    | Pgeq -> F.geq t bound
    | Peq  -> F.eq t bound
  in
  BatEnum.fold F.conj F.top (BatEnum.map f (BatList.enum bounds))

(* Check that Apron's expression evaluation agrees with ark's *)
let assert_eval_equal t =
  let apron_ivl =
    Interval.of_apron (NumDomain.eval_texpr (T.to_apron Env.empty t))
  in
  match Interval.const_of apron_ivl with
  | Some apron_val ->
    let ark_val = T.evaluate (fun _ -> assert false) t in
    assert_equal ~cmp:QQ.equal ~printer:QQ.show apron_val ark_val
  | None -> assert false


(* Make sure Apron's modulus & integer division operators agrees with ark's. *)
let modulo () =
  let expr1 = T.modulo (T.const (QQ.of_int 14)) (T.const (QQ.of_int (-3))) in
  let expr2 = T.modulo (T.const (QQ.of_int (-14))) (T.const (QQ.of_int 3)) in
  let expr3 = T.modulo (T.const (QQ.of_int (-14))) (T.const (QQ.of_int (-3))) in
  assert_eval_equal expr1;
  assert_eval_equal expr2;
  assert_eval_equal expr3

let div () =
  let expr1 = T.idiv (T.const (QQ.of_int 14)) (T.const (QQ.of_int (-3))) in
  let expr2 = T.idiv (T.const (QQ.of_int (-14))) (T.const (QQ.of_int 3)) in
  let expr3 = T.idiv (T.const (QQ.of_int (-14))) (T.const (QQ.of_int (-3))) in
  assert_eval_equal expr1;
  assert_eval_equal expr2;
  assert_eval_equal expr3

let suite = "Numerical" >:::
            [
              "roundtrip1" >:: roundtrip1;
              "roundtrip2" >:: roundtrip2;
              "roundtrip3" >:: roundtrip3;
              "abstract1" >:: abstract1;
              "box" >:: box;
              "env1" >:: env1;
              "env2" >:: env2;
              "assign1" >:: assign1;
              "assign2" >:: assign2;
              "assign3" >:: assign3;
              "modulo" >:: modulo;
              "div" >:: div
            ]

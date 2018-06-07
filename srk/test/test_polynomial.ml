open OUnit
open Polynomial
open BatPervasives

let mk_qqx vec =
  List.fold_left
    (fun vec (i, k) -> QQX.add_term k i vec)
    QQX.zero
    (List.mapi (fun i k -> (i, QQ.of_int k)) vec)

module QQXsInfix = struct
  let ( + ) = QQXs.add
  let ( - ) = QQXs.sub
  let ( * ) = QQXs.mul
  let int k = QQXs.scalar (QQ.of_int k)
  let dim k = QQXs.of_dim (Char.code k)
end

let assert_equal_qqx p q =
  assert_equal ~cmp:QQX.equal ~printer:QQX.show p q

let assert_equal_qqxs p q =
  let pp_dim formatter i =
    Format.pp_print_string formatter (Char.escaped (Char.chr i))
  in
  let show = SrkUtil.mk_show (QQXs.pp pp_dim) in
  assert_equal ~printer:show ~cmp:QQXs.equal p q

let test_mul () =
  let p = mk_qqx [1; 1] in
  let q = mk_qqx [-1; 1] in
  let r = mk_qqx [-1; 0; 1] in
  assert_equal_qqx r (QQX.mul p q)

let test_compose1 () = 
  let p = mk_qqx [-1; 1] in
  let q = mk_qqx [-1; 0; 1] in
  let r = mk_qqx [0; -2; 1] in
  assert_equal_qqx r (QQX.compose q p)

let test_compose2 () =
  let p = mk_qqx [1; 0; 1] in
  let q = mk_qqx [1; 2; 3; 4] in
  let r = mk_qqx [10; 0; 20; 0; 15; 0; 4] in
  (*  let r = mk_qqx [6; 0; 8; 0; 3; 0; 0] in*)
  assert_equal_qqx r (QQX.compose q p)

let test_eval () =
  let p = mk_qqx [-1; 2; -3; 4] in
  assert_equal ~printer:QQ.show (QQ.of_int 23) (QQX.eval p (QQ.of_int 2))

let test_summation1 () =
  let p = mk_qqx [2] in
  let r = mk_qqx [2; 2] in
  assert_equal_qqx r (QQX.summation p)

let test_summation2 () = (* Gauss sum *)
  let p = mk_qqx [0; 1] in
  let r =
    QQX.scalar_mul (QQ.inverse (QQ.of_int 2))
      (QQX.mul (mk_qqx [0;1]) (mk_qqx [1;1]))
  in
  assert_equal_qqx r (QQX.summation p)

let test_rewrite1 () =
  let open QQXsInfix in
  let x = dim 'x' in
  let y = dim 'y' in
  let rewrite =
    Rewrite.mk_rewrite Monomial.deglex [
      y * y - (int 2);
      x * x + y * x + (int 1)
    ]
  in
  assert_equal_qqxs (int (-1)) (Rewrite.reduce rewrite (x * x * x * x))

(* Linear system of equations *)
let test_rewrite2 () =
  let open QQXsInfix in
  let x = dim 'x' in
  let y = dim 'y' in
  let z = dim 'z' in
  let rewrite =
    Rewrite.mk_rewrite Monomial.lex [
      (int 2) * x - (int 2) * y + (int 4) * z + (int 2);
      (int 3) * x + (int 2) * y - z - (int 1);
      (int (-2)) * x + y - (int 2) * z;
    ] |> Rewrite.reduce_rewrite
  in
  assert_equal_qqxs (int 1) (Rewrite.reduce rewrite x);
  assert_equal_qqxs (int (-2)) (Rewrite.reduce rewrite y);
  assert_equal_qqxs (int (-2)) (Rewrite.reduce rewrite z)

let test_grobner1 () =
  let open QQXsInfix in
  let a = dim 'a' in
  let b = dim 'b' in
  let c = dim 'c' in
  let x = dim 'x' in
  let y = dim 'y' in
  let z = dim 'z' in
  let rewrite =
    Rewrite.mk_rewrite Monomial.degrevlex [
      a * x * x + b * x + c;
      a * y * y + b * y + c;
      z * (x - y) - (int 1);
    ] |> Rewrite.grobner_basis
  in
  let p = a * x * y - c in
  let q = a * (x + y) + b in
  assert_equal_qqxs (int 0) (Rewrite.reduce rewrite p);
  assert_equal_qqxs (int 0) (Rewrite.reduce rewrite q)

let test_grobner2 () =
  let open QQXsInfix in
  let x = dim 'x' in
  let y = dim 'y' in
  let rewrite =
    Rewrite.mk_rewrite Monomial.degrevlex [
      x * x - y;
      x * x * x - x
    ] |> Rewrite.grobner_basis
  in
  let p = x * y - x in
  let q = y * y - y in
  assert_equal_qqxs (int 0) (Rewrite.reduce rewrite p);
  assert_equal_qqxs (int 0) (Rewrite.reduce rewrite q)

let test_grobner_elim () =
  let open QQXsInfix in
  let x = dim 'x' in
  let y = dim 'y' in
  let elim_order =
    Monomial.block [fun d -> d = (Char.code 'x')] Monomial.degrevlex
  in
  let rewrite =
    Rewrite.mk_rewrite elim_order [
      x - y * y;
      x * x - x
    ] |> Rewrite.grobner_basis
  in
  let p = x * x * y - x in
  let q = y * y * y - y * y in
  assert_equal_qqxs q (Rewrite.reduce rewrite p)

let rec mul_factors = function
  | [] -> QQX.of_term QQ.one 0
  | (p,n)::factors ->
    QQX.mul (QQX.exp p n) (mul_factors factors)

let qqx_of_list = QQX.of_enum % BatList.enum
let qq = QQ.of_int

let factor () =
  let correct_factorization p =
    let (content, factors) = QQX.factor p in
    assert_equal_qqx p (QQX.scalar_mul content (mul_factors factors))
  in
  correct_factorization (qqx_of_list [(qq (-1), 0); (qq 1, 2)]);
  correct_factorization (qqx_of_list [(QQ.of_frac 1 2, 4);
                                      (QQ.of_frac 1 4, 2)])

let suite = "Polynomial" >::: [
    "mul" >:: test_mul;
    "compose1" >:: test_compose1;
    "compose2" >:: test_compose2;
    "eval" >:: test_eval;
    "test_summation1" >:: test_summation1;
    "test_summation2" >:: test_summation2;
    "test_rewrite1" >:: test_rewrite1;
    "test_rewrite2" >:: test_rewrite2;
    "test_grobner1" >:: test_grobner1;
    "test_grobner2" >:: test_grobner2;
    "test_grobner_elim" >:: test_grobner_elim;
    "factor" >:: factor;
  ]

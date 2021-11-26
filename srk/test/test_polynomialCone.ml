open Srk
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

let assert_equal_ideal p q =
  let pp_dim formatter i =
    Format.pp_print_string formatter (Char.escaped (Char.chr i))
  in
  let show = SrkUtil.mk_show (Ideal.pp pp_dim) in
  assert_equal ~printer:show ~cmp:Ideal.equal p q

(* let test_build_cone1 () = *)


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

let suite = "PolynomialCone" >::: [
    "test_grobner1" >:: test_grobner1;
  ]

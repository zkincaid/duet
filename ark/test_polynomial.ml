open OUnit
open Polynomial
open BatPervasives

let mk_uvp vec =
  List.fold_left
    (fun vec (i, k) -> QQUvp.add_term k i vec)
    QQUvp.zero
    (List.mapi (fun i k -> (i, QQ.of_int k)) vec)

module MvpInfix = struct
  let ( + ) = Mvp.add
  let ( - ) = Mvp.sub
  let ( * ) = Mvp.mul
  let int k = Mvp.scalar (QQ.of_int k)
  let dim k = Mvp.of_dim (Char.code k)
end

let assert_equal_mvp p q =
  let pp_dim formatter i =
    Format.pp_print_string formatter (Char.escaped (Char.chr i))
  in
  let show = ArkUtil.mk_show (Mvp.pp pp_dim) in
  assert_equal ~printer:show ~cmp:Mvp.equal p q

let test_mul () =
  let p = mk_uvp [1; 1] in
  let q = mk_uvp [-1; 1] in
  let r = mk_uvp [-1; 0; 1] in
  assert_equal ~printer:QQUvp.show r (QQUvp.mul p q)

let test_compose1 () = 
  let p = mk_uvp [-1; 1] in
  let q = mk_uvp [-1; 0; 1] in
  let r = mk_uvp [0; -2; 1] in
  assert_equal ~printer:QQUvp.show r (QQUvp.compose q p)

let test_compose2 () =
  let p = mk_uvp [1; 0; 1] in
  let q = mk_uvp [1; 2; 3; 4] in
  let r = mk_uvp [10; 0; 20; 0; 15; 0; 4] in
  (*  let r = mk_uvp [6; 0; 8; 0; 3; 0; 0] in*)
  assert_equal ~printer:QQUvp.show r (QQUvp.compose q p)

let test_eval () =
  let p = mk_uvp [-1; 2; -3; 4] in  
  assert_equal ~printer:QQ.show (QQ.of_int 23) (QQUvp.eval p (QQ.of_int 2))

let test_summation1 () =
  let p = mk_uvp [2] in
  let r = mk_uvp [2; 2] in
  assert_equal ~printer:QQUvp.show r (QQUvp.summation p)

let test_summation2 () = (* Gauss sum *)
  let p = mk_uvp [0; 1] in
  let r =
    QQUvp.scalar_mul (QQ.inverse (QQ.of_int 2))
      (QQUvp.mul (mk_uvp [0;1]) (mk_uvp [1;1]))
  in
  assert_equal ~printer:QQUvp.show r (QQUvp.summation p)

let test_rewrite1 () =
  let open MvpInfix in
  let x = dim 'x' in
  let y = dim 'y' in
  let rewrite =
    Rewrite.mk_rewrite Monomial.deglex [
      y * y - (int 2);
      x * x + y * x + (int 1)
    ]
  in
  assert_equal_mvp (int (-1)) (Rewrite.reduce rewrite (x * x * x * x))

(* Linear system of equations *)
let test_rewrite2 () =
  let open MvpInfix in
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
  assert_equal_mvp (int 1) (Rewrite.reduce rewrite x);
  assert_equal_mvp (int (-2)) (Rewrite.reduce rewrite y);
  assert_equal_mvp (int (-2)) (Rewrite.reduce rewrite z)

let test_grobner1 () =
  let open MvpInfix in
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
  assert_equal_mvp (int 0) (Rewrite.reduce rewrite p);
  assert_equal_mvp (int 0) (Rewrite.reduce rewrite q)

let test_grobner2 () =
  let open MvpInfix in
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
  assert_equal_mvp (int 0) (Rewrite.reduce rewrite p);
  assert_equal_mvp (int 0) (Rewrite.reduce rewrite q)

let test_grobner_elim () =
  let open MvpInfix in
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
  assert_equal_mvp q (Rewrite.reduce rewrite p)

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
  ]

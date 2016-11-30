open OUnit
open Polynomial

let mk_uvp vec =
  List.fold_left
    (fun vec (i, k) -> QQUvp.add_term k i vec)
    QQUvp.zero
    (List.mapi (fun i k -> (i, QQ.of_int k)) vec)

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

let suite = "Polynomial" >::: [
    "mul" >:: test_mul;
    "compose1" >:: test_compose1;
    "compose2" >:: test_compose2;
    "eval" >:: test_eval;
    "test_summation1" >:: test_summation1;
    "test_summation2" >:: test_summation2;
  ]

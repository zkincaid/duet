open OUnit
open Linear

let mk_vector vec =
  List.fold_left
    (fun vec (i, k) -> QQVector.add_term k i vec)
    QQVector.zero
    (List.mapi (fun i k -> (i, QQ.of_int k)) vec)

let mk_matrix mat =
  List.fold_left
    (fun mat (i, row) -> QQMatrix.add_row i row mat)
    QQMatrix.zero
    (List.mapi (fun i row -> (i, mk_vector row)) mat)

let dot () =
  let u = mk_vector [1; 2; 3] in
  let v = mk_vector [2; 3] in
  assert_equal ~printer:QQ.show (QQ.of_int 8) (QQVector.dot u v);
  assert_equal ~printer:QQ.show (QQ.of_int 8) (QQVector.dot v u)

let mul () =
  let m1 = mk_matrix [[7; 3];
                      [2; 5];
                      [6; 8];
                      [9; 0]]
  in
  let m2 = mk_matrix [[7; 4; 9];
                      [8; 1; 5]]
  in
  let res1 = mk_matrix [[73; 31; 78];
                        [54; 13; 43];
                        [106; 32; 94];
                        [63; 36; 81]]
  in
  let res2 = mk_matrix [[111; 113];
                        [88; 69]]
  in
  assert_equal ~printer:QQMatrix.show res1 (QQMatrix.mul m1 m2);
  assert_equal ~printer:QQMatrix.show res2 (QQMatrix.mul m2 m1)

let solve1 () =
  let m = mk_matrix [[2; 4; 1];
                     [3; 2; 5];
                     [4; 1; 1]]
  in
  let b = mk_vector [6; 5; 4] in
  let x = solve_exn m b in
  assert_equal ~printer:QQVector.show b (vector_right_mul m x)

let solve2 () =
  let m = mk_matrix [[1; 2; 3];
                     [7; 0; 7]]
  in
  let b = mk_vector [15; 31] in
  let b2 = mk_vector [15] in
  let x = solve_exn m b in
  let x2 = solve_exn m b2 in
  assert_equal ~printer:QQVector.show b (vector_right_mul m x);
  assert_equal ~printer:QQVector.show b2 (vector_right_mul m x2)

let solve3 () =
  let m = mk_matrix [[1; 2; 3];
                     [2; 0; 1];
                     [3; 2; 4]]
  in
  let b = mk_vector [1; 2; 3] in
  assert_bool
    "Unsolvable system of linear equations"
     (solve m b = None)

let suite = "Linear" >::: [
    "dot" >:: dot;
    "mul" >:: mul;
    "solve1" >:: solve1;
    "solve2" >:: solve2;
    "solve3" >:: solve3;
  ]

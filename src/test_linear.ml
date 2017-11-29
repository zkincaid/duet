open OUnit
open Linear
open Test_pervasives

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

let mk_qqvector vec =
  List.fold_left
    (fun vec (i, k) -> QQVector.add_term k i vec)
    QQVector.zero
    (List.mapi (fun i k -> (i, k)) vec)

let mk_qqmatrix mat =
  List.fold_left
    (fun mat (i, row) -> QQMatrix.add_row i row mat)
    QQMatrix.zero
    (List.mapi (fun i row -> (i, mk_qqvector row)) mat)

let dot () =
  let u = mk_vector [1; 2; 3] in
  let v = mk_vector [2; 3] in
  assert_equal_qq (QQ.of_int 8) (QQVector.dot u v);
  assert_equal_qq (QQ.of_int 8) (QQVector.dot v u)

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
  let m = mk_matrix [[1; 0; 2];
                     [2; 1; 0];
                     [3; 1; 1];
                     [0; 1; 1]]
  in
  let b = mk_vector [1; 2; 3; 4] in
  assert_bool
    "Unsolvable system of linear equations"
     (solve m b = None)

let solve4 () =
  let m = mk_matrix [[1; -1; -1];
                     [0; 0; 1]]
  in
  let b = mk_vector [1] in
  let x = solve_exn m b in
  assert_equal ~printer:QQVector.show b (vector_right_mul m x)

let solve5 () =
  let m = mk_matrix [[1; 0; 0];
                     [1; 0; 0];
                     [0; 0; 1]]
  in
  let b = mk_vector [1; 1] in
  let x = solve_exn m b in
  assert_equal ~printer:QQVector.show b (vector_right_mul m x)

let rowspace1 () =
  let a = mk_matrix [[1; 0; 0];
                     [1; 1; 1];
                     [0; 0; 1]]
  in
  let b = mk_matrix [[1; 0; 0];
                     [1; 1; 1];
                     [0; 1; 1]]
  in
  let (c, d) = intersect_rowspace a b in
  assert_equal (QQMatrix.nb_rows c) 2;
  assert_equal ~printer:QQMatrix.show (QQMatrix.mul c a) (QQMatrix.mul d b)

let rowspace2 () =
  let a = mk_matrix [[1; 1; 0];
                     [1; 1; 1]]
  in
  let b = mk_matrix [[1; 0; 0];
                     [0; 1; 1]]
  in
  let rowspace = mk_matrix [[1; 1; 1]] in
  let (c, d) = intersect_rowspace a b in
  assert_equal ~printer:QQMatrix.show rowspace (QQMatrix.mul d b)

let rowspace3 () =
  let a = mk_matrix [[1; 1; 0; 0];
                     [0; 2; -1; 1]]
  in
  let b = mk_matrix [[1; 0; 2; 1];
                     [0; 1; 1; 1]]
  in
  let rowspace = mk_matrix [[]] in
  let (c, d) = intersect_rowspace a b in
  assert_equal ~printer:QQMatrix.show rowspace (QQMatrix.mul d b)

let div1 () =
  let a = mk_matrix [[4; 0; 0];
                     [0; 4; 0];
                     [0; 0; 4]]
  in
  let b = mk_matrix [[2; -1; 0];
                     [-1; 2; -1];
                     [0; -1; 2]]
  in
  match divide_right a b with
  | Some div ->
    assert_equal ~printer:QQMatrix.show a (QQMatrix.mul div b)
  | None -> assert false

let div2 () =
  let a = mk_matrix [[1; 0; 0];
                     [0; 1; 0];
                     [0; 0; 1]]
  in
  let b = mk_matrix [[2; 1; 1];
                     [1; 1; 0];
                     [1; 0; 1]]
  in
  assert_equal None (divide_right a b);
  match divide_right b a with
  | Some div ->
    assert_equal ~printer:QQMatrix.show b (QQMatrix.mul div a)
  | None -> assert false

let rational_eigenvalues1 () =
  let a = mk_matrix [[1; 2];
                     [2; 1]]
  in
  match QQMatrix.rational_eigenvalues a with
  | [(x, 1); (y, 1)] when QQ.equal x (QQ.of_int 3) ->
    assert_equal_qq y (QQ.of_int (-1))
  | [(x, 1); (y, 1)] ->
    assert_equal_qq x (QQ.of_int (-1));
    assert_equal_qq y (QQ.of_int 3);
  | _ -> assert false

let rational_eigenvalues2 () =
  let half = QQ.of_frac 1 2 in
  let third = QQ.of_frac 1 3 in
  let a = mk_qqmatrix [[half; QQ.one];
                       [QQ.zero; third]]
  in
  match QQMatrix.rational_eigenvalues a with
  | [(x, 1); (y, 1)] when QQ.equal x half ->
    assert_equal_qq y third
  | [(x, 1); (y, 1)] ->
    assert_equal_qq x third;
    assert_equal_qq y half
  | _ -> assert false

let rational_eigenvalues3 () =
  let a = mk_matrix [[0; 1; 0];
                     [0; 0; 1];
                     [8; -12; 6]]
  in
  match QQMatrix.rational_eigenvalues a with
  | [(x, m)] ->
    assert_equal_qq x (QQ.of_int 2);
    assert_equal m 3
  | _ -> assert false

let rational_eigenvalues4 () =
  let a = mk_matrix [[0; 1; 0];
                     [0; 0; 1];
                     [0; -1; 0]]
  in
  match QQMatrix.rational_eigenvalues a with
  | [(x, m)] ->
    assert_equal_qq x QQ.zero;
    assert_equal m 1
  | _ -> assert false

let nullspace1 () =
  let m = mk_matrix [[1; 2; 1];
                     [0; 1; 1];
                     [1; 3; 2]]
  in
  let basis =
    Linear.nullspace m [0; 1; 2]
  in
  assert_equal 1 (List.length basis);
  basis |> List.iter (fun x ->
      assert_equal ~printer:QQVector.show QQVector.zero (vector_right_mul m x))

let nullspace2 () =
  let m = mk_matrix [[1; 2; 1];
                     [0; 1; 1];
                     [1; 0; 2]]
  in
  assert_equal 0 (List.length (Linear.nullspace m [0; 1; 2]))

let nullspace3 () =
  let m = mk_matrix [[1; 0; 1; 1];
                     [0; 1; 0; 0];
                     [1; 1; 1; 1];
                     [-1; 1; -1; -1]]
  in
  let basis =
    Linear.nullspace m [0; 1; 2; 3]
  in
  assert_equal 2 (List.length basis);
  basis |> List.iter (fun x ->
      assert_equal ~printer:QQVector.show QQVector.zero (vector_right_mul m x))

let suite = "Linear" >::: [
    "dot" >:: dot;
    "mul" >:: mul;
    "solve1" >:: solve1;
    "solve2" >:: solve2;
    "solve3" >:: solve3;
    "solve4" >:: solve4;
    "solve5" >:: solve5;
    "rowspace1" >:: rowspace1;
    "rowspace2" >:: rowspace2;
    "rowspace3" >:: rowspace3;
    "div1" >:: div1;
    "div2" >:: div2;
    "rational_eigenvalues1" >:: rational_eigenvalues1;
    "rational_eigenvalues2" >:: rational_eigenvalues2;
    "rational_eigenvalues3" >:: rational_eigenvalues3;
    "rational_eigenvalues4" >:: rational_eigenvalues4;
    "nullspace1" >:: nullspace1;
    "nullspace2" >:: nullspace2;
    "nullspace3" >:: nullspace3;
  ]

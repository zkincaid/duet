open OUnit
open AlmostCommuting
open Linear
open Test_pervasives

let comm_space1 () =
  let eye = QQMatrix.identity [0; 1; 2] in
  let res = commuting_space eye eye in
  assert_equal_qqvectorspace (QQVectorSpace.of_matrix eye) res

let comm_space2 () =
  let eye = QQMatrix.identity [0; 1; 2] in
  let m = mk_matrix [[1; 0; 0];
                     [0; 1; 0];
                     [0; 0; 0]]
  in
  let res = commuting_space m eye in
  assert_equal_qqvectorspace (QQVectorSpace.of_matrix m) res

let suite = "AlmostCommuting" >::: [
  "comm_space1" >:: comm_space1;
  "comm_space2" >:: comm_space2
]
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

let comm_space3 () =
  let half = QQ.of_frac 1 2 in
  let mA = mk_qqmatrix [[QQ.of_int 3; QQ.zero];
                        [QQ.zero; half]]
  in
  let mB = mk_matrix [[0; 4];
                      [0; 2]]
  in
  let exp = QQVectorSpace.of_matrix (mk_matrix [[0; 1]]) in
  let res = commuting_space mA mB in
  assert_equal_qqvectorspace exp res

let comm1 () =
  let eye = QQMatrix.identity [0; 1; 2] in
  let mS, _ = commuting_segment [eye; eye] in
  assert_equal_qqmatrix eye mS

let comm2 () =
  let eye = QQMatrix.identity [0; 1; 2] in
  let m = mk_matrix [[1; 0; 0];
                     [0; 1; 0];
                     [0; 0; 0]]
  in
  let mS, _ = commuting_segment [eye; m] in
  assert_equal_qqmatrix m mS

let comm3 () =
  let half = QQ.of_frac 1 2 in
  let mA = mk_qqmatrix [[QQ.of_int 3; QQ.zero];
                        [QQ.zero; half]]
  in
  let mB = mk_matrix [[0; 4];
                      [0; 2]]
  in
  let exp = mk_matrix [[0; 1]] in
  let mS, _ = commuting_segment [mA; mB] in
  assert_equal_qqmatrix exp mS

let suite = "AlmostCommuting" >::: [
  "comm_space1" >:: comm_space1;
  "comm_space2" >:: comm_space2;
  "comm_space3" >:: comm_space3;
  "comm1" >:: comm1;
  "comm2" >:: comm2;
  "comm3" >:: comm3
]
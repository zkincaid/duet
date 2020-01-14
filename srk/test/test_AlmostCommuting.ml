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

let comm_segment1 () =
  let eye = QQMatrix.identity [0; 1; 2] in
  let mS, _ = commuting_segment [| eye; eye |] in
  assert_equal_qqmatrix eye mS

let comm_segment2 () =
  let eye = QQMatrix.identity [0; 1; 2] in
  let m = mk_matrix [[1; 0; 0];
                     [0; 1; 0];
                     [0; 0; 0]]
  in
  let mS, _ = commuting_segment [| eye; m |] in
  assert_equal_qqmatrix m mS

let comm_segment3 () =
  let half = QQ.of_frac 1 2 in
  let mA = mk_qqmatrix [[QQ.of_int 3; QQ.zero];
                        [QQ.zero; half]]
  in
  let mB = mk_matrix [[0; 4];
                      [0; 2]]
  in
  let exp = mk_matrix [[0; 1]] in
  let mS, _ = commuting_segment [| mA; mB |] in
  assert_equal_qqmatrix exp mS

let phased_segment1 () = 
  let mA = mk_matrix [[1; 0; 1];
                      [0; 1; 1];
                      [0; 0; 1]]
  in
  let mB = mk_matrix [[0; 0; 2];
                      [0; 1; 0];
                      [0; 0; 1]]
  in
  let mC = mk_matrix [[1; 0; 0];
                      [0; 0; 3];
                      [0; 0; 1]]
  in
  let input = [| (Commute, mA); (Reset, mB); (Commute, mC) |] in
  let segment = mk_phased_segment input in
  let sim1 = mk_matrix [[0; 0; 1]] in
  let m1 = mk_matrix [[1]] in
  let phase1 = [| m1; m1; m1 |] in
  let sim2 = mk_matrix [[1; 0; 0];
                        [0; 0; 1]]
  in
  let tA = mk_matrix [[1; 1]; [0; 1]] in
  let tC = mk_matrix [[1; 0]; [0; 1]] in
  let rB = mk_matrix [[2]; [1]] in
  let phase2 = [| (Commute, tA); (Reset, rB); (Commute, tC) |] in
  assert_equal_qqmatrix sim1 segment.sim1;
  assert_equal_qqmatrix sim2 segment.sim2;
  assert_equal_qqmatrix m1 (Array.get segment.phase1 0);
  assert_equal_qqmatrix m1 (Array.get segment.phase1 1);
  assert_equal_qqmatrix m1 (Array.get segment.phase1 2);
  assert_equal_qqmatrix tA (let _, m = Array.get segment.phase2 0 in m);
  assert_equal_qqmatrix rB (let _, m = Array.get segment.phase2 1 in m);
  assert_equal_qqmatrix tC (let _, m = Array.get segment.phase2 2 in m)

let phased_segment2 () = 
  let mA = mk_matrix [[1; 0; 1];
                      [0; 1; 1];
                      [0; 0; 1]]
  in
  let mB = mk_matrix [[0; 0; 2];
                      [0; 1; 0];
                      [0; 0; 1]]
  in
  let mC = mk_matrix [[1; 0; 0];
                      [0; 0; 3];
                      [0; 0; 1]]
  in
  let input = [| (Commute, mA); (Commute, mB); (Reset, mC) |] in
  let segment = mk_phased_segment input in
  let sim1 = mk_matrix [[0; 0; 1]] in
  let m1 = mk_matrix [[1]] in
  let phase1 = [| m1; m1; m1 |] in
  let sim2 = mk_matrix [[0; 1; 0];
                        [0; 0; 1]]
  in
  let tA = mk_matrix [[1; 1]; [0; 1]] in
  let tB = mk_matrix [[1; 0]; [0; 1]] in
  let rC = mk_matrix [[3]; [1]] in
  let phase2 = [| (Commute, tA); (Commute, tB); (Reset, rC) |] in
  assert_equal_qqmatrix sim1 segment.sim1;
  assert_equal_qqmatrix sim2 segment.sim2;
  assert_equal_qqmatrix m1 (Array.get segment.phase1 0);
  assert_equal_qqmatrix m1 (Array.get segment.phase1 1);
  assert_equal_qqmatrix m1 (Array.get segment.phase1 2);
  assert_equal_qqmatrix tA (let _, m = Array.get segment.phase2 0 in m);
  assert_equal_qqmatrix tB (let _, m = Array.get segment.phase2 1 in m);
  assert_equal_qqmatrix rC (let _, m = Array.get segment.phase2 2 in m)

let suite = "AlmostCommuting" >::: [
  "comm_space1" >:: comm_space1;
  "comm_space2" >:: comm_space2;
  "comm_space3" >:: comm_space3;
  "comm_segment1" >:: comm_segment1;
  "comm_segment2" >:: comm_segment2;
  "comm_segment3" >:: comm_segment3;
  "phased_segment1" >:: phased_segment1;
  "phased_segment2" >:: phased_segment2;
]
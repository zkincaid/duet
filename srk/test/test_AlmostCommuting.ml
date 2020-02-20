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
  let dims = [0; 1; 2] in
  let eye = QQMatrix.identity dims in
  let mS, _ = commuting_segment [| eye; eye |] dims in
  assert_equal_qqmatrix eye mS

let comm_segment2 () =
  let dims = [0; 1; 2] in
  let eye = QQMatrix.identity dims in
  let m = mk_matrix [[1; 0; 0];
                     [0; 1; 0];
                     [0; 0; 0]]
  in
  let mS, _ = commuting_segment [| eye; m |] dims in
  assert_equal_qqmatrix m mS

let comm_segment3 () =
  let dims = [0; 1] in
  let half = QQ.of_frac 1 2 in
  let mA = mk_qqmatrix [[QQ.of_int 3; QQ.zero];
                        [QQ.zero; half]]
  in
  let mB = mk_matrix [[0; 4];
                      [0; 2]]
  in
  let exp = mk_matrix [[0; 1]] in
  let mS, _ = commuting_segment [| mA; mB |] dims in
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
  let output = PhasedSegment.make input in
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
  let expected =
    { sim1 = sim1;
      sim2 = sim2;
      phase1 = phase1;
      phase2 = phase2 }
  in
  assert_equal_phasedsegment expected output

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
  let output = PhasedSegment.make input in
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
  let expected =
    { sim1 = sim1;
      sim2 = sim2;
      phase1 = phase1;
      phase2 = phase2 }
  in
  assert_equal_phasedsegment expected output

let phased_segment3 () = 
  let mA = mk_matrix [[1; 0; 1];
                      [0; 1; 1];
                      [0; 0; 1]]
  in
  let mB = mk_matrix [[1; 0; -1];
                      [0; 1; -1];
                      [0; 0; 1]]
  in
  let mC = mk_matrix [[0; 0; 2];
                      [0; 1; 2];
                      [0; 0; 1]]
  in
  let mD = mk_matrix [[0; 1; 0];
                      [0; 1; 0];
                      [0; 0; 1]]
  in
  let input = [| (Commute, mA); (Commute, mB); (Reset, mC); (Reset, mD) |] in
  let output = PhasedSegment.make input in
  (* Phase 1 *)
  let sim1 = mk_matrix [[0; 1; 0]; [0; 0; 1]] in
  let sA = mk_matrix [[1; 1]; [0; 1]] in
  let sB = mk_matrix [[1; -1]; [0; 1]] in
  let sC = mk_matrix [[1; 2]; [0; 1]] in
  let sD = mk_matrix [[1; 0]; [0; 1]] in
  let phase1 = [| sA; sB; sC; sD |] in
  (* Phase 2 *)
  let sim2 = mk_matrix [[1; 0; 0]; [0; 1; 0]; [0; 0; 1]] in
  let tC = mk_matrix [[0; 2]; [1; 2]; [0; 1]] in
  let tD = mk_matrix [[1; 0]; [1; 0]; [0; 1]] in
  let phase2 = [| (Commute, mA); (Commute, mB); (Reset, tC); (Reset, tD) |] in
  let expected =
    { sim1 = sim1;
      sim2 = sim2;
      phase1 = phase1;
      phase2 = phase2 }
  in
  assert_equal_phasedsegment expected output

let phased_segment4 () = 
  let mA = mk_matrix [[1; 0; 1];
                      [0; 1; 1];
                      [0; 0; 1]]
  in
  let mB = mk_matrix [[1; 0; -1];
                      [0; 1; -1];
                      [0; 0; 1]]
  in
  let mC = mk_matrix [[0; 0; 2];
                      [0; 1; 2];
                      [0; 0; 1]]
  in
  let mD = mk_matrix [[0; 1; 0];
                      [0; 1; 0];
                      [0; 0; 1]]
  in
  let input = [| (Commute, mA); (Commute, mB); (Commute, mC); (Commute, mD) |] in
  let output = PhasedSegment.make input in
  let sim1 = mk_matrix [[0; 1; 0]; [0; 0; 1]] in
  let sA = mk_matrix [[1; 1]; [0; 1]] in
  let sB = mk_matrix [[1; -1]; [0; 1]] in
  let sC = mk_matrix [[1; 2]; [0; 1]] in
  let sD = mk_matrix [[1; 0]; [0; 1]] in
  let phase1 = [| sA; sB; sC; sD |] in
  let phase2 = [| (Commute, sA); (Commute, sB); (Commute, sC); (Commute, sD) |] in
  let expected =
    { sim1 = sim1;
      sim2 = sim1;
      phase1 = phase1;
      phase2 = phase2 }
  in
  assert_equal_phasedsegment expected output

let phased_segment5 () = 
  let mA = mk_matrix [[1; 0; 1];
                      [0; 1; 1];
                      [0; 0; 1]]
  in
  let mB = mk_matrix [[1; 0; -1];
                      [0; 1; -1];
                      [0; 0; 1]]
  in
  let mC = mk_matrix [[0; 0; 2];
                      [0; 1; 2];
                      [0; 0; 1]]
  in
  let mD = mk_matrix [[0; 1; 0];
                      [0; 1; 0];
                      [0; 0; 1]]
  in
  let input = [| (Reset, mA); (Ignore, mB); (Ignore, mC); (Ignore, mD) |] in
  let output = PhasedSegment.make input in
  let sim1 = mk_matrix [[0; 1; 0]; [0; 0; 1]] in
  let sA = mk_matrix [[1; 1]; [0; 1]] in
  let sB = mk_matrix [[1; -1]; [0; 1]] in
  let sC = mk_matrix [[1; 2]; [0; 1]] in
  let sD = mk_matrix [[1; 0]; [0; 1]] in
  let phase1 = [| sA; sB; sC; sD |] in
  let phase2 = [| (Reset, sA); (Ignore, mB); (Ignore, mC); (Ignore, mD) |] in
  let expected =
    { sim1 = sim1;
      sim2 = sim1;
      phase1 = phase1;
      phase2 = phase2 }
  in
  assert_equal_phasedsegment expected output

let almost_commuting1 () = 
  let mA = mk_matrix [[1; 0; 1];
                      [0; 1; 1];
                      [0; 0; 1]]
  in
  let mB = mk_matrix [[1; 0; -1];
                      [0; 1; -1];
                      [0; 0; 1]]
  in
  let mC = mk_matrix [[0; 0; 2];
                      [0; 1; 2];
                      [0; 0; 1]]
  in
  let mD = mk_matrix [[0; 1; 0];
                      [0; 1; 0];
                      [0; 0; 1]]
  in
  let output = PhasedSegmentation.make_naive [| mA; mB; mC; mD |] in
  let dim = QQVectorSpace.dimension (PhasedSegmentation.almost_commuting_space output) in
  assert_equal 3 dim

let almost_commuting2 () = 
  let mA = mk_matrix [[1; 0; 1];
                      [0; 1; 1];
                      [0; 0; 1]]
  in
  let mB = mk_matrix [[1; 0; -1];
                      [0; 1; -1];
                      [0; 0; 1]]
  in
  let mC = mk_matrix [[0; 0; 2];
                      [0; 1; 2];
                      [0; 0; 1]]
  in
  let mD = mk_matrix [[0; 1; 0];
                      [0; 1; 0];
                      [0; 0; 1]]
  in
  let output = PhasedSegmentation.make [| mA; mB; mC; mD |] in
  let dim = QQVectorSpace.dimension (PhasedSegmentation.almost_commuting_space output) in
  assert_equal 3 dim

let suite = "AlmostCommuting" >::: [
  "comm_space1" >:: comm_space1;
  "comm_space2" >:: comm_space2;
  "comm_space3" >:: comm_space3;
  "comm_segment1" >:: comm_segment1;
  "comm_segment2" >:: comm_segment2;
  "comm_segment3" >:: comm_segment3;
  "phased_segment1" >:: phased_segment1;
  "phased_segment2" >:: phased_segment2;
  "phased_segment3" >:: phased_segment3;
  "phased_segment4" >:: phased_segment4;
  "phased_segment5" >:: phased_segment5;
  "almost_commuting1" >:: almost_commuting1;
  "almost_commuting2" >:: almost_commuting2;
]
open Test_pervasives
open Srk
open OUnit
open Linear

module PLM = Lts.PartialLinearMap

let pp_dim formatter i =
  Format.pp_print_char formatter (Char.chr (i + 65))

let assert_equal_plm x y =
  assert_equal ~cmp:PLM.equal ~printer:(SrkUtil.mk_show PLM.pp) x y

let assert_equal_lts x y =
  let eq x y = Lts.contains x y && Lts.contains y x in
  assert_equal ~cmp:eq ~printer:(SrkUtil.mk_show (Lts.pp pp_dim)) x y


let suite = "LTS" >::: [
      "plm_compose1" >:: (fun () ->
        let f =
          let m = mk_matrix [[1; 0; 1];
                             [0; 1; -1];
                             [0; 0; 2]]
          in
          let guard = [mk_vector [1; -1; 0]] in
          PLM.make m guard
        in
        let ff =
          let m = mk_matrix [[1; 0; 0];
                             [0; 1; 0];
                             [0; 0; 0]]
          in
          let guard = [mk_vector [-1; 1; 0];
                       mk_vector [0; 0; 1]]
          in
          PLM.make m guard
        in
        assert_equal_plm ff (PLM.compose f f));
      "plm_compose2" >:: (fun () ->
        let f =
          let m = mk_matrix [[0; 1; 1];
                             [1; 0; 1];
                             [-3; 3; 1]]
          in
          let guard = [mk_vector [3; -3; 0]] in
          PLM.make m guard
        in
        let ff =
          let m = mk_matrix [[1; 0; 2];
                             [0; 1; 2];
                             [0; 0; 1]]
          in
          let guard = [mk_vector [-1; 1; 0]]
          in
          PLM.make m guard
        in
        assert_equal_plm ff (PLM.compose f f));

      "determinize1" >:: (fun () ->
        let a = mk_matrix [[1; 0];
                           [0; 0]]
        in
        let b = mk_matrix [[1; 1];
                           [0; 1]]
        in
        let (dlts, sim) = Lts.determinize (a, b) in
        let sim_expected = mk_matrix [[1; 0]] in
        let dlts_expected = PLM.make (mk_matrix [[1]]) [] in
        assert_equal_qqmatrix sim_expected sim;
        assert_equal_plm dlts_expected dlts);
      "determinize2" >:: (fun () ->
        let a = mk_matrix [[1; 0];
                           [0; 1];
                           [0; 0]]
        in
        let b = mk_matrix [[1; 1];
                           [1; 0];
                           [0; 1]]
        in
        let (dlts, sim) = Lts.determinize (a, b) in
        let sim_expected = mk_matrix [[1; 0];
                                      [0; 1]]
        in
        let dlts_expected =
          PLM.make
            (mk_matrix [[1; 1];
                        [1; 0]])
            [mk_vector [0; 1]]
        in
        assert_equal_qqmatrix sim_expected sim;
        assert_equal_plm dlts_expected dlts);
      "determinize3" >:: (fun () ->
        let a = mk_matrix [[0; 1; 0];
                           [0; 0; 1];
                           [1; 0; 0]]
        in
        let b = mk_matrix [[2; 1; 0];
                           [3; 3; 1];
                           [1; 0; 0]]
        in
        let (dlts, sim) = Lts.determinize (a, b) in
        let dlts_expected =
          PLM.make
            (mk_matrix [[1; 0; 2];
                        [3; 1; 3];
                        [0; 0; 1]])
            []
        in
        let id = QQMatrix.identity [0;1;2] in
        assert_equal_lts
          (Lts.dlts_inverse_image id dlts_expected)
          (Lts.dlts_inverse_image sim dlts));
      "determinize4" >:: (fun () ->
        let a = mk_matrix [[0; 0; 0];
                           [1; 0; 0];
                           [0; 1; 0]]
        in
        let b = mk_matrix [[0; 0; 1];
                           [1; 0; 0];
                           [0; 0; 0]]
        in
        let (dlts, sim) = Lts.determinize (a, b) in
        let dlts_expected =
          PLM.make
            (mk_matrix [[1; 0];
                        [0; 0]])
            []
        in
        let sim_expected = mk_matrix [[1; 0; 0];
                                      [0; 1; 0]]
        in
        assert_equal_lts
          (Lts.dlts_inverse_image sim_expected dlts_expected)
          (Lts.dlts_inverse_image sim dlts))
    ]

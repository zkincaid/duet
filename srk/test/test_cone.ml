open Srk
open OUnit
open Test_pervasives

module QQMatrix = Linear.QQMatrix
module QQVector = Linear.QQVector

let suite = "Cone" >::: [
      "simplex" >:: (fun () ->
        let generators =
          [|
            mk_vector [1; 1; 0];
            mk_vector [-1; 0; 1];
            mk_vector [0; 1; -1];
            mk_vector [-1; -1; -1]
          |]
        in
        let generator_matrix =
          QQMatrix.transpose (QQMatrix.of_rows (Array.to_list generators))
        in
        let t1 = mk_vector [-2; -1; -3] in
        let r1 = BatOption.get (Cone.simplex generators t1) in
        assert_equal_qqvector (QQMatrix.vector_right_mul generator_matrix r1) t1;
        let t2 = mk_vector [-1; 1; -1] in
        let r2 = BatOption.get (Cone.simplex generators t2) in
        assert_equal_qqvector (QQMatrix.vector_right_mul generator_matrix r2) t2;
        assert_equal (Cone.simplex generators (mk_vector [0; -1; 0])) None);

      "simplex2" >:: (fun () ->
        let generators =
          [|
            mk_vector [1; 0; 1];
            mk_vector [1; 0; 2];
            mk_vector [2; 0; 1]
          |]
        in
        let generator_matrix =
          QQMatrix.transpose (QQMatrix.of_rows (Array.to_list generators))
        in
        let t1 = mk_vector [5; 0; 4] in
        let r1 = BatOption.get (Cone.simplex generators t1) in
        assert_equal_qqvector (QQMatrix.vector_right_mul generator_matrix r1) t1;
        let t2 = mk_vector [5; 0; 7] in
        let r2 = BatOption.get (Cone.simplex generators t2) in
        assert_equal_qqvector (QQMatrix.vector_right_mul generator_matrix r2) t2;
        assert_equal (Cone.simplex generators (mk_vector [0; 1; 0])) None;
        assert_equal (Cone.simplex generators (mk_vector [1; 0; 0])) None);

      "simplex_zero_generators" >:: (fun () ->
          let generators = [| |] in
          assert_equal (Cone.simplex generators (mk_vector [])) (Some QQVector.zero);
          assert_equal (Cone.simplex generators (mk_vector [1])) None);

      "simplex_zero_dim" >:: (fun () ->
        let generators = [| QQVector.zero |] in
        assert_equal (Cone.simplex generators (mk_vector [])) (Some QQVector.zero);
        assert_equal (Cone.simplex generators (mk_vector [1])) None);

    ]

open Srk
open OUnit
open BatPervasives
open Test_pervasives

module V = Linear.QQVector

let mk_polyhedron halfspaces =
  BatList.enum halfspaces
  /@ (fun (v, a) -> (`Nonneg,
                    (V.add_term (QQ.of_int (-a)) Linear.const_dim (mk_vector v))))
  |> Polyhedron.of_constraints


let mk_polyhedron_generators dim vertices rays =
  (List.map (fun v -> (`Vertex, mk_vector v)) vertices)
  @(List.map (fun v -> (`Ray, mk_vector v)) rays)
  |> BatList.enum
  |> Polyhedron.DD.of_generators dim
  |> Polyhedron.DD.of_dd
  

let assert_equal_polyhedron p q =
  assert_equal ~cmp:Polyhedron.equal p q

let suite = "Polyhedron" >::: [
      "equal1" >:: (fun () ->
        let p =
          mk_polyhedron [([1; 0; 0], 42);
                         ([-1; 0; 1], 0);
                         ([-2; 0; 2], -10);
                         ([1; 0; -1], 0)]
        in
        let q =
          mk_polyhedron [([0; 0; 1], 42);
                         ([-8; 0; 8], 0);
                         ([2; 0; -2], 0)]
        in
        assert_equal_polyhedron p q);

      "disequal1" >:: (fun () ->
        let p =
          mk_polyhedron [([1; 0; 1], 12);
                         ([0; 1; 0], 2)]
        in
        let q =
          mk_polyhedron [([1; 0; 1], 12);
                         ([1; 1; 0], 2)]
        in
        assert_bool "Disequal constraint space" (not (Polyhedron.equal p q)));
            
      "disequal2" >:: (fun () ->
        let p =
          mk_polyhedron [([1; 0; -1], 0);
                         ([-1; 0; 1], 0);
                         ([0; 1; 0], 1)]
        in
        let q =
          mk_polyhedron [([-1; 0; 1], 0);
                         ([1; 0; -1], 0);
                         ([1; 1; 0], 1)]
        in
        assert_bool "Disequal constraints" (not (Polyhedron.equal p q)));

      "conical_hull_cone" >:: (fun () ->
        let polyhedron =
          mk_polyhedron [([1; 0; 0], 0);
                         ([0; 0; 1], 0)]
        in
        let cone = Polyhedron.conical_hull polyhedron in
        assert_equal_polyhedron polyhedron cone
      );
      "conical_hull" >:: (fun () ->
        let polyhedron =
          mk_polyhedron [([1; 0; 0], -1);
                         ([0; 1; 0], 0);
                         ([0; 0; 1], 1)]
        in
        let cone = Polyhedron.conical_hull polyhedron in
        let ch =
          mk_polyhedron [([1; 0; 1], 0);
                         ([0; 1; 0], 0);
                         ([0; 0; 1], 0)]
        in
        assert_equal_polyhedron ch cone
      );
      "conical_hull_eq" >:: (fun () ->
        let polyhedron =
          mk_polyhedron [([1; -1; 0], 0);
                         ([-1; 1; 0], 0);
                         ([0; 0; 1], 1)]
        in
        let cone = Polyhedron.conical_hull polyhedron in
        let ch =
          mk_polyhedron [([1; -1; 0], 0);
                         ([-1; 1; 0], 0);
                         ([0; 0; 1], 0)]
        in
        assert_equal_polyhedron ch cone
      );
      "conical_hull_triv" >:: (fun () ->
        let polyhedron =
          mk_polyhedron [([1; 1; 0], -1);
                         ([-1; 0; 0], -1);
                         ([0; 0; 1], -1)]
        in
        let cone = Polyhedron.conical_hull polyhedron in
        let ch = mk_polyhedron [] in
        assert_equal_polyhedron ch cone
      );
      "dual_cone_inconsistent" >:: (fun () ->
        let polyhedron =
          mk_polyhedron [([1], 1);
                         ([-1], 1)]
        in
        let dual_cone = Polyhedron.dual_cone 1 polyhedron in
        assert_equal_polyhedron (mk_polyhedron []) dual_cone
      );
      "dual_cone_trivial" >:: (fun () ->
        let dual_cone = Polyhedron.dual_cone 2 (mk_polyhedron []) in
        let zero =
          mk_polyhedron [([1; 0], 0); ([-1; 0], 0);
                         ([0; 1], 0); ([0; -1], 0)]
        in
        assert_equal_polyhedron zero dual_cone
      );

      "conical_hull_inconsistent" >:: (fun () ->
        let polyhedron =
          mk_polyhedron [([1], 1);
                         ([-1], 1)]
        in
        let cone = Polyhedron.conical_hull polyhedron in
        let ch = mk_polyhedron [([1], 0); ([-1], 0)] in
        assert_equal_polyhedron ch cone
      );
      "generator1" >:: (fun () ->
        let p =
          mk_polyhedron [([1; 0; 0], 0);
                         ([0; 0; 1], 0)]
        in
        let q =
          mk_polyhedron_generators 3
            [[0; 0; 0]]
            [[1; 0; 0];
             [0; 1; 0];
             [0; -1; 0];
             [0; 0; 1]]
        in
        assert_equal_polyhedron p q);
      "generator2" >:: (fun () ->
        let p =
          mk_polyhedron [([1; -1; 0], 0);
                         ([-1; 1; 0], 0);
                         ([0; 1; 0], -1);
                         ([0; 0; 1], 42)]
        in
        let q =
          mk_polyhedron_generators 3
            [[-1; -1; 42]]
            [[1; 1; 0];
             [0; 0; 1]]
        in
        assert_equal_polyhedron p q);
      "generator3" >:: (fun () ->
        let p =
          mk_polyhedron [([1; 0], 1);
                         ([-1; 0], -2);
                         ([0; 1], 3);
                         ([0; -1], -4)]
        in
        let q =
          mk_polyhedron_generators 2
            [[1; 3];
             [1; 4];
             [2; 3];
             [2; 4]]
            []
        in
        assert_equal_polyhedron p q)
  ]

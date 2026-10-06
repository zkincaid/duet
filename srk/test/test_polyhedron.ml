open Srk
open OUnit
open BatPervasives
open Test_pervasives

module V = Linear.QQVector

let qqify v = List.map (fun (a, b) -> QQ.of_frac a b) v

let test_vertical_integer_hull k () =
  (*
       x >= 0
       x + ky <= k
       x - ky <= 0
   *)
  let p = mk_polyhedron [ ([1; 0], 0)
                        ; ([-1; -k], -k)
                        ; ([-1; k], 0) ] in
  let hull_gc = Polyhedron.integer_hull `GomoryChvatal p in
  let hull_normaliz = Polyhedron.integer_hull `Normaliz p in
  let expected_hull = mk_polyhedron [ ([1; 0], 0)
                                    ; ([-1; 0], 0)
                                    ; ([0; 1], 0)
                                    ; ([0; -1], -1) ] in
  assert_equal ~cmp:Polyhedron.equal hull_gc expected_hull;
  assert_equal ~cmp:Polyhedron.equal hull_normaliz expected_hull

let test_translated_parallelogram height () =
  let p = mk_polyhedron_from_generators mk_qqvector 2
            (List.map qqify [ [(1, 2); (0, 1)]
                            ; [(3, 2); (0, 1)]
                            ; [(3, 2); (height, 1)]
                            ; [(5, 2); (height, 1)] ])
            []
  in
  let hull_gc = Polyhedron.integer_hull `GomoryChvatal p in
  let hull_normaliz = Polyhedron.integer_hull `Normaliz p in
  let expected_hull =
    mk_polyhedron_from_generators mk_vector 2
      [ [1; 0]; [1; height/2]; [2; height - (height/2)]; [2; height] ] []
  in
  assert_equal ~cmp:Polyhedron.equal hull_gc expected_hull;
  assert_equal ~cmp:Polyhedron.equal hull_normaliz expected_hull

let test_halfspace () =
  let p = mk_polyhedron [ ([2 ; 0], 3) ] in
  let hull_gc = Polyhedron.integer_hull `GomoryChvatal p in
  let hull_normaliz = Polyhedron.integer_hull `Normaliz p in
  let expected_hull = mk_polyhedron [ ([1 ; 0], 2) ] in
  assert_equal ~cmp:Polyhedron.equal hull_gc expected_hull;
  assert_equal ~cmp:Polyhedron.equal hull_normaliz expected_hull

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
          mk_polyhedron_from_generators mk_vector 3
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
          mk_polyhedron_from_generators mk_vector 3
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
          mk_polyhedron_from_generators mk_vector 2
            [[1; 3];
             [1; 4];
             [2; 3];
             [2; 4]]
            []
        in
        assert_equal_polyhedron p q);

    "integer_hull_1" >:: test_vertical_integer_hull 3;
    "integer_hull_2" >:: test_translated_parallelogram 3;
    "integer_hull_3" >:: test_halfspace;
    "closed_dd" >:: (fun () ->
        let to_vec (v, a) =
          V.add_term (QQ.of_int (-a)) Linear.const_dim (mk_vector v)
        in
        let q =
          BatList.enum [([1; 0], 1);
                        ([0; 1], 0)]
          /@ (fun h -> (`Pos, to_vec h))
          |> DD.of_constraints_closed 2
        in
        let q' =
          BatList.enum [([1; 0], 1);
                        ([0; 1], 0)]
          /@ (fun h -> (`Nonneg, to_vec h))
          |> DD.of_constraints_closed 2
        in
        assert_equal_dd q' q)

    ; "close_integer_point1" >:: (fun () ->
        let p =
          mk_polyhedron [([1; 0], 0);
                         ([0; 1], 0);
                         ([-1; 2], -30);
                         ([2; -1], -50)]
        in
        let rational = V.scalar_mul (QQ.of_frac 1 16) (mk_vector [0; 1]) in
        let integer = mk_vector [19; 26] in
        let integer' = Polyhedron.close_integral_point p ~rational ~integer 2 in
        assert_bool "integral" (V.is_integral integer');
        assert_bool "membership" (Polyhedron.mem (fun i -> V.coeff i integer') p))

    ; "close_integer_point2" >:: (fun () ->
        let p =
          mk_polyhedron [([-1; 1; 0; 0], 0);
                         ([0; -1; 1; 0], 0);
                         ([0; 0; -1; 1], 0);
                         ([1; 0; 0; -1], -50);
                         ([0; 1; 0; -1], -50);
                         ([0; 0; 0; -1], -50);
                         ([-1; 1; -1; 1], -10);
                         ([1; -1; 1; -1], -10)
                        ]
        in
        let rational = V.scalar_mul (QQ.of_frac 1 5) (mk_vector [1; 15; 17; 35]) in
        let integer = mk_vector [1; 2; 3; 4] in
        let integer' = Polyhedron.close_integral_point p ~rational ~integer 4 in
        assert_bool "integral" (V.is_integral integer');
        assert_bool "membership" (Polyhedron.mem (fun i -> V.coeff i integer') p))

    ; "close_integer_point3" >:: (fun () ->
        (* High-dimensional stress test *)
        let n = 1000 in
        let p =
          BatEnum.fold
            (fun constraints i ->
               (`Nonneg,
                V.add_term
                  (QQ.of_int n)
                  Linear.const_dim
                  (V.of_term QQ.one i))
               ::(`Nonneg,
                  V.add_term
                    (QQ.of_int n)
                    Linear.const_dim
                    (V.of_term (QQ.of_int (-1)) i))
               ::constraints)
            []
            (0--(n-1))
          |> BatList.enum
          |> Polyhedron.of_constraints
        in
        let rational =
          V.add
            (V.scalar_mul (QQ.of_frac 1 4)
               (mk_vector (BatList.of_enum (((0 -- (n-1))
                                             /@ (fun i -> i mod 11))))))
            (V.scalar_mul (QQ.of_frac 1 3)
               (mk_vector (BatList.of_enum (((0 -- (n-1))
                                             /@ (fun i -> (i mod 5) - 2))))))
        in
        let integer =
          mk_vector (BatList.of_enum ((0 -- (n-1)) /@ (fun i -> i - n/2)))
        in
        let integer' = Polyhedron.close_integral_point p ~rational ~integer n in
        assert_bool "integral" (V.is_integral integer');
        assert_bool "membership" (Polyhedron.mem (fun i -> V.coeff i integer') p))

    ; "find_point" >:: (fun () ->
        let check p =
          match Polyhedron.find_point p with
          | Some x -> assert_bool "membership" (Polyhedron.mem (fun i -> V.coeff i x) p)
          | None -> assert_failure "expected a point"
        in
        let strict cs =
          BatList.enum cs
          /@ (fun (kind, v, a) ->
              (kind, V.add_term (QQ.of_int (-a)) Linear.const_dim (mk_vector v)))
          |> Polyhedron.of_constraints
        in
        (* bounded *)
        check (mk_polyhedron [([1; 0], 0); ([0; 1], 0); ([-1; -1], -2)]);
        (* strict: 0 < x < 1, y > x *)
        check (strict [(`Pos, [1; 0], 0); (`Pos, [-1; 0], -1); (`Pos, [-1; 1], 0)]);
        (* equality, unbounded: x + y = 3, x >= 5 *)
        check (strict [(`Zero, [1; 1], 3); (`Nonneg, [1; 0], 5)]);
        check Polyhedron.top;
        (* determined by equalities: x + y = 3, x - y = 1, x > 1 *)
        check (strict [(`Zero, [1; 1], 3); (`Zero, [1; -1], 1); (`Pos, [1; 0], 1)]);
        (* inconsistent equalities: x + y = 3, 2x + 2y = 5 *)
        assert_equal None
          (Polyhedron.find_point (strict [(`Zero, [1; 1], 3); (`Zero, [2; 2], 5)]));
        (* infeasible: x >= 1, x < 1 *)
        assert_equal None
          (Polyhedron.find_point (strict [(`Nonneg, [1], 1); (`Pos, [-1], -1)])))

    ; "close_lattice_point_long_cone" >:: (fun () ->
        (* 10k >= 1, i >= 0, 1000000k - i >= 1: the cone at r is generated by
           (1,0) and (1,1000000), so the closest point to r obtained from
           the decomposition of z - r is z itself *)
        let p =
          mk_polyhedron [([10; 0], 1);
                         ([0; 1], 0);
                         ([1000000; -1], 1)]
        in
        let rational = V.of_list [(QQ.of_frac 1 10, 0)] in
        let integer = mk_vector [1; 899998] in
        let covectors = [V.of_term QQ.one 0; V.of_term QQ.one 1] in
        let p' =
          Polyhedron.close_lattice_point covectors p ~rational ~integer 2
        in
        assert_equal ~cmp:V.equal ~printer:V.show (mk_vector [1; 0]) p')

    ; "close_lattice_point_facet" >:: (fun () ->
        (* 1 <= i + k <= 2, i >= 1, k <= -1/10, i <= 999999; the rational
           point lies on the facet i + k = 2, and so should the result *)
        let p =
          mk_polyhedron [([1; 1], 1);
                         ([-1; -1], -2);
                         ([0; 1], 1);
                         ([-10; 0], 1);
                         ([0; -1], -999999)]
        in
        let rational = V.of_list [(QQ.of_frac (-1) 10, 0); (QQ.of_frac 21 10, 1)] in
        let integer = mk_vector [-999517; 999519] in
        let covectors = [V.of_term QQ.one 0; V.of_term QQ.one 1] in
        let p' =
          Polyhedron.close_lattice_point covectors p ~rational ~integer 2
        in
        assert_equal ~cmp:V.equal ~printer:V.show (mk_vector [-1; 3]) p')

    ; "close_lattice_point_simplex" >:: (fun () ->
        (* x >= 0, y >= 0, x + y <= 2, only x is integral.  Rounding x from
           r = (1/2, 7/5) towards z = (2, 0) gives x = 1, but (1, 7/5) is not
           in p, so y must be adjusted. *)
        let p =
          mk_polyhedron [([1; 0], 0);
                         ([0; 1], 0);
                         ([-1; -1], -2)]
        in
        let rational = V.of_list [(QQ.of_frac 1 2, 0); (QQ.of_frac 7 5, 1)] in
        let integer = mk_vector [2; 0] in
        let covectors = [V.of_term QQ.one 0] in
        let p' =
          Polyhedron.close_lattice_point covectors p ~rational ~integer 2
        in
        assert_bool "membership" (Polyhedron.mem (fun i -> V.coeff i p') p);
        assert_equal ~printer:QQ.show QQ.one (V.coeff 0 p'))
  ]


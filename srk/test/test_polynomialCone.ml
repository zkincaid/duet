open Srk
open OUnit
open Polynomial
open PolynomialCone
open Test_pervasives

let mk_qqx vec =
  List.fold_left
    (fun vec (i, k) -> QQX.add_term k i vec)
    QQX.zero
    (List.mapi (fun i k -> (i, QQ.of_int k)) vec)

let pp_dim formatter i =
    Format.pp_print_string formatter (Char.escaped (Char.chr i))

module QQXsInfix = struct
  let ( + ) = QQXs.add
  let ( - ) = QQXs.sub
  let ( * ) = QQXs.mul
  let ( ~- ) = QQXs.negate
  let int k = QQXs.scalar (QQ.of_int k)
  let dim k = QQXs.of_dim (Char.code k)
end

let assert_equal_qqx p q =
  assert_equal ~cmp:QQX.equal ~printer:QQX.show p q

let assert_equal_qqxs p q =
  let show = SrkUtil.mk_show (QQXs.pp pp_dim) in
  assert_equal ~printer:show ~cmp:QQXs.equal p q

let assert_equal_ideal p q =
  let show = SrkUtil.mk_show (Ideal.pp pp_dim) in
  assert_equal ~printer:show ~cmp:Ideal.equal p q

let assert_equal_pc p q =
  let show = SrkUtil.mk_show (PolynomialCone.pp pp_dim) in
  assert_equal ~printer:show ~cmp:PolynomialCone.equal p q

let test_make_enclosing1 () =
  let open QQXsInfix in
  let x = dim 'x' in
  let y = dim 'y' in
  let z = dim 'z' in
  let basis =
    Rewrite.mk_rewrite Monomial.degrevlex [
      x;
    ]
  in
  let geq_zero_polys =
    [x - y;
     y - x;
     z - y;]
  in
  let pc = regularize basis geq_zero_polys in
  let q = regularize
      (Rewrite.mk_rewrite Monomial.degrevlex [y; x])
      [(int 1) ; z]
  in
  assert_equal_pc q pc

let test_make_enclosing2 () =
  let open QQXsInfix in
  let x = dim 'x' in
  let y = dim 'y' in
  let z = dim 'z' in
  let basis =
    Rewrite.mk_rewrite Monomial.degrevlex [
      x;
    ]
  in
  let geq_zero_polys =
    [x - y * y;
     y * y - x;
     y * y - z * z * z;
     z * z * z - y * y;]
  in
  let pc = regularize basis geq_zero_polys in
  let q = regularize
      (Rewrite.mk_rewrite Monomial.degrevlex [y * y; z * z * z; x])
      [(int 1)]
  in
  assert_equal_pc q pc

let test_make_enclosing3 () =
  let open QQXsInfix in
  let x = dim 'x' in
  let y = dim 'y' in
  let z = dim 'z' in
  let basis =
    Rewrite.mk_rewrite Monomial.degrevlex [
      x;
    ]
  in
  let geq_zero_polys =
    [x - y;
     y - z;
     z - x;]
  in
  let pc = regularize basis geq_zero_polys in
  let q = regularize
      (Rewrite.mk_rewrite Monomial.degrevlex [x; y; z])
      [(int 1)]
  in
  assert_equal_pc q pc


let test_proj1 () =
  let open QQXsInfix in
  let x = dim 'x' in
  let y = dim 'y' in
  let z = dim 'z' in
  let basis =
    Rewrite.mk_rewrite Monomial.degrevlex [
      x;
    ]
  in
  let geq_zero_polys =
    [x - y;
     y - x;
     z - y;]
  in
  let pc = regularize basis geq_zero_polys in
  let pc = project pc (fun d -> d != Char.code 'y') in
  let q = regularize
      (Rewrite.mk_rewrite Monomial.degrevlex [x])
      [(int 1) ; z]
  in
  assert_equal_pc q pc

let test_proj2 () =
  let open QQXsInfix in
  let x = dim 'x' in
  let y = dim 'y' in
  let z = dim 'z' in
  let basis =
    Rewrite.mk_rewrite Monomial.degrevlex [
      x;
    ]
  in
  let geq_zero_polys =
    [y - x * y;
     z - y;]
  in
  let pc = regularize basis geq_zero_polys in
  let pc = project pc (fun d -> d != Char.code 'y') in
  let q = regularize
      (Rewrite.mk_rewrite Monomial.degrevlex [x])
      [(int 1) ; z]
  in
  assert_equal_pc q pc

let test_proj3 () =
  let open QQXsInfix in
  let x = dim 'x' in
  let y = dim 'y' in
  let z = dim 'z' in
  let basis =
    Rewrite.mk_rewrite Monomial.degrevlex [
      x * x
    ]
  in
  let geq_zero_polys =
    [y - x * y;
     z - y;]
  in
  let pc = regularize basis geq_zero_polys in
  let pc = project pc (fun d -> d != Char.code 'y') in
  let q = regularize
      (Rewrite.mk_rewrite Monomial.degrevlex [x * x])
      [(int 1)]
  in
  assert_equal_pc q pc

let test_intersec1 () =
  let open QQXsInfix in
  let x = dim 'x' in
  let y = dim 'y' in
  let z = dim 'z' in
  let x_zero = Rewrite.mk_rewrite Monomial.degrevlex [x] in
  let geq_polys1 =
    [x - y;
     z - y;]
  in
  let geq_polys2 = [y - x] in
  let pc1 = regularize x_zero geq_polys1 in
  let pc2 = regularize x_zero geq_polys2 in
  let pc = intersection pc1 pc2 in
  let q = regularize (x_zero) [] in
  assert_equal_pc q pc

let test_intersec2 () =
  let open QQXsInfix in
  let x = dim 'x' in
  let y = dim 'y' in
  let basis1 =
    Rewrite.mk_rewrite Monomial.degrevlex [
      x;
    ]
  in
  let geq_polys1 =
    [y - int 1;
    ]
  in
  let basis2 =
    Rewrite.mk_rewrite Monomial.degrevlex [
      y - int 1;
    ]
  in
  let geq_polys2 =
    [x - y;]
  in

  let pc1 = regularize basis1 geq_polys1 in
  let pc2 = regularize basis2 geq_polys2 in
  let pc = intersection pc1 pc2 in
  let q = regularize
      (Rewrite.mk_rewrite Monomial.degrevlex [x * y - x])
      [int 1; x; y - int 1 ]
  in
  assert_equal_pc q pc

let test_intersec3 () =
  let open QQXsInfix in
  let x = dim 'x' in
  let y = dim 'y' in
  let basis1 =
    Rewrite.mk_rewrite Monomial.degrevlex [
      x;
    ]
  in
  let geq_polys1 =
    [y - int 1;
    ]
  in
  let basis2 =
    Rewrite.mk_rewrite Monomial.degrevlex [
    ]
  in
  let geq_polys2 =
    [int 0 - int 1]
  in

  let pc1 = regularize basis1 geq_polys1 in
  let pc2 = regularize basis2 geq_polys2 in
  let pc = intersection pc1 pc2 in
  let q = regularize
      (Rewrite.mk_rewrite Monomial.degrevlex [x ])
      [int 1; y - int 1 ]
  in
  assert_equal_pc q pc

let test_intersec4 () =
  let open QQXsInfix in
  let x = dim 'x' in
  let basis1 =
    Rewrite.mk_rewrite Monomial.degrevlex [
      x;
    ]
  in
  let geq_polys1 =
    [
    ]
  in
  let basis2 =
    Rewrite.mk_rewrite Monomial.degrevlex [
      x - int 1
    ]
  in
  let geq_polys2 =
    []
  in

  let pc1 = regularize basis1 geq_polys1 in
  let pc2 = regularize basis2 geq_polys2 in
  let pc = intersection pc1 pc2 in
  let q = regularize
      (Rewrite.mk_rewrite Monomial.degrevlex [ x - x * x ])
      [x;  int 1 - x ]
  in
  assert_equal_pc q pc

let test_proper1 () =
  let open QQXsInfix in
  let x = dim 'x' in
  let y = dim 'y' in
  let basis =
    Rewrite.mk_rewrite Monomial.degrevlex [
      x;
    ]
  in
  let geq_polys =
    [y - int 1;
    ]
  in
  let pc = regularize basis geq_polys in
  assert_bool "should be proper" (is_proper pc)

let test_proper2 () =
  let open QQXsInfix in
  let x = dim 'x' in
  let y = dim 'y' in
  let basis =
    Rewrite.mk_rewrite Monomial.degrevlex [
      x;
    ]
  in
  let geq_polys =
    [x * y - int 1;
    ]
  in
  let pc = regularize basis geq_polys in
  assert_bool "should be non proper" (not (is_proper pc))

let test_mem () =
  let open QQXsInfix in
  let x = dim 'x' in
  let y = dim 'y' in
  let b =
    Rewrite.mk_rewrite Monomial.degrevlex [x] in
  let pc = regularize b [] in
  assert_bool "xy should be in the cone" (mem (x * y) pc)

let test_top () =
  let open QQXsInfix in
  let b =
    Rewrite.mk_rewrite Monomial.degrevlex [] in
  let pc = regularize b [int 1; int 0 - int 1] in
  assert_equal_pc pc top;
  assert_bool "top should be non proper" (not (is_proper top))

module PV = Polynomial.LinearQQXs

let test_inverse_hom () =
  let open QQXsInfix in
  let x1, x2  = QQXs.of_dim 1, QQXs.of_dim 2 in
  let y1, y2, y3 = QQXs.of_dim 3, QQXs.of_dim 4, QQXs.of_dim 5 in
  let ideal = Rewrite.mk_rewrite Monomial.degrevlex in
  let cone = regularize (ideal [x1 ; x2 * x2]) [-x2] in
  let inverse_image = inverse_homomorphism cone [ (3, x1 * x2 * x2)
                                                ; (4, x1 * x1)
                                                ; (5, x2) ] in
  let expected = regularize (ideal [y1 ; y2 ; y3 * y3])
                   [QQXs.one; -QQXs.of_dim 5] in
  assert_equal (equal inverse_image expected) true

let test_inverse_linear1 () =
  let open QQXsInfix in
  let x1, x2  = QQXs.of_dim 1, QQXs.of_dim 2 in
  let ideal = Rewrite.mk_rewrite Monomial.degrevlex in
  let cone = regularize (ideal [x1]) [-x2] in
  let (lines, rays) = inverse_linear_map cone [(3, x1 * x1); (4, x2)] in
  let mono dim = Monomial.singleton dim 1 in
  let context = PV.make_context [ mono 3 ; mono 4 ] in
  let conv = List.map (PV.densify_affine context) in
  let (lines, rays) = ( conv lines, conv rays ) in
  let inverse_image = Cone.make ~lines ~rays 2 in
  let expected = Cone.make ~lines:(conv [QQXs.of_dim 3])
                   ~rays:(conv [ QQXs.one; -QQXs.of_dim 4]) 2 in
  assert_equal (Cone.equal inverse_image expected) true

let test_inverse_linear2 () =
  let open QQXsInfix in
  let x1, x2  = QQXs.of_dim 1, QQXs.of_dim 2 in
  let ideal = Rewrite.mk_rewrite Monomial.degrevlex in
  let cone = regularize (ideal [x1]) [-x2] in
  let (lines, rays) = inverse_linear_map cone [ (3, x1 * x1)
                                              ; (4, x1 * x1 * x1) ; (5 , x1 * x1 * x1)
                                              ; (6, x2) ; (7, x1 - x2) ] in
  let mono dim = Monomial.singleton dim 1 in
  let context = PV.make_context [ mono 3; mono 4; mono 5; mono 6; mono 7] in
  let conv = List.map (PV.densify_affine context) in
  let (lines, rays) = ( conv lines, conv rays ) in
  let inverse_image = Cone.make ~lines ~rays 5 in
  let expected = Cone.make
                   ~lines:(conv [QQXs.of_dim 3; QQXs.of_dim 4; QQXs.of_dim 5;
                                 QQXs.of_dim 6 + QQXs.of_dim 7])
                   ~rays:(conv [ QQXs.one; -QQXs.of_dim 6]) 5 in
  assert_equal (Cone.equal inverse_image expected) true

let suite = "PolynomialCone" >::: [
    "test_make_enclosing1" >:: test_make_enclosing1;
    "test_make_enclosing2" >:: test_make_enclosing2;
    "test_make_enclosing3" >:: test_make_enclosing3;
    "test_proj1" >:: test_proj1;
    "test_proj2" >:: test_proj2;
    "test_proj3" >:: test_proj3;
    "test_intersec1" >:: test_intersec1;
    "test_intersec2" >:: test_intersec2;
    "test_intersec3" >:: test_intersec3;
    "test_intersec4" >:: test_intersec4;
    "test_proper1" >:: test_proper1;
    "test_proper2" >:: test_proper2;
    "test_mem" >:: test_mem;
    "test_top" >:: test_top;
    "test_inverse_hom" >:: test_inverse_hom;
    "test_inverse_linear1" >:: test_inverse_linear1;
    "test_inverse_linear2" >:: test_inverse_linear2

    ; "sat1" >:: (fun () ->
        let phi =
          let open Infix in
          (int 0) <= x && (int 0) <= y && !((int 0) <= x + y)
        in
        assert_equal (LirrSolver.is_sat srk phi) `Unsat)

    ; "sat2" >:: (fun () ->
        let phi =
          let open Infix in
          (int 0) <= x && (int 0) <= y && !(x + y <= (int 0))
        in
        assert_equal (LirrSolver.is_sat srk phi) `Sat)

    ; "lattice_unsat" >:: (fun () ->
        let phi =
          let open Infix in
          let open Syntax in
          (mk_is_int srk (q + r))
          && (mk_is_int srk (s - r))
          && !(mk_is_int srk ((int 2) * q + (int 2) * r))
        in
        assert_equal (LirrSolver.is_sat srk phi) `Unsat)

    ; "lattice_sat" >:: (fun () ->
        let phi =
          let open Infix in
          let open Syntax in
          (mk_is_int srk ((int 2) * q + r))
          && (mk_is_int srk r)
          && !(mk_is_int srk (r * r))
          && !(mk_is_int srk q)
        in
        assert_equal (LirrSolver.is_sat srk phi) `Sat)

    ; "cutting_plane" >:: (fun () ->
        let phi =
          let open Infix in
          let open Syntax in
          mk_is_int srk (q / (int 2))
          && (int 0) <= q
          && q <= (int 1)
          && !(q <= (int 0))
        in
        assert_equal (LirrSolver.is_sat srk phi) `Unsat)
  ]

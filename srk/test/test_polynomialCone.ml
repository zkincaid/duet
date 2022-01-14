open Srk
open OUnit
open Polynomial
open PolynomialCone

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
  let pc = make_enclosing_cone basis geq_zero_polys in
  let q = make_enclosing_cone
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
  let pc = make_enclosing_cone basis geq_zero_polys in
  let q = make_enclosing_cone
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
  let pc = make_enclosing_cone basis geq_zero_polys in
  let q = make_enclosing_cone
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
  let pc = make_enclosing_cone basis geq_zero_polys in
  let pc = project pc (fun d -> d != Char.code 'y') in
  let q = make_enclosing_cone
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
  let pc = make_enclosing_cone basis geq_zero_polys in
  let pc = project pc (fun d -> d != Char.code 'y') in
  let q = make_enclosing_cone
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
  let pc = make_enclosing_cone basis geq_zero_polys in
  let pc = project pc (fun d -> d != Char.code 'y') in
  let q = make_enclosing_cone
      (Rewrite.mk_rewrite Monomial.degrevlex [x * x])
      [(int 1)]
  in
  assert_equal_pc q pc

let test_intersec1 () =
  let open QQXsInfix in
  let x = dim 'x' in
  let y = dim 'y' in
  let z = dim 'z' in
  let basis1 =
    Rewrite.mk_rewrite Monomial.degrevlex [
      x;
    ]
  in
  let geq_polys1 =
    [x - y;
     z - y;]
  in
  let basis2 =
    Rewrite.mk_rewrite Monomial.degrevlex [
      x
    ]
  in
  let geq_polys2 =
    [y - x;]
  in

  let pc1 = make_enclosing_cone basis1 geq_polys1 in
  let pc2 = make_enclosing_cone basis2 geq_polys2 in
  let pc = intersection pc1 pc2 in
  let q = make_enclosing_cone
      (Rewrite.mk_rewrite Monomial.degrevlex [x])
      [(int 1) ]
  in
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

  let pc1 = make_enclosing_cone basis1 geq_polys1 in
  let pc2 = make_enclosing_cone basis2 geq_polys2 in
  let pc = intersection pc1 pc2 in
  let q = make_enclosing_cone
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

  let pc1 = make_enclosing_cone basis1 geq_polys1 in
  let pc2 = make_enclosing_cone basis2 geq_polys2 in
  let pc = intersection pc1 pc2 in
  let q = make_enclosing_cone
      (Rewrite.mk_rewrite Monomial.degrevlex [x ])
      [int 1; y - int 1 ]
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
  let pc = make_enclosing_cone basis geq_polys in
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
  let pc = make_enclosing_cone basis geq_polys in
  assert_bool "should be non proper" (not (is_proper pc))

let test_mem () =
  let open QQXsInfix in
  let x = dim 'x' in
  let y = dim 'y' in
  let b =
    Rewrite.mk_rewrite Monomial.degrevlex [x] in
  let pc = make_enclosing_cone b [] in
  assert_bool "xy should be in the cone" (mem (x * y) pc)

let test_trivial () =
   let open QQXsInfix in
  let b =
    Rewrite.mk_rewrite Monomial.degrevlex [] in
  let pc = make_enclosing_cone b [int 1; int 0 - int 1] in
   assert_equal_pc pc trivial;
   assert_bool "trivial should be non proper" (not (is_proper trivial))



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
    "test_proper1" >:: test_proper1;
    "test_proper2" >:: test_proper2;
    "test_mem" >:: test_mem;
    "test_trivial" >:: test_trivial
  ]

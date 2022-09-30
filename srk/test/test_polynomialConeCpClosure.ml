open Srk
open OUnit
open Polynomial
open PolynomialConeCpClosure

module Infix = struct
  let int k = QQXs.scalar (QQ.of_int k)
  let ( * ) = QQXs.mul
  let ( + ) = QQXs.add
  let ( ~- ) = QQXs.negate
  let ( - ) = QQXs.sub
  let ( / ) a b = QQXs.scalar (QQ.of_frac a b)
end

let x = QQXs.of_dim 1
let y = QQXs.of_dim 2
let z = QQXs.of_dim 3

let ideal = Rewrite.mk_rewrite Monomial.degrevlex
let empty_cone = PolynomialCone.regularize (ideal []) []

let test_polycone_triangle k () =
  (* Test if cuts in non-standard lattices work.
     Isomorphic to polyhedral triangle, whose integer hull should be vertical line
     segment in the image of the isomorphism.
   *)
  let open Infix in
  let x_gen = x * x + int(2) * x in
  let y_gen = y * y + int(2) * y in
  let polycone =
    let lattice = [x_gen ; y_gen] in
    let positives = [ x_gen
                    ; int(-1) * x_gen + int(-2) * int(k) * y_gen + int(2) * int(k)
                    ; int(-1) * x_gen + int(2) * int(k) * y_gen
                    ]
    in
    let cone = PolynomialCone.add_generators ~nonnegatives:positives empty_cone in
    let (cp, _) = regular_cutting_plane_closure cone lattice in
    cp
  in
  let expected_zeroes = [ x_gen ] in
  let expected_positives = [ int(1) - y_gen ; y_gen ] in
  let expected_cone = PolynomialCone.make_cone (ideal expected_zeroes) expected_positives
  in
  assert_equal (PolynomialCone.equal polycone expected_cone) true

let test_polycone_exploding_cut () =
  (* Test that a cut in a lattice at dimensions above the Groebner basis
       indeed strengthens the polyhedron.

       Lattice: 2x^2 y, 2xy^2
       Zeroes: x^2 - y
       Positives:
       3x^2 y + 3xy^2 - 1 >= 0 -- cut --> 2x^2 y + 2xy^2 - 1 >= 0 -- reduce --> 2y^2 + 2xy^2 - 1 >= 0
       -y^2 - x^5 >= 0 -- reduce --> -y^2 - xy^2, so -1 >= 0, contradiction.

       vs. without strengthening:
       3y^2 + 3xy^2 - 1 >= 0
       -y^2 + xy^2 >= 0
   *)
  let open Infix in
    let lattice = [ int(2) * x * x * y ; int(2) * x * y * y ]
    in
    let zeros = [ x * x - y ] in
    let positives = [ int(3) * x * x * y + int(3) * x * y * y - int(1)
                    ; int(-1) * y * y + int(-1) * x * x * x * x * x
                    ] in
    let cone = PolynomialCone.add_generators ~zeros ~nonnegatives:positives empty_cone in
    let (polycone, _) = regular_cutting_plane_closure cone lattice in
    let expected_zeroes = [ int(-1)  ] in
    let expected_positives = [ int(1) ] in
    let expected_cone = PolynomialCone.make_cone (ideal expected_zeroes) expected_positives in
    assert_equal (PolynomialCone.equal polycone expected_cone) true

let test_polycone_add_zero_exploding_cut _ =
  (* Same as exploding cut test, but we have to add 0 to align with lattice first.

     Lattice: 2x^2 y, 2xy^2
     Zeroes: x^2 - y
     Positives:
     3xy^2 + 3y^2 - 1 >= 0 --> 3xy^2 + (3x^2y - 3y^2) + 3y^2 - 1 >= 0, then continue as before.
     -y^2 - x^5 >= 0
   *)
  let open Infix in
  let lattice = [ int(2) * x * x * y ; int(2) * x * y * y ] in
  let zeros = [ x * x - y ] in
  let positives = [ int(3) * x * y * y + int(3) * y * y + int(-1)
                  ; int(-1) * y * y + int(-1) * x * x * x * x * x
                  ] in
  let cone = PolynomialCone.add_generators ~zeros ~nonnegatives:positives empty_cone in
  let (polycone, _) = regular_cutting_plane_closure cone lattice in
  let expected_zeroes = [ int(-1) ] in
  let expected_positives = [ int(1) ] in
  let expected_cone = PolynomialCone.make_cone (ideal expected_zeroes) expected_positives in
  assert_equal (PolynomialCone.equal polycone expected_cone) true

let half_in_lattice =
  let lattice = [ QQXs.scalar (QQ.of_frac 1 2) ] in
  let zeros = [ ] in
  let positives = [ x ] in
  let (polycone, _) =
    let c = PolynomialCone.add_generators ~zeros ~nonnegatives:positives empty_cone in
    regular_cutting_plane_closure c lattice in
  assert_bool "half_in_lattice" (not ((PolynomialCone.is_proper polycone)))

let suite = "PolynomialConeCpClosure" >::: [
      "polycone triangle" >:: test_polycone_triangle 10
    ; "exploding cut" >:: test_polycone_exploding_cut
    ; "zeros for exploding cut" >:: test_polycone_add_zero_exploding_cut
    ; "half_in_lattice" >:: (fun _ -> half_in_lattice)
    ]

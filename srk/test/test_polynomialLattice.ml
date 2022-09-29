open Srk
open OUnit
open Polynomial

module PL = PolynomialLattice

module Infix = struct
  let int k = QQXs.scalar (QQ.of_int k)
  let ( * ) = QQXs.mul
  let ( + ) = QQXs.add
  let ( ~- ) = QQXs.negate
end

let x = QQXs.of_dim 1
let y = QQXs.of_dim 2
let z = QQXs.of_dim 3


(* 3 x^2 y - 2xy + 2x + 2y ; 2 xy ; 2y + 1
   [ -2 ; 2 ; 2 ; 0
   ;  2 ; 0 ; 0 ; 0
   ;  0 ; 0 ; 2 ; 1
   ]
   ->
   [ 2 ; 0 ; 0 ;  0
   ; 0 ; 2 ; 0 ; -1
   ; 0 ; 0 ; 2 ;  1
   ]
*)
let lattice_of_twos =
  let open Infix in
  let quadratic = Ideal.make [int(2) * x * x] in
  let p1 = int(3) * x * x * y + ((- (int(2) * x * y)) + int(2) * x) + int(2) * y in
  let p2 = int(2) * x * y in
  let p3 = int(2) * y + int (1) in
  PL.make quadratic [p1; p2; p3]

(*
  3y^2 ; 3x ; 3y
  [ 3 ; 0 ; 0 ; 0 ; 0
  ; 0 ; 0 ; 3 ; 0 ; 0
  ; 0 ; 0 ; 0 ; 3 ; 0
  ]
 *)
let lattice_of_threes =
  let open Infix in
  let p1 = int(3) * y * y in
  let p2 = int(3) * x in
  let p3 = int(3) * y in
  PL.make (Ideal.make []) [p1; p2; p3]

let test_member () =
  let open Infix in
  let p = int(3) * x * x + int(4) * x + int(2) * y + int(-1) in
  let q = int(3) * x * x + int(4) * x + int(2) * y in
  assert_equal (PL.member p lattice_of_twos) true;
  assert_equal (PL.member q lattice_of_twos) false

let test_sum () =
  (*
    x^2 + 3y^2 + x + y + 2 \in sum
   *)
  let open Infix in
  let lattice = PL.sum lattice_of_twos lattice_of_threes in
  let p0 = int(3) * y * y in
  let _p1 = int(3) * y * y + int(2) * x + int(2) * y * int(-1) in
  let _p2 = x * x + int(3) * y * y + x + y + int(2) in
  let _q2 = x * x + int(3) * y * y + x + y + int(1) in
  assert_equal (PL.member p0 lattice) true

let suite = "PolynomialLattice" >::: [
      "membership" >:: test_member
    ; "sum" >:: test_sum
    ]

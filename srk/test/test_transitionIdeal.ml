open Srk
open OUnit
module I = Polynomial.Rewrite
module QQXs = Polynomial.QQXs
module Monomial = Polynomial.Monomial

module QQXsInfix = struct
  let ( + ) = QQXs.add
  let ( - ) = QQXs.sub
  let ( * ) = QQXs.mul
  let int k = QQXs.scalar (QQ.of_int k)
  let dim k = QQXs.of_dim (Char.code k)
end

let w = QQXs.of_dim 0
let x = QQXs.of_dim 1
let y = QQXs.of_dim 2
let z = QQXs.of_dim 3
let w' = QQXs.of_dim 4
let x' = QQXs.of_dim 5
let y' = QQXs.of_dim 6
let z' = QQXs.of_dim 7

let make_ti polys =
  TransitionIdeal.make 4 (I.grobner_basis (I.mk_rewrite Monomial.degrevlex polys))

let show_ti =
  let pp_dim formatter i = match i with
    | 0 -> Format.fprintf formatter "w"
    | 1 -> Format.fprintf formatter "x"
    | 2 -> Format.fprintf formatter "y"
    | 3 -> Format.fprintf formatter "z"
    | _ -> assert false
  in
  SrkUtil.mk_show (TransitionIdeal.pp pp_dim)  

let assert_equal_ti = assert_equal ~cmp:TransitionIdeal.equal ~printer:show_ti

let suite = "TransitionIdeal" >::: [
    "compose" >:: (fun () ->
        let open QQXsInfix in
        let a =
          make_ti
            [ x' - x - (int 1)
            ; y' - y - x*x
            ; y - (int 3)
            ; w' - (int 2) ]
        in
        let b =
          make_ti
            [ x' - x
            ; y' - z
            ; w' - x*x ]
        in
        let composed =
          make_ti
            [ x' - x - (int 1)
            ; y' - (int 3) - x*x
            ; z - (int 3)
            ; w' - (int 2) ]
        in
        assert_equal_ti composed (TransitionIdeal.compose a b))
  ; "invariant_domain" >:: (fun () ->
        let open QQXsInfix in
        let t =
          make_ti
            [ x' - x + x*y
            ; y' - y - z
            ; z' - (int 3) * z
            ; y - z - (int 1) ]
        in
        let expected_dom = make_ti [y - (int 1); z ] in
        assert_equal_ti
          expected_dom
          (make_ti (I.generators (TransitionIdeal.invariant_domain t)));
        let (seq, dom) = TransitionIdeal.iteration_sequence t in
        begin match seq with
        | [one; two] ->
          assert_equal_ti t one;
          assert_equal_ti (TransitionIdeal.compose t t) two;
        | _ -> assert_failure "Incorrect length for iteration sequence"
        end;
        assert_equal_ti expected_dom (make_ti (I.generators dom)))

  ; "solvable1" >:: (fun () ->
      let open QQXsInfix in
      let t =
        make_ti
          [ x' - x - (int 1)
          ; y' - y - x*x
          ; z' - z - x*y
          ; w' - w - w*z ]
      in
      let (solvable, sim, _) = TransitionIdeal.solvable_reflection t in
      let (ult_solvable, ult_sim, _) =
        TransitionIdeal.ultimately_solvable_reflection t
      in
      let result = TransitionIdeal.image solvable sim 4 in
      let ult_result = TransitionIdeal.image ult_solvable ult_sim 4 in
      let expected =
        make_ti
          [ x' - x - (int 1)
          ; y' - y - x*x
          ; z' - z - x*y ]
      in
      assert_equal_ti expected result;
      assert_equal_ti expected ult_result)
  ; "solvable2" >:: (fun () ->
      let open QQXsInfix in
      let t =
        make_ti
          [ x' - y - (int 1)
          ; y' - x - (int 1)
          ; z' - z - x*y*x ]
      in
      let (solvable, sim, _) = TransitionIdeal.solvable_reflection t in
      let result = TransitionIdeal.image solvable sim 4 in
      assert_equal_ti t result)
  ; "solvable3" >:: (fun () ->
      let open QQXsInfix in
      let t =
        make_ti
          [ x' - y - (int 1)
          ; y' - z - (int 1)
          ; z' - x - (int 1)
          ; (x' - y')*z ]
      in
      let (solvable, sim, _) = TransitionIdeal.solvable_reflection t in
      let result = TransitionIdeal.image solvable sim 4 in
      assert_equal_ti t result)
  ; "solvable4" >:: (fun () ->
      let open QQXsInfix in
      let t =
        make_ti
          [ w' - w - (int 1)
          ; x' - x - y*y + w*w'
          ; y' - y + y*y + w*w'
          ; z' - (x + y)*w ]
      in
      let (solvable, sim, _) = TransitionIdeal.solvable_reflection t in
      let result = TransitionIdeal.image solvable sim 4 in
      let expected =
        make_ti
          [ w' - w - (int 1)
          ; (x' + y') - (x + y) + (int 2)*w*w'
          ; z' - (x + y)*w ]
      in
      assert_equal_ti expected result)
  ; "ult_solvable1" >:: (fun () ->
      let open QQXsInfix in
      let t =
        make_ti
          [ x' - z*z*x
          ; y' - z*y*y
          ; w' - z*z
          ; z' - w
          ; w - (int 1)]
      in
      let (solvable, sim, _) = TransitionIdeal.ultimately_solvable_reflection t in
      let result = TransitionIdeal.image solvable sim 4 in
      let expected =
        make_ti
          [ x' - z*z*x
          ; w' - z*z
          ; z' - w
          ; w - (int 1)]
      in
      assert_equal_ti expected result)
  ; "ult_solvable2" >:: (fun () ->
      let open QQXsInfix in
      let t =
        make_ti
          [ w' - x
          ; x' - y
          ; y' - w * w
          ; x
          ; z' - z*z]
      in
      let (solvable, sim, _) = TransitionIdeal.ultimately_solvable_reflection t in
      let result = TransitionIdeal.image solvable sim 4 in
      let expected =
        make_ti
          [ w' - x
          ; x' - y
          ; y' - w * w
          ; x]
      in
      assert_equal_ti expected result)
  ; "ult_solvable3" >:: (fun () ->
      let open QQXsInfix in
      let t =
        make_ti
          [ x' - y*y
          ; z'
          ; w' - w - y*y
          ; x - z ]
      in
      let (solvable, sim, _) = TransitionIdeal.ultimately_solvable_reflection t in
      let result = TransitionIdeal.image solvable sim 4 in
      let expected =
        make_ti
          [ z'
          ; (x' - w') - (x - w) + z ]
      in
      assert_equal_ti expected result)
  ]

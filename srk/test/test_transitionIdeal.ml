open Srk
open OUnit
module I = Polynomial.Ideal
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
  TransitionIdeal.make 4 (I.make polys)

let pp_dim offset formatter i =
  if i = 2* offset then
    Format.fprintf formatter "K"
  else if i < offset then
    match i with
    | 0 -> Format.fprintf formatter "w"
    | 1 -> Format.fprintf formatter "x"
    | 2 -> Format.fprintf formatter "y"
    | 3 -> Format.fprintf formatter "z"
    | _ -> assert false
  else
    match (i-offset) with
    | 0 -> Format.fprintf formatter "w'"
    | 1 -> Format.fprintf formatter "x'"
    | 2 -> Format.fprintf formatter "y'"
    | 3 -> Format.fprintf formatter "z'"
    | _ -> assert false


let show_ti =
  SrkUtil.mk_show (TransitionIdeal.pp (pp_dim 4))  

let assert_equal_ti = assert_equal ~cmp:TransitionIdeal.equal ~printer:show_ti

let enumerate (ti : TransitionIdeal.t) n = 
  let rec ti_to_n acc ti_to_i_minus_1 i = 
    if i > n then acc
    else if i = 0 then 
      let ti_0 = make_ti (List.init ti.dim (fun d -> QQXs.sub (QQXs.of_dim (d + ti.dim)) (QQXs.of_dim d))) in
      let ti_0_id = I.add_saturate ti_0.ideal (QQXs.sub (QQXs.of_dim (2*ti.dim)) (QQXs.scalar (QQ.of_int i))) in
      ti_to_n ti_0_id ti_0 (i+1)
    else if i = 1 then
      let ti_1 = I.add_saturate ti.ideal (QQXs.sub (QQXs.of_dim (2*ti.dim)) (QQXs.scalar (QQ.of_int i))) in
      ti_to_n (I.intersect ti_1 acc) ti (i+1)
    else
      let ti_i = TransitionIdeal.compose ti_to_i_minus_1 ti in
      let ti_i_id = I.add_saturate ti_i.ideal (QQXs.sub (QQXs.of_dim (2*ti.dim)) (QQXs.scalar (QQ.of_int i))) in
      ti_to_n (I.intersect ti_i_id acc) ti_i (i+1)
  in
  ti_to_n (I.make [QQXs.zero]) (make_ti [QQXs.zero]) 0


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
  ; "solvable_cl1" >:: (fun () ->
      let open QQXsInfix in
      let t =
        make_ti
          [ x' - x - (int 1)
          ; y' - y
          ; w' - w
          ; z'- z
          ]
      in
      (*Log.logf ~level:`always "t : %a" (TransitionIdeal.pp (pp_dim t.dim)) t;*)
      let (solvable, _, witness) = TransitionIdeal.solvable_reflection t in
      (*Log.logf ~level:`always "solvable : %a" (TransitionIdeal.pp (pp_dim solvable.dim)) solvable;*)
      let sp_lirr_t = SolvablePolynomial.SolvablePolynomialLIRR.make_sp solvable witness in
      let cl = SolvablePolynomial.SolvablePolynomialLIRR.exp_ti sp_lirr_t in
      (*Log.logf ~level:`always "Cl : %a" (TransitionIdeal.pp (pp_dim cl.dim)) cl;*)
      let first_few = enumerate solvable 2 in
      let res = Polynomial.Ideal.subset (Polynomial.Ideal.make (I.generators cl.ideal)) first_few in
      (*Log.logf ~level:`always "T^0 inter T^1 inter T^2 : %a" (Polynomial.Ideal.pp (pp_dim solvable.dim)) first_few;*)
      assert_bool "Not subset" res)
  ; "solvable_cl2" >:: (fun () ->
    let open QQXsInfix in
    let t =
      make_ti
        [ x' - x + x*y
        ; y' - y - z
        ; z' - (int 3) * z
        ; y - z - (int 1) ]
    in
    (*Log.logf ~level:`always "t : %a" (TransitionIdeal.pp (pp_dim t.dim)) t;*)
    let (solvable, _, witness) = TransitionIdeal.solvable_reflection t in
    (*Log.logf ~level:`always "solvable : %a" (TransitionIdeal.pp (pp_dim solvable.dim)) solvable;*)
    let sp_lirr_t = SolvablePolynomial.SolvablePolynomialLIRR.make_sp solvable witness in
    let cl = SolvablePolynomial.SolvablePolynomialLIRR.exp_ti sp_lirr_t in
    (*Log.logf ~level:`always "Cl : %a" (TransitionIdeal.pp (pp_dim cl.dim)) cl;*)
    let first_few = enumerate solvable 2 in
    let res = Polynomial.Ideal.subset (Polynomial.Ideal.make (I.generators cl.ideal)) first_few in
    (*Log.logf ~level:`always "T^0 inter T^1 inter T^2 : %a" (Polynomial.Ideal.pp (pp_dim solvable.dim)) first_few;*)
    assert_bool "Not subset" res)
  ; "solvable_cl3" >:: (fun () ->
    let open QQXsInfix in
    let t =
      make_ti
        [ x' - x - (int 1)
        ; y' - y - x*x
        ; z' - z - x*y
        ; w' - w - w*z ]
    in
    (*Log.logf ~level:`always "t : %a" (TransitionIdeal.pp (pp_dim t.dim)) t;*)
    let (solvable, _, witness) = TransitionIdeal.solvable_reflection t in
    (*Log.logf ~level:`always "solvable : %a" (TransitionIdeal.pp (pp_dim solvable.dim)) solvable;*)
    let sp_lirr_t = SolvablePolynomial.SolvablePolynomialLIRR.make_sp solvable witness in
    let cl = SolvablePolynomial.SolvablePolynomialLIRR.exp_ti sp_lirr_t in
    (*Log.logf ~level:`always "Cl : %a" (TransitionIdeal.pp (pp_dim cl.dim)) cl;*)
    let first_few = enumerate solvable 2 in
    let res = Polynomial.Ideal.subset (Polynomial.Ideal.make (I.generators cl.ideal)) first_few in
    (*Log.logf ~level:`always "T^0 inter T^1 inter T^2 : %a" (Polynomial.Ideal.pp (pp_dim solvable.dim)) first_few;*)
    assert_bool "Not subset" res)
  ; "solvable_cl4" >:: (fun () ->
    let open QQXsInfix in
    let t =
      make_ti
        [ x' - y - (int 1)
        ; y' - z - (int 1)
        ; z' - x - (int 1)
        ; (x' - y')*z ]
    in
    (*Log.logf ~level:`always "t : %a" (TransitionIdeal.pp (pp_dim t.dim)) t;*)
    let (solvable, _, witness) = TransitionIdeal.solvable_reflection t in
    (*Log.logf ~level:`always "solvable : %a" (TransitionIdeal.pp (pp_dim solvable.dim)) solvable;*)
    let sp_lirr_t = SolvablePolynomial.SolvablePolynomialLIRR.make_sp solvable witness in
    let cl = SolvablePolynomial.SolvablePolynomialLIRR.exp_ti sp_lirr_t in
    (*Log.logf ~level:`always "Cl : %a" (TransitionIdeal.pp (pp_dim cl.dim)) cl;*)
    let first_few = enumerate solvable 2 in
    let res = Polynomial.Ideal.subset (Polynomial.Ideal.make (I.generators cl.ideal)) first_few in
    (*Log.logf ~level:`always "T^0 inter T^1 inter T^2 : %a" (Polynomial.Ideal.pp (pp_dim solvable.dim)) first_few;*)
    assert_bool "Not subset" res)
  ; "solvable_cl5" >:: (fun () ->
    let open QQXsInfix in
    let t =
      make_ti
        [ w' - w - (int 1)
        ; x' - x - y*y + w*w'
        ; y' - y + y*y + w*w'
        ; z' - (x + y)*w ]
    in
    (*Log.logf ~level:`always "t : %a" (TransitionIdeal.pp (pp_dim t.dim)) t;*)
    let (solvable, _, witness) = TransitionIdeal.solvable_reflection t in
    (*Log.logf ~level:`always "solvable : %a" (TransitionIdeal.pp (pp_dim solvable.dim)) solvable;*)
    let sp_lirr_t = SolvablePolynomial.SolvablePolynomialLIRR.make_sp solvable witness in
    let cl = SolvablePolynomial.SolvablePolynomialLIRR.exp_ti sp_lirr_t in
    (*Log.logf ~level:`always "Cl : %a" (TransitionIdeal.pp (pp_dim cl.dim)) cl;*)
    let first_few = enumerate solvable 2 in
    let res = Polynomial.Ideal.subset (Polynomial.Ideal.make (I.generators cl.ideal)) first_few in
    (*Log.logf ~level:`always "T^0 inter T^1 inter T^2 : %a" (Polynomial.Ideal.pp (pp_dim solvable.dim)) first_few;*)
    assert_bool "Not subset" res)
  ; "ultsolvable_cl1" >:: (fun () ->
    let open QQXsInfix in
    let t =
      make_ti
        [ x' - x + x*y
        ; y' - y - z
        ; z' - (int 3) * z
        ; y - z - (int 1) ]
    in
    let (solvable, _, witness) = TransitionIdeal.ultimately_solvable_reflection t in
    let sp_lirr_t = SolvablePolynomial.SolvablePolynomialLIRR.make_sp solvable witness in
    let cl = SolvablePolynomial.SolvablePolynomialLIRR.exp_ti sp_lirr_t in
    let first_few = enumerate solvable 2 in
    let res = Polynomial.Ideal.subset (Polynomial.Ideal.make (I.generators cl.ideal)) first_few in
    assert_bool "Not subset" res)
  ; "quadratic_sim" >:: (fun () ->
      let base_dim = 3 in
      let w = QQXs.of_dim 0 in
      let x = QQXs.of_dim 1 in
      let y = QQXs.of_dim 2 in
      let w' = QQXs.of_dim (base_dim + 0) in
      let x' = QQXs.of_dim (base_dim + 1) in
      let y' = QQXs.of_dim (base_dim + 2) in
      let open QQXsInfix in
      let t =
        TransitionIdeal.make base_dim (I.make
                                            [ (x' * x') - (x * x) + (int 1)
                                            ; y' - y - x
                                            ; w' - w - x * x ])
      in
      let (t2, sim2) = TransitionIdeal.universal_degree_limited t 2 in
      let (solvable, sim, _) = TransitionIdeal.solvable_reflection t2 in
      let sim = TransitionIdeal.compose_polynomial_map sim sim2 in
      let result = TransitionIdeal.image solvable sim base_dim in
      let expected =
        TransitionIdeal.make base_dim
          (I.make
                [ (x' * x') - (x * x) + (int 1)
                ; w' - w - x * x ])
      in
      assert_equal_ti expected result)
  ]

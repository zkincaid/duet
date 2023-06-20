open OUnit
open Srk
open Rational


module ConstRingInfix = struct
  let ( + ) = ConstRing.add
  let ( - ) = ConstRing.sub
  let ( * ) = ConstRing.mul
  let int k = ConstRing.scalar (QQ.of_int k)
  let rat n d = ConstRing.scalar (QQ.of_frac n d)
  let dim k = ConstRing.of_dim k
end

let qqify_v = Array.map (QQ.of_int)

let qqify = Array.map qqify_v

module RatEP = RatSeq.RatEP

let assert_equal_ep = 
  assert_equal ~cmp:(RatEP.equal) ~printer:(SrkUtil.mk_show RatEP.pp)

type block = TransitionIdeal.block



let mat_rec_test1 () =
  let open ConstRingInfix in
  let transform = qqify [|[|2; 0|];
                        [|0; 3|]|] in
  let add = [|Polynomial.QQXs.zero; Polynomial.QQXs.zero|] in
  let eps = RatSeq.solve_rec [({blk_transform = transform; blk_add = add} : block)] in
  let dim0_cor = RatEP.mul (RatEP.scalar (dim 0)) (RatEP.of_exponential (QQ.of_int 2)) in
  let dim1_cor = RatEP.mul (RatEP.scalar (dim 1)) (RatEP.of_exponential (QQ.of_int 3)) in
  assert_equal_ep dim0_cor eps.(0);
  assert_equal_ep dim1_cor eps.(1)


let sp_test1 () =
  let open ConstRingInfix in
  let transform1 = qqify [|[|2; 0|];
                          [|0; 3|]|] in
  let add1 = [|Polynomial.QQXs.zero; Polynomial.QQXs.zero|] in
  let blk1 : block = {blk_transform = transform1; blk_add = add1} in
  let transform2 = qqify [|[|4|]|] in
  let add2 = [|Polynomial.QQXs.mul (Polynomial.QQXs.of_dim 0) (Polynomial.QQXs.of_dim 1)|] in
  let blk2 : block = {blk_transform = transform2; blk_add = add2} in
  let eps = RatSeq.solve_rec [blk1; blk2] in
  let dim0_cor = RatEP.mul (RatEP.scalar (dim 0)) (RatEP.of_exponential (QQ.of_int 2)) in
  let dim1_cor = RatEP.mul (RatEP.scalar (dim 1)) (RatEP.of_exponential (QQ.of_int 3)) in
  let t1 = RatEP.mul (RatEP.scalar ((dim 2) - (rat 1 2) * (dim 0) * (dim 1))) (RatEP.of_exponential (QQ.of_int 4)) in
  let t2 = RatEP.mul (RatEP.scalar ((rat 1 2) * (dim 0) * (dim 1))) (RatEP.of_exponential (QQ.of_int 6)) in
  assert_equal_ep dim0_cor eps.(0);
  assert_equal_ep dim1_cor eps.(1);
  assert_equal_ep (RatEP.add t1 t2) eps.(2)

let iif_test1 () =
  let transform1 = qqify [|[|1; 1|];
                          [|1; 0|]|] in
  let add1 = [|Polynomial.QQXs.zero; Polynomial.QQXs.zero|] in
  let blk : block = {blk_transform = transform1; blk_add = add1} in
  let eps = RatSeq.solve_rec [blk] in
  Array.iteri (fun dim ep ->
    logf ~level:`always "Dim %d : %a" dim RatEP.pp ep) eps

let pp_facts f (n, (den, pow)) = 
  Format.fprintf f "(%a)/(%a)^%d" (ConstRingX.pp ConstRing.pp) n Polynomial.QQX.pp den pow

let zero_eigen_test () = 
  let transform1 = qqify [|[|0; 1|];
                          [|0; 0|]|] in
  let add1 = [|Polynomial.QQXs.zero; Polynomial.QQXs.zero|] in
  let blk : block = {blk_transform = transform1; blk_add = add1} in
  let eps = RatSeq.solve_rec [blk] in
  Array.iteri (fun dim ep ->
    logf ~level:`always "Dim %d : %a" dim RatEP.pp ep) eps


let nf_test1 () =
  let transform1 = qqify [|[|1; 1|];
                          [|1; 0|]|] in
  let add1 = [|Polynomial.QQXs.zero; Polynomial.QQXs.zero|] in
  let blk : block = {blk_transform = transform1; blk_add = add1} in
  let eps = RatSeq.solve_rec [blk] in
  let module EP = (val RatEP.to_nf eps) in
  let nf_eps = EP.get_rec_sols () in
  Array.iteri (fun dim ep ->
    logf ~level:`always "Dim %d : %a" dim EP.pp ep) nf_eps

let suite = "Rational" >:::
  [
    "mat_rec_test1" >:: mat_rec_test1;
    "sp_test1" >:: sp_test1;
    "iif_test1" >:: iif_test1;
    "zero_eigen_test" >:: zero_eigen_test;
    "nf_test1" >:: nf_test1
  ]
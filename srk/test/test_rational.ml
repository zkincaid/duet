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


let assert_equal_ep = 
  assert_equal ~cmp:(RatEP.equal) ~printer:(RatEP.show)

let mat_rec_test1 () =
  let open ConstRingInfix in
  let transform = qqify [|[|2; 0|];
                        [|0; 3|]|] in
  let init = [|ConstRing.of_dim 0; ConstRing.of_dim 1|] in
  let add = [|RatSeq.zero;RatSeq.zero|] in
  let res = RatSeq.solve_mat_rec_rs transform init add in
  let eps = translate_rs res in
  let dim0_cor = RatEP.mul (RatEP.scalar (dim 0)) (RatEP.of_exponential (QQ.of_int 2)) in
  let dim1_cor = RatEP.mul (RatEP.scalar (dim 1)) (RatEP.of_exponential (QQ.of_int 3)) in
  assert_equal_ep dim0_cor eps.(0);
  assert_equal_ep dim1_cor eps.(1)


let sp_test1 () =
  let open ConstRingInfix in
  let transform1 = qqify [|[|2; 0|];
                          [|0; 3|]|] in
  let add1 = [|Polynomial.QQXs.zero; Polynomial.QQXs.zero|] in
  let blk1 = {RatSeq.blk_transform = transform1; RatSeq.blk_add = add1} in
  let transform2 = qqify [|[|4|]|] in
  let add2 = [|Polynomial.QQXs.mul (Polynomial.QQXs.of_dim 0) (Polynomial.QQXs.of_dim 1)|] in
  let blk2 = {RatSeq.blk_transform = transform2; RatSeq.blk_add = add2} in
  let res = RatSeq.solve_rec_rs [blk1; blk2] in
  let eps = translate_rs res in
  let dim0_cor = RatEP.mul (RatEP.scalar (dim 0)) (RatEP.of_exponential (QQ.of_int 2)) in
  let dim1_cor = RatEP.mul (RatEP.scalar (dim 1)) (RatEP.of_exponential (QQ.of_int 3)) in
  let t1 = RatEP.mul (RatEP.scalar ((dim 2) - (rat 1 2) * (dim 0) * (dim 1))) (RatEP.of_exponential (QQ.of_int 4)) in
  let t2 = RatEP.mul (RatEP.scalar ((rat 1 2) * (dim 0) * (dim 1))) (RatEP.of_exponential (QQ.of_int 6)) in
  assert_equal_ep dim0_cor eps.(0);
  assert_equal_ep dim1_cor eps.(1);
  assert_equal_ep (RatEP.add t1 t2) eps.(2)



let suite = "Rational" >:::
  [
    "mat_rec_test1" >:: mat_rec_test1;
    "sp_test1" >:: sp_test1
  ]
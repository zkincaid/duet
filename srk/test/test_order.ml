open OUnit
open Srk

module QQXInfix = struct
  let ( + ) = Polynomial.QQX.add
  let ( - ) = Polynomial.QQX.sub
  let ( * ) = Polynomial.QQX.mul
  let int k = Polynomial.QQX.scalar (QQ.of_int k)
  let v = Polynomial.QQX.identity
end

let zzify = Array.map (Array.map ZZ.of_int)

let zzify_v = Array.map ZZ.of_int

module ZZM = Ring.MakeMatrix(ZZ)

let zzmify = ZZM.of_dense

let unzzmify matrix = 
  ZZM.dense_of matrix (ZZM.nb_rows matrix) (ZZM.nb_columns matrix)


module SqrtNeg5F = NumberField.MakeNF(struct
  let min_poly = 
    let open QQXInfix in
    v * v + int(5)
end)

module SqrtNeg5 = SqrtNeg5F.O

(*module SqrtNeg5 = Order.MakeOrder(
  struct 
    let rank = 2 
    let mult i j = 
      if i = 0 && j = 0 then
        [|ZZ.zero; ZZ.of_int (-5)|] 
      else if (i = 1 && j = 0) || (i=0 && j = 1) then
        [|ZZ.one; ZZ.zero|]
      else
        [|ZZ.zero; ZZ.one|]
  end)*)

let assert_equal_ideal p q =
  assert_equal ~cmp:SqrtNeg5.equal_i ~printer:(SrkUtil.mk_show SqrtNeg5.pp_i) p q

let assert_equal_frac_ideal p q =
  assert_equal ~cmp:SqrtNeg5.equal ~printer:(SrkUtil.mk_show SqrtNeg5.pp) p q

let pp_zv f v = ZZM.pp (ZZ.pp) f (zzmify [|v|])


(*let test_hnf () = 
  let a = SqrtNeg5.idealify (zzify [|
    [|1; 1|];
    [|-5; 1|]|]
  ) in
  let b = SqrtNeg5.idealify (zzify [|
    [|1; 1|];
    [|0; 6|]|]
  ) in
  assert_equal_ideal a b

let test_ideal_create1 () = 
  let six = SqrtNeg5.ideal_generated_by (zzify_v [|0; 6|]) in
  let corr = SqrtNeg5.idealify (zzify [|
    [|6; 0|];
    [|0; 6|]|]
  ) in
  assert_equal_ideal corr six

let test_ideal_create2 () = 
  let one_plus_sqrt_mfive = SqrtNeg5.ideal_generated_by (zzify_v [|1; 1|]) in
  let corr = SqrtNeg5.idealify (zzify [|
    [|1; 1|];
    [|0; 6|]|]
  ) in
  assert_equal_ideal corr one_plus_sqrt_mfive*)

let make_ideal_sqrt_neg_5 p = 
  SqrtNeg5.ideal_generated_by (snd (SqrtNeg5.make_o_el (SqrtNeg5F.make_elem p)))

let test_sum1 () = 
  let open QQXInfix in
  let two = make_ideal_sqrt_neg_5 (int(2)) in
  let one_plus_sqrt_m5 = make_ideal_sqrt_neg_5 (int(1) + v) in
  let s = SqrtNeg5.sum_i two one_plus_sqrt_m5 in
  let s_corr = SqrtNeg5.idealify (zzify [|
    [|1; 1|];
    [|0; 2|]
  |]) in
  assert_equal_ideal s_corr s


let test_mul1 () = 
  let open QQXInfix in
  let six = make_ideal_sqrt_neg_5 (int(6)) in
  let one_plus_sqrt_m5 = make_ideal_sqrt_neg_5 (int(1) + v) in
  let one_minus_sqrt_m5 = make_ideal_sqrt_neg_5 (int(1) - v) in
  assert_equal_ideal six (SqrtNeg5.mul_i one_plus_sqrt_m5 one_minus_sqrt_m5)

let test_intersect1 () = 
  let open QQXInfix in
  let six = make_ideal_sqrt_neg_5 (int(6)) in
  let one_plus_sqrt_m5 = make_ideal_sqrt_neg_5 (int(1) + v) in
  let i = SqrtNeg5.intersect_i six one_plus_sqrt_m5 in
  assert_equal_ideal six i

let test_intersect2 () = 
  let open QQXInfix in
  let two = make_ideal_sqrt_neg_5 (int(2)) in
  let one_plus_sqrt_m5 = make_ideal_sqrt_neg_5 (int(1) + v) in
  let two_plus_2_sqrt_m5 = make_ideal_sqrt_neg_5 (int(2) + int(2)*v) in
  let six = make_ideal_sqrt_neg_5 (int(6)) in
  let i = SqrtNeg5.intersect_i two one_plus_sqrt_m5 in
  let i_corr = SqrtNeg5.sum_i six two_plus_2_sqrt_m5 in
  assert_equal_ideal i_corr i

let test_quotient1 () = 
  let open QQXInfix in
  let six = make_ideal_sqrt_neg_5 (int(6)) in
  let one_plus_sqrt_m5 = make_ideal_sqrt_neg_5 (int(1) + v) in
  let one_minus_sqrt_m5 = make_ideal_sqrt_neg_5 (int(1) - v) in
  let i = SqrtNeg5.quotient_i six one_plus_sqrt_m5 in
  assert_equal_ideal one_minus_sqrt_m5 i

let test_quotient2 () = 
  let open QQXInfix in
  let three = make_ideal_sqrt_neg_5 (int(3)) in
  let one_plus_sqrt_m5 = make_ideal_sqrt_neg_5 (int(1) + v) in
  let i = SqrtNeg5.quotient_i three one_plus_sqrt_m5 in
  let i_corr = SqrtNeg5.sum_i (make_ideal_sqrt_neg_5 (int(1) + int(2)*v)) three in
  assert_equal_ideal i_corr i

let test_smallest_int1 () = 
  let open QQXInfix in
  let three = make_ideal_sqrt_neg_5 (int(3)) in
  assert_equal ~cmp:(ZZ.equal) ~printer:(ZZ.show) (ZZ.of_int 3) (SqrtNeg5.get_smallest_int three)

let test_smallest_int2 () = 
  let open QQXInfix in
  let one_plus_sqrt_m5 = make_ideal_sqrt_neg_5 (int(1) + v) in
  assert_equal ~cmp:(ZZ.equal) ~printer:(ZZ.show) (ZZ.of_int 6) (SqrtNeg5.get_smallest_int one_plus_sqrt_m5)

let test_frac_quotient1 () = 
  let open QQXInfix in
  let three = SqrtNeg5.make_frac_ideal ZZ.one (make_ideal_sqrt_neg_5 (int(3))) in
  let one_plus_sqrt_m5 = SqrtNeg5.make_frac_ideal ZZ.one (make_ideal_sqrt_neg_5 (int(1) + v))  in
  let one_minus_sqrt_m5_over_2 = SqrtNeg5.make_frac_ideal (ZZ.of_int 2) (make_ideal_sqrt_neg_5 (int(1) - v))  in
  assert_equal_frac_ideal one_minus_sqrt_m5_over_2 (SqrtNeg5.quotient three one_plus_sqrt_m5);
  (*This assertion should hold because Z[sqrt(-5)] is the ring of integers*)
  assert_equal_frac_ideal three (SqrtNeg5.mul one_minus_sqrt_m5_over_2 one_plus_sqrt_m5)
  
let test_frac_quotient2 () = 
  let open QQXInfix in
  let six = SqrtNeg5.make_frac_ideal ZZ.one (make_ideal_sqrt_neg_5 (int(6))) in
  let one_plus_sqrt_m5 = SqrtNeg5.make_frac_ideal ZZ.one (make_ideal_sqrt_neg_5 (int(1) + v))  in
  let one_minus_sqrt_m5 = SqrtNeg5.make_frac_ideal (ZZ.of_int 1) (make_ideal_sqrt_neg_5 (int(1) - v)) in
  assert_equal_frac_ideal one_minus_sqrt_m5 (SqrtNeg5.quotient six one_plus_sqrt_m5);
  (*This assertion should hold because Z[sqrt(-5)] is the ring of integers*)
  assert_equal_frac_ideal six (SqrtNeg5.mul one_minus_sqrt_m5 one_plus_sqrt_m5)

let test_frac_quotient3 () = 
  let open QQXInfix in
  let one = SqrtNeg5.make_frac_ideal ZZ.one (make_ideal_sqrt_neg_5 (int(1))) in
  let one_plus_sqrt_m5 = SqrtNeg5.make_frac_ideal ZZ.one (make_ideal_sqrt_neg_5 (int(1) + v))  in
  let one_minus_sqrt_m5_over_6 = SqrtNeg5.make_frac_ideal (ZZ.of_int 6) (make_ideal_sqrt_neg_5 (int(1) - v)) in
  assert_equal_frac_ideal one_minus_sqrt_m5_over_6 (SqrtNeg5.quotient one one_plus_sqrt_m5);
  (*This assertion should hold because Z[sqrt(-5)] is the ring of integers*)
  assert_equal_frac_ideal one (SqrtNeg5.mul one_minus_sqrt_m5_over_6 one_plus_sqrt_m5)


  
let test_overorder1 () = 
  let open QQXInfix in
  let one_plus_sqrt_m5 = SqrtNeg5.make_frac_ideal ZZ.one (make_ideal_sqrt_neg_5 (int(1))) in
  let overorder, invertible = SqrtNeg5.compute_overorder SqrtNeg5.one one_plus_sqrt_m5 in
  assert_equal_frac_ideal SqrtNeg5.one overorder;
  assert_equal_frac_ideal one_plus_sqrt_m5 invertible
  
let test_factor_refinement () = 
  let open QQXInfix in
  let six = SqrtNeg5.make_frac_ideal ZZ.one (make_ideal_sqrt_neg_5 (int(6))) in
  let one_plus_sqrt_m5 = SqrtNeg5.make_frac_ideal ZZ.one (make_ideal_sqrt_neg_5 (int(1) + v))  in
  let one_minus_sqrt_m5 = SqrtNeg5.make_frac_ideal (ZZ.of_int 1) (make_ideal_sqrt_neg_5 (int(1) - v)) in
  let c, gcd_basis = SqrtNeg5.factor_refinement [six; one_plus_sqrt_m5; one_minus_sqrt_m5] in
  (*let print_factor f (j, e) = 
    SqrtNeg5.pp f j;
    Format.fprintf f "@[^%d@]" e
  in
  let print_list = Format.pp_print_list ~pp_sep:(Format.pp_print_newline) print_factor in
  Log.log ~level:`always "Factors";
  Log.log_pp ~level:`always print_list gcd_basis;*)
  let multiplied_rhs = List.fold_left (fun acc (factor, deg) -> SqrtNeg5.mul acc (SqrtNeg5.exp factor deg)) (SqrtNeg5.one) gcd_basis in
  let multiplied_lhs = List.fold_left SqrtNeg5.mul c [six; one_plus_sqrt_m5; one_minus_sqrt_m5] in
  assert_equal_frac_ideal multiplied_rhs multiplied_lhs

let test_factor () = 
  let open QQXInfix in
  let six = SqrtNeg5.make_frac_ideal ZZ.one (make_ideal_sqrt_neg_5 (int(6))) in
  let one_plus_sqrt_m5 = SqrtNeg5.make_frac_ideal ZZ.one (make_ideal_sqrt_neg_5 (int(1) + v))  in
  let one_minus_sqrt_m5 = SqrtNeg5.make_frac_ideal (ZZ.of_int 1) (make_ideal_sqrt_neg_5 (int(1) - v)) in
  let exp_list, gcd_basis, overorder = SqrtNeg5.compute_factorization [six; one_plus_sqrt_m5; one_minus_sqrt_m5] in
  let check_factor i ideal = 
    let exp_list = List.nth exp_list i in
    let rhs = List.fold_left SqrtNeg5.mul SqrtNeg5.one (List.map2 SqrtNeg5.exp gcd_basis exp_list) in
    let lhs = SqrtNeg5.mul ideal overorder in
    assert_equal_frac_ideal lhs rhs
  in
  List.iteri check_factor [six; one_plus_sqrt_m5; one_minus_sqrt_m5]


let test_unit_find () = 
  let open QQXInfix in
  let _, six = SqrtNeg5.make_o_el (SqrtNeg5F.make_elem (int(6))) in
  let _, one_plus_sqrt_m5 = SqrtNeg5.make_o_el (SqrtNeg5F.make_elem (int(1)+v)) in
  let _, one_minus_sqrt_m5 = SqrtNeg5.make_o_el (SqrtNeg5F.make_elem (int(1)-v)) in
  let exp_list = SqrtNeg5.find_unit_basis [six; one_plus_sqrt_m5; one_minus_sqrt_m5] in
  assert_equal 1 (List.length exp_list);
  let unit_exp = List.hd exp_list in
  let open QQXInfix in
  let six_e = SqrtNeg5F.make_elem (int(6)) in
  let one_plus_sqrt_m5_e = SqrtNeg5F.make_elem (int(1) + v) in
  let one_minus_sqrt_m5_e = SqrtNeg5F.make_elem (int(1) - v) in
  let exp = List.map2 SqrtNeg5F.exp [six_e; one_plus_sqrt_m5_e; one_minus_sqrt_m5_e] unit_exp in
  let prod = List.fold_left SqrtNeg5F.mul SqrtNeg5F.one exp in
  assert_bool "Looking for unit" (SqrtNeg5F.equal prod SqrtNeg5F.one)

module Sqrt5F = NumberField.MakeNF(struct
  let min_poly = 
    let open QQXInfix in
    v * v - int(5)
end)

module Sqrt5 = Sqrt5F.O

(*module Sqrt5 = Order.MakeOrder(
  struct 
    let rank = 2 
    let mult i j = 
      if i = 0 && j = 0 then
        [|ZZ.zero; ZZ.of_int 5|] 
      else if (i = 1 && j = 0) || (i=0 && j = 1) then
        [|ZZ.one; ZZ.zero|]
      else
        [|ZZ.zero; ZZ.one|]
  
  end)*)

let assert_equal_ideal p q =
  assert_equal ~cmp:Sqrt5.equal_i ~printer:(SrkUtil.mk_show Sqrt5.pp_i) p q
  
let assert_equal_frac_ideal p q =
  assert_equal ~cmp:Sqrt5.equal ~printer:(SrkUtil.mk_show Sqrt5.pp) p q

let test_overorder2 () = 
  let a = Sqrt5.idealify (zzify [|
    [|1; 1|];
    [|2; 0|]
  |]) in
  let not_invert = Sqrt5.make_frac_ideal ZZ.one a in
  let overorder, invertible = Sqrt5.compute_overorder Sqrt5.one not_invert in
  let c_overorder = Sqrt5.make_frac_ideal (ZZ.of_int 2) a in
  let inverse = Sqrt5.quotient overorder invertible in
  assert_equal_frac_ideal c_overorder overorder;
  assert_equal_frac_ideal overorder (Sqrt5.mul inverse invertible)


let suite = "Order" >:::
  [
    "test_sum1" >:: test_sum1;
    "test_mul1" >:: test_mul1;
    "test_intersect1" >:: test_intersect1;
    "test_intersect2" >:: test_intersect2;
    "test_quotient1" >:: test_quotient1;
    "test_quotient2" >:: test_quotient2;
    "test_smallest_int1" >:: test_smallest_int1;
    "test_smallest_int2" >:: test_smallest_int2;
    "test_frac_quotient1" >:: test_frac_quotient1;
    "test_frac_quotient2" >:: test_frac_quotient2;
    "test_frac_quotient3" >:: test_frac_quotient3;
    "test_overorder1" >:: test_overorder1;
    "test_overorder2" >:: test_overorder2;
    "test_factor_refinement" >:: test_factor_refinement;
    "test_factor" >:: test_factor;
    "test_unit_find" >:: test_unit_find
  ]
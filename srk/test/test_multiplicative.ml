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

module SqrtNeg5 = Multiplicative.MakeOrder(
  struct 
    let rank = 2 
    let mult i j = 
      if i = 0 && j = 0 then
        [|ZZ.zero; ZZ.of_int (-5)|] 
      else if (i = 1 && j = 0) || (i=0 && j = 1) then
        [|ZZ.one; ZZ.zero|]
      else
        [|ZZ.zero; ZZ.one|]
  end)

let assert_equal_ideal p q =
  assert_equal ~cmp:SqrtNeg5.equal_i ~printer:(SrkUtil.mk_show SqrtNeg5.pp_i) p q

let assert_equal_frac_ideal p q =
  assert_equal ~cmp:SqrtNeg5.equal ~printer:(SrkUtil.mk_show SqrtNeg5.pp) p q

let pp_zv f v = ZZM.pp (ZZ.pp) f (zzmify [|v|])


let test_hnf () = 
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
  assert_equal_ideal corr one_plus_sqrt_mfive


let test_sum1 () = 
  let two = SqrtNeg5.ideal_generated_by (zzify_v [|0; 2|]) in
  let one_plus_sqrt_mfive = SqrtNeg5.ideal_generated_by (zzify_v [|1; 1|]) in
  let s = SqrtNeg5.sum_i two one_plus_sqrt_mfive in
  let s_corr = SqrtNeg5.idealify (zzify [|
    [|1; 1|];
    [|0; 2|]
  |]) in
  assert_equal_ideal s_corr s


let test_mul1 () = 
  let six = SqrtNeg5.ideal_generated_by (zzify_v [|0;6|]) in
  let one_plus_sqrt_m5 = SqrtNeg5.ideal_generated_by (zzify_v [|1;1|]) in
  let one_minus_sqrt_m5 = SqrtNeg5.ideal_generated_by (zzify_v [|-1;1|]) in
  assert_equal_ideal six (SqrtNeg5.mul_i one_plus_sqrt_m5 one_minus_sqrt_m5)

let test_intersect1 () = 
  let six = SqrtNeg5.ideal_generated_by (zzify_v [|0;6|]) in
  let one_plus_sqrt_m5 = SqrtNeg5.ideal_generated_by (zzify_v [|1;1|]) in
  let i = SqrtNeg5.intersect_i six one_plus_sqrt_m5 in
  assert_equal_ideal six i

let test_intersect2 () = 
  let two = SqrtNeg5.ideal_generated_by (zzify_v [|0;2|]) in
  let one_plus_sqrt_m5 = SqrtNeg5.ideal_generated_by (zzify_v [|1;1|]) in
  let i = SqrtNeg5.intersect_i two one_plus_sqrt_m5 in
  let i_corr = SqrtNeg5.idealify (zzify [|
    [|2; 2|];
    [|0; 6|]
  |]) in
  assert_equal_ideal i_corr i

let test_quotient1 () = 
  let six = SqrtNeg5.ideal_generated_by (zzify_v [|0;6|]) in
  let one_plus_sqrt_m5 = SqrtNeg5.ideal_generated_by (zzify_v [|1;1|]) in
  let i = SqrtNeg5.quotient_i six one_plus_sqrt_m5 in
  let one_minus_sqrt_m5 = SqrtNeg5.ideal_generated_by (zzify_v [|-1;1|]) in
  assert_equal_ideal one_minus_sqrt_m5 i

let test_quotient2 () = 
  let three = SqrtNeg5.ideal_generated_by (zzify_v [|0;3|]) in
  let one_plus_sqrt_m5 = SqrtNeg5.ideal_generated_by (zzify_v [|1;1|]) in
  let i = SqrtNeg5.quotient_i three one_plus_sqrt_m5 in
  let i_corr = SqrtNeg5.idealify (zzify [|
    [|1; 2|];
    [|0; 3|]
  |]) in
  assert_equal_ideal i_corr i

let test_smallest_int1 () = 
  let three = SqrtNeg5.ideal_generated_by (zzify_v [|0;3|]) in
  assert_equal ~cmp:(ZZ.equal) ~printer:(ZZ.show) (ZZ.of_int 3) (SqrtNeg5.get_smallest_int three)

let test_smallest_int2 () = 
  let one_plus_sqrt_m5 = SqrtNeg5.ideal_generated_by (zzify_v [|1;1|]) in
  assert_equal ~cmp:(ZZ.equal) ~printer:(ZZ.show) (ZZ.of_int 6) (SqrtNeg5.get_smallest_int one_plus_sqrt_m5)

let test_frac_quotient1 () = 
  let three = SqrtNeg5.make_frac_ideal ZZ.one (SqrtNeg5.ideal_generated_by (zzify_v [|0;3|])) in
  let one_plus_sqrt_m5 = SqrtNeg5.make_frac_ideal ZZ.one (SqrtNeg5.ideal_generated_by (zzify_v [|1;1|])) in
  let one_minus_sqrt_m5_over_2 = SqrtNeg5.make_frac_ideal (ZZ.of_int 2) (SqrtNeg5.ideal_generated_by (zzify_v [|-1;1|])) in
  assert_equal_frac_ideal one_minus_sqrt_m5_over_2 (SqrtNeg5.quotient three one_plus_sqrt_m5);
  (*This assertion should hold because Z[sqrt(-5)] is the ring of integers*)
  assert_equal_frac_ideal three (SqrtNeg5.mul one_minus_sqrt_m5_over_2 one_plus_sqrt_m5)
  
let test_frac_quotient2 () = 
  let six = SqrtNeg5.make_frac_ideal ZZ.one (SqrtNeg5.ideal_generated_by (zzify_v [|0;6|])) in
  let one_plus_sqrt_m5 = SqrtNeg5.make_frac_ideal ZZ.one (SqrtNeg5.ideal_generated_by (zzify_v [|1;1|])) in
  let one_minus_sqrt_m5 = SqrtNeg5.make_frac_ideal (ZZ.of_int 1) (SqrtNeg5.ideal_generated_by (zzify_v [|-1;1|])) in
  assert_equal_frac_ideal one_minus_sqrt_m5 (SqrtNeg5.quotient six one_plus_sqrt_m5);
  (*This assertion should hold because Z[sqrt(-5)] is the ring of integers*)
  assert_equal_frac_ideal six (SqrtNeg5.mul one_minus_sqrt_m5 one_plus_sqrt_m5)

let test_frac_quotient3 () = 
  let one = SqrtNeg5.make_frac_ideal ZZ.one (SqrtNeg5.ideal_generated_by (zzify_v [|0;1|])) in
  let one_plus_sqrt_m5 = SqrtNeg5.make_frac_ideal ZZ.one (SqrtNeg5.ideal_generated_by (zzify_v [|1;1|])) in
  let one_minus_sqrt_m5_over_6 = SqrtNeg5.make_frac_ideal (ZZ.of_int 6) (SqrtNeg5.ideal_generated_by (zzify_v [|-1;1|])) in
  assert_equal_frac_ideal one_minus_sqrt_m5_over_6 (SqrtNeg5.quotient one one_plus_sqrt_m5);
  (*This assertion should hold because Z[sqrt(-5)] is the ring of integers*)
  assert_equal_frac_ideal one (SqrtNeg5.mul one_minus_sqrt_m5_over_6 one_plus_sqrt_m5)


  
let test_overorder1 () = 
  let one_plus_sqrt_m5 = SqrtNeg5.make_frac_ideal ZZ.one (SqrtNeg5.ideal_generated_by (zzify_v [|1;1|])) in
  let overorder, invertible = SqrtNeg5.compute_overorder SqrtNeg5.one one_plus_sqrt_m5 in
  assert_equal_frac_ideal SqrtNeg5.one overorder;
  assert_equal_frac_ideal one_plus_sqrt_m5 invertible
  
let test_factor_refinement () = 
  let six = SqrtNeg5.make_frac_ideal ZZ.one (SqrtNeg5.ideal_generated_by (zzify_v [|0;6|])) in
  let one_plus_sqrt_m5 = SqrtNeg5.make_frac_ideal ZZ.one (SqrtNeg5.ideal_generated_by (zzify_v [|1;1|])) in
  let one_minus_sqrt_m5 = SqrtNeg5.make_frac_ideal (ZZ.of_int 1) (SqrtNeg5.ideal_generated_by (zzify_v [|-1;1|])) in
  let c, gcd_basis = SqrtNeg5.factor_refinement [six; one_plus_sqrt_m5; one_minus_sqrt_m5] in
  (*let print_factor f (j, e) = 
    SqrtNeg5.pp f j;
    Format.fprintf f "@[^%d@]" e
  in
  let print_list = Format.pp_print_list ~pp_sep:(Format.pp_print_newline) print_factor in
  Log.log ~level:`always "Factors";
  Log.log_pp ~level:`always print_list gcd_basis;*)
  let multiplied_rhs = List.fold_left (fun acc (factor, deg) -> SqrtNeg5.mul acc (SqrtNeg5.exp deg factor)) (SqrtNeg5.one) gcd_basis in
  let multiplied_lhs = List.fold_left SqrtNeg5.mul c [six; one_plus_sqrt_m5; one_minus_sqrt_m5] in
  assert_equal_frac_ideal multiplied_rhs multiplied_lhs

let test_factor () = 
  let six = SqrtNeg5.make_frac_ideal ZZ.one (SqrtNeg5.ideal_generated_by (zzify_v [|0;6|])) in
  let one_plus_sqrt_m5 = SqrtNeg5.make_frac_ideal ZZ.one (SqrtNeg5.ideal_generated_by (zzify_v [|1;1|])) in
  let one_minus_sqrt_m5 = SqrtNeg5.make_frac_ideal (ZZ.of_int 1) (SqrtNeg5.ideal_generated_by (zzify_v [|-1;1|])) in
  let exp_list, gcd_basis, overorder = SqrtNeg5.compute_factorization [six; one_plus_sqrt_m5; one_minus_sqrt_m5] in
  let check_factor i ideal = 
    let exp_list = List.nth exp_list i in
    let rhs = List.fold_left SqrtNeg5.mul SqrtNeg5.one (List.map2 SqrtNeg5.exp exp_list gcd_basis) in
    let lhs = SqrtNeg5.mul ideal overorder in
    assert_equal_frac_ideal lhs rhs
  in
  List.iteri check_factor [six; one_plus_sqrt_m5; one_minus_sqrt_m5]


let test_unit_find () = 
  let six = zzify_v [|0;6|] in
  let one_plus_sqrt_m5 = zzify_v [|1;1|] in
  let one_minus_sqrt_m5 = zzify_v [|-1;1|] in
  let exp_list = SqrtNeg5.find_unit_basis [six; one_plus_sqrt_m5; one_minus_sqrt_m5] in
  assert_equal 1 (List.length exp_list);
  let unit_exp = List.hd exp_list in
  let open QQXInfix in
  let module NF = NumberField.MakeNF(struct let min_poly = v * v + int(5) end) in
  let six_e = NF.make_elem (int(6)) in
  let one_plus_sqrt_m5_e = NF.make_elem (int(1) + v) in
  let one_minus_sqrt_m5_e = NF.make_elem (int(1) - v) in
  let exp = List.map2 NF.exp [six_e; one_plus_sqrt_m5_e; one_minus_sqrt_m5_e] unit_exp in
  let prod = List.fold_left NF.mul NF.one exp in
  assert_bool "Looking for unit" (NF.equal prod NF.one)

module Sqrt5 = Multiplicative.MakeOrder(
  struct 
    let rank = 2 
    let mult i j = 
      if i = 0 && j = 0 then
        [|ZZ.zero; ZZ.of_int 5|] 
      else if (i = 1 && j = 0) || (i=0 && j = 1) then
        [|ZZ.one; ZZ.zero|]
      else
        [|ZZ.zero; ZZ.one|]
  
  end)

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


let suite = "Multiplicative" >:::
  [
    "test_ideal_create1" >:: test_ideal_create1;
    "test_hnf" >:: test_hnf;
    "test_ideal_create2" >:: test_ideal_create2;
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
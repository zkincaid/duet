open OUnit
open Srk
open Polynomial

module QQXInfix = struct
  let ( + ) = QQX.add
  let ( - ) = QQX.sub
  let ( * ) = QQX.mul
  let int k = QQX.scalar (QQ.of_int k)
  let rat n d = Polynomial.QQX.scalar (QQ.of_frac n d)
  let v = QQX.identity
end

module QQXsInfix = struct
  let ( + ) = QQXs.add
  let ( - ) = QQXs.sub
  let ( * ) = QQXs.mul
  let int k = QQXs.scalar (QQ.of_int k)
  let dim k = QQXs.of_dim (Char.code k)
end


let int_poly_test1 () = 
  let open QQXInfix in
  let module N = NumberField.MakeNF (struct
    let min_poly = v * v + (rat 3 4) * v + (rat 1 3)
  end) in
  assert_equal ~cmp:(Polynomial.QQX.equal) ~printer:(SrkUtil.mk_show Polynomial.QQX.pp) (v * v + int(9) * v + int(48)) N.int_poly

let min_poly_test1 () = 
  let open QQXInfix in
  let p = v * v - int(2) in
  let module NF = NumberField.MakeNF(struct let min_poly = p end) in
  assert_equal ~cmp:(Polynomial.QQX.equal) ~printer:(SrkUtil.mk_show Polynomial.QQX.pp) p (NF.compute_min_poly (NF.make_elem v))

let inverse_test1 () = 
  let open QQXInfix in
  let p = v * v - int(2) in
  let module NF = NumberField.MakeNF(struct let min_poly = p end) in
  let e1 = NF.make_elem v in
  let e2 = NF.make_elem (int(2)*v - int(1)) in
  let e1_inv = NF.inverse e1 in
  let e2_inv = NF.inverse e2 in
  assert_equal NF.one (NF.mul e1 e1_inv);
  assert_equal NF.one (NF.mul e2 e2_inv)

let primitive_test1 () = 
  let open QQXInfix in
  let p1 = v * v - int(2) in
  let p2 = v * v - int(3) in
  let p1x = NumberField.make_multivariate (Char.code 'x') p1 in
  let p2y = NumberField.make_multivariate (Char.code 'y') p2 in
  let (prim, x_in_prim, y_in_prim) = NumberField.primitive_elem 4 p1x p2y (Char.code 'x') (Char.code 'y') in
  let module NF = NumberField.MakeNF(struct let min_poly = prim end) in
  let p1r_in_NF = NF.make_elem x_in_prim in
  let p2r_in_NF = NF.make_elem y_in_prim in
  (*Log.log ~level:`always "x in new field:";
  Log.log_pp ~level:`always NF.pp p1r_in_NF;
  Log.log ~level:`always "y in new field:";
  Log.log_pp ~level:`always NF.pp p2r_in_NF;*)
  let eval_1_res = NF.X.eval (NF.X.lift p1) p1r_in_NF in
  let eval_2_res = NF.X.eval (NF.X.lift p2) p2r_in_NF in
  (*Log.log ~level:`always "eval_1_res in new field:";
  Log.log_pp ~level:`always NF.pp eval_1_res;
  Log.log ~level:`always "eval_2_res in new field:";
  Log.log_pp ~level:`always NF.pp eval_2_res;*)
  assert_equal 4 (QQX.order prim);
  assert_bool "Root of p1 is still a root of p1" (NF.is_zero eval_1_res);
  assert_bool "Root of p2 is still a root of p2" (NF.is_zero eval_2_res)

let primitive_test2 () = 
  let open QQXInfix in
  let p1 = v * v * v - int(2) in
  let p2 = v * v * v * v * v * v + int(108) in
  let p1x = NumberField.make_multivariate (Char.code 'x') p1 in
  let p2y = NumberField.make_multivariate (Char.code 'y') p2 in
  let (prim, x_in_prim, y_in_prim) = NumberField.primitive_elem 18 p1x p2y (Char.code 'x') (Char.code 'y') in
  let module NF = NumberField.MakeNF(struct let min_poly = prim end) in
  let p1r_in_NF = NF.make_elem x_in_prim in
  let p2r_in_NF = NF.make_elem y_in_prim in
  let eval_1_res = NF.X.eval (NF.X.lift p1) p1r_in_NF in
  let eval_2_res = NF.X.eval (NF.X.lift p2) p2r_in_NF in
  assert_equal 18 (QQX.order prim);
  assert_bool "Root of p1 is still a root of p1" (NF.is_zero eval_1_res);
  assert_bool "Root of p2 is still a root of p2" (NF.is_zero eval_2_res)


  
let factor_test1 () = 
  let open QQXInfix in
  let module NF = NumberField.MakeNF(struct let min_poly = v * v * v - int(2) end) in
  let p = NF.X.lift (v * v * v - int(2)) in
  let (c, factors) = NF.X.factor p in
  (*let print_factor f (fact, deg) = 
    if deg = 1 then
      NF.pp f fact
    else
      (Format.pp_print_string f "("; NF.pp f fact; Format.pp_print_string f ")^"; Format.pp_print_int f deg)
  in
  let print_factors f = Format.pp_print_list ~pp_sep:(fun fo () -> Format.pp_print_string fo "; ") print_factor f in*)
  let multiplied = List.fold_left (fun acc (factor, deg) -> NF.X.mul acc (NF.X.exp factor deg)) (NF.X.scalar c) factors in
  (*Log.log ~level:`always "Factors";
  Log.log_pp ~level:`always print_factors factors;
  Log.log ~level:`always "Multiplied factors";
  Log.log_pp ~level:`always NF.pp multiplied;*)
  assert_equal 2 (List.length factors);
  assert_bool "Multiplied factor equals" (NF.X.equal multiplied p)

let factor_test2 () = 
  let open QQXInfix in
  let module NF = NumberField.MakeNF(struct let min_poly = v * v * v * v * v * v + int(108) end) in
  let p = NF.X.lift (v * v * v - int(2)) in
  let (c, factors) = NF.X.factor p in
  (*let print_factor f (fact, deg) = 
    if deg = 1 then
      NF.PNF.pp f fact
    else
      (Format.pp_print_string f "("; NF.PNF.pp f fact; Format.pp_print_string f ")^"; Format.pp_print_int f deg)
  in
  let print_factors f = Format.pp_print_list ~pp_sep:(fun fo () -> Format.pp_print_string fo "; ") print_factor f in*)
  let multiplied = List.fold_left (fun acc (factor, deg) -> NF.X.mul acc (NF.X.exp factor deg)) (NF.X.scalar c) factors in
  (*Log.log ~level:`always "Factors";
  Log.log_pp ~level:`always print_factors factors;
  Log.log ~level:`always "Multiplied factors";
  Log.log_pp ~level:`always NF.PNF.pp multiplied;*)
  assert_equal 3 (List.length factors);
  assert_bool "Multiplied factor equals" (NF.X.equal multiplied p)

let factor_test3 () = 
  let open QQXInfix in
  let module NF = NumberField.MakeNF(struct let min_poly = int(0) end) in
  let p = NF.X.lift (v * v - int(4)*v + int(3)) in
  let (c, factors) = NF.X.factor p in
  (*let print_factor f (fact, deg) = 
    if deg = 1 then
      NF.X.pp f fact
    else
      (Format.pp_print_string f "("; NF.X.pp f fact; Format.pp_print_string f ")^"; Format.pp_print_int f deg)
  in
  let print_factors f = Format.pp_print_list ~pp_sep:(fun fo () -> Format.pp_print_string fo "; ") print_factor f in*)
  let multiplied = List.fold_left (fun acc (factor, deg) -> NF.X.mul acc (NF.X.exp factor deg)) (NF.X.scalar c) factors in
  (*Log.log ~level:`always "Factors";
  Log.log_pp ~level:`always print_factors factors;
  Log.log ~level:`always "Multiplied factors";
  Log.log_pp ~level:`always NF.X.pp multiplied;*)
  assert_equal 2 (List.length factors);
  assert_bool "Multiplied factor equals" (NF.X.equal multiplied p)

let splitting_test1 () =
  let open QQXInfix in
  let p = v * v * v - int(2) in
  let NumberField.Sf ((module NF), roots) = NumberField.splitting_field p in
  (*let print_roots f rs = Format.pp_print_list ~pp_sep:(fun fo () -> Format.pp_print_string fo "; ") NF.pp f (List.map fst rs) in
  Log.log ~level:`always "Field polynomial";
  Log.log_pp ~level:`always QQX.pp root_field;
  Log.log ~level:`always "Roots";
  Log.log_pp ~level:`always print_roots roots;*)
  let check_root (r, _) = 
    assert_bool "Test root" (NF.is_zero (NF.X.eval (NF.X.lift p) r))
  in
  List.iter check_root roots


let zzify = Array.map (Array.map ZZ.of_int)


module ZZM = Ring.MakeMatrix(ZZ)

module SqrtNeg5F = NumberField.MakeNF(struct
  let min_poly = 
    let open QQXInfix in
    v * v + int(5)
end)

module SqrtNeg5 = SqrtNeg5F.O


let assert_equal_ideal p q =
  assert_equal ~cmp:SqrtNeg5.equal_i ~printer:(SrkUtil.mk_show SqrtNeg5.pp_i) p q

let assert_equal_frac_ideal p q =
  assert_equal ~cmp:SqrtNeg5.equal ~printer:(SrkUtil.mk_show SqrtNeg5.pp) p q


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
  
let test_factor_refinement1 () = 
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

let test_factor1 () = 
  let open QQXInfix in
  let six = SqrtNeg5.make_frac_ideal ZZ.one (make_ideal_sqrt_neg_5 (int(6))) in
  let one_plus_sqrt_m5 = SqrtNeg5.make_frac_ideal ZZ.one (make_ideal_sqrt_neg_5 (int(1) + v))  in
  let one_minus_sqrt_m5 = SqrtNeg5.make_frac_ideal (ZZ.of_int 1) (make_ideal_sqrt_neg_5 (int(1) - v)) in
  let exp_list, gcd_basis, overorder = SqrtNeg5.compute_factorization [six; one_plus_sqrt_m5; one_minus_sqrt_m5] in
  let check_factor i ideal = 
    let exp_list = List.nth exp_list i in
    if SqrtNeg5.equal ideal SqrtNeg5.one then
      assert_bool "Non-proper ideal is basis to zero'th power" (List.for_all ((=) 0) exp_list)
    else
      let rhs = List.fold_left SqrtNeg5.mul SqrtNeg5.one (List.map2 SqrtNeg5.exp gcd_basis exp_list) in
      let lhs = SqrtNeg5.mul ideal overorder in
    assert_equal_frac_ideal lhs rhs
  in
  List.iteri check_factor [six; one_plus_sqrt_m5; one_minus_sqrt_m5]


(*let test_unit_find1 () = 
  let open QQXInfix in
  let six = SqrtNeg5F.make_elem (int(6)) in
  let one_plus_sqrt_m5 = SqrtNeg5F.make_elem (int(1)+v) in
  let one_minus_sqrt_m5 = SqrtNeg5F.make_elem (int(1)-v) in
  let exp_list = SqrtNeg5F.find_unit_basis [six; one_plus_sqrt_m5; one_minus_sqrt_m5] in
  assert_equal 1 (List.length exp_list);
  let unit_exp = List.hd exp_list in
  let exp = List.map2 SqrtNeg5F.exp [six; one_plus_sqrt_m5; one_minus_sqrt_m5] unit_exp in
  let prod = List.fold_left SqrtNeg5F.mul SqrtNeg5F.one exp in
  assert_equal ~cmp:SqrtNeg5F.equal ~printer:(SrkUtil.mk_show SqrtNeg5F.pp) SqrtNeg5F.one prod


let test_unit_find2 () = 
  let open QQXInfix in
  let module NF = NumberField.MakeNF(struct let min_poly = QQX.zero end) in
  let two = NF.make_elem (int(2)) in
  let three_fourths = NF.make_elem (rat 3 4) in
  let nine_eighths = NF.make_elem (rat 9 8) in
  let exp_list = NF.find_unit_basis [two; three_fourths; nine_eighths] in
  assert_equal 1 (List.length exp_list);
  let unit_exp = List.hd exp_list in
  let exp = List.map2 NF.exp [two; three_fourths; nine_eighths] unit_exp in
  let prod = List.fold_left NF.mul NF.one exp in
  assert_equal ~cmp:NF.equal ~printer:(SrkUtil.mk_show NF.pp) NF.one prod*)

module Sqrt5F = NumberField.MakeNF(struct
  let min_poly = 
    let open QQXInfix in
    v * v - int(5)
end)

module Sqrt5 = Sqrt5F.O

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


let test_make_order () = 
  let open QQXInfix in
  let module N = NumberField.MakeNF(struct
    let min_poly = int(4) * v * v + int(5)
  end) in
  let sqrt5_over_2 = N.make_elem (v) in
  let d, o = N.O.make_o_el sqrt5_over_2 in
  let back_as_el = N.O.order_el_to_f_elem (d, o) in
  assert_equal ~cmp:(ZZ.equal) ~printer:(ZZ.show) (ZZ.of_int 4) d;
  assert_equal ~cmp:(N.equal) ~printer:(SrkUtil.mk_show N.pp) sqrt5_over_2 back_as_el
 
let test_factor_refinement2 () = 
  let open QQXInfix in
  let two_o = (snd (Sqrt5.make_o_el (Sqrt5F.make_elem (int(2))))) in
  let minus_one_o = (snd (Sqrt5.make_o_el (Sqrt5F.make_elem (int(-1))))) in
  let one_plus_sqrt_5_o = (snd (Sqrt5.make_o_el (Sqrt5F.make_elem (int(1) + v)))) in
  let one_minus_sqrt_5_o = (snd (Sqrt5.make_o_el (Sqrt5F.make_elem (int(1) - v)))) in
  let two_i = Sqrt5.make_frac_ideal ZZ.one (Sqrt5.ideal_generated_by two_o) in
  let minus_one_i = Sqrt5.make_frac_ideal ZZ.one (Sqrt5.ideal_generated_by minus_one_o) in
  let one_plus_sqrt_5_i = Sqrt5.make_frac_ideal ZZ.one (Sqrt5.ideal_generated_by one_plus_sqrt_5_o) in
  let one_minus_sqrt_5_i = Sqrt5.make_frac_ideal ZZ.one (Sqrt5.ideal_generated_by one_minus_sqrt_5_o) in
  let c, gcd_basis = Sqrt5.factor_refinement [minus_one_i; one_plus_sqrt_5_i; one_minus_sqrt_5_i; two_i] in
  (*let print_factor f (j, e) = 
    Sqrt5.pp f j;
    Format.fprintf f "@[^%d@]" e
  in
  let print_list = Format.pp_print_list ~pp_sep:(Format.pp_print_newline) print_factor in
  Log.log ~level:`always "Overorder";
  Log.log_pp ~level:`always Sqrt5.pp c;
  Log.log ~level:`always "Factors";
  Log.log_pp ~level:`always print_list gcd_basis;*)
  let multiplied_rhs = List.fold_left (fun acc (factor, deg) -> Sqrt5.mul acc (Sqrt5.exp factor deg)) (Sqrt5.one) gcd_basis in
  let multiplied_lhs = List.fold_left Sqrt5.mul c [minus_one_i; one_plus_sqrt_5_i; one_minus_sqrt_5_i; two_i] in
  assert_equal_frac_ideal multiplied_rhs multiplied_lhs


let test_factor2 () = 
  let open QQXInfix in
  let two_o = (snd (Sqrt5.make_o_el (Sqrt5F.make_elem (int(2))))) in
  let minus_one_o = (snd (Sqrt5.make_o_el (Sqrt5F.make_elem (int(-1))))) in
  let one_plus_sqrt_5_o = (snd (Sqrt5.make_o_el (Sqrt5F.make_elem (int(1) + v)))) in
  let one_minus_sqrt_5_o = (snd (Sqrt5.make_o_el (Sqrt5F.make_elem (int(1) - v)))) in
  let two_i = Sqrt5.make_frac_ideal ZZ.one (Sqrt5.ideal_generated_by two_o) in
  let minus_one_i = Sqrt5.make_frac_ideal ZZ.one (Sqrt5.ideal_generated_by minus_one_o) in
  let one_plus_sqrt_5_i = Sqrt5.make_frac_ideal ZZ.one (Sqrt5.ideal_generated_by one_plus_sqrt_5_o) in
  let one_minus_sqrt_5_i = Sqrt5.make_frac_ideal ZZ.one (Sqrt5.ideal_generated_by one_minus_sqrt_5_o) in
  let exp_list, gcd_basis, overorder = Sqrt5.compute_factorization [two_i; minus_one_i; one_plus_sqrt_5_i; one_minus_sqrt_5_i] in
  let check_factor i ideal = 
    let exp_list = List.nth exp_list i in
    if Sqrt5.equal ideal Sqrt5.one then
      assert_bool "Non-proper ideal is basis to zero'th power" (List.for_all ((=) 0) exp_list)
    else
      let rhs = List.fold_left Sqrt5.mul Sqrt5.one (List.map2 Sqrt5.exp gcd_basis exp_list) in
      let lhs = Sqrt5.mul ideal overorder in
    assert_equal_frac_ideal lhs rhs
  in
  List.iteri check_factor [two_i; minus_one_i; one_plus_sqrt_5_i; one_minus_sqrt_5_i] 

(*let test_unit_find3 () = 
  let open QQXInfix in
  let minus_one = Sqrt5F.make_elem (int(-1)) in
  let one_plus_sqrt_5_over_2 = Sqrt5F.make_elem ((rat 1 2) + (rat 1 2) * v) in
  let one_minus_sqrt_5_over_2 = Sqrt5F.make_elem ((rat 1 2) - (rat 1 2) * v) in
  let exp_list = Sqrt5F.find_unit_basis [minus_one; one_plus_sqrt_5_over_2; one_minus_sqrt_5_over_2] in
  assert_equal 3 (List.length exp_list);
  let check_unit e =
    let e_inv = Sqrt5F.inverse e in
    let e_min_poly = Sqrt5F.compute_min_poly e in
    let e_inv_min_poly = Sqrt5F.compute_min_poly e_inv in
    let is_monic_int_poly p =
      let lc = QQX.coeff (QQX.order p) p in
      let is_int = QQX.fold (fun _ c b -> (ZZ.equal (QQ.denominator c) ZZ.one) && b) p true in
      QQ.equal lc QQ.one && is_int
    in
    assert_bool "e min poly is monic int poly" (is_monic_int_poly e_min_poly);
    assert_bool "e inv min poly is monic int poly" (is_monic_int_poly e_inv_min_poly);
  in
  let units = List.map (
    fun e_l ->
      List.fold_left2 (
        fun acc elem e ->
          Sqrt5F.mul acc (Sqrt5F.exp elem e)
      ) Sqrt5F.one [minus_one; one_plus_sqrt_5_over_2; one_minus_sqrt_5_over_2] e_l    
    ) exp_list in
  List.iter check_unit units

let test_unit_relations1 () = 
  let open QQXInfix in
  let minus_one = Sqrt5F.make_elem (int(-1)) in
  let one_plus_sqrt_5_over_2 = Sqrt5F.make_elem ((rat 1 2) + (rat 1 2) * v) in
  let one_minus_sqrt_5_over_2 = Sqrt5F.make_elem ((rat 1 2) - (rat 1 2) * v) in
  let relations = Sqrt5F.find_relations_of_units [minus_one; one_plus_sqrt_5_over_2; one_minus_sqrt_5_over_2] in
  assert_equal ~printer:(string_of_int) 2 (List.length relations);
  let res = List.fold_left2 (
    fun acc elem e ->
      Sqrt5F.mul acc (Sqrt5F.exp elem e)
  ) Sqrt5F.one [minus_one; one_plus_sqrt_5_over_2; one_minus_sqrt_5_over_2] (List.hd relations)   
  in
  assert_equal ~cmp:Sqrt5F.equal ~printer:(SrkUtil.mk_show Sqrt5F.pp) Sqrt5F.one res*)


let test_find_relations1 () = 
  let open QQXInfix in
  let minus_one = Sqrt5F.make_elem (int(-1)) in
  let one_plus_sqrt_5_over_2 = Sqrt5F.make_elem ((rat 1 2) + (rat 1 2) * v) in
  let one_minus_sqrt_5_over_2 = Sqrt5F.make_elem ((rat 1 2) - (rat 1 2) * v) in
  let relations = Sqrt5F.find_relations [minus_one; one_plus_sqrt_5_over_2; one_minus_sqrt_5_over_2] in
  assert_equal ~printer:(string_of_int) 2 (List.length relations);
  let res = List.fold_left2 (
    fun acc elem e ->
      Sqrt5F.mul acc (Sqrt5F.exp elem e)
  ) Sqrt5F.one [minus_one; one_plus_sqrt_5_over_2; one_minus_sqrt_5_over_2] (List.hd relations)   
  in
  assert_equal ~cmp:Sqrt5F.equal ~printer:(SrkUtil.mk_show Sqrt5F.pp) Sqrt5F.one res

let test_find_relations2 () = 
  let open QQXInfix in
  let six = SqrtNeg5F.make_elem (int(6)) in
  let one_plus_sqrt_m5 = SqrtNeg5F.make_elem (int(1)+v) in
  let one_minus_sqrt_m5 = SqrtNeg5F.make_elem (int(1)-v) in
  let exp_list = SqrtNeg5F.find_relations [six; one_plus_sqrt_m5; one_minus_sqrt_m5] in
  assert_equal ~printer:(string_of_int) 1 (List.length exp_list);
  let unit_exp = List.hd exp_list in
  let exp = List.map2 SqrtNeg5F.exp [six; one_plus_sqrt_m5; one_minus_sqrt_m5] unit_exp in
  let prod = List.fold_left SqrtNeg5F.mul SqrtNeg5F.one exp in
  assert_equal ~cmp:SqrtNeg5F.equal ~printer:(SrkUtil.mk_show SqrtNeg5F.pp) SqrtNeg5F.one prod


let test_find_relations3 () = 
  let open QQXInfix in
  let module NF = NumberField.MakeNF(struct let min_poly = QQX.zero end) in
  let two = NF.make_elem (int(2)) in
  let three_fourths = NF.make_elem (rat 3 4) in
  let nine_eighths = NF.make_elem (rat 9 8) in
  let exp_list = NF.find_relations [two; three_fourths; nine_eighths] in
  assert_equal ~printer:(string_of_int) 1 (List.length exp_list);
  let unit_exp = List.hd exp_list in
  let exp = List.map2 NF.exp [two; three_fourths; nine_eighths] unit_exp in
  let prod = List.fold_left NF.mul NF.one exp in
  assert_equal ~cmp:NF.equal ~printer:(SrkUtil.mk_show NF.pp) NF.one prod

let find_root_relations1 () =
  let open QQXInfix in
  let p = v * v * v - int(2) in
  let NumberField.Sf ((module NF), roots) = NumberField.splitting_field p in
  (*let print_roots f rs = Format.pp_print_list ~pp_sep:(fun fo () -> Format.pp_print_string fo "; ") NF.pp f (List.map fst rs) in
  Log.log ~level:`always "Field polynomial";
  Log.log_pp ~level:`always QQX.pp root_field;
  Log.log ~level:`always "Roots";
  Log.log_pp ~level:`always print_roots roots;*)
  let roots_e = fst (List.split roots) in
  let relations = NF.find_relations roots_e in
  let check_relation rel = 
    let prod = List.fold_left NF.mul NF.one (List.map2 NF.exp roots_e rel) in
    assert_equal ~cmp:NF.equal ~printer:(SrkUtil.mk_show NF.pp) NF.one prod
  in
  List.iter check_relation relations

let find_root_relations2 () =
  (*Log.set_verbosity_level "srk.numberField" `trace;*)
  let open QQXInfix in
  (* p = (x-2)(x^2+1)(x^3-2)*)
  let p = v * v * v * v * v * v - int(2) * v* v*v *v *v + v*v*v*v - int(4)*v*v*v +int(4)*v*v-int(2)*v + int(4) in
  let NumberField.Sf ((module NF), roots) = NumberField.splitting_field p in
  let roots_e = fst (List.split roots) in
  (*Log.log ~level:`always "Root_field";
  Log.log_pp ~level:`always QQX.pp NF.int_poly;
  let print_roots = Format.pp_print_list ~pp_sep:(fun fo () -> Format.pp_print_newline fo ()) NF.pp in
  Log.log ~level:`always "Roots";
  Log.log_pp ~level:`always print_roots roots_e;*)
  let relations = NF.find_relations roots_e in
  let check_relation rel = 
    let prod = List.fold_left NF.mul NF.one (List.map2 NF.exp roots_e rel) in
    assert_equal ~cmp:NF.equal ~printer:(SrkUtil.mk_show NF.pp) NF.one prod
  in
  List.iter check_relation relations(*;
  Log.log ~level:`always "Root relations";
  Log.log_pp ~level:`always (ZZM.pp ZZ.pp) (ZZM.of_dense (zzify (Array.of_list (List.map (Array.of_list) relations))))*)

let suite = "NumberField" >:::
  [
    "int_poly_test1" >:: int_poly_test1;
    "min_poly_test1" >:: min_poly_test1;
    "inverse_test1" >:: inverse_test1;
    "primitive_test1" >:: primitive_test1;
    "primitive_test2" >:: primitive_test2;
    "factor_test1" >:: factor_test1;
    "factor_test2" >:: factor_test2;
    "factor_test3" >:: factor_test3;
    "splitting_test1" >:: splitting_test1;
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
    "test_factor_refinement1" >:: test_factor_refinement1;
    "test_factor1" >:: test_factor1;
    "test_factor_refinement2" >:: test_factor_refinement2;
    "test_factor2" >:: test_factor2;
    "test_make_order" >:: test_make_order;
    "test_find_relations1" >:: test_find_relations1;
    "test_find_relations2" >:: test_find_relations2;
    "test_find_relations3" >:: test_find_relations3;
    "find_root_relations1" >:: find_root_relations1;
    (*"find_root_relations2" >:: find_root_relations2;*) (*This one's a bit expensive ~ 3 min.*)
  ]
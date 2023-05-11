open OUnit
open Srk
open Polynomial

module QQXInfix = struct
  let ( + ) = QQX.add
  let ( - ) = QQX.sub
  let ( * ) = QQX.mul
  let int k = QQX.scalar (QQ.of_int k)
  let v = QQX.identity
end

let primitive_test1 () = 
  let open QQXInfix in
  let p1 = v * v - int(2) in
  let p2 = v * v - int(3) in
  let (prim, p1r, p2r) = NumberField.primitive_elem p1 p2 in
  let module NF = NumberField.MakeNF(struct let min_poly = prim end) in
  let p1r_in_NF = NF.make_elem p1r in
  let p2r_in_NF = NF.make_elem p2r in
  let eval_1_res = NF.PNF.eval (NF.PNF.lift p1) p1r_in_NF in
  let eval_2_res = NF.PNF.eval (NF.PNF.lift p2) p2r_in_NF in
  assert_equal 4 (QQX.order prim);
  assert_bool "Root of p1 is still a root of p1" (NF.is_zero eval_1_res);
  assert_bool "Root of p2 is still a root of p2" (NF.is_zero eval_2_res)

let primitive_test2 () = 
  (*let open QQXInfix in
  let p1 = v * v * v - int(2) in
  let p1x = NumberField.make_multivariate 0 p1 in
  let p2 = v * v * v * v * v * v + int(108) in
  let p2y = NumberField.make_multivariate 1 p2 in*)
  (*let p3z = QQXs.of_list [Q.one, Monomial.singleton 0 1; Q.of_int 1, Monomial.singleton 1 1; Q.minus_one, Monomial.singleton 2 1] in*)
  (**)
  (*let r = Rewrite.reduce_rewrite (Rewrite.grobner_basis (Rewrite.mk_rewrite block_order [p1x;p2y;p3z])) in
  Log.log_pp ~level:`always (Rewrite.pp (fun fo v -> if v = 0 then Format.pp_print_string fo "x" else if v = 1 then Format.pp_print_string fo "y" else Format.pp_print_string fo "z")) r;*)
  let block_order = Monomial.block ([fun i -> if i <> 0 && i <> 1 then false else true]) Monomial.degrevlex in
  let p1x = QQXs.add (QQXs.of_list [Q.one, Monomial.singleton 0 3]) (QQXs.scalar (QQ.of_int (-2))) in
  let p2y = QQXs.add (QQXs.of_list [Q.one, Monomial.singleton 1 6]) (QQXs.scalar (QQ.of_int (108))) in
  let p3zp = QQXs.of_list [Q.one, Monomial.singleton 0 1; Q.of_int 2, Monomial.singleton 1 1; Q.minus_one, Monomial.singleton 2 1] in
  let r = Rewrite.reduce_rewrite (Rewrite.grobner_basis (Rewrite.mk_rewrite block_order [p1x;p2y;p3zp])) in
  Log.log_pp ~level:`always (Rewrite.pp (fun fo v -> if v = 0 then Format.pp_print_string fo "x" else if v = 1 then Format.pp_print_string fo "y" else Format.pp_print_string fo "z")) r;
  assert_bool "test" true
  (*let (prim, p1r, p2r) = NumberField.primitive_elem p1 p2 in
  let module NF = NumberField.MakeNF(struct let min_poly = prim end) in
  let p1r_in_NF = NF.make_elem p1r in
  let p2r_in_NF = NF.make_elem p2r in
  let eval_1_res = NF.PNF.eval (NF.PNF.lift p1) p1r_in_NF in
  let eval_2_res = NF.PNF.eval (NF.PNF.lift p2) p2r_in_NF in
  assert_equal 18 (QQX.order prim);
  assert_bool "Root of p1 is still a root of p1" (NF.is_zero eval_1_res);
  assert_bool "Root of p2 is still a root of p2" (NF.is_zero eval_2_res)*)


  
let factor_test1 () = 
  let open QQXInfix in
  let p = v * v * v - int(2) in
  let module NF = NumberField.MakeNF(struct let min_poly = v * v * v - int(2) end) in
  let (c, factors) = NF.factor p in
  (*let print_factor f (fact, deg) = 
    if deg = 1 then
      NF.pp f fact
    else
      (Format.pp_print_string f "("; NF.pp f fact; Format.pp_print_string f ")^"; Format.pp_print_int f deg)
  in
  let print_factors f = Format.pp_print_list ~pp_sep:(fun fo () -> Format.pp_print_string fo "; ") print_factor f in*)
  let multiplied = List.fold_left (fun acc (factor, deg) -> NF.PNF.mul acc (NF.PNF.exp factor deg)) (NF.PNF.scalar (QQXs.scalar c)) factors in
  let p_in_NF = NF.PNF.lift p in
  (*Log.log ~level:`always "Factors";
  Log.log_pp ~level:`always print_factors factors;
  Log.log ~level:`always "Multiplied factors";
  Log.log_pp ~level:`always NF.pp multiplied;*)
  assert_equal 2 (List.length factors);
  assert_bool "Multiplied factor equals" (NF.PNF.equal multiplied p_in_NF)

let factor_test2 () = 
  let open QQXInfix in
  let p = v * v * v - int(2) in
  let module NF = NumberField.MakeNF(struct let min_poly = v * v * v * v * v * v + int(108) end) in
  let (c, factors) = NF.factor p in
  (*let print_factor f (fact, deg) = 
    if deg = 1 then
      NF.pp f fact
    else
      (Format.pp_print_string f "("; NF.pp f fact; Format.pp_print_string f ")^"; Format.pp_print_int f deg)
  in
  let print_factors f = Format.pp_print_list ~pp_sep:(fun fo () -> Format.pp_print_string fo "; ") print_factor f in*)
  let multiplied = List.fold_left (fun acc (factor, deg) -> NF.PNF.mul acc (NF.PNF.exp factor deg)) (NF.PNF.scalar (QQXs.scalar c)) factors in
  let p_in_NF = NF.PNF.lift p in
  (*Log.log ~level:`always "Factors";
  Log.log_pp ~level:`always print_factors factors;
  Log.log ~level:`always "Multiplied factors";
  Log.log_pp ~level:`always NF.pp multiplied;*)
  assert_equal 3 (List.length factors);
  assert_bool "Multiplied factor equals" (NF.PNF.equal multiplied p_in_NF)

let suite = "NumberField" >:::
  [
    "primitive_test1" >:: primitive_test1;
    (*"primitive_test2" >:: primitive_test2;*)
    "factor_test1" >:: factor_test1;
    (*"factor_test2" >:: factor_test2;*)

  ]
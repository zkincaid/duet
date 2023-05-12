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

let inverse_test1 () = 
  let min_poly = QQXs.add (QQXs.exp (QQXs.of_dim 0) 2) (QQXs.scalar (QQ.of_int (-2))) in
  let p = QQXs.of_dim 0 in
  let re = Rewrite.mk_rewrite Monomial.degrevlex [min_poly] in
  let (r, muls) = Rewrite.preduce re p in
  Log.log ~level:`always "Remainder";
  Log.log_pp ~level:`always (QQXs.pp (fun f _ -> Format.pp_print_string f "z")) r;
  Log.log ~level:`always "Muls";
  let plist = Format.pp_print_list ~pp_sep:(fun f () -> Format.pp_print_newline f ()) (QQXs.pp (fun f _ -> Format.pp_print_string f "z")) in
  Log.log_pp ~level:`always plist muls;
  assert_bool "test1" true

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
  let open QQXInfix in
  let p1 = v * v * v - int(2) in
  let p2 = v * v * v * v * v * v + int(108) in
  let (prim, p1r, p2r) = NumberField.primitive_elem p1 p2 in
  let module NF = NumberField.MakeNF(struct let min_poly = prim end) in
  let p1r_in_NF = NF.make_elem p1r in
  let p2r_in_NF = NF.make_elem p2r in
  let eval_1_res = NF.PNF.eval (NF.PNF.lift p1) p1r_in_NF in
  let eval_2_res = NF.PNF.eval (NF.PNF.lift p2) p2r_in_NF in
  assert_equal 18 (QQX.order prim);
  assert_bool "Root of p1 is still a root of p1" (NF.is_zero eval_1_res);
  assert_bool "Root of p2 is still a root of p2" (NF.is_zero eval_2_res)


  
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
      NF.PNF.pp f fact
    else
      (Format.pp_print_string f "("; NF.PNF.pp f fact; Format.pp_print_string f ")^"; Format.pp_print_int f deg)
  in
  let print_factors f = Format.pp_print_list ~pp_sep:(fun fo () -> Format.pp_print_string fo "; ") print_factor f in*)
  let multiplied = List.fold_left (fun acc (factor, deg) -> NF.PNF.mul acc (NF.PNF.exp factor deg)) (NF.PNF.scalar (QQXs.scalar c)) factors in
  let p_in_NF = NF.PNF.lift p in
  (*Log.log ~level:`always "Factors";
  Log.log_pp ~level:`always print_factors factors;
  Log.log ~level:`always "Multiplied factors";
  Log.log_pp ~level:`always NF.PNF.pp multiplied;*)
  assert_equal 3 (List.length factors);
  assert_bool "Multiplied factor equals" (NF.PNF.equal multiplied p_in_NF)

let suite = "NumberField" >:::
  [
    (*"inverse_test1" >:: inverse_test1;*)
    "primitive_test1" >:: primitive_test1;
    "primitive_test2" >:: primitive_test2;
    "factor_test1" >:: factor_test1;
    "factor_test2" >:: factor_test2;

  ]
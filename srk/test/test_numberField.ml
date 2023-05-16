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

module QQXsInfix = struct
  let ( + ) = QQXs.add
  let ( - ) = QQXs.sub
  let ( * ) = QQXs.mul
  let int k = QQXs.scalar (QQ.of_int k)
  let dim k = QQXs.of_dim (Char.code k)
end

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
  let (prim, x_in_prim, y_in_prim) = NumberField.primitive_elem p1x p2y (Char.code 'x') (Char.code 'y') in
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
  let (prim, x_in_prim, y_in_prim) = NumberField.primitive_elem p1x p2y (Char.code 'x') (Char.code 'y') in
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
  let root_field, roots = NumberField.splitting_field p in
  let module NF = NumberField.MakeNF(struct let min_poly = root_field end) in
  (*let print_roots f rs = Format.pp_print_list ~pp_sep:(fun fo () -> Format.pp_print_string fo "; ") NF.pp f (List.map fst rs) in
  Log.log ~level:`always "Field polynomial";
  Log.log_pp ~level:`always QQX.pp root_field;
  Log.log ~level:`always "Roots";
  Log.log_pp ~level:`always print_roots roots;*)
  let check_root (r, _) = 
    assert_bool "Test root" (NF.is_zero (NF.X.eval (NF.X.lift p) (NF.make_elem r)))
  in
  List.iter check_root roots

let suite = "NumberField" >:::
  [
    "inverse_test1" >:: inverse_test1;
    "primitive_test1" >:: primitive_test1;
    "primitive_test2" >:: primitive_test2;
    "factor_test1" >:: factor_test1;
    "factor_test2" >:: factor_test2;
    "factor_test3" >:: factor_test3;
    "splitting_test1" >:: splitting_test1;
  ]
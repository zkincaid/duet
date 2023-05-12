open OUnit
open Srk
open Polynomial

let mk_qqx vec =
  List.fold_left
    (fun vec (i, k) -> QQX.add_term k i vec)
    QQX.zero
    (List.mapi (fun i k -> (i, QQ.of_int k)) vec)

module QQXsInfix = struct
  let ( + ) = QQXs.add
  let ( - ) = QQXs.sub
  let ( * ) = QQXs.mul
  let int k = QQXs.scalar (QQ.of_int k)
  let dim k = QQXs.of_dim (Char.code k)
end

let assert_equal_qqxs p q =
  let pp_dim formatter i =
    Format.pp_print_string formatter (Char.escaped (Char.chr i))
  in
  let show = SrkUtil.mk_show (QQXs.pp pp_dim) in
  assert_equal ~printer:show ~cmp:QQXs.equal p q

let grobner_test1 () = 
  let open QQXsInfix in
  let x = dim 'x' in
  let y = dim 'y' in
  let z = dim 'z' in
  let p1 = x * x * x - int(2) in
  let p2 = y * y * y * y * y * y + int(108) in
  let p3 = x + int(2) * y - z in
  let gb = FGb.grobner_basis [Char.code 'x';Char.code 'y'] [Char.code 'z'] [p1;p2;p3] in
  let order = FGb.get_mon_order [Char.code 'x';Char.code 'y'] [Char.code 'z'] in
  let r = Rewrite.mk_rewrite order gb in
  (*let pv fo v = if v = Char.code 'x' then Format.pp_print_string fo "x" else if v = Char.code 'y' then Format.pp_print_string fo "y" else Format.pp_print_string fo "z" in
  let ppoly = 
    QQXs.pp pv in
  let plist = Format.pp_print_list ~pp_sep:(fun fo () -> Format.pp_print_newline fo ()) ppoly in
  Log.log_pp ~level:`always plist gb;
  Log.log ~level:`always "Rewrite";
  Log.log_pp ~level:`always (Rewrite.pp pv) r;*)

  let p1red = Rewrite.reduce r p1 in
  let p2red = Rewrite.reduce r p2 in
  let p3red = Rewrite.reduce r p3 in
  assert_equal_qqxs (int (0)) p1red;
  assert_equal_qqxs (int (0)) p2red;
  assert_equal_qqxs (int (0)) p3red

let suite = "FGb" >:::
  [
    "grobner_test1" >:: grobner_test1
  ]
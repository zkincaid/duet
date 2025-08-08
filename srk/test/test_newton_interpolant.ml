open Srk
open OUnit
open Syntax
open Test_pervasives
open NewtonInterpolant
module V = struct
  type t = string

  let typ_table = Hashtbl.create 991
  let sym_table = Hashtbl.create 991
  let rev_sym_table = Hashtbl.create 991

  let register_var name typ =
    assert (not (Hashtbl.mem typ_table name));
    let sym = Ctx.mk_symbol ~name (typ :> typ) in
    Hashtbl.add typ_table name typ;
    Hashtbl.add sym_table name sym;
    Hashtbl.add rev_sym_table sym name

  let pp = Format.pp_print_string
  let show x = x
  let typ = Hashtbl.find typ_table
  let compare = Stdlib.compare
  let symbol_of = Hashtbl.find sym_table
  let of_symbol sym =
    if Hashtbl.mem rev_sym_table sym then
      Some (Hashtbl.find rev_sym_table sym)
    else
      None
  let is_global _ = true
end
module T = Transition.Make(Ctx)(V)
module NITP = NewtonBackwards(Ctx)(V)(T)

let () =
  T.domain := Iteration.split (!T.domain)

let () =
  V.register_var "i" `TyInt;
  V.register_var "j" `TyInt;
  V.register_var "k" `TyInt;
  V.register_var "n" `TyInt;
  V.register_var "x" `TyInt;
  V.register_var "y" `TyInt;
  V.register_var "z" `TyInt

let x = Ctx.mk_const (V.symbol_of "x")
let y = Ctx.mk_const (V.symbol_of "y")
let z = Ctx.mk_const (V.symbol_of "z")
let i = Ctx.mk_const (V.symbol_of "i")
let j = Ctx.mk_const (V.symbol_of "j")
let k = Ctx.mk_const (V.symbol_of "k")
let n = Ctx.mk_const (V.symbol_of "n")

let assert_post tr phi =
  let not_post =
    rewrite srk ~down:(pos_rewriter srk) (Ctx.mk_not phi)
  in
  let pathcond =
    T.guard (T.mul tr (T.assume not_post))
  in
  if Wedge.is_sat srk pathcond != `Unsat then
    assert_failure (Printf.sprintf "%s\n is not a post-condition of\n%s"
                      (Formula.show srk phi)
                      (T.show tr))

let assert_equal_tr = assert_equal ~cmp:T.equal ~printer:T.show

let mk_block = BatList.reduce T.mul

let mk_if cond bthen belse =
  T.add
    (mk_block ((T.assume cond)::bthen))
    (mk_block ((T.assume (Ctx.mk_not cond))::belse))

let mk_while cond body =
  T.mul
    (T.star (mk_block ((T.assume cond)::body)))
    (T.assume (Ctx.mk_not cond))

let assert_valid pre tr post =
  if (T.valid_triple pre [tr] post) != `Valid then
    assert_failure (Printf.sprintf "Invalid Hoare triple: {%s} %s {%s}"
                      (Formula.show srk pre)
                      (T.show tr)
                      (Formula.show srk post))


let check_interpolant path itp =
  let rec go path itp =
    match path, itp with
    | tr::path, pre::post::itp ->
      assert_valid pre tr post;
      go path (post::itp)
    | [], [_] -> ()
    | _, _ -> assert false
  in
  go path (Ctx.mk_true::itp)

let interpolate1 () =
  let path =
    let open Infix in
    [T.assign "x" (int 0);
     T.assign "y" (int 0);
     T.assume (x < (int 10));
     T.assign "x" (x + (int 1));
     T.assign "y" (y + (int 1));
     T.assume ((int 10) <= x);
     T.assume ((int 10) < x || x < (int 10))]
  in
  let post = Ctx.mk_false in
  match NITP.interpolate path post with
  | `Valid itp ->
    check_interpolant path itp
  | _ -> assert_failure "Invalid post-condition"

let interpolate2 () =
  let path =
    let open Infix in
    [T.assume (x < (int 10));
     T.assign "x" (x + (int 1));
     T.assign "y" (y + (int 1));
     T.assume ((int 10) <= x);
     T.assume ((int 10) < x || x < (int 10))]
  in
  let post = Ctx.mk_false in
  match NITP.interpolate path post with
  | `Valid itp ->
    check_interpolant path itp
  | _ -> assert_failure "Invalid post-condition"

let interpolate_havoc () =
  let path =
    let open Infix in
    [T.assign "x" (int 0);
     T.assign "y" v; (* havoc *)
     T.assume (x <= y);
     T.assume (y < (int 0))]
  in
  let post = Ctx.mk_false in
  match NITP.interpolate path post with
  | `Valid itp ->
    check_interpolant path itp
  | _ -> assert_failure "Invalid post-condition"

let suite = "Newton_interpolant" >::: [
    "interpolate1" >:: interpolate1;
    "interpolate2" >:: interpolate2;
    "interpolate_havoc" >:: interpolate_havoc;
    ]

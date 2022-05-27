open Srk
open OUnit
open Syntax
open Test_pervasives

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
end
module T = Transition.Make(Ctx)(V)

let () =
  T.domain := (module Iteration.Split(val !T.domain))

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

let degree1 () =
  let tr =
    let open Infix in
    mk_block [
      T.assign "i" (int 0);
      mk_while (i < n) [
        T.assign "i" (i + (int 1));
      ]
    ]
  in
  let post =
    let open Infix in
    n < (int 0) || i = n
  in
  assert_post tr post

let degree2 () =
  let tr =
    let open Infix in
    mk_block [
      T.assume ((int 0) <= n);
      T.assign "i" (int 0);
      T.assign "x" (int 0);
      mk_while (i < n) [
        T.assume ((int 0) <= n); (* Needed w/o forward inv gen *)
        T.assign "i" (i + (int 1));
        T.assign "j" (int 0);
        mk_while (j < n) [
          T.assign "j" (j + (int 1));
          T.assign "x" (x + (int 1));
        ]
      ]
    ]
  in
  let post =
    let open Infix in
    x = n*n
  in
  assert_post tr post

let degree3 () =
  let tr =
    let open Infix in
    mk_block [
      T.assume ((int 0) <= n);
      T.assign "i" (int 0);
      T.assign "x" (int 0);
      mk_while (i < n) [
        T.assume ((int 0) <= n); (* Needed w/o forward inv gen *)
        T.assign "i" (i + (int 1));
        T.assign "j" (int 0);
        mk_while (j < n) [
        T.assume ((int 0) <= n); (* Needed w/o forward inv gen *)
          T.assign "j" (j + (int 1));
          T.assign "k" (int 0);
          mk_while (k < n) [
            T.assign "k" (k + (int 1));
            T.assign "x" (x + (int 1));
          ]
        ]
      ]
    ]
  in
  let post =
    let open Infix in
    x = n*n*n
  in
  assert_post tr post

let gauss_sum () =
  let tr =
    let open Infix in
    mk_block [
      T.assume ((int 0) <= n);
      T.assign "i" (int 0);
      T.assign "x" (int 0);
      mk_while (i < n) [
        T.assume ((int 0) <= n); (* Needed w/o forward inv gen *)
        T.assume ((int 0) <= i); (* Needed w/o forward inv gen *)
        T.assign "j" i;
        T.assign "i" (i + (int 1));
        mk_while (j < n) [
          T.assign "j" (j + (int 1));
          T.assign "x" (x + (int 1));
        ]
      ]
    ]
  in
  let post =
    let open Infix in
    (int 2) * x <= (n*(n+(int 1)))
  in
  assert_post tr post

let inc_nondet () =
  let tr =
    let open Infix in
    mk_block [
      T.assign "x" (int 0);
      T.assign "y" (int 0);
      T.assign "z" (int 0);
      mk_while (z < n) [
        T.assign "z" (z + (int 1));
        mk_if (z mod (int 2) = (int 0)) [
          T.assign "x" (x + (int 1));
        ] [
          T.assign "y" (y + (int 1));
        ]
      ]
    ]
  in
  let post =
    let open Infix in
    n < (int 0) || x + y = n
  in
  assert_post tr post

let split () =
  let tr =
    let open Infix in
    mk_block [
      T.assume ((int 0) <= n);
      T.assign "x" (int 0);
      T.assign "y" (int 0);
      T.havoc ["z"];
      mk_while (x + y < n) [
        mk_if (z <= (int 0)) [
          T.assign "x" (x + (int 1));
        ] [
          T.assign "y" (y + (int 1));
        ]
      ]
    ]
  in
  let post =
    let open Infix in
    x = n || y = n
  in
  assert_post tr post

let split2 () =
  let tr =
    let open Infix in
    mk_block [
      T.assign "n" (int 100);
      T.assign "x" (int 0);
      T.assign "y" (int 0);
      T.havoc ["z"];
      mk_while (x + y < n) [
        mk_if (x < (int 50)) [
          T.assign "x" (x + (int 1));
        ] [
          T.assign "y" (y + (int 1));
        ]
      ]
    ]
  in
  let post =
    let open Infix in
    x = y
  in
  assert_post tr post

let equal1 () =
  let tr1 =
    mk_block [
      T.havoc ["x"];
      T.assign "y" x;
    ]
  in
  let tr2 =
    mk_block [
      T.havoc ["y"];
      T.assign "x" y;
    ]
  in
  assert_equal_tr tr1 tr2

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
  match T.interpolate path post with
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
  match T.interpolate path post with
  | `Valid itp ->
    check_interpolant path itp
  | _ -> assert_failure "Invalid post-condition"

let negative_eigenvalue () =
  let tr =
    let open Infix in
    mk_block [
      T.assume ((int 0) < x);
      T.assume ((int 0) < y);
      T.assign "n" (x + y);
      T.assign "k" (int 0);
      T.assume ((int 0) < y);
      mk_while ((int 0) < x && (int 0) <= y) [
        T.parallel_assign [("x", y);
                           ("y", x - (int 1));
                           ("k", k + (int 1))]
      ]
    ]
  in
  let post = mk_leq srk k n in
  assert_post tr post

let suite = "Transition" >::: [
    "degree1" >:: degree1;
    "degree2" >:: degree2;
    "degree3" >:: degree3;
    "gauss_sum" >:: gauss_sum;
    "inc_nondet" >:: inc_nondet;
    "split" >:: split;
    "split2" >:: split2;
    "equal1" >:: equal1;
(*
    "interpolate1" >:: interpolate1;
    "interpolate2" >:: interpolate2;
*)
    "negative_eigenvalue" >:: negative_eigenvalue;
  ]

open OUnit
open Abstract
open Syntax


module Ctx = MakeSimplifyingContext ()
module Infix = Syntax.Infix(Ctx)
let ctx = Ctx.context
let smt_ctx = Smt.mk_context ctx []

let rsym = Ctx.mk_symbol ~name:"r" `TyReal
let ssym = Ctx.mk_symbol ~name:"s" `TyReal

let wsym = Ctx.mk_symbol ~name:"w" `TyInt
let xsym = Ctx.mk_symbol ~name:"x" `TyInt
let ysym = Ctx.mk_symbol ~name:"y" `TyInt
let zsym = Ctx.mk_symbol ~name:"z" `TyInt

let r = mk_const ctx rsym
let s = mk_const ctx ssym

let w = mk_const ctx wsym
let x = mk_const ctx xsym
let y = mk_const ctx ysym
let z = mk_const ctx zsym

let frac num den = Ctx.mk_real (QQ.of_frac num den)
let int k = Ctx.mk_real (QQ.of_int k)

let assert_equal_term s t =
  assert_equal ~printer:(Term.show ctx) s t
let assert_equiv_formula s t =
  assert_equal ~printer:(Formula.show ctx) ~cmp:(smt_ctx#equiv) s t
let assert_equal_qq x y =
  assert_equal ~printer:QQ.show ~cmp:QQ.equal x y


let hull_formula hull = Ctx.mk_and (List.map (Ctx.mk_eq (int 0)) hull)

let affine_hull1 () =
  let phi =
    let open Infix in
    x = y && y = z + (int 1)
  in
  let hull = affine_hull smt_ctx phi [xsym; ysym; zsym] in
  let hull_xz = affine_hull smt_ctx phi [xsym; zsym] in
  assert_equiv_formula phi (hull_formula hull);
  assert_equiv_formula
    (Ctx.mk_eq x (Ctx.mk_add [z; int 1]))
    (hull_formula hull_xz)

let affine_hull2 () =
  let phi =
    let open Infix in
    (x = y || x = z)
  in
  let hull = affine_hull smt_ctx phi [xsym;ysym;zsym] in
  assert_equiv_formula Ctx.mk_true (hull_formula hull)

let affine_hull3 () =
  let phi =
    let open Infix in
    ((w = x && x = y) || (w = z && z = y))
  in
  let hull = affine_hull smt_ctx phi [wsym;xsym;ysym;zsym] in
  let hull_xyz = affine_hull smt_ctx phi [xsym;ysym;zsym] in
  let hull_wy = affine_hull smt_ctx phi [wsym;ysym] in
  assert_equiv_formula (Ctx.mk_eq w y) (hull_formula hull);
  assert_equiv_formula Ctx.mk_true (hull_formula hull_xyz);
  assert_equiv_formula (Ctx.mk_eq w y) (hull_formula hull_wy)

let affine_hull4 () =
  let phi =
    let open Infix in
    x <= w && ((w <= x && x = y) || (w = z && z = y))
  in
  let hull = affine_hull smt_ctx phi [wsym;ysym] in
  assert_equiv_formula (Ctx.mk_eq w y) (hull_formula hull)

let affine_hull5 () =
  let phi = Ctx.mk_eq x (int 12) in
  let hull = affine_hull smt_ctx phi [xsym] in
  assert_equiv_formula phi (hull_formula hull)

let affine_hull6 () =
  let phi =
    let open Infix in
    x <= w && z <= (int 1) && ((w <= x && x = y && z = (int 1))
                             || (w = z && z = y && (int 1) <= z))
  in
  let phi_hull =
    let open Infix in
    z = (int 1) && w = y
  in
  let hull = affine_hull smt_ctx phi [wsym;xsym;ysym;zsym] in
  assert_equiv_formula phi_hull (hull_formula hull)

let optimize1 () =
  let phi =
    let open Infix in
    (int 0) <= r && r <= (int 1)
  in
  assert_equiv_formula phi (Abstract.boxify smt_ctx phi [r])

let optimize2 () =
  let phi =
    let open Infix in
    (int 0) <= r && r <= (int 1)
    && (int (-3)) <= s && s <= (int 28)
  in
  let phi_r =
    let open Infix in
    (int 0) <= r && r <= (int 1)
  in
  let phi_rs =
    let open Infix in
    (int (-3)) <= (r + s) && (r + s) <= (int 29)
  in
  assert_equiv_formula phi (Abstract.boxify smt_ctx phi [r; s]);
  assert_equiv_formula phi_r (Abstract.boxify smt_ctx phi [r]);
  assert_equiv_formula phi_rs
		       (Abstract.boxify smt_ctx phi [Ctx.mk_add [r; s]])

let optimize3 () =
  let phi =
    let open Infix in
    (int 0) <= r && s <= (int 1)
  in
  assert_equiv_formula phi (Abstract.boxify smt_ctx phi [r; s])

let optimize4 () =
  let phi =
    let open Infix in
    (int 1) < r && r < (int 5)
  in
  let phi_closed =
    let open Infix in
    (int 1) <= r && r <= (int 5)
  in
  assert_equiv_formula phi_closed (Abstract.boxify smt_ctx phi [r])

(*
let optimize5 () =
  let phi =
    Ctx.mk_exists ~name:"s" `TyReal
      (let open Infix in
       r <= (Ctx.mk_var 0 `TyReal) && (Ctx.mk_var 0 `TyReal) < (int 0))
  in
  let ivl = Interval.make None (Some QQ.zero) in
  match Abstract.aqopt smt_ctx phi r with
  | `Sat ivl2 ->
    assert_equal ~printer:Interval.show ~cmp:Interval.equal ivl ivl2
  | _ -> assert false
*)

let aqsat1 () =
  let phi =
    Ctx.mk_forall ~name:"r" `TyReal
      (Ctx.mk_exists ~name:"s" `TyReal
         (Ctx.mk_lt (Ctx.mk_var 1 `TyReal) (Ctx.mk_var 0 `TyReal)))
  in
  assert_equal `Sat (Abstract.aqsat smt_ctx phi)



let suite = "Abstract" >::: [
    "affine_hull1" >:: affine_hull1;
    "affine_hull2" >:: affine_hull2;
    "affine_hull3" >:: affine_hull3;
    "affine_hull4" >:: affine_hull4;
    "affine_hull5" >:: affine_hull5;
    "affine_hull6" >:: affine_hull6;
    "optimize1" >:: optimize1;
    "optimize2" >:: optimize2;
    "optimize3" >:: optimize3;
    "optimize4" >:: optimize4;
    (*    "optimize5" >:: optimize5;*)
    "aqsat1" >:: aqsat1;
  ]

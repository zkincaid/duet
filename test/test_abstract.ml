open Srk
open OUnit
open Abstract
open Nonlinear
open Test_pervasives

let hull_formula hull = Ctx.mk_and (List.map (Ctx.mk_eq (int 0)) hull)

let affine_hull1 () =
  let phi =
    let open Infix in
    x = y && y = z + (int 1)
  in
  let hull = affine_hull srk phi [xsym; ysym; zsym] in
  let hull_xz = affine_hull srk phi [xsym; zsym] in
  assert_equiv_formula phi (hull_formula hull);
  assert_equiv_formula
    (Ctx.mk_eq x (Ctx.mk_add [z; int 1]))
    (hull_formula hull_xz)

let affine_hull2 () =
  let phi =
    let open Infix in
    (x = y || x = z)
  in
  let hull = affine_hull srk phi [xsym;ysym;zsym] in
  assert_equiv_formula Ctx.mk_true (hull_formula hull)

let affine_hull3 () =
  let phi =
    let open Infix in
    ((w = x && x = y) || (w = z && z = y))
  in
  let hull = affine_hull srk phi [wsym;xsym;ysym;zsym] in
  let hull_xyz = affine_hull srk phi [xsym;ysym;zsym] in
  let hull_wy = affine_hull srk phi [wsym;ysym] in
  assert_equiv_formula (Ctx.mk_eq w y) (hull_formula hull);
  assert_equiv_formula Ctx.mk_true (hull_formula hull_xyz);
  assert_equiv_formula (Ctx.mk_eq w y) (hull_formula hull_wy)

let affine_hull4 () =
  let phi =
    let open Infix in
    x <= w && ((w <= x && x = y) || (w = z && z = y))
  in
  let hull = affine_hull srk phi [wsym;ysym] in
  assert_equiv_formula (Ctx.mk_eq w y) (hull_formula hull)

let affine_hull5 () =
  let phi = Ctx.mk_eq x (int 12) in
  let hull = affine_hull srk phi [xsym] in
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
  let hull = affine_hull srk phi [wsym;xsym;ysym;zsym] in
  assert_equiv_formula phi_hull (hull_formula hull)

let optimize1 () =
  let phi =
    let open Infix in
    (int 0) <= r && r <= (int 1)
  in
  assert_equiv_formula phi (Abstract.boxify srk phi [r])

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
  assert_equiv_formula phi (Abstract.boxify srk phi [r; s]);
  assert_equiv_formula phi_r (Abstract.boxify srk phi [r]);
  assert_equiv_formula phi_rs
		       (Abstract.boxify srk phi [Ctx.mk_add [r; s]])

let optimize3 () =
  let phi =
    let open Infix in
    (int 0) <= r && s <= (int 1)
  in
  assert_equiv_formula phi (Abstract.boxify srk phi [r; s])

let optimize4 () =
  let phi =
    let open Infix in
    (int 1) < r && r < (int 5)
  in
  let phi_closed =
    let open Infix in
    (int 1) <= r && r <= (int 5)
  in
  assert_equiv_formula phi_closed (Abstract.boxify srk phi [r])

(*
let optimize5 () =
  let phi =
    Ctx.mk_exists ~name:"s" `TyReal
      (let open Infix in
       r <= (Ctx.mk_var 0 `TyReal) && (Ctx.mk_var 0 `TyReal) < (int 0))
  in
  let ivl = Interval.make None (Some QQ.zero) in
  match Abstract.aqopt smt_srk phi r with
  | `Sat ivl2 ->
    assert_equal ~printer:Interval.show ~cmp:Interval.equal ivl ivl2
  | _ -> assert false
*)

let polka = Polka.manager_alloc_loose ()

let abstract1 () =
  let phi =
    let open Infix in
    (int 1) < r && r < (int 5)
  in
  let phi_closed =
    let open Infix in
    (int 1) <= r && r <= (int 5)
  in
  assert_equiv_formula
    phi_closed
    (SrkApron.formula_of_property (Abstract.abstract srk polka phi))

let abstract2 () =
  let phi =
    let open Infix in
    (int 1) < r && r < s && r < (int 5)
  in
  let phi_closed =
    let open Infix in
    (int 1) <= r && r <= (int 5)
  in
  let phi_abstract =
    Abstract.abstract ~exists:((=) rsym) srk polka phi
    |> SrkApron.formula_of_property
  in
  assert_equiv_formula phi_closed phi_abstract

let abstract3 () =
  let phi =
    let open Infix in
    ((w = x && x = y) || (w = z && z = y))
  in
  let phi_abstract =
    Abstract.abstract srk polka phi
    |> SrkApron.formula_of_property
  in
  assert_equiv_formula (Ctx.mk_eq w y) phi_abstract

(* Convex hull of { (0,0), (0,1), (1,1) } *)
let abstract4 () =
  let phi =
    let open Infix in
    (x = (int 0) && y = (int 0))
    || (x = (int 1) && y = (int 1))
    || (x = (int 0) && y = (int 1))
  in
  let phi_abstract =
    Abstract.abstract srk polka phi
    |> SrkApron.formula_of_property
  in
  let psi =
    let open Infix in
    ((int 0) <= x && x <= y)
    && ((int 0) <= y && y <= (int 1))
  in
  assert_equiv_formula psi phi_abstract

let linearize1 () =
  let phi =
    let open Infix in
    (int 0) <= x
    && x <= (int 1000)
    && y = x * x
    && (int 1000000) <= y
  in
  let psi =
    let open Infix in
    (x = int 1000) && (y = int 1000000)
  in
  assert_implies (linearize srk phi) psi

let linearize2 () =
  let phi =
    let open Infix in
    (int 1) <= x
    && x <= (int 1)
    && w = (int 0)
    && z = y / x + w * y
  in
  assert_implies (linearize srk phi) (Ctx.mk_eq z y)

let linearize3 () =
  let phi =
    let open Infix in
    w <= x
    && (int 0) <= y
    && (int 0) <= w
    && z = x * y
  in
  assert_implies (linearize srk phi) (Ctx.mk_leq (int 0) z)

(* easier version of linearization5: y * y appears twice, but we when we
   replace nonlinear terms by variables we lose that information. *)
let linearize4 () =
  let phi =
    let open Infix in
    x = y * y && z = y * y + (int 1)
  in
  assert_implies (linearize srk phi) (Ctx.mk_lt x z)

(* to pass this test case, we need linearization to be smart enough to see
   that x = y implies x * x = y * y *)
let linearize5 () =
  let phi =
    let open Infix in
    x = y && z = x * x && z = y * y + (int 1)
  in
  assert_implies (linearize srk phi) Ctx.mk_false

let linearize6 () =
  let open Infix in
  let phi =
    (int 3) <= y && y <= (int 10)
    && (int 0) <= x
    && z = x mod y
  in
  let lin_phi = linearize srk phi in
  assert_implies lin_phi (z < (int 10));
  assert_implies lin_phi ((int 0) <= z);
  assert_implies lin_phi (z <= x)

let linearize7 () =
  let open Infix in
  let phi =
    w = x * y && x <= (int 0) && y <= (int 0)
  in
  let lin_phi = linearize srk phi in
  assert_implies lin_phi ((int 0) <= w)

(* Convex hull of { (0,0), (0,1), (1,1) } *)
let nonlinear_abstract1 () =
  let phi =
    let open Infix in
    (x = (int 0) && y = (int 0))
    || (x = (int 1) && y = (int 1))
    || (x = (int 0) && y = (int 1))
  in
  let phi_abstract =
    Wedge.to_formula (Wedge.abstract srk phi)
  in
  let psi =
    let open Infix in
    ((int 0) <= x && x <= y)
    && ((int 0) <= y && y <= (int 1))
  in
  assert_equiv_formula psi phi_abstract

let nonlinear_abstract2 () =
  let phi =
    let open Infix in
    (x = y && z = x * x && (int 2) <= z)
    || (w = y && z = w * w && z <= (int 100))
  in
  let phi_abstract =
    let abstract =
      Wedge.abstract
        ~exists:(fun sym -> sym = zsym || sym = ysym)
        srk
        phi
    in
    Wedge.to_formula abstract
  in
  let psi =
    let open Infix in
    z = y * y
  in
  assert_equiv_formula psi phi_abstract

let mod_abstract () =
  let phi =
    let open Infix in
    ((int 0) <= z)
    && ((x = (int 1) && z mod (int 2) = (int 1))
        || (x = (int 0) && z mod (int 2) = (int 0)))
  in
  let phi_abstract =
    let abstract =
      Wedge.abstract
        srk
        phi
    in
    Wedge.to_formula abstract
  in
  let psi =
    let open Infix in
    (int 0) <= z && x = z mod (int 2)
    && (int 0) <= x && x <= (int 1)
  in
  assert_equiv_formula psi phi_abstract

let degree3_abstract () =
  let phi =
    let open Infix in
    (x <= y * y * y)
  in
  let phi_abstract =
    let abstract =
      Wedge.abstract srk phi
    in
    Wedge.to_formula abstract
  in
  let psi =
    let open Infix in
    x <= y * y * y
  in
  assert_equiv_formula psi phi_abstract

let lt_abstract () =
  let phi =
    let open Infix in
    (x < y * y)
  in
  let phi_abstract =
    let abstract =
      Wedge.abstract srk phi
    in
    Wedge.to_formula abstract
  in
  assert_equiv_formula phi phi_abstract

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
    "abstract1" >:: abstract1;
    "abstract2" >:: abstract2;
    "abstract3" >:: abstract3;
    "abstract4" >:: abstract4;
    "linearize1" >:: linearize1;
    "linearize2" >:: linearize2;
    "linearize3" >:: linearize3;
    "linearize4" >:: linearize4;
    "linearize5" >:: linearize5;
    "linearize6" >:: linearize6;
    "linearize7" >:: linearize7;
    "nonlinear_abstract1" >:: nonlinear_abstract1;
    "nonlinear_abstract2" >:: nonlinear_abstract2;
    "mod_abstract" >:: mod_abstract;
    "degree3_abstract" >:: degree3_abstract;
    "lt_abstract" >:: lt_abstract
  ]

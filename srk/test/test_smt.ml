open OUnit
open Syntax
open Test_pervasives

let b = Ctx.mk_const (Ctx.mk_symbol ~name:"b" `TyBool)

let gsym = Ctx.mk_symbol ~name:"g" (`TyFun ([`TyInt; `TyInt], `TyInt))
let g : Ctx.term * Ctx.term -> Ctx.term =
  fun (x, y) -> Ctx.mk_app gsym [x; y]

let fsym = Ctx.mk_symbol ~name:"f" (`TyFun ([`TyInt; `TyBool], `TyInt))
let f : Ctx.term * Ctx.formula -> Ctx.term =
  fun (x, y) -> Ctx.mk_app fsym [(x :> (Ctx.t, typ_fo) expr);
                                 (y :> (Ctx.t, typ_fo) expr)]

let p = Ctx.mk_symbol ~name:"p" (`TyFun ([`TyInt; `TyBool], `TyBool))

let hsym = Ctx.mk_symbol ~name:"h" (`TyFun ([`TyReal; `TyReal], `TyReal))
let h : Ctx.term * Ctx.term -> Ctx.term =
  fun (x, y) -> Ctx.mk_app hsym [x; y]

let roundtrip0 () =
  let tru = mk_true srk in
  let fls = mk_false srk in
  assert_equal_formula tru (formula_of_z3 (z3_of_formula tru));
  assert_equal_formula fls (formula_of_z3 (z3_of_formula fls))

let roundtrip1 () =
  let term =
    let open Infix in
    x * x * x mod (int 10) + (frac 100 3) / (r - z + s)
  in
  assert_equal_term term (term_of_z3 (z3_of_term term))

let roundtrip2 () =
  let phi =
    let open Infix in
    x <= y && y <= z && x < z
    || x = y && y = z
  in
  assert_equal_formula phi (formula_of_z3 (z3_of_formula phi))

let roundtrip3 () =
  let phi =
    let open Infix in
    forall ~name:"a" `TyInt
      (forall ~name:"b" `TyInt
         (!((var 0 `TyInt) < (var 1 `TyInt))
          || (exists ~name:"c" `TyReal
                ((var 1 `TyInt) < (var 0 `TyReal)
                 && (var 0 `TyReal) < (var 2 `TyInt)))))
  in
  assert_equal_formula phi (formula_of_z3 (z3_of_formula phi))

let roundtrip4 () =
  let term =
    let open Infix in
    (f (x, b)) + x
  in
  assert_equal_term term (term_of_z3 (z3_of_term term))

let is_interpolant phi psi itp =
  (Smt.entails srk phi itp = `Yes)
  && Smt.is_sat srk (mk_and srk [itp; psi]) = `Unsat

let interpolate1 () =
  let phi =
    let open Infix in
    x = y && (int 0) = x
  in
  let psi =
    let open Infix in
    y = z && z < (int 0)
  in
  (match SrkZ3.interpolate_seq srk [phi; psi] with
   | `Unsat [itp] ->
     assert_bool "itp(y == x < 0, 0 < z = y)" (is_interpolant phi psi itp)
   | _ -> assert false);
  (match SrkZ3.interpolate_seq srk [psi; phi] with
   | `Unsat [itp] ->
     assert_bool "itp(0 < z = y, y == x < 0)" (is_interpolant psi phi itp)
   | _ -> assert false)

let interpolate2 () =
  let phi =
    let open Infix in
    x = (int 0) && y = x + (int 1) && y < (int 1)
  in
  let psi = Ctx.mk_true in
  (match SrkZ3.interpolate_seq srk [phi; psi] with
   | `Unsat [itp] ->
     assert_bool "itp(x = 0 /\\ y = x + 1 /\\ y < 1, true)"
       (is_interpolant phi psi itp)
   | _ -> assert false);
  (match SrkZ3.interpolate_seq srk [psi; phi] with
   | `Unsat [itp] ->
     assert_bool "itp(true, x = 0 /\\ y = x + 1 /\\ y < 1)"
       (is_interpolant psi phi itp)
   | _ -> assert false)

let interpolate3 () =
  let phi =
    let open Infix in
    x = (int 1) && w = (int 1)
  in
  let psi =
    let open Infix in
    y = x + w && y <= (int 1)
  in
  (match SrkZ3.interpolate_seq srk [phi; psi] with
   | `Unsat [itp] ->
     assert_bool "itp(x = w = 1, y = x + w <= 1)"
       (is_interpolant phi psi itp)
   | _ -> assert false);
  (match SrkZ3.interpolate_seq srk [psi; phi] with
   | `Unsat [itp] ->
     assert_bool "itp(y = x + w <= 1, x = w = 1)"
       (is_interpolant psi phi itp)
   | _ -> assert false)

let interpretation1 () =
  let phi =
    let open Infix in
    (int 0) = x && x <= y
    && g(x, y) < g(y, x) && g(int 0, int 0) = (int 0)
  in
  match Smt.get_model srk phi with
  | `Sat m ->
    assert_bool "is_model"
      (Interpretation.evaluate_formula m phi)
  | _ -> assert false

let implicant1 () =
  let phi =
    let open Infix in
    (int 0) = x
    && x <= f((int 0), (int 1) = y || (int 2)= y)
    && (y <= (int 0) || (x = (int 3)))
  in
  match Smt.get_model srk phi with
  | `Sat m ->
    begin match Interpretation.select_implicant m phi with
      | Some implicant ->
        List.iter (fun psi ->
            assert_bool "is_model"
              (Interpretation.evaluate_formula m psi))
          implicant
      | None -> assert false
    end
  | _ -> assert false

let affine_interp1 () =
  let phi =
    let open Infix in
    h(x, y) = h(y, x)
    && x < y
    && h(x, (int 0)) = x
    && h(y, (int 0)) = y
  in
  match Smt.get_model srk phi with
  | `Sat m ->
    let has_affine_interp =
      match Smt.affine_interpretation srk m phi with
      | `Sat _ -> true
      | _ -> false
    in
    assert_bool "has_affine_interp" has_affine_interp
  | _ -> assert false

let affine_interp2 () =
  let phi =
    let open Infix in
    h(x, y) < h(y, x)
    && h(x, z) < h(y, z)
    && h(x, z) < h(y, y)
  in
  match Smt.get_model srk phi with
  | `Sat m ->
    (match Smt.affine_interpretation srk m phi with
     | `Sat m ->
       assert_bool "is_model"
         (Interpretation.evaluate_formula m phi)
     | _ -> assert false)
  | _ -> assert false

let substitute_solution fp expr =
  let rewriter expr =
    match destruct srk expr with
    | `App (_, []) -> expr
    | `App (relation, args) ->
      (substitute srk
         (List.nth args)
         (SrkZ3.CHC.get_solution fp relation) :> ('a,typ_fo) expr)
    | _ -> expr
  in
  rewrite srk ~down:rewriter expr

let verify_chc relations rules =
  let solver = SrkZ3.CHC.mk_solver srk in
  List.iter (SrkZ3.CHC.register_relation solver) relations;
  rules |> List.iter (fun (hypothesis, conclusion) ->
      SrkZ3.CHC.add_rule solver hypothesis conclusion);
  assert_equal (SrkZ3.CHC.check solver) `Sat;
  rules |> List.iter (fun (hypothesis, conclusion) ->
      let check =
        mk_and srk [hypothesis; (mk_not srk conclusion)]
        |> substitute_solution solver
        |> Formula.existential_closure srk
      in
      assert_equal (Smt.is_sat srk check) `Unsat)

let chc1 () =
  let psym = Ctx.mk_symbol ~name:"p" (`TyFun ([`TyInt; `TyInt], `TyBool)) in
  let qsym = Ctx.mk_symbol ~name:"q" (`TyFun ([`TyInt; `TyInt], `TyBool)) in
  let p (x, y) = Ctx.mk_app psym [x; y] in
  let q (x, y) = Ctx.mk_app qsym [x; y] in

  let rules =
    let open Infix in
    let (-->) x y = (x, y) in
    let v0 = var 0 `TyInt in
    let v1 = var 1 `TyInt in
    let v2 = var 2 `TyInt in
    [(v0 = (int 0) && (int 0) <= v1) --> p(v0, v1);
     (p(v0, v1) && v0 < v1 && v2 = v0 + (int 1)) --> p(v2, v1);
     (p(v0, v1) && v1 <= v0) --> q(v0, v1);
     q(v0, v1) --> (v0 = v1)]
  in
  verify_chc [psym; qsym] rules

let chc2 () =
  let psym = Ctx.mk_symbol ~name:"p" (`TyFun ([`TyInt; `TyInt], `TyBool)) in
  let qsym = Ctx.mk_symbol ~name:"q" (`TyFun ([`TyInt; `TyInt], `TyBool)) in
  let p (x, y) = Ctx.mk_app psym [x; y] in
  let q (x, y) = Ctx.mk_app qsym [x; y] in

  let rules =
    let open Infix in
    let (-->) x y = (x, y) in
    let v0 = var 0 `TyInt in
    let v1 = var 1 `TyInt in
    let v2 = var 2 `TyInt in
    [(v0 = (int 0) && (int 0) <= v1) --> p(v0, v1);
     (p(v0, v1) && v0 < v1 && v2 = v0 + (int 2)) --> p(v2, v1);
     (p(v0, v1) && v1 <= v0) --> q(v0, v1);
     q(v0, v1) --> (v0 = v1)]
  in
  let solver = SrkZ3.CHC.mk_solver srk in
  List.iter (SrkZ3.CHC.register_relation solver) [psym; qsym];
  rules |> List.iter (fun (hypothesis, conclusion) ->
      SrkZ3.CHC.add_rule solver hypothesis conclusion);
  assert_equal (SrkZ3.CHC.check solver) `Unsat

let chc3 () =
  let psym1 = Ctx.mk_symbol ~name:"p1" (`TyFun ([`TyInt; `TyInt], `TyBool)) in
  let qsym1 = Ctx.mk_symbol ~name:"q1" (`TyFun ([`TyInt; `TyInt], `TyBool)) in
  let rsym1 = Ctx.mk_symbol ~name:"r1" (`TyFun ([`TyInt; `TyInt], `TyBool)) in
  let psym2 = Ctx.mk_symbol ~name:"p2" (`TyFun ([`TyInt; `TyInt], `TyBool)) in
  let qsym2 = Ctx.mk_symbol ~name:"q2" (`TyFun ([`TyInt; `TyInt], `TyBool)) in
  let rsym2 = Ctx.mk_symbol ~name:"r2" (`TyFun ([`TyInt; `TyInt], `TyBool)) in
  let p1 (x, y) = Ctx.mk_app psym1 [x; y] in
  let q1 (x, y) = Ctx.mk_app qsym1 [x; y] in
  let r1 (x, y) = Ctx.mk_app rsym1 [x; y] in
  let p2 (x, y) = Ctx.mk_app psym2 [x; y] in
  let q2 (x, y) = Ctx.mk_app qsym2 [x; y] in
  let r2 (x, y) = Ctx.mk_app rsym2 [x; y] in

  let rules =
    let open Infix in
    let (-->) x y = (x, y) in
    let v0 = var 0 `TyInt in
    let v1 = var 1 `TyInt in
    let v2 = var 2 `TyInt in
    [((int 1) <= v0) --> p1(v0,v1);
     ((int 1) <= v0) --> p2(v0,v2);

     (p1(v0,v1) && p2(v0,v2)) --> q1(v0,v0);
     (p1(v0,v1) && p2(v0,v2)) --> p2(v0,v2);

     (q1(v0,v1) && p2(v0,v2)) --> q1(v0,v1);
     (q1(v0,v1) && p2(v0,v2)) --> q2(v0,v0);

     (q1(v0,v1) && q2(v0,v2)) --> r1(v0 + v1,v1);
     (q1(v0,v1) && q2(v0,v2)) --> q2(v0 + v1,v2);

     (r1(v0,v1) && q2(v0,v2)) --> r1(v0 + v2,v1);
     (r1(v0,v1) && q2(v0,v2)) --> r2(v0 + v2,v2);

     (r1(v0,v1) && r2(v0,v2)) --> ((int 2) <= v0)]
  in
  verify_chc [psym1; qsym1; rsym1; psym2; qsym2; rsym2] rules

let chc_trivial_false () =
  let psym = Ctx.mk_symbol ~name:"p" (`TyFun ([`TyInt], `TyBool)) in
  let qsym = Ctx.mk_symbol ~name:"q" (`TyFun ([`TyInt], `TyBool)) in
  let p x = Ctx.mk_app psym [x] in
  let q x = Ctx.mk_app qsym [x] in
  let rules =
    let open Infix in
    let (-->) x y = (x, y) in
    let v0 = var 0 `TyInt in
    [fls --> p(v0);
     p(v0) --> q(v0)]
  in
  verify_chc [psym; qsym] rules

let chc_trivial_true () =
  let psym = Ctx.mk_symbol ~name:"p" (`TyFun ([`TyInt], `TyBool)) in
  let qsym = Ctx.mk_symbol ~name:"q" (`TyFun ([`TyInt], `TyBool)) in
  let p x = Ctx.mk_app psym [x] in
  let q x = Ctx.mk_app qsym [x] in
  let rules =
    let open Infix in
    let (-->) x y = (x, y) in
    let v0 = var 0 `TyInt in
    [tru --> p(v0);
     (p(v0) && v0 <= (int 0)) --> q(v0);
     (q(v0) && (int 0) < v0) --> fls]
  in
  verify_chc [psym; qsym] rules

let suite = "SMT" >:::
  [
    "roundtrip0" >:: roundtrip0;
    "roundtrip1" >:: roundtrip1;
    "roundtrip2" >:: roundtrip2;
    "roundtrip3" >:: roundtrip3;
    "roundtrip4" >:: roundtrip4;
    "interpolate1" >:: interpolate1;
    "interpolate2" >:: interpolate2;
    "interpolate3" >:: interpolate3;
    "interpretation1" >:: interpretation1;
    "implicant1" >:: implicant1;
    "affine_interp1" >:: affine_interp1;
    "affine_interp2" >:: affine_interp2;
    "chc1" >:: chc1;
    "chc2" >:: chc2;
    "chc3" >:: chc3;
    "chc_trivial_false" >:: chc_trivial_false;
    "chc_trivial_true" >:: chc_trivial_true;
  ]

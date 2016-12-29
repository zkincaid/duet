open Apak
open OUnit
open BatPervasives
open Syntax
open ArkApron

module Ctx = MakeSimplifyingContext ()
module Infix = Syntax.Infix(Ctx)
let ctx = Ctx.context
let smt_ctx = ArkZ3.mk_context ctx []

let vsym = Ctx.mk_symbol ~name:"v" `TyInt
let wsym = Ctx.mk_symbol ~name:"w" `TyInt
let xsym = Ctx.mk_symbol ~name:"x" `TyInt
let ysym = Ctx.mk_symbol ~name:"y" `TyInt
let zsym = Ctx.mk_symbol ~name:"z" `TyInt
let v : 'a term = Ctx.mk_const vsym
let w : 'a term = Ctx.mk_const wsym
let x : 'a term = Ctx.mk_const xsym
let y : 'a term = Ctx.mk_const ysym
let z : 'a term = Ctx.mk_const zsym

let frac num den = Ctx.mk_real (QQ.of_frac num den)
let int k = Ctx.mk_real (QQ.of_int k)

let assert_equiv_formula s t =
  assert_equal ~printer:(Formula.show ctx) ~cmp:(smt_ctx#equiv) s t

let assert_implies phi psi =
  psi |> List.iter (fun atom ->
      let not_atom =
        rewrite ctx ~down:(nnf_rewriter ctx) (mk_not ctx atom)
      in
      if not (Synthetic.is_bottom (Synthetic.of_atoms ctx (not_atom::phi))) then
        assert_failure (Printf.sprintf "%s\ndoes not imply\n%s"
                          (Formula.show ctx (mk_and ctx phi))
                          (Formula.show ctx atom)))

let roundtrip1 () =
  let atoms =
    let open Infix in
    [(x + (int 2) * y + (int 3) * z) <= (int 0);
     w + y <= (int 0)]
  in
  let phi =
    Synthetic.of_atoms ctx atoms
    |> Synthetic.to_atoms
    |> mk_and ctx
  in
  let psi = mk_and ctx atoms in
  assert_equiv_formula psi phi

let roundtrip2 () =
  let atoms =
    let open Infix in
    [(x * y) <= (int 0);
     ((y * z * z) / x) <= (int 0)]
  in
  let phi =
    Synthetic.of_atoms ctx atoms
    |> Synthetic.to_atoms
    |> mk_and ctx
  in
  let psi = mk_and ctx atoms in
  assert_equiv_formula psi phi

let strengthen1 () =
  let phi =
    let open Infix in
    [(int 4) <= (x * x)]
  in
  let psi =
    let open Infix in
    [(int 2) <= (x * x)]
  in
  assert_implies phi psi

let strengthen2 () =
  let phi =
    let open Infix in
    [(int 0) <= x;
     x <= (int 1000);
     y = x * x;
     (int 1000000) <= y]
  in
  let psi =
    let open Infix in
    [(int 1000) <= x;
     y <= (int 1000000)]
  in
  assert_implies phi psi

let strengthen3 () =
  let phi =
    let open Infix in
    [w <= x;
     (int 0) <= y;
     (int 0) <= w;
     z = x * y]
  in
  assert_implies phi [Ctx.mk_leq (int 0) z]

let strengthen4 () =
  let phi =
    let open Infix in
    [x = y * y; z = y * y + (int 1)]
  in
  assert_implies phi [Ctx.mk_lt x z]

let strengthen5 () =
  let phi =
    let open Infix in
    [x = y; z = x * x]
  in
  let psi =
    let open Infix in
    [z <= y * y; y * y <= z]
  in
  assert_implies phi psi

let strengthen6 () =
  let phi =
    let open Infix in
    [(int 0) <= y; (int 1) <= x; z = x * y; z <= (int 10) * x]
  in
  let psi =
    let open Infix in
    [(int 0) <= z; y <= (int 10)]
  in
  assert_implies phi psi

let join1 () =
  let phi =
    let open Infix in
    Synthetic.of_atoms ctx [x = int 0; y = int 1]
  in
  let psi =
    let open Infix in
    Synthetic.of_atoms ctx [int 0 <= x; x = y * y]
  in
  let result =
    let open Infix in
    [x <= y * y]
  in
  assert_implies (Synthetic.to_atoms (Synthetic.join phi psi)) result

let join2 () =
  let phi =
    let open Infix in
    Synthetic.of_atoms ctx [x = int 0; y = int 1]
  in
  let psi =
    let open Infix in
    Synthetic.of_atoms ctx [y = int 2; x = int 1]
  in
  let result =
    let open Infix in
    [x <= y]
  in
  assert_implies (Synthetic.to_atoms (Synthetic.join phi psi)) result

let exists1 () =
  let phi =
    (let open Infix in
     Synthetic.of_atoms ctx [x = y; z = y * y])
    |> Synthetic.exists (fun sym -> sym = xsym || sym = zsym)
  in
  let psi =
    let open Infix in
    [z <= x * x; x * x <= z]
  in
  assert_implies (Synthetic.to_atoms phi) psi

let exists2 () =
  let phi =
    (let open Infix in
     Synthetic.of_atoms ctx [x = y; z <= y * y; w <= x * x])
    |> Synthetic.exists (fun sym -> sym = xsym || sym = zsym || sym = wsym)
  in
  let psi =
    let open Infix in
    [z <= x * x; w <= x * x]
  in
  assert_implies (Synthetic.to_atoms phi) psi

let suite = "Synthetic" >::: [
    "roundtrip1" >:: roundtrip1;
    "roundtrip2" >:: roundtrip2;
    "strengthen1" >:: strengthen1;
    "strengthen2" >:: strengthen2;
    "strengthen3" >:: strengthen3;
    "strengthen4" >:: strengthen4;
    "strengthen5" >:: strengthen5;
    "strengthen6" >:: strengthen6;
    "join1" >:: join1;
    "join2" >:: join2;
    "exist1" >:: exists1;
    "exist2" >:: exists2;
  ]

open Apak
open OUnit
open BatPervasives
open Syntax
open ArkApron

module Ctx = MakeSimplifyingContext ()
module Infix = Syntax.Infix(Ctx)
let ctx = Ctx.context
let smt_ctx = ArkZ3.mk_context ctx []

let qsym = Ctx.mk_symbol ~name:"q" `TyReal
let rsym = Ctx.mk_symbol ~name:"r" `TyReal
let ssym = Ctx.mk_symbol ~name:"s" `TyReal
let q : 'a term = Ctx.mk_const qsym
let r : 'a term = Ctx.mk_const rsym
let s : 'a term = Ctx.mk_const ssym

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
      if not (Cube.is_bottom (Cube.of_atoms ctx (not_atom::phi))) then
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
    Cube.of_atoms ctx atoms
    |> Cube.to_atoms
    |> mk_and ctx
  in
  let psi = mk_and ctx atoms in
  assert_equiv_formula psi phi

let roundtrip2 () =
  let atoms =
    let open Infix in
    [(x * y) <= (int 0);
     ((y * z * z) * ((int 1) / x)) <= (int 0)]
  in
  let phi =
    Cube.of_atoms ctx atoms
    |> Cube.to_atoms
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
    Cube.of_atoms ctx [x = int 0; y = int 1]
  in
  let psi =
    let open Infix in
    Cube.of_atoms ctx [int 0 <= x; x = y * y]
  in
  let result =
    let open Infix in
    [x <= y * y]
  in
  assert_implies (Cube.to_atoms (Cube.join phi psi)) result

let join2 () =
  let phi =
    let open Infix in
    Cube.of_atoms ctx [x = int 0; y = int 1]
  in
  let psi =
    let open Infix in
    Cube.of_atoms ctx [y = int 2; x = int 1]
  in
  let result =
    let open Infix in
    [x <= y]
  in
  assert_implies (Cube.to_atoms (Cube.join phi psi)) result

let exists1 () =
  let phi =
    (let open Infix in
     Cube.of_atoms ctx [x = y; z = y * y])
    |> Cube.exists (fun sym -> sym = xsym || sym = zsym)
  in
  let psi =
    let open Infix in
    [z <= x * x; x * x <= z]
  in
  assert_implies (Cube.to_atoms phi) psi

let exists2 () =
  let phi =
    (let open Infix in
     Cube.of_atoms ctx [x = y; z <= y * y; w <= x * x])
    |> Cube.exists (fun sym -> sym = xsym || sym = zsym || sym = wsym)
  in
  let psi =
    let open Infix in
    [z <= x * x; w <= x * x]
  in
  assert_implies (Cube.to_atoms phi) psi

let exists3 () =
  let phi =
    (let open Infix in
     Cube.of_atoms ctx [x <= y; y <= z])
    |> Cube.exists (fun sym -> sym != ysym)
  in
  let psi =
    let open Infix in
    [x <= z]
  in
  assert_implies (Cube.to_atoms phi) psi

let exists4 () =
  let phi =
    (let open Infix in
     Cube.of_atoms ctx [x = q; y = r; y <= q])
    |> Cube.exists (fun sym -> sym = xsym || sym = rsym)
  in
  let psi =
    let open Infix in
    [r <= x]
  in
  assert_implies (Cube.to_atoms phi) psi

let widen1 () =
  let phi =
    let open Infix in
    Cube.of_atoms ctx [x = int 0; y = int 1]
  in
  let psi =
    let open Infix in
    Cube.of_atoms ctx [y = int 1; z = int 0]
  in
  let top_formula =
    let open Infix in
    Cube.of_atoms ctx [x = int 0; z = int 0]
  in
  let result =
    let open Infix in
    [y <= int 1; int 1 <= y]
  in
  assert_implies (Cube.to_atoms (Cube.widen phi psi)) result;
  assert_equal
    ~printer:Cube.show
    ~cmp:Cube.equal
    (Cube.top ctx)
    (Cube.join (Cube.widen phi psi) top_formula)

let widen2 () =
  let phi =
    let open Infix in
    Cube.of_atoms ctx [x = y * y; (int 2) <= y; x <= (int 100)]
  in
  let psi =
    let open Infix in
    Cube.of_atoms ctx [(int 4) <= x; x <= (int 101); (int 2) <= y]
  in
  let result =
    let open Infix in
    Cube.of_atoms ctx [(int 2) <= y]
  in
  assert_equal
    ~printer:Cube.show
    ~cmp:Cube.equal
    result
    (Cube.widen phi psi)

let abstract_bounds cube symbol =
  let symbol_term = Ctx.mk_const symbol in
  let (lower, upper) = Cube.symbolic_bounds cube symbol in
  let lower = List.map (fun lb -> Ctx.mk_leq lb symbol_term) lower in
  let upper = List.map (fun ub -> Ctx.mk_leq symbol_term ub) upper in
  lower@upper

let symbound () =
  let open Infix in
  let phi =
    [x = y; x <= (int 2); z <= x; r <= s]
  in
  let x_bounds = abstract_bounds (Cube.of_atoms ctx phi) xsym in
  assert_implies x_bounds [x <= y];
  assert_implies x_bounds [y <= x];
  assert_implies x_bounds [x <= (int 2)];
  assert_implies x_bounds [z <= x]

let suite = "Cube" >::: [
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
    "exist3" >:: exists3;
    "exist4" >:: exists4;
    "widen1" >:: widen1;
    "widen2" >:: widen2;
    "symbound" >:: symbound;
  ]

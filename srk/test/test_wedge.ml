open Srk
open OUnit
open BatPervasives
open Syntax
open Test_pervasives

module CS = CoordinateSystem

let (pow, log) =
  Nonlinear.ensure_symbols srk;
  (get_named_symbol srk "pow",
   get_named_symbol srk "log")

let mk_log (base : 'a arith_term) (x : 'a arith_term) = mk_app srk log [base; x]
let mk_pow (base : 'a arith_term) (exp : 'a arith_term) = mk_app srk pow [base; exp]

let assert_implies phi psi =
  psi |> List.iter (fun atom ->
      let not_atom =
        rewrite srk ~down:(pos_rewriter srk) (mk_not srk atom)
      in
      let wedge = Wedge.of_atoms srk (not_atom::phi) in
      Wedge.strengthen wedge;
      if not (Wedge.is_bottom wedge) then
        assert_failure (Printf.sprintf "%s\ndoes not imply\n%s"
                          (Formula.show srk (mk_and srk phi))
                          (Formula.show srk atom)))

let cs_roundtrip1 () =
  let cs = CoordinateSystem.mk_empty srk in
  let xy = mk_mul srk [x; y] in
  let yx = mk_mul srk [y; x] in
  CS.admit_term cs xy;
  CS.admit_term cs yx;
  assert_equal_arith_term xy (CS.term_of_vec cs (CS.vec_of_term cs xy));
  assert_equal_arith_term yx (CS.term_of_vec cs (CS.vec_of_term cs yx))

let cs_roundtrip2 () =
  let cs = CoordinateSystem.mk_empty srk in
  let x4x = mk_mul srk [x; mk_real srk (QQ.of_int 4); x] in
  let xx = mk_mul srk [x; x] in
  let fourxx = mk_mul srk [mk_real srk (QQ.of_int 4); xx] in
  CS.admit_term cs x4x;
  assert_equal_arith_term fourxx (CS.term_of_vec cs (CS.vec_of_term cs x4x))

let roundtrip1 () =
  let atoms =
    let open Infix in
    [(x + (int 2) * y + (int 3) * z) <= (int 0);
     w + y <= (int 0)]
  in
  let phi =
    Wedge.of_atoms srk atoms
    |> Wedge.to_atoms
    |> mk_and srk
  in
  let psi = mk_and srk atoms in
  assert_equiv_formula psi phi

let roundtrip2 () =
  let atoms =
    let open Infix in
    [(x * y) <= (int 0);
     ((y * z * z) * ((int 1) / x)) <= (int 0)]
  in
  let phi =
    Wedge.of_atoms srk atoms
    |> Wedge.to_atoms
    |> mk_and srk
  in
  let psi = mk_and srk atoms in
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
    Wedge.of_atoms srk [x = int 0; y = int 1]
  in
  let psi =
    let open Infix in
    Wedge.of_atoms srk [int 0 <= x; x = y * y]
  in
  let result =
    let open Infix in
    [x <= y * y]
  in
  assert_implies (Wedge.to_atoms (Wedge.join phi psi)) result

let join2 () =
  let phi =
    let open Infix in
    Wedge.of_atoms srk [x = int 0; y = int 1]
  in
  let psi =
    let open Infix in
    Wedge.of_atoms srk [y = int 2; x = int 1]
  in
  let result =
    let open Infix in
    [x <= y]
  in
  assert_implies (Wedge.to_atoms (Wedge.join phi psi)) result

let exists1 () =
  let phi =
    (let open Infix in
     Wedge.of_atoms srk [x = y; z = y * y])
    |> Wedge.exists (fun sym -> sym = xsym || sym = zsym)
  in
  let psi =
    let open Infix in
    [z <= x * x; x * x <= z]
  in
  assert_implies (Wedge.to_atoms phi) psi

let exists2 () =
  let phi =
    (let open Infix in
     Wedge.of_atoms srk [x = y; z <= y * y; w <= x * x])
    |> Wedge.exists (fun sym -> sym = xsym || sym = zsym || sym = wsym)
  in
  let psi =
    let open Infix in
    [z <= x * x; w <= x * x]
  in
  assert_implies (Wedge.to_atoms phi) psi

let exists3 () =
  let phi =
    (let open Infix in
     Wedge.of_atoms srk [x <= y; y <= z])
    |> Wedge.exists (fun sym -> sym != ysym)
  in
  let psi =
    let open Infix in
    [x <= z]
  in
  assert_implies (Wedge.to_atoms phi) psi

let exists4 () =
  let phi =
    (let open Infix in
     Wedge.of_atoms srk [x = q; y = r; y <= q])
    |> Wedge.exists (fun sym -> sym = xsym || sym = rsym)
  in
  let psi =
    let open Infix in
    [r <= x]
  in
  assert_implies (Wedge.to_atoms phi) psi

let exists_powlog () =
  let phi =
    Wedge.of_atoms srk
      Infix.[y = mk_pow (int 2) x;
             x = w;
             (int 1) <= y;
             z <= y;
             y <= z]
    |> Wedge.exists
      (fun (sym : Syntax.symbol) -> sym = wsym || sym = zsym)
      ~subterm:(fun sym -> sym = zsym)
  in
  let psi =
    Infix.[mk_log (int 2) z <= w;
           w <= mk_log (int 2) z]
  in
  assert_implies (Wedge.to_atoms phi) psi

let exists_mul2 () =
  let phi =
    Wedge.of_atoms srk
      Infix.[(int 0) <= x;
             x <= y;
             z <= x * x]
    |> Wedge.exists
      (fun (sym : Syntax.symbol) -> sym = ysym || sym = zsym)
  in
  let psi =
    Infix.[z <= y * y]
  in
  assert_implies (Wedge.to_atoms phi) psi

let exists_mul3 () =
  let phi =
    Wedge.of_atoms srk
      Infix.[(int 0) <= x;
             x <= y;
             z <= x * x * x]
    |> Wedge.exists
      (fun (sym : Syntax.symbol) -> sym = ysym || sym = zsym)
  in
  let psi =
    Infix.[z <= y * y * y]
  in
  assert_implies (Wedge.to_atoms phi) psi

let exists_mul4 () =
  let phi =
    Wedge.of_atoms srk
      Infix.[(int 0) <= x;
             x <= y;
             z <= x * x * x * x]
    |> Wedge.exists
      (fun (sym : Syntax.symbol) -> sym = ysym || sym = zsym)
  in
  let psi =
    Infix.[z <= y * y * y * y]
  in
  assert_implies (Wedge.to_atoms phi) psi

let exists_nlogn () =
  let phi =
    Wedge.of_atoms srk
      Infix.[(int 0) <= x;
             x <= y;
             z <= x * (mk_log (int 2) x)]
    |> Wedge.exists
      (fun (sym : Syntax.symbol) -> sym = ysym || sym = zsym)
  in
  let psi =
    Infix.[z <= y * (mk_log (int 2) y)]
  in
  assert_implies (Wedge.to_atoms phi) psi

let elim_inverse () =
  let phi =
    Infix.((int 0) <= (int 1) / x + ((int 1) / x) * y
           && (int 0) <= x
           && y <= (int (-2)))
  in
  assert_equal (Wedge.is_sat srk phi) `Unsat

let widen1 () =
  let phi =
    let open Infix in
    Wedge.of_atoms srk [x = int 0; y = int 1]
  in
  let psi =
    let open Infix in
    Wedge.of_atoms srk [y = int 1; z = int 0]
  in
  let top_formula =
    let open Infix in
    Wedge.of_atoms srk [x = int 0; z = int 0]
  in
  let result =
    let open Infix in
    [y <= int 1; int 1 <= y]
  in
  assert_implies (Wedge.to_atoms (Wedge.widen phi psi)) result;
  assert_equal
    ~printer:Wedge.show
    ~cmp:Wedge.equal
    (Wedge.top srk)
    (Wedge.join (Wedge.widen phi psi) top_formula)

let widen2 () =
  let phi =
    let open Infix in
    Wedge.of_atoms srk [x <= y * y; (int 2) <= y; x <= (int 100)]
  in
  let psi =
    let open Infix in
    Wedge.of_atoms srk [(int 4) <= x; x <= (int 101); (int 2) <= y]
  in
  let result =
    let open Infix in
    Wedge.of_atoms srk [(int 2) <= y]
  in
  assert_equal
    ~printer:Wedge.show
    ~cmp:Wedge.equal
    result
    (Wedge.widen phi psi)

let abstract_bounds wedge symbol =
  let symbol_term = Ctx.mk_const symbol in
  let (lower, upper) = Wedge.symbolic_bounds wedge symbol in
  let lower = List.map (fun lb -> Ctx.mk_leq lb symbol_term) lower in
  let upper = List.map (fun ub -> Ctx.mk_leq symbol_term ub) upper in
  lower@upper

let symbound () =
  let open Infix in
  let phi =
    [x = y; x <= (int 2); z <= x; r <= s]
  in
  let x_bounds = abstract_bounds (Wedge.of_atoms srk phi) xsym in
  assert_implies x_bounds [x <= y];
  assert_implies x_bounds [y <= x];
  assert_implies x_bounds [x <= (int 2)];
  assert_implies x_bounds [z <= x]

let powlog () =
  let open Infix in
  let phi =
    [(int 1) <= x; x <= mk_pow (int 2) y; y + (int 1) = mk_log (int 2) x]
  in
  assert_implies phi [(int 1) <= (int 0)]

let suite = "Wedge" >::: [
    "cs_roundtrip1" >:: cs_roundtrip1;
    "cs_roundtrip2" >:: cs_roundtrip2;
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
    "exists_powlog" >:: exists_powlog;
    "exists_mul2" >:: exists_mul2;
    "exists_mul3" >:: exists_mul3;
    "exists_mul4" >:: exists_mul4;
    "exists_nlogn" >:: exists_nlogn;
    "elim_inverse" >:: elim_inverse;
    "widen1" >:: widen1;
    "widen2" >:: widen2;
    "symbound" >:: symbound;
    "powlog" >:: powlog;
  ]

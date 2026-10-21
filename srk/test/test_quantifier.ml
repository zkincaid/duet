open Srk
open OUnit
open Quantifier
open Test_pervasives

let simsat_ground () =
  assert_equal `Sat (simsat srk (Ctx.mk_leq x y))

let simsat_forward_ground () =
  assert_equal `Sat (simsat_forward srk (Ctx.mk_leq x y))

let simsat1 () =
  let phi =
    Ctx.mk_forall ~name:"r" `TyReal
      (Ctx.mk_exists ~name:"s" `TyReal
         (Ctx.mk_lt (Ctx.mk_var 1 `TyReal) (Ctx.mk_var 0 `TyReal)))
  in
  assert_equal `Sat (simsat srk phi)

let mbp1 () =
  let phi =
    let open Infix in
    let s = Ctx.mk_var 0 `TyReal in
    (Ctx.mk_exists ~name:"s" `TyReal
       (s = r && (s <= (int 0) || r <= (int 1))))
  in
  let psi =
    let open Infix in
    r <= (int 1)
  in
  assert_equiv_formula (qe_mbp srk phi) psi

let mbp2 () =
  let phi =
    let s = Ctx.mk_var 0 `TyReal in
    Ctx.mk_forall ~name:"s" `TyReal
      (Ctx.mk_leq r (Ctx.mk_ite
                       (Ctx.mk_lt (int 0) s)
                       s
                       (Ctx.mk_neg s)))
  in
  let psi = Ctx.mk_leq r (int 0) in
  assert_equiv_formula (qe_mbp srk phi) psi

(* Free Boolean constants are kept by quantifier elimination, and
   quantified ones are eliminated *)
let qe_mbp_booleans () =
  let b : Ctx.formula = Ctx.mk_const (Ctx.mk_symbol ~name:"b" `TyBool) in
  let open Infix in
  let s = Ctx.mk_var 0 `TyReal in
  assert_equiv_formula
    (qe_mbp srk (Ctx.mk_exists ~name:"s" `TyReal
                   ((b && r < s && s < q) || (!b && s = r && s <= (int 0)))))
    ((b && r < q) || (!b && r <= (int 0)));
  let b = Ctx.mk_var 0 `TyBool in
  assert_equiv_formula
    (qe_mbp srk (Ctx.mk_exists ~name:"b" `TyBool ((b && r < q) || (!b && q < r))))
    (r < q || q < r);
  assert_equiv_formula
    (qe_mbp srk (Ctx.mk_forall ~name:"b" `TyBool (b || r < q)))
    (r < q)

let sim1 () =
  let phi =
    let x = Ctx.mk_var 1 `TyInt in
    let y = Ctx.mk_var 0 `TyInt in
    let open Infix in
    Ctx.mk_exists ~name:"x" `TyInt
      (Ctx.mk_forall ~name:"y" `TyInt
         ((Ctx.mk_not ((y < x) && (x < (int 2))))
          || x = (int 1)))
  in
  assert_bool "sim1" (simsat srk phi = `Sat)

let sim2 () =
  let phi =
    let x = Ctx.mk_var 1 `TyInt in
    let y = Ctx.mk_var 0 `TyInt in
    let open Infix in
    Ctx.mk_exists ~name:"x" `TyInt
      (Ctx.mk_forall ~name:"y" `TyInt
         (x <= (Ctx.mk_ite ((int 0) < y) y (Ctx.mk_neg y))))
  in
  assert_bool "sim2" (simsat srk phi = `Sat)

let strategy1 () =
  let phi =
    let open Infix in
    (((int 0) <= x) && (x < y))
    || ((x < (int 0)) && (y < x))
  in
  let qf_prefix = [`Forall, xsym; `Exists, ysym] in
  match winning_strategy srk qf_prefix phi with
  | `Sat strategy ->
    assert_bool "strategy1" (check_strategy srk qf_prefix phi strategy)
  | _ -> assert false

let strategy2 () =
  let phi =
    let open Infix in
    (y < w) && (y < x)
    && (w < z) && (x < z)
  in
  let qf_prefix =
    [`Forall, wsym; `Forall, xsym; `Exists, ysym; `Exists, zsym]
  in
  match winning_strategy srk qf_prefix phi with
  | `Sat strategy ->
    assert_bool "strategy2" (check_strategy srk qf_prefix phi strategy)
  | _ -> assert false

(* Model-based projection fixes eliminated Booleans to their model values,
   and records kept Booleans as they appear in implicants, without
   enumerating their valuations.  Other non-arithmetic symbols cannot be
   projected. *)
let mbp_booleans () =
  let open Syntax in
  let p : Ctx.formula = Ctx.mk_const (Ctx.mk_symbol ~name:"p" `TyBool) in
  let phi = Test_pervasives.Infix.(mk_eq srk p (x < y) && p) in
  let keep = Symbol.Set.of_list [xsym; ysym] in
  assert_equiv_formula (Quantifier.mbp srk keep phi) Test_pervasives.Infix.(x < y);
  assert_equiv_formula (Quantifier.mbp ~dnf:true srk keep phi) Test_pervasives.Infix.(x < y);
  let bs = List.init 6 (fun i -> Ctx.mk_symbol ~name:("b" ^ string_of_int i) `TyBool) in
  let disjunction = mk_or srk (List.map (mk_const srk) bs) in
  let phi = mk_and srk [mk_leq srk y x; disjunction] in
  let keep = Symbol.Set.of_list (ysym::bs) in
  let result = Quantifier.mbp srk keep phi in
  assert_equiv_formula disjunction result;
  assert_equiv_formula disjunction (Quantifier.mbp ~dnf:true srk keep phi);
  let nb_disjuncts = match Formula.destruct srk result with
    | `Or xs -> List.length xs
    | _ -> 1
  in
  assert_bool (Printf.sprintf "%d disjuncts" nb_disjuncts) (nb_disjuncts <= 6);
  (* Only arithmetic and Boolean constants can be projected *)
  let projects_function =
    try ignore (Quantifier.mbp srk (Symbol.Set.singleton ysym)
                  (mk_leq srk (f x) y)); true
    with Invalid_argument _ -> false
  in
  assert_bool "mbp projects a function symbol" (not projects_function)

(* Boolean substitution also works when constructors do not simplify
   negated Boolean constants. *)
let mbp_boolean_contexts () =
  let open Syntax in
  let check srk =
    let b = mk_const srk (mk_symbol srk ~name:"b" `TyBool) in
    let xsym = mk_symbol srk ~name:"x" `TyInt in
    let eq = mk_eq srk (mk_const srk xsym) (mk_int srk 1) in
    let cases = [mk_and srk [mk_not srk b; eq];
                 mk_and srk [b; eq];
                 mk_and srk [mk_eq srk b eq; b]] in
    List.iter (fun dnf ->
        List.iter (fun phi ->
            let result = Quantifier.mbp ~dnf srk (Symbol.Set.singleton xsym) phi in
            assert_bool "Boolean projection preserves x = 1"
              (Smt.is_sat srk (mk_not srk (mk_iff srk result eq)) = `Unsat))
          cases)
      [false; true]
  in
  let module Raw = MakeContext () in
  let module Simplifying = MakeSimplifyingContext () in
  check Raw.context;
  check Simplifying.context

let suite = "Quantifier" >::: [
    "simsat_ground" >:: simsat_ground;
    "simsat_forward_ground" >:: simsat_forward_ground;
    "simsat1" >:: simsat1;
    "mbp1" >:: mbp1;
    "mbp2" >:: mbp2;
    "qe_mbp_booleans" >:: qe_mbp_booleans;
    "mbp_booleans" >:: mbp_booleans;
    "mbp_boolean_contexts" >:: mbp_boolean_contexts;
    "sim1" >:: sim1;
    "sim2" >:: sim2;
(*
    "strategy1" >:: strategy1;
    "strategy2" >:: strategy2;
*)
  ]

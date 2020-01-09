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

let suite = "Quantifier" >::: [
    "simsat_ground" >:: simsat_ground;
    "simsat_forward_ground" >:: simsat_forward_ground;
    "simsat1" >:: simsat1;
    "mbp1" >:: mbp1;
    "mbp2" >:: mbp2;
    "sim1" >:: sim1;
    "sim2" >:: sim2;
    "strategy1" >:: strategy1;
    "strategy2" >:: strategy2;
  ]

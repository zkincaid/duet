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

(* Exact output formula may differ if miniscope procedure is changed *)
let miniscope1 () = 
  let phi =
    let open Infix in
    exists ~name:"outer" `TyInt (
      exists `TyInt (
        (var 1 `TyInt = x) || (var 1 `TyInt) = (var 0 `TyInt)))
  in
  let psi = 
    let open Infix in
    exists `TyInt (exists ~name:"outer" `TyInt (var 0 `TyInt = var 1 `TyInt)) ||
    exists ~name:"outer" `TyInt (var 0 `TyInt = x) 
  in
  assert_equal_formula (miniscope srk phi) psi

let miniscope2 () = 
  let phi =
    let open Infix in
    exists ~name:"one" `TyInt (
      forall ~name:"two" `TyInt (
        exists ~name:"three" `TyInt (var 2 `TyInt = x || var 2 `TyInt + (int 5) = var 1 `TyInt)))
  in
  let psi =
    let open Infix in
    exists ~name:"one" `TyInt (forall `TyInt ~name:"two" (var 1 `TyInt + (int 5) = var 0 `TyInt)) ||
    exists ~name:"one" `TyInt (var 0 `TyInt = x)
  in
  assert_equal_formula (miniscope srk phi) psi

let miniscope3 () =
  let phi =
    let open Infix in
    forall ~name:"outer" `TyInt (
      ! (exists `TyInt ((var 0 `TyInt = var 1 `TyInt) || var 0 `TyInt = (int 1))))
  in
  let psi =
    let open Infix in
    ! (exists `TyInt (exists ~name:"outer" `TyInt (var 1 `TyInt = var 0 `TyInt)) ||
       exists `TyInt (var 0 `TyInt = (int 1)))
  in
  assert_equal_formula (miniscope srk phi) psi

let miniscope4 () =
  let phi =
    let open Infix in
    exists `TyInt (
      exists `TyInt (var 0 `TyInt = (int 1) || var 0 `TyInt = (int 1)))
  in
  let psi =
    let open Infix in
    exists `TyInt (var 0 `TyInt = (int 1)) || exists `TyInt (var 0 `TyInt = (int 1))
  in
  assert_equal_formula (miniscope srk phi) psi

let miniscope5 () =
  let phi =
    let open Infix in
    exists `TyInt (
      exists `TyInt (
        forall `TyInt (var 0 `TyInt = var 2 `TyInt)))
  in
  let psi =
    let open Infix in
    exists `TyInt (forall `TyInt (var 0 `TyInt = var 1 `TyInt))
  in
  assert_equal_formula (miniscope srk phi) psi

let miniscope6 () =
  let phi =
    let open Infix in
    exists `TyInt (
      forall `TyInt (
        var 0 `TyInt + (int 5) = var 1 `TyInt))
  in
  assert_equal_formula (miniscope srk phi) phi


let miniscope7 () =
  let phi =
    let open Infix in
    exists ~name:"outer" `TyInt (
      forall `TyInt (
        exists `TyInt (
        var 0 `TyInt + (int 5)= var 2 `TyInt)))
  in
  let psi = 
    let open Infix in
    exists `TyInt 
      (exists ~name:"outer" `TyInt (var 1 `TyInt + (int 5)= var 0 `TyInt))
  in
  assert_equal_formula (miniscope srk phi) psi

let miniscope8 () =
  let phi = 
    let open Infix in
    exists ~name:"q1"`TyInt (
      exists ~name:"q2" `TyInt (
        exists `TyInt (
          var 1 `TyInt = y))
      &&
      exists `TyInt (
        var 1 `TyInt = x))
  in
  let psi =
    let open Infix in
    exists ~name:"q1" `TyInt (var 0 `TyInt = x) &&
    exists ~name:"q2" `TyInt (var 0 `TyInt = y)
  in
  assert_equal_formula (miniscope srk phi) psi

let miniscope9 () =
  let phi = 
    let open Infix in
    forall ~name:"q1"`TyInt (
      exists ~name:"q2" `TyInt (
        Syntax.mk_and srk [var 0 `TyInt = x; var 0 `TyInt = y; var 1 `TyInt = x]))
  in
  let psi =
    let open Infix in
    forall ~name:"q1" `TyInt (var 0 `TyInt = x) &&
    exists ~name:"q2" `TyInt (var 0 `TyInt = x && var 0 `TyInt = y)
  in
  assert_equal_formula (miniscope srk phi) psi

let suite = "Quantifier" >::: [
    "simsat_ground" >:: simsat_ground;
    "simsat_forward_ground" >:: simsat_forward_ground;
    "simsat1" >:: simsat1;
    "mbp1" >:: mbp1;
    "mbp2" >:: mbp2;
    "sim1" >:: sim1;
    "sim2" >:: sim2;
    "miniscope1" >:: miniscope1;
    "miniscope2" >:: miniscope2;
    "miniscope3" >:: miniscope3;
    "miniscope4" >:: miniscope4;
    "miniscope5" >:: miniscope5;
    "miniscope6" >:: miniscope6;
    "miniscope7" >:: miniscope7;
    "miniscope8" >:: miniscope8;
    "miniscope9" >:: miniscope9;
(*
    "strategy1" >:: strategy1;
    "strategy2" >:: strategy2;
*)
  ]

open Srk
open OUnit
open Syntax
open Test_pervasives
open BatPervasives

let substitute () =
  let subst =
    let open Infix in
    function
    | 0 -> x
    | 2 -> (var 0 `TyInt)
    | _ -> raise Not_found
  in
  let phi =
    let open Infix in
    (y = (var 0 `TyInt))
    || (exists `TyInt
          ((y = (var 0 `TyInt) + (var 1 `TyInt))
           && (var 1 `TyInt) < (var 3 `TyInt)))
  in
  let psi =
    let open Infix in
    (y = x)
    || (exists `TyInt
          ((y = (var 0 `TyInt) + x)
           && x < (var 1 `TyInt)))
  in
  assert_equal_formula (substitute srk subst phi) psi

let existential_closure1 () =
  let phi =
    let open Infix in
    (x = (var 34 `TyInt) || (var 34 `TyInt) < y)
    && (var 35 `TyReal) <= (var 42 `TyReal)
    && (var 42 `TyReal) <= (var 34 `TyInt)
  in
  let psi =
    let open Infix in
    ((x = (var 0 `TyInt) || (var 0 `TyInt) < y)
     && (var 1 `TyReal) <= (var 2 `TyReal)
     && (var 2 `TyReal) <= (var 0 `TyInt))
    |> exists `TyInt
    |> exists `TyReal
    |> exists `TyReal
  in
  assert_equal_formula (Formula.existential_closure srk phi) psi

let existential_closure2 () =
  let phi =
    let open Infix in
    ((var 5 `TyReal) = (var 0 `TyInt) + (int 1))
    && (exists `TyInt
          ((var 0 `TyInt) = (var 6 `TyReal)))
  in
  let psi =
    let open Infix in
    exists `TyReal
      (exists `TyInt
         (((var 1 `TyReal) = (var 0 `TyInt) + (int 1))
          && (exists `TyInt
                ((var 0 `TyInt) = (var 2 `TyReal)))))
  in
  assert_equal_formula (Formula.existential_closure srk phi) psi

(* This test will fail if the implementation of prenex changes the way that
   unordered quantifiers get ordered (swap var 0 and var 1 in psi). *)
let prenex () =
  let phi =
    let open Infix in
    exists `TyReal
      ((exists `TyReal ((var 0 `TyReal) = (var 1 `TyReal)))
       && (exists `TyReal ((var 0 `TyReal) <= (var 1 `TyReal))))
  in
  let psi =
    let open Infix in
    exists `TyReal
      (exists `TyReal
         (exists `TyReal
            ((var 1 `TyReal) = (var 2 `TyReal)
             && (var 0 `TyReal) <= (var 2 `TyReal))))
  in
  assert_equal_formula (Formula.prenex srk phi) psi

let nnf () =
  let phi =
    let open Infix in
    exists `TyReal
      ((forall `TyReal ((var 0 `TyReal) <= (var 1 `TyReal)))
       && (x <= y || x < z))
  in
  let negate psi =
    rewrite srk ~down:(nnf_rewriter srk) (mk_not srk psi)
  in
  assert_equal_formula (negate (negate phi)) phi

let elim_ite1 () =
  let phi =
    let open Infix in
    (int 0) <= (Ctx.mk_ite (x < y) x y)
  in
  assert_equiv_formula (eliminate_ite srk phi) phi

let elim_ite2 () =
  let phi =
    let open Infix in
    x + (Ctx.mk_ite (x < z) x z)
    <= (Ctx.mk_ite (x < y) x y) + (Ctx.mk_ite (y < z) y z)
  in
  assert_equiv_formula (eliminate_ite srk phi) phi

let elim_ite3 () =
  let phi =
    let open Infix in
    (int 0) <= x + (Ctx.mk_ite ((Ctx.mk_ite (x < z) x z) < z) x y)
  in
  assert_equiv_formula (eliminate_ite srk phi) phi

let suite = "Syntax" >:::
  [
    "substitute" >:: substitute;
    "existential_closure1" >:: existential_closure1;
    "existential_closure2" >:: existential_closure2;
    "prenex" >:: prenex;
    "nnf" >:: nnf;
    "elim_ite1" >:: elim_ite1;
    "elim_ite2" >:: elim_ite2;
    "elim_ite3" >:: elim_ite3;
    "env1" >:: (fun () ->
      let e = List.fold_right Env.push [1;2;3;4;5] Env.empty in
      (0 -- 4) |> BatEnum.iter (fun i ->
                      assert_equal (Env.find e i) (i + 1)));
    "env2" >:: (fun () ->
      let e = List.fold_right Env.push [1;2;3;4;5] Env.empty in
      let e' = List.fold_right Env.push [-2;-1;0] e in
      assert_equal (Env.find e 0) 1;
      (0 -- 7) |> BatEnum.iter (fun i ->
                      assert_equal (Env.find e' i) (i - 2)));
  ]

open OUnit
open Syntax

let ctx = Syntax.mk_string_context ()

module S = ImplicitContext(struct
    type t = string * typ
    let context = ctx
  end)

let r = S.const (symbol_of_const ctx ("r", TyReal))
let s = S.const (symbol_of_const ctx ("s", TyReal))
let t = S.const (symbol_of_const ctx ("t", TyReal))

let w = S.const (symbol_of_const ctx ("w", TyInt))
let x = S.const (symbol_of_const ctx ("x", TyInt))
let y = S.const (symbol_of_const ctx ("y", TyInt))
let z = S.const (symbol_of_const ctx ("z", TyInt))

let frac num den = Term.mk_real ctx (QQ.of_frac num den)
let int k = Term.mk_real ctx (QQ.of_int k)

let assert_equal_term s t =
  assert_equal ~printer:(Term.show ctx) s t
let assert_equal_formula s t =
  assert_equal ~printer:(Formula.show ctx) s t

let substitute () =
  let subst =
    let open S in
    function
    | 0 -> x
    | 2 -> (var 0 TyInt)
    | _ -> raise Not_found
  in
  let phi =
    let open S in
    (y = (var 0 TyInt))
    || (exists TyInt
          ((y = (var 0 TyInt) + (var 1 TyInt))
           && (var 1 TyInt) < (var 3 TyInt)))
  in
  let psi =
    let open S in
    (y = x)
    || (exists TyInt
          ((y = (var 0 TyInt) + x)
           && x < (var 1 TyInt)))
  in
  assert_equal_formula (Formula.substitute ctx subst phi) psi

let existential_closure1 () =
  let phi =
    let open S in
    (x = (var 34 TyInt) || (var 34 TyInt) < y)
    && (var 35 TyReal) <= (var 42 TyReal)
    && (var 42 TyReal) <= (var 34 TyInt)
  in
  let psi =
    let open S in
    ((x = (var 0 TyInt) || (var 0 TyInt) < y)
     && (var 1 TyReal) <= (var 2 TyReal)
     && (var 2 TyReal) <= (var 0 TyInt))
    |> exists TyInt
    |> exists TyReal
    |> exists TyReal
  in
  assert_equal_formula (Formula.existential_closure ctx phi) psi

let existential_closure2 () =
  let phi =
    let open S in
    ((var 5 TyReal) = (var 0 TyInt) + (int 1))
    && (exists TyInt
          ((var 0 TyInt) = (var 6 TyReal)))
  in
  let psi =
    let open S in
    exists TyReal
      (exists TyInt
         (((var 1 TyReal) = (var 0 TyInt) + (int 1))         
          && (exists TyInt
                ((var 0 TyInt) = (var 2 TyReal)))))
  in
  assert_equal_formula (Formula.existential_closure ctx phi) psi

let suite = "SMT" >:::
  [
    "substitute" >:: substitute;
    "existential_closure1" >:: existential_closure1;
    "existential_closure2" >:: existential_closure2;
  ]

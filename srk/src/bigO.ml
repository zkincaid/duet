open Syntax
open BatPervasives

type t =
    Polynomial of int
  | Log
  | Exp of QQ.t
  | Unknown

let pp formatter x =
  let open Format in
  match x with
  | Polynomial 0 -> pp_print_string formatter "1"
  | Polynomial 1 -> pp_print_string formatter "n"
  | Polynomial k -> fprintf formatter "n^%d" k
  | Log -> pp_print_string formatter "log(n)"
  | Exp b -> fprintf formatter "%a^n" QQ.pp b
  | Unknown -> pp_print_string formatter "??"

let rec compare x y =
  match x, y with
  | Polynomial 0, Polynomial 0 -> `Eq
  | Polynomial 0, _ -> `Leq
  | _, Polynomial 0 -> `Geq
  | Unknown, _ | _, Unknown -> `Unknown
  | Log, Log -> `Eq
  | Log, _ -> `Leq
  | _, Log -> `Geq
  | Polynomial x, Polynomial y ->
    if x = y then
      `Eq
    else if x < y then
      `Leq
    else
      `Geq
  | Polynomial _, Exp _ -> `Leq
  | Exp _, Polynomial _ -> `Geq
  | Exp x, Exp y ->
    if QQ.equal x y then `Eq
    else if QQ.lt x y then `Leq
    else `Geq

let mul x y =
  match x, y with
  | Polynomial 0, x | x, Polynomial 0 -> x
  | Polynomial x, Polynomial y -> Polynomial (x + y)
  | Exp b, Exp b' -> Exp (QQ.max b b')
  | _, _ -> Unknown

let add x y =
  match x, y with
  | Unknown, _ | _, Unknown -> Unknown
  | Polynomial 0, x | x, Polynomial 0 -> x
  | Log, x | x, Log -> x
  | Polynomial x, Polynomial y -> Polynomial (max x y)
  | Exp b, Exp b' -> Exp (QQ.max b b')
  | Exp b, _ | _, Exp b -> Exp b

let minimum x y =
  match compare x y with
  | `Eq -> x
  | `Leq -> x
  | `Geq -> y
  | `Unknown -> Unknown

let maximum x y =
  match compare x y with
  | `Eq -> x
  | `Leq -> y
  | `Geq -> x
  | `Unknown -> Unknown

let of_term srk term =
  Nonlinear.ensure_symbols srk;
  Wedge.ensure_min_max srk;

  let pow = get_named_symbol srk "pow" in
  let log = get_named_symbol srk "log" in
  let min = get_named_symbol srk "min" in
  let max = get_named_symbol srk "max" in

  let rec go term =
    match Term.destruct srk term with
    | `Real _ -> Polynomial 0
    | `App (const, []) -> Polynomial 1
    | `App (func, [base; exp]) when func = pow ->
      let exp = match Expr.refine srk exp with
        | `Term t -> t
        | _ -> assert false
      in
      begin match destruct srk base, go exp with
        | `Real b, Polynomial 1 -> Exp b
        | _ , _ -> Unknown
      end
    | `App (func, [base; exp]) when func = log ->
      let exp = match Expr.refine srk exp with
        | `Term t -> t
        | _ -> assert false
      in
      begin match go exp with
        | Polynomial 0 -> Polynomial 0
        | Polynomial _ -> Log
        | Log -> Log (* imprecise *)
        | Exp _ -> Polynomial 1
        | _ -> Unknown
      end
    | `App (func, [x; y]) when func = min ->
      let (x, y) = match Expr.refine srk x, Expr.refine srk y with
        | (`Term s, `Term t) -> (s, t)
        | (_, _) -> assert false
      in
      minimum (go x) (go y)
    | `App (func, [x; y]) when func = max ->
      let (x, y) = match Expr.refine srk x, Expr.refine srk y with
        | (`Term s, `Term t) -> (s, t)
        | (_, _) -> assert false
      in
      maximum (go x) (go y)
    | `Add xs ->
      List.fold_left (fun x y -> add x (go y)) (Polynomial 0) xs
    | `Mul xs ->
      List.fold_left (fun x y -> mul x (go y)) (Polynomial 0) xs
    | `Unop (`Floor, t) | `Unop (`Neg, t) -> go t
    | _ -> Unknown
  in
  go term

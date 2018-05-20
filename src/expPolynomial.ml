open BatPervasives
open Syntax

module QQX = Polynomial.QQX
module QQMap = BatMap.Make(QQ)
module E = Ring.RingMap(QQMap)(QQX)

type t = E.t

let equal = E.equal

let pp formatter f =
  let pp_elt formatter (p, lambda) =
    if QQ.equal lambda QQ.one then
      QQX.pp formatter p
    else
      Format.fprintf formatter "(%a)%a^x" QQX.pp p QQ.pp lambda
  in
  let pp_sep fomatter () =
    Format.fprintf formatter "@ + "
  in
  SrkUtil.pp_print_enum_nobox ~pp_sep pp_elt formatter (E.enum f)

let show = SrkUtil.mk_show pp

let add = E.add

let negate = E.negate

let zero = E.zero

let one = E.of_term QQX.one QQ.one

let mul f g =
  BatEnum.fold (fun h (p1, lambda1) ->
      BatEnum.fold (fun h (p2, lambda2) ->
          E.add_term (QQX.mul p1 p2) (QQ.mul lambda1 lambda2) h)
        h
        (E.enum g))
    zero
    (E.enum f)

let compose_left_affine f coeff add =
  let g = QQX.add_term (QQ.of_int coeff) 1 (QQX.scalar (QQ.of_int add)) in
  BatEnum.fold (fun h (p, lambda) ->
      E.add_term
        ((QQX.scalar_mul (QQ.exp lambda add)) (QQX.compose p g))
        (QQ.exp lambda coeff)
        h)
    zero
    (E.enum f)

let of_polynomial p = E.of_term p QQ.one
let of_exponential lambda = E.of_term QQX.one lambda
let scalar k = E.of_term (QQX.scalar k) QQ.one

(* Given a list of (lambda_1, d_1)...(lambda_n, d_n) pairs and a list of values (v_0,...,v_m)
   find an exponential-polynomial of the form 
   f(x) = (lambda_1^x)(c_{1,0} + c_1x + ... + c_{d_1}x^{d_1})
          + ...
          + (lambda_n^x)(c_{n,0} + c_1x + ... + c_{d_n}x^{d_n})
   such that f(0) = v_0, ..., f(m) = v_m *)
let fit_curve lambda_orders values =
  let module M = Linear.QQMatrix in
  let module V = Linear.QQVector in
  (* Create a corresponding system of linear inequalities.  One row
     for each value in the list, one variable for each unknown
     coefficient. *)
  let (m, b) =
    BatList.fold_lefti (fun (m, b) i v ->
        let (row, _) =
          List.fold_left (fun (row, j) (lambda, order) ->
              let lambdai = QQ.exp lambda i in
              BatEnum.fold
                (fun (row, j) d ->
                  (V.add_term (QQ.mul lambdai (QQ.exp (QQ.of_int i) d)) j row, j + 1))
                (row, j)
                (0 -- order))
            (V.zero, 0)
            lambda_orders
        in
        (M.add_row i row m, V.add_term v i b))
      (M.zero, V.zero)
      values
  in
  let coeffs = Linear.solve_exn m b in
  List.fold_left (fun (f, i) (lambda, order) ->
      let (p, i) =
        BatEnum.fold
          (fun (p, i) d ->
            (QQX.add_term (V.coeff i coeffs) d p, i + 1))
          (QQX.zero, i)
          (0 -- order)
      in
      (E.add_term p lambda f, i))
    (E.zero, 0)
    lambda_orders
  |> fst

let solve_term_rec coeff lambda p =
  let p_order = QQX.order p in
  let lambda_orders =
    if QQ.equal coeff lambda then
      [lambda, p_order + 1]
    else
      [(coeff, 0); (lambda, p_order)]
  in
  let (values, _) =
    BatEnum.fold (fun (values, sum) i ->
        let qqi = QQ.of_int i in
        let sum =
          QQ.add (QQ.mul coeff sum) (QQ.mul (QQ.exp lambda i) (QQX.eval p qqi))
        in
        (sum::values, sum))
      ([], QQ.zero)
      (0 -- (p_order + 3))
  in
  fit_curve lambda_orders (List.rev values)

let summation f =
  BatEnum.fold (fun h (p, lambda) ->
      add h (solve_term_rec QQ.one lambda p))
    zero
    (E.enum f)

let solve_rec coeff f =
  BatEnum.fold (fun h (p, lambda) ->
      add h (solve_term_rec coeff lambda p))
    zero
    (E.enum f)

let term_of srk t f =
  Nonlinear.ensure_symbols srk;
  E.enum f /@ (fun (p, lambda) ->
      if QQ.equal lambda QQ.zero then
        mk_real srk (QQ.zero)
      else if QQ.equal lambda QQ.one then
        QQX.term_of srk t p
      else
        mk_mul srk [QQX.term_of srk t p;
                    Nonlinear.mk_pow srk (mk_real srk lambda) t])
  |> BatList.of_enum
  |> mk_add srk

open BatPervasives
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

let term_sum p lambda =
  let module M = Linear.QQMatrix in
  let module V = Linear.QQVector in
  if QQ.equal QQ.one lambda then
    E.of_term (QQX.summation p) QQ.one
  else
    let sum_order = QQX.order p in
    (* Create a system of linear equalities:
         c_n*0^n + ... + c_1*0 + c_0 = lambda^0 * p(0)
         c_n*1^n*lambda^1 + ... + c_1*1*lambda^1 + c_0 = lambda^0 * p(0) + lambda^1 * p(1)
         ...
         c_n*n^n*lambda^n + ... + c_1*1^lambda^n + c_0 = lambda^0 * p(0) + ... + lambda^n * p(n)
       
       We then solve for the c_i coefficients to get the sum *)
    let c0 = V.add_term QQ.one (-1) V.zero in
    let rec mk_sys k =
      if k = 0 then begin
        let rhs = QQX.eval p QQ.zero in
        let lhs = V.add_term QQ.one 0 c0 in
        (rhs, M.add_row 0 lhs M.zero, V.of_term rhs 0)
      end else begin
        let (prev, mat, b) = mk_sys (k - 1) in
        let qq_k = QQ.of_int k in
        let rhs = QQ.add prev (QQ.mul (QQ.exp lambda k) (QQX.eval p qq_k)) in
        let vars = 0 -- sum_order in
        let lhs =
          BatEnum.fold
            (fun (lhs, coeff) ord ->
               (V.add_term coeff ord lhs, QQ.mul coeff qq_k))
            (c0, QQ.exp lambda k)
            vars
          |> fst
        in
        (rhs, M.add_row k lhs mat, V.add_term rhs k b)
      end
    in
    let (_, mat, b) = mk_sys (sum_order+1) in
    let coeffs = Linear.solve_exn mat b in
    let (const, coeffs) = V.pivot (-1) coeffs in
    E.add_term
      (QQX.scalar const)
      QQ.one
      (E.of_term (QQX.of_enum (V.enum coeffs)) lambda)

let summation f =
  BatEnum.fold (fun h (p, lambda) ->
      add h (term_sum p lambda))
    zero
    (E.enum f)

let of_polynomial p = E.of_term p QQ.one
let of_exponential lambda = E.of_term QQX.one lambda
let scalar k = E.of_term (QQX.scalar k) QQ.one

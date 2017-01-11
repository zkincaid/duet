open BatPervasives

module type Ring = Linear.Ring

module type Univariate = sig
  include Linear.Vector with type dim = int
  val order : t -> int
  val mul : t -> t -> t
  val one : t
  val compose : t -> t -> t
  val identity : t
  val eval : t -> scalar -> scalar
  val exp : t -> int -> t
end

module Int = struct
  type t = int [@@deriving show,ord]
  let tag k = k
end
module IntMap = Apak.Tagged.PTMap(Int)

module Uvp(R : Ring) = struct
  include Linear.RingMap(IntMap)(R)

  let order p = IntMap.fold (fun power _ hi -> max hi power) p 0

  let one = of_term R.one 0

  let identity = of_term R.one 1

  let monomial_mul coeff power p =
    (IntMap.enum p)
    /@ (fun (power',coeff') -> (power * power', R.mul coeff coeff'))
    |> IntMap.of_enum

  let mul p q =
    BatEnum.fold
      (fun r ((pp,pc), (qp,qc)) -> add_term (R.mul pc qc) (pp + qp) r)
      zero
      (ApakEnum.cartesian_product (IntMap.enum p) (IntMap.enum q))

  let rec exp p n =
    if n = 0 then one
    else if n = 1 then p
    else begin
      let q = exp p (n / 2) in
      let q_squared = mul q q in
      if n mod 2 = 0 then q_squared
      else mul q q_squared
    end

  let compose p q =
    let rec go n = function
      | [] -> zero
      | (k,coeff)::xs ->
        let multiplier = exp q (k-n) in
        mul multiplier (add_term coeff 0 (go k xs))
    in
    IntMap.enum p
    |> BatList.of_enum
    |> BatList.sort (fun x y -> Pervasives.compare (fst x) (fst y))
    |> go 0

  let scalar k = add_term k 0 zero

  let eval p k = fst (pivot 0 (compose p (scalar k)))
end

module QQUvp = struct
  include Uvp(QQ)

  let pp formatter p =
    let pp_monomial formatter (order, coeff) =
      if order = 0 then
        QQ.pp formatter coeff
      else if QQ.equal coeff QQ.one then
        Format.fprintf formatter "@[x^%d@]" order
      else if QQ.equal coeff (QQ.negate QQ.one) then
        Format.fprintf formatter "@[-x^%d@]" order
      else
        Format.fprintf formatter "@[%a*x^%d@]" QQ.pp coeff order
    in
    ApakEnum.pp_print_enum
      ~pp_sep:(fun formatter () -> Format.fprintf formatter "@ + ")
      pp_monomial
      formatter
      (IntMap.enum p)

  let show = Apak.Putil.mk_show pp

  let summation p =
    let module M = Linear.QQMatrix in
    let module V = Linear.QQVector in
    let sum_order = (order p) + 1 in
    assert (sum_order > 0);
    (* Create a system of linear equalities:
           c_n*0^n + ... + c_1*0 + c_0 = p(0)
           c_n*1^n + ... + c_1*1 + c_0 = p(0) + p(1)
           c_n*2^n + ... + c_1*2 + c_0 = p(0) + p(1) + p(2)
           ...
           c_n*n^n + ... + c_1*n + c_0 = p(0) + p(1) + ... + p(n)

       We then solve for the c_i coefficients to get q *)
    let c0 = V.add_term QQ.one 0 V.zero in
    let rec mk_sys k =
      if k = 0 then begin
        let rhs = eval p QQ.zero in
        (rhs, M.add_row 0 c0 M.zero, V.of_term rhs 0)
      end else begin
        let (prev, mat, b) = mk_sys (k - 1) in
        let qq_k = QQ.of_int k in
        let rhs = QQ.add prev (eval p qq_k) in
        let vars = 1 --- sum_order in
        let lhs =
          (* compute lhs right-to-left: c_0 + k*c_1 + k^2*c_2 ... This avoids
             raising k to increasingly higher powers. *)
          BatEnum.fold
            (fun (lhs, last_coeff) ord ->
               let next_coeff = QQ.mul last_coeff qq_k in
               (V.add_term next_coeff ord lhs, next_coeff))
            (c0, QQ.one)
            vars
          |> fst
        in
        (rhs, M.add_row k lhs mat, V.add_term rhs k b)
      end
    in
    let (_, mat, b) = mk_sys sum_order in
    let coeffs = Linear.solve_exn mat b in
    of_enum (V.enum coeffs)
end

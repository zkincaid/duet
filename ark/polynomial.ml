open BatPervasives

module QQUvp = struct
  include Linear.QQVector

  let order p =
    BatEnum.fold (fun hi (_, power) -> max hi power) 0 (enum p) 

  let one = of_term QQ.one 0

  let identity = of_term QQ.one 1

  let monomial_mul coeff power p =
    (enum p)
    /@ (fun (coeff',power') -> (QQ.mul coeff coeff', power * power'))
    |> of_enum

  let mul p q =
    BatEnum.fold
      (fun r ((pc,pp), (qc,qp)) -> add_term (QQ.mul pc qc) (pp + qp) r)
      zero
      (ApakEnum.cartesian_product (enum p) (enum q))

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
      | (coeff,k)::xs ->
        let multiplier = exp q (k-n) in
        mul multiplier (add_term coeff 0 (go k xs))
    in
    enum p
    |> BatList.of_enum
    |> BatList.sort (fun x y -> Pervasives.compare (snd x) (snd y))
    |> go 0

  let eval p qq =
    let q = compose p (add_term qq 0 zero) in
    let (result, empty) = pivot 0 q in
    assert (equal empty zero);
    result

  let summation p =
    let module M = Linear.QQMatrix in
    let sum_order = (order p) + 1 in
    assert (sum_order > 0);
    (* Create a system of linear equalities:
           c_n*0^n + ... + c_1*0 + c_0 = p(0)
           c_n*1^n + ... + c_1*1 + c_0 = p(0) + p(1)
           c_n*2^n + ... + c_1*2 + c_0 = p(0) + p(1) + p(2)
           ...
           c_n*n^n + ... + c_1*n + c_0 = p(0) + p(1) + ... + p(n)

       We then solve for the c_i coefficients to get q *)
    let rec mk_sys k =
      if k = 0 then begin
        let rhs = eval p QQ.zero in
        (rhs, M.add_row 0 one M.zero, of_term rhs 0)
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
               (add_term next_coeff ord lhs, next_coeff))
            (one, QQ.one)
            vars
          |> fst
        in
        (rhs, M.add_row k lhs mat, add_term rhs k b)
      end
    in
    let (_, mat, b) = mk_sys sum_order in
    Linear.solve_exn mat b
end

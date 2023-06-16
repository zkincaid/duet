open BatPervasives
open Syntax

module QQX = Polynomial.QQX
module QQMatrix = Linear.QQMatrix

module MakeEP 
  (B : sig 
    include Algebra.Ring 
    val compare : t -> t -> int 
    val exp : t -> int -> t 
    val pp : Format.formatter -> t -> unit
  end)
  (C : sig
    include Algebra.Ring
    val lift : B.t -> t
    val int_mul : int -> t -> t
  end)
  (CX : sig
    include Polynomial.Univariate with type scalar = C.t
    val pp : Format.formatter -> t -> unit
  end) = struct

  open BatPervasives

  module E = Ring.RingMap(B)(CX)

  type t = E.t (*TODO include IIF*)

  let equal = E.equal

  let pp formatter f =
    let pp_elt formatter (p, lambda) =
      if B.equal lambda B.one then
        CX.pp formatter p
      else
        Format.fprintf formatter "(%a)%a^x" CX.pp p B.pp lambda
    in
    let pp_sep formatter () =
      Format.fprintf formatter "@ + "
    in
    if E.equal E.zero f then
      Format.pp_print_string formatter "0"
    else
      SrkUtil.pp_print_enum_nobox ~pp_sep pp_elt formatter (E.enum f)

  let show = SrkUtil.mk_show pp

  let add = E.add

  let negate = E.negate

  let zero = E.zero

  let one = E.of_term CX.one B.one

  let mul f g =
    BatEnum.fold (fun h (p1, lambda1) ->
        BatEnum.fold (fun h (p2, lambda2) ->
            E.add_term (CX.mul p1 p2) (B.mul lambda1 lambda2) h)
          h
          (E.enum g))
      zero
      (E.enum f)

  let of_polynomial p = E.of_term p B.one
  let of_exponential lambda = E.of_term CX.one lambda
  let scalar k = E.of_term (CX.scalar k) B.one
  let scalar_mul lambda f = E.map (fun _ -> CX.scalar_mul lambda) f

  let eval f x =
    let qq_x = C.int_mul x C.one in
    E.enum f
    /@ (fun (p, lambda) ->
        (C.mul (CX.eval p qq_x) (C.lift (B.exp lambda x))))
    |> BatEnum.fold C.add C.zero

end

include MakeEP(QQ)(struct include QQ let lift x = x end)(struct include QQX end)

let compose_left_affine f coeff add =
  let g = QQX.add_term (QQ.of_int coeff) 1 (QQX.scalar (QQ.of_int add)) in
  BatEnum.fold (fun h (p, lambda) ->
      E.add_term
        ((QQX.scalar_mul (QQ.exp lambda add)) (QQX.compose p g))
        (QQ.exp lambda coeff)
        h)
    zero
    (E.enum f)

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

(* Find a function f such that
   f(0) = 0
   f(n+1) = coeff*f(n) + lambda^n*p(n) *)
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
      ([QQ.zero], QQ.zero)
      (0 -- p_order)
  in
  fit_curve lambda_orders (List.rev values)

(* Find a function g such that
   g(0) = initial
   g(n+1) = coeff*g(n) + f(n) *)
let solve_rec ?(initial=QQ.zero) coeff f =
  let homogenous =
    BatEnum.fold (fun h (p, lambda) ->
        add h (solve_term_rec coeff lambda p))
      zero
      (E.enum f)
  in
  E.add_term (QQX.scalar initial) coeff homogenous

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

let summation f =
  solve_rec ~initial:(eval f 0) QQ.one (compose_left_affine f 1 1)

let enum = E.enum
let add_term = E.add_term
let of_term = E.of_term

module EP = struct
  type nonrec t = t
  let pp = pp
  let compose_left_affine = compose_left_affine
  let eval = eval
  let add = add
  let mul = mul
  let scalar = scalar
  let zero = zero
  let one = one
  let negate = negate
  let equal = equal
  let term_of = term_of
  let scalar_mul = scalar_mul
  let of_term = of_term
end

module Vector = struct
  include Ring.MakeVector(EP)
  let of_qqvector vec =
    Linear.QQVector.enum vec
    /@ (fun (k, dim) -> (EP.scalar k, dim))
    |> of_enum
end

module Matrix = struct
  include Ring.MakeMatrix(EP)
  let of_qqmatrix mat =
    BatEnum.fold
      (fun m (i, row) ->
         add_row i (Vector.of_qqvector row) m)
      zero
      (Linear.QQMatrix.rowsi mat)
  let pp = pp EP.pp
end

let exponentiate_rational matrix =
  let dims =
    SrkUtil.Int.Set.union
      (QQMatrix.row_set matrix)
      (QQMatrix.column_set matrix)
    |> SrkUtil.Int.Set.elements
  in
  let rsd = Linear.rational_spectral_decomposition matrix dims in
  if List.length rsd != List.length dims then
    None
  else
    let rsd_mat =
      BatList.fold_lefti (fun rsd_mat i (_, v) ->
          QQMatrix.add_row i v rsd_mat)
        QQMatrix.zero
        rsd
    in
    let cf_matrix = (* rsd_mat * matrix^k *)
      BatList.fold_lefti (fun cf i (lambda, v) ->
          if QQ.equal lambda QQ.zero then
            cf
          else
            let lambdak = of_exponential lambda in
            (* If we have a Jordan chain
                  v_0*M = lambda*v_0 + v_1
                  v_1*M = lambda*v_1 + v_2
                  ...
                  v_m*M = lambda*v_m,
               then
                  v_1*M^k = sum_i lambda^{k-i} * (k choose i) * v_i *)
            let cf_v =
              BatList.fold_lefti (fun cf i v ->
                  let coeff =
                    (* lambda^{k-i} * (k choose i) *)
                    mul
                      (scalar_mul (QQ.inverse (QQ.exp lambda i)) lambdak)
                      (of_polynomial (Polynomial.QQX.choose i))
                  in
                  Vector.add
                    (Vector.scalar_mul coeff (Vector.of_qqvector v))
                    cf)
                Vector.zero
                (Linear.jordan_chain matrix lambda v)
            in
            Matrix.add_row i cf_v cf)
        Matrix.zero
        rsd
    in
    (* rsd_mat_inv * cf_matrix = rsd_mat_inv * rsd_mat * matrix^k = matrix^k *)
    let rsd_mat_inv =
      match Linear.divide_right (QQMatrix.identity dims) rsd_mat with
      | Some m -> m
      | _ -> assert false (* dimension of rsd is equal to matrix size *)
    in
    Some (Matrix.mul (Matrix.of_qqmatrix rsd_mat_inv) cf_matrix)

module UltPeriodic = struct
  type elt = EP.t
  type t = QQ.t list * elt list

  let lcm x y =
    match ZZ.to_int (ZZ.lcm (ZZ.of_int x) (ZZ.of_int y)) with
    | Some lcm -> lcm
    | None -> invalid_arg "Period length too long"

  let gcd x y =
    match ZZ.to_int (ZZ.gcd (ZZ.of_int x) (ZZ.of_int y)) with
    | Some lcm -> lcm
    | None -> assert false

  let pp formatter (t, p) =
    if t = [] then
      Format.fprintf
        formatter
        "<%a>"
        (SrkUtil.pp_print_enum EP.pp) (BatList.enum p)
    else
      Format.fprintf
        formatter
        "<%a; %a>"
        (SrkUtil.pp_print_enum QQ.pp) (BatList.enum t)
        (SrkUtil.pp_print_enum EP.pp) (BatList.enum p)

  let show = SrkUtil.mk_show pp

  let transient_len (t, _) = List.length t
  let period_len (_, p) = List.length p

  let transient (t, _) = t
  let periodic (_, p) = p

  let mul_period k xs =
    (0 -- (k - 1))
    |> BatEnum.map (fun i ->
           List.map (fun f -> EP.compose_left_affine f k i) xs)
    |> BatEnum.reduce List.append

  let elongate_transient k (t, p) =
    let period_enum =
      BatEnum.range 0 /@ (fun i ->
        BatList.enum p /@ (fun f -> EP.eval f i))
      |> BatEnum.concat
    in
    let current_transient = List.length t in
    BatEnum.drop current_transient period_enum;
    t @ (BatList.of_enum (BatEnum.take (k - current_transient) period_enum))

  let pointwise g f seq seq' =
    let t_len = max (transient_len seq) (transient_len seq') in
    let p_len = lcm (period_len seq) (period_len seq') in
    (List.map2 g
       (elongate_transient t_len seq)
       (elongate_transient t_len seq'),
     List.map2 f
       (mul_period (p_len/(period_len seq)) (periodic seq))
       (mul_period (p_len/(period_len seq')) (periodic seq')))

  let add = pointwise QQ.add EP.add

  let mul = pointwise QQ.mul EP.mul

  let make t p = (t, p)

  let scalar k = ([], [EP.scalar k])
  let zero = ([], [EP.zero])
  let one = ([], [EP.one])
  let negate (t, p) = (List.map QQ.negate t, List.map EP.negate p)
  let equal seq seq' =
    let (t, p) = pointwise QQ.equal EP.equal seq seq' in
    List.for_all (fun x -> x) (t@p)

  let term_of srk q r up =
    let period_len = period_len up in
    let k = mk_add srk [mk_mul srk [q; mk_real srk (QQ.of_int period_len)]; r] in
    BatList.fold_righti (fun i f else_ ->
        mk_ite srk
          (mk_eq srk k (mk_real srk (QQ.of_int i)))
          (mk_real srk f)
          else_)
      (transient up)
      (BatList.fold_lefti (fun else_ i f ->
           mk_ite srk
             (mk_eq srk r (mk_real srk (QQ.of_int (i + 1))))
             (EP.term_of srk q f)
             else_)
         (EP.term_of srk q (List.hd (periodic up)))
         (List.tl (periodic up)))

  let compose_left_affine seq a b =
    assert (a > 0);
    assert (b >= 0);
    let t = transient seq in
    let p = periodic seq in
    let p_len = List.length p in
    let rec transient current = function
      | (x::xs) when current = 0 -> x::(transient (a - 1) xs)
      | (_::xs) -> transient (current - 1) xs
      | [] -> []
    in
    let first_periodic = b mod p_len in
    let coeff = a / (gcd a p_len) in
    let rec periodic current offset =
      let next = (current + a) mod p_len in
      let offset' = offset + ((current + a) / p_len) in
      let current_fun =
        EP.compose_left_affine (List.nth p current) coeff offset
      in
      if next = first_periodic then [current_fun]
      else current_fun::(periodic next offset')
    in
    make (transient b t) (periodic first_periodic (b / p_len))

  (* Given a periodic sequence of exponential-polynomials
        p_0, ..., p_{m-1}
     and a coefficient coeff, comptue a (periodic) solution to the recurrence
     g_0(0) = initial
     g_n(n+1) = coeff*g_{n}(n) + f_n(n) *)
  let solve_rec_periodic coeff period initial =
    let len = List.length period in
    let full_period = (* coeff^{m-1} * p_0(x) + ... + coeff^0 * p_{m-1}(x) *)
      BatList.fold_left (fun ps f ->
          EP.add (EP.scalar_mul coeff ps) f)
        EP.zero
        period
    in

    (* full_period_sln is a solution to the recurrence
       full_period_sln(0) = initial
       full_period_sln(n+1) = coeff^m * full_period_sln(n) + full_period(n) *)
    let full_period_sln =
      solve_rec ~initial (QQ.exp coeff len) full_period
    in

    BatList.map (fun i ->
        (* coeff^{i}*full_period_sln(x) + sum_{j=0}^{i-1} coeff*{i-j-1} * f(j) *)
        BatList.fold_left (fun total f ->
            EP.add (EP.scalar_mul coeff total) f)
          full_period_sln
          (BatList.take i period))
      (BatList.of_enum (0 -- (len-1)))

  let eval (t, p) k =
    if k < (List.length t) then
      List.nth t k
    else
      let period_len = List.length p in
      let q = k / period_len in
      let r = k mod period_len in
      EP.eval (List.nth p r) q

  let enum f = BatEnum.range 0 /@ (eval f)

  let solve_rec ?(initial=QQ.zero) lambda (t, p) =
    match t with
    | [] -> ([], solve_rec_periodic lambda p initial)
    | _ ->
      (* Solve the cyclic recurrence and compute a correction term to
         account for the transient part. *)
      let (total, rev_transient) =
        List.fold_left (fun (next, ts) qq ->
            let next' = QQ.add (QQ.mul lambda next) qq in
            (next', next'::ts))
          (initial, [initial])
          t
      in
      let period_len = List.length p in
      let transient_len = List.length t in
      (* sum_{i=0}^{transient_len-1} coeff^{transient_len-i-1}*p(i) *)
      let transient_period_total =
        BatEnum.cycle (BatList.enum p)
        |> BatEnum.mapi (fun k f -> EP.eval f (k / period_len))
        |> BatEnum.take transient_len
        |> BatEnum.fold (fun total next ->
            QQ.add (QQ.mul lambda total) next)
          QQ.zero
      in
      let correction_term i =
        (* lambda^{i-transient_len} * (total - transient_period_total) *)
        EP.of_term
          (QQX.scalar
             (QQ.mul
                (QQ.exp lambda (i - transient_len))
                (QQ.sub total transient_period_total)))
          (QQ.exp lambda period_len)
      in
      let periodic =
        solve_rec_periodic lambda p QQ.zero
        |> BatList.mapi (fun i -> EP.add (correction_term i))
      in
      (List.rev rev_transient, periodic)

  let flatten xs =
    let period =
      List.fold_left (fun period up -> lcm (period_len up) period) 1 xs
    in
    let xs_len = List.length xs in
    let transient_len =
      BatList.fold_lefti (fun transient i up ->
          let up_t = transient_len up in
          if up_t > 0 then
            max (xs_len * (up_t - 1) + i + 1) transient
          else
            transient)
        0
        xs
    in
    let transient =
      BatEnum.cycle (BatList.enum xs)
      |> BatEnum.mapi (fun k up -> eval up (k / xs_len))
      |> BatEnum.take transient_len
      |> BatList.of_enum
    in

    let periodic =
      BatEnum.mapi (fun i up ->
          let up_p = periodic up in
          let up_p_len = List.length up_p in
          let f = List.nth up_p ((i / xs_len) mod up_p_len) in
          EP.compose_left_affine f (period / up_p_len) (i / (up_p_len*xs_len)))
        (BatEnum.cycle ~times:period (BatList.enum xs))
      |> BatList.of_enum
    in
    (transient, periodic)

  let summation f = solve_rec ~initial:(eval f 0) QQ.one (compose_left_affine f 1 1)

  let of_polynomial p = make [] [E.of_term p QQ.one]
  let of_exponential lambda = make [] [E.of_term QQX.one lambda]
  let of_exp_polynomial f = make [] [f]

  let shift seq (t, p) =
    let seq_len = List.length seq in
    let period_len = List.length p in
    let (first, second) = BatList.takedrop (period_len - (seq_len mod period_len)) p in
    let offset = seq_len / period_len in
    let period =
      List.map (fun f -> EP.compose_left_affine f 1 (-offset - 1)) second
      @ List.map (fun f -> EP.compose_left_affine f 1 (-offset)) first
    in
    (seq @ t, period)
end

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
let scalar_mul lambda f = QQMap.map (QQX.scalar_mul lambda) f

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
      (0 -- (p_order + 1))
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

let eval f x =
  let qq_x = QQ.of_int x in
  E.enum f
  /@ (fun (p, lambda) ->
      (QQ.mul (QQX.eval p qq_x) (QQ.exp lambda x)))
  |> BatEnum.fold QQ.add QQ.zero

module UltPeriodic = struct
  type elt = t

  let pp_elt = pp

  include Ring.MakeUltPeriodicSeq(struct
      type t = elt
      let equal = equal
      let add = add
      let mul = mul
      let one = one
      let zero = zero
      let negate = negate
    end)

  let pp = pp pp_elt
  let show = SrkUtil.mk_show pp

  (* Given a periodic sequence of exponential-polynomials
     f_0 f_1 ... = [p_1;...;p_m]^omega
     and a coefficient coeff, comptue a (periodic) solution to the recurrence
     g_0(0) = f_0(0)
     g_n(n) = coeff*g_{n-1}(n-1) + f_n(n) *)
  let solve_rec_periodic coeff period =
    (* period is [p_1; ...; p_m] *)
    let len = List.length period in

    let full_period = (* coeff^{m-1} * p_1(x) + ... + coeff^0 * p_m(x+m-1) *)
      BatList.fold_lefti (fun ps i f ->
          E.add (scalar_mul coeff ps) (compose_left_affine f 1 i))
        E.zero
        period
    in
    let root_map = (* map each lambda^m to lambda *)
      BatEnum.fold (fun root_map (_, lambda) ->
          QQMap.add (QQ.exp lambda len) lambda root_map)
        (QQMap.add (QQ.exp coeff len) coeff QQMap.empty)
        (E.enum full_period)
    in

    (* fp_sln is a solution to the recurrence
       fp_sln(0) = full_period(0)
       fp_sln(n+1) = coeff^m * fp_sln(n) + full_period(m*n) *)
    let fp_sln =
      solve_rec (QQ.exp coeff len) (compose_left_affine full_period len 0)
    in
    (* next_full_period overshoots the solution to the next full
       period.  tail is the correction term. *)
    let next_full_period offset = (* fp_sln((x-offset)/m) *)
      let g = (* (x-offset)/m *)
        QQX.add_term
          (QQ.of_frac 1 len)
          1
          (QQX.scalar (QQ.of_frac (-offset) len))
      in
      BatEnum.fold (fun h (p, lambda) ->
          let root_lambda = QQMap.find lambda root_map in
          E.add_term
            (QQX.scalar_mul (QQ.inverse (QQ.exp root_lambda offset)) (QQX.compose p g))
            root_lambda
            h)
        E.zero
        (E.enum fp_sln)
    in
    let tail i = (* p_{i+1}(x+1) + ... + p_m(x+m-i) *)
      BatList.fold_lefti (fun sum i f ->
          E.add (scalar_mul coeff sum) (compose_left_affine f 1 (i + 1)))
        E.zero
        (BatList.drop (i+1) period)
    in
    BatList.map (fun i ->
        E.scalar_mul
          (QQX.scalar (QQ.exp coeff (i - len + 1)))
          (E.add (next_full_period i) (E.negate (tail i))))
      (BatList.of_enum (0 -- (len-1)))

  (* [x_1; ...; x_n; x_{n+1}; ...; x_m] -> [x_{n+1}; ...; x_m; x_1; ... x_n] *)
  let cyclic_shift n xs =
    let rec go k xs ys =
      if k = 0 then
        xs @ (List.rev ys)
      else
        go (k - 1) (List.tl xs) ((List.hd xs)::ys)
    in
    go n xs []

  let solve_rec coeff seq =
    (* seq = t1 ... tn (p1 ... pm)^omega *)
    (* We can think of seq as the pointwise sum of a periodic sequence
       (p1' ... pm')^omega (some cyclic shift of (p1 ... pm)) and a
       transient, ultimately zero sequence. *)
    let period_len = period_len seq in
    let transient_len = transient_len seq in

    let shifted_period =
      cyclic_shift (period_len - (transient_len mod period_len)) (periodic seq)
    in

    let (rev_transient, transient_sum) =
      BatList.fold_lefti (fun (t, sum) i f ->
          let sum' = QQ.add (QQ.mul coeff sum) (eval f i) in
          ((scalar sum')::t, sum'))
        ([], QQ.zero)
        (transient seq)
    in
    (* Sum the periodic sequence up to the length of the transient. *)
    let transient_period_sum =
      BatEnum.foldi (fun i f sum ->
          QQ.add (QQ.mul coeff sum) (eval f i))
        QQ.zero
        (BatEnum.take
           transient_len
           (enum (make [] shifted_period)))
    in
    let period_sln =
      solve_rec_periodic coeff shifted_period
      |> cyclic_shift (transient_len mod period_len) (* deshift *)
      |> BatList.mapi (fun i f ->
          let offset =
            QQ.mul
              (QQ.exp coeff (1-transient_len))
              (QQ.sub transient_sum transient_period_sum)
          in
          E.add f (QQMap.singleton coeff (QQX.scalar offset)))
    in
    make (List.rev rev_transient) period_sln

  let summation = solve_rec QQ.one
end

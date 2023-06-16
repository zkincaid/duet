exception Divide_by_zero

include Log.Make(struct let name = "rational" end)

(*The given ring should be an integral domain. There is no way to enforce this in code.*)
module MakeFoF (D : sig 
    include Algebra.Ring 
    val int_mul : int -> t -> t 
    val pp : Format.formatter -> t -> unit
  end) = struct

  type t = D.t * D.t (*Technically equivalence classes*)

  (*This is equiv, not structural equal*)
  let equal (p, q) (r, s) = D.equal (D.mul p s) (D.mul q r)

  let equal_syn (p, q) (r, s) = D.equal p r && D.equal q s

  let add (p, q) (r, s) =
    if D.equal q s then
      D.add p r, q
    else
      (D.add (D.mul p s) (D.mul r q), D.mul q s)

      

  let negate (p, q) = D.negate p, q
  
  let inverse (p, q) = 
    if D.equal q D.zero then raise Divide_by_zero;
    (q, p)

  let lift (p : D.t) = (p, D.one)

  let zero = D.zero, D.one

  let mul (p, q) (r, s) = 
    if D.equal p D.zero || D.equal r D.zero then zero
    else
      D.mul p r, D.mul q s

  let int_mul i (p, q) = 
    if D.equal D.zero p then zero
    else
      D.int_mul i p, q

  let one = D.one, D.one

  let pp f (p, q) = 
    if D.equal q D.one then
      Format.fprintf f "@[%a@]" D.pp p
    else
      Format.fprintf f "@[(%a)/(%a)@]" D.pp p D.pp q
    
end


(*The given ring should be an integral domain. There is no way to enforce this in code.*)
module MakeRat (D : sig 
  include Polynomial.Euclidean
  val pp : Format.formatter -> t -> unit
end) = struct

  let gcd a b = 
    let g, _, _ = D.ex_euc a b in
    g

  let div_factor a factor = fst (D.qr a factor)

  type pre_t = Norm of (D.t * D.t) | Unnorm of (D.t * D.t)

  type t = pre_t ref

  let zero = ref (Norm (D.zero, D.one))

  let one = ref (Norm (D.one, D.one))

  let of_n_d (n, d) = ref (Unnorm (n, d))

  let get_normalized a = 
    match !a with
    | Norm (n, d) -> (n, d)
    | Unnorm (n, d) ->
      if D.equal n D.zero then (D.zero, D.one)
      else
        let gcd = gcd n d in
        let res = div_factor n gcd, div_factor d gcd in (* is this normal? could have const factor*)
        a := Norm res;
        res

  let get_n_d a = 
    match !a with
    | Norm (n, d) | Unnorm (n, d) -> (n, d)

  (*This is equiv, not structural equal*)
  let equal a b = 
    let (p, q) = get_n_d a in
    let (r, s) = get_n_d b in
    D.equal (D.mul p s) (D.mul q r)

  let equal_syn a b = 
    let (p, q) = get_normalized a in
    let (r, s) = get_normalized b in
    D.equal p r && D.equal q s

  let add a b =
    let (p, q) = get_n_d a in
    let (r, s) = get_n_d b in
    if D.equal q s then
      ref (Unnorm (D.add p r, q))
    else
      ref (Unnorm (D.add (D.mul p s) (D.mul r q), D.mul q s))

  let negate a =
    match !a with
    | Unnorm (p, q) -> ref (Unnorm (D.negate p, q))
    | Norm (p, q) -> ref (Norm (D.negate p, q))

  let inverse a = 
    match !a with
    | Unnorm (p, q) when not (D.equal q D.zero) -> ref (Unnorm (q, p))
    | Norm (p, q) when not (D.equal q D.zero) -> ref (Norm (q, p))
    | _ -> raise Divide_by_zero

  let lift (p : D.t) = ref (Norm (p, D.one))



  let mul a b = 
    let (p, q) = get_n_d a in
    let (r, s) = get_n_d b in
    if D.equal p D.zero || D.equal r D.zero then zero
    else
      ref (Unnorm (D.mul p r, D.mul q s))

  let int_mul i a = 
    let (p, q) = get_n_d a in
    if D.equal D.zero p then zero
    else
      ref (Unnorm (D.int_mul i p, q))


  let pp f a = 
    let (p, q) = get_normalized a in
    if D.equal q D.one then
      Format.fprintf f "@[%a@]" D.pp p
    else
      Format.fprintf f "@[(%a)/(%a)@]" D.pp p D.pp q

  (*den_fact1 and den_fact2 must be coprime*)
  let partial_fraction_pair (num : D.t) (den_fact1 : D.t) (den_fact2 : D.t) = 
    let gcd, c, d = D.ex_euc den_fact1 den_fact2 in
    if not (D.equal gcd D.one) then failwith "Trying to partial fraction with non coprime factors";
    let (q, f1) = D.qr (D.mul d num) den_fact1 in
    let f2 = D.add (D.mul c num) (D.mul q den_fact2) in
    (f1, f2)

  (*den_fact must be an square free polynomial*)
  let partial_fraction_power num den_fact power = 
    if power <= 1 then [(num, power)]
    else
      let den_fact_prime = D.derivative den_fact in
      let g, c, d = D.ex_euc den_fact den_fact_prime in
      if not (D.equal g D.one) then failwith "Trying to partial frac power of polynomial with squares";
      let rec aux f k = 
        if k <= 1 then [(f, k)]
        else
          let (q, hk) = D.qr (D.mul f (D.mul d den_fact_prime)) den_fact in
          (hk, k) :: (aux (D.add (D.mul f c) q) (k-1))
      in
      aux num power

  let partial_fraction (num : D.t) (den_fact_list : (D.t * int) list) = 
    let multiply_denoms = List.fold_left (
      fun acc (g, p) -> D.mul (D.exp g p) acc
      ) D.one in
    let den = multiply_denoms den_fact_list in
    let num_deg, den_deg = D.order num, D.order den in
    let const_part, num = 
      if num_deg >= den_deg then
        D.qr num den
      else
        D.zero, num
    in
    let rec aux curr_num l = 
      match l with
      | [] -> [(curr_num, (D.one, 1))]
      | (factor, power) :: [] -> 
        let fact_list = partial_fraction_power curr_num factor power in
        List.map (fun (f, i) -> (f, (factor, i))) fact_list
      | (g1, p1) :: ls ->
        let den1 = D.exp g1 p1 in
        let den2 = multiply_denoms ls in
        let (f1, f2) = partial_fraction_pair curr_num den1 den2 in
        let fact_list = partial_fraction_power f1 g1 p1 in
        let f1_part_frac = List.map (fun (f, i) -> (f, (g1, i))) fact_list in
        f1_part_frac @ (aux f2 ls)
    in
    if D.is_zero const_part then
      aux num den_fact_list
    else
      (const_part, (D.one, 1)) :: aux num den_fact_list

end



open Polynomial

module RX = MakeRat(struct
  include QQX
  let int_mul i = QQX.scalar_mul (QQ.of_int i)
end)

module RXVector = struct
  include Ring.MakeVector(RX)
  
  let split_leading v =
    try
      let (d, b) = min_support v in
      let v' = set d RX.zero v in
      Some (d, b, v')
    with Not_found ->
      None

  let pp formatter vec =
    let pp_elt formatter (v, k) = Format.fprintf formatter "%d:%a" k RX.pp v in
    enum vec
    |> Format.fprintf formatter "[@[%a@]]" (SrkUtil.pp_print_enum pp_elt)
end

module RXMatrix = Ring.MakeMatrix(RX)

module RXMap = Linear.MakeLinearMap(RX)(SrkUtil.Int)(RXVector)(RXVector)


(** Given two matrices A and B, compute a matrix C such that CB = A (if one
    exists).  C exists when the rowspace of B is contained in the rowspace of
    A.  If A and B are invertible, then C is exactly AB{^-1}. *)
let divide_right a b =
  (* Map the ith row to ith unit vector.  Applying to_row_comb expresses its input
     as a linear combination of the rows of b (if possible) *)
  let to_row_comb =
    BatEnum.fold (fun map (i, row) ->
        RXMap.may_add row (RXVector.of_term RX.one i) map)
      RXMap.empty
      (RXMatrix.rowsi b)
  in
  SrkUtil.fold_opt (fun div (i, row) ->
      BatOption.map
        (fun soln -> RXMatrix.add_row i soln div)
        (RXMap.apply to_row_comb row))
    RXMatrix.zero
    (RXMatrix.rowsi a)

let inverse a = 
  let m, n = RXMatrix.nb_rows a, RXMatrix.nb_columns a in
  if m <> n then failwith "Finding inverse of non square matrix";
  let ident = RXMatrix.identity (List.init m (fun i -> i)) in
  match divide_right ident a with
  | None -> failwith "Failure finding inverse of a matrix that should be invertible"
  | Some x -> x



module MakeRatDiff
  (N : sig 
    include Univariate
    val pp : Format.formatter -> t -> unit

    val int_mul : int -> t -> t
  end)
  (D : sig
    include Euclidean
    val pp: Format.formatter -> t -> unit
  end)
  (I : sig
    val lift : D.t -> N.t

    val qr : N.t -> D.t -> N.t * N.t
  end) = struct
  
  module N = N

  module D = D


  type t = N.t * D.t

  let zero = N.zero, D.one

  let one = N.one, D.one
  
  let gcd a b = 
    let g, _, _ = D.ex_euc a b in
    g

  let div_factor a fact = fst (D.qr a fact)

  let add (p, q) (r, s) =
    let lcm = div_factor (D.mul q s) (gcd q s) in
    let left = N.mul (I.lift (div_factor lcm q)) p in
    let right = N.mul (I.lift (div_factor lcm s)) r in
    (N.add left right, lcm)

  let negate (p, q) = (N.negate p, q)

  let lift (p : N.t) = (p, D.one)

  let mul (p, q) (r, s) = 
    if N.equal p N.zero || N.equal r N.zero then zero
    else
      N.mul p r, D.mul q s

  let int_mul i (p, q) = (N.int_mul i p, q)

  let pp f (p, q) = 
    if D.equal q D.one then
      Format.fprintf f "@[%a@]" N.pp p
    else
      Format.fprintf f "@[(%a)/(%a)@]" N.pp p D.pp q


  (*den_fact1 and den_fact2 must be coprime*)
  let partial_fraction_pair (num : N.t) (den_fact1 : D.t) (den_fact2 : D.t) = 
    let gcd, c, d = D.ex_euc den_fact1 den_fact2 in
    if not (D.equal gcd D.one) then failwith "Trying to partial fraction with non coprime factors";
    let (q, f1) = I.qr (N.mul (I.lift d) num) den_fact1 in
    let f2 = N.add (N.mul (I.lift c) num) (N.mul q (I.lift den_fact2)) in
    (f1, f2)

  (*den_fact must be an square free polynomial*)
  let partial_fraction_power (num : N.t) den_fact power = 
    if power <= 1 then [(num, power)]
    else
      let den_fact_prime = D.derivative den_fact in
      let g, c, d = D.ex_euc den_fact den_fact_prime in
      if not (D.equal g D.one) then failwith "Trying to partial frac power of polynomial with squares";
      let rec aux f k = 
        if k <= 1 then [(f, k)]
        else
          let (q, hk) = I.qr (N.mul f (I.lift (D.mul d den_fact_prime))) den_fact in
          (hk, k) :: (aux (N.add (N.mul f (I.lift c)) q) (k-1))
      in
      aux num power

  let partial_fraction (num : N.t) (den_fact_list : (D.t * int) list) = 
    let multiply_denoms = List.fold_left (
      fun acc (g, p) -> D.mul (D.exp g p) acc
      ) D.one in
    let den = multiply_denoms den_fact_list in
    let num_deg, den_deg = N.order num, D.order den in
    let const_part, num = 
      if num_deg >= den_deg then
        I.qr num den
      else
        N.zero, num
    in
    let rec aux curr_num l = 
      match l with
      | [] -> [(curr_num, (D.one, 1))]
      | (factor, power) :: [] -> 
        let fact_list = partial_fraction_power curr_num factor power in
        List.map (fun (f, i) -> (f, (factor, i))) fact_list
      | (g1, p1) :: ls ->
        let den1 = D.exp g1 p1 in
        let den2 = multiply_denoms ls in
        let (f1, f2) = partial_fraction_pair curr_num den1 den2 in
        let fact_list = partial_fraction_power f1 g1 p1 in
        let f1_part_frac = List.map (fun (f, i) -> (f, (g1, i))) fact_list in
        f1_part_frac @ (aux f2 ls)
    in
    if N.is_zero const_part then
      aux num den_fact_list
    else
      (const_part, (D.one, 1)) :: aux num den_fact_list


end

module MakeConstRing (
  R : sig 
    include Algebra.Ring 
    val lift : QQ.t -> t 
    val pp : Format.formatter -> t -> unit 
    val compare : t -> t -> int
  end) = struct
  include MakeMultivariate(R)
  
  let int_mul i = scalar_mul (R.lift (QQ.of_int i))

  let pp = pp R.pp (fun f i -> Format.pp_print_string f ("x_" ^ (string_of_int i)))

  let compare = compare R.compare

end

module ConstRing = MakeConstRing(struct include QQ let lift x = x end)

module ConstRingX = struct
  include Polynomial.MakeUnivariate(ConstRing)

  let int_mul i a = scalar_mul (ConstRing.int_mul i ConstRing.one) a
end

let lift_qqx_to_constfofx d =
  let e = BatEnum.map (
      fun (c, deg) ->
        ConstRing.scalar c, deg
    ) (QQX.enum d) in
    ConstRingX.of_enum e


(*For most of the computation we need to keep the numerator and the denominator separate, because
   we eventually will want to factor the denominator. We can factor QQX but not ConstFoFX.*)
module RatSeq = struct

  include MakeRatDiff(struct include ConstRingX let pp = ConstRingX.pp ConstRing.pp end)(QQX)(
    struct 
      let lift = lift_qqx_to_constfofx

      let qr (a : ConstRingX.t) (b : QQX.t) : ConstRingX.t * ConstRingX.t = 
        if QQX.is_zero b then failwith "Divide by 0";
        let d = QQX.order b in
        let c = QQX.coeff d b in
        if d = 0 then 
          (ConstRingX.scalar_mul (ConstRing.scalar (QQ.inverse c)) a, ConstRingX.zero)
        else
          let rec aux q r =
            let rd = ConstRingX.order r in
            if rd = 0 || rd < d then (q, r)
            else
              let s = (ConstRingX.of_term (ConstRing.scalar_mul (QQ.inverse c) (ConstRingX.coeff rd r)) (rd - d)) in
              aux (ConstRingX.add q s) (ConstRingX.sub r (ConstRingX.mul s (lift b)))
            in
          aux ConstRingX.zero a
    end)

  let lift_rx_to_rat_sequence (a : RX.t) : t = 
    let rxn, rxd = RX.get_normalized a in
    (lift_qqx_to_constfofx rxn, rxd)

  let mat_mul_v rxm (rsv : t array) = 
    let nrows = RXMatrix.nb_rows rxm in
    let rxma = RXMatrix.dense_of rxm nrows (RXMatrix.nb_columns rxm) in
    Array.map (
      fun row ->
        let dot_prod = Array.map2 (
          fun rx rs ->  mul (lift_rx_to_rat_sequence rx) rs
        ) row rsv in
        Array.fold_left add zero dot_prod
    ) rxma
  
  let solve_mat_rec_rs (transform : QQ.t array array) (init : ConstRing.t array) (b : t array) =
    let n = Array.length transform in
    let qI = RXMatrix.scalar_mul (RX.lift (QQX.identity)) (RXMatrix.identity (List.init n (fun i -> i))) in (*qI*)
    let neg_transform_rx = RXMatrix.of_dense (Array.map (Array.map (fun i -> RX.lift (QQX.scalar (QQ.negate i)))) transform) in (*-transform*)
    let qI_minus_transform = RXMatrix.add qI neg_transform_rx in
    let qI_minus_transform_inv = inverse qI_minus_transform in
    let init_q_minus_1 = Array.map (fun const -> N.scalar_mul const (N.sub N.identity N.one), QQX.one) init in (*(q-1)init*)
    let init_q_minus_1_plus_b = Array.map2 add init_q_minus_1 b in
    mat_mul_v qI_minus_transform_inv init_q_minus_1_plus_b


  let build_comp_matrix (q : QQX.t) = 
    let rank = (D.order q) + 1 in
    let m = Array.make_matrix rank rank QQ.zero in
    m.(0).(rank-1) <- QQ.one;
    for i = 0 to rank - 2 do
      m.(0).(i) <- QQ.negate (D.coeff (rank - 2 - i) q)
    done;
    for i = 1 to rank - 2 do
      for j = 0 to rank - 2 do
        if i - 1 = j then m.(i).(j) <- QQ.one
      done
    done;
    m.(rank-1).(rank-1) <- QQ.one;
    m
  
  let get_init_vector first_row shift = 
    let rank = Array.length first_row in
    let temp = Array.make rank QQ.zero in
    temp.(rank - 1) <- QQ.one;
    let res = Array.make rank QQ.zero in
    res.(rank - 1) <- QQ.one;
    for _ = 1 to shift do
      for j = 0 to (rank - 3) do
        res.(rank - 2 - j) <- res.(rank - 3 - j)
      done;
      res.(0) <- Array.fold_left QQ.add QQ.zero (Array.map2 QQ.mul temp first_row);
      for j = 0 to rank - 1 do
        temp.(j) <- res.(j)
      done
    done;
    res
  
  let kronecker mul a b =
    let m = Array.length a in
    let n = Array.length (Array.get a 0) in
    let p = Array.length b in
    let q = Array.length (Array.get b 0) in
    let res = Array.make_matrix (m*p) (n*q) 0 in
    Array.mapi (
      fun i row ->
        Array.mapi (
          fun j _->
            mul a.(i/p).(j/q) b.(i mod p).(j mod q)
        ) row
    ) res
  
  let had_mult ((an, ad) : t) ((bn, bd) : t) : t = 
    if (D.order ad < 1) then (*if either sequence is constant had prod is regular prod*)
      (if N.order an >= 1 then failwith "Ill formed rational sequence. Num deg is >= den deg.";
      mul (an, ad) (bn, bd))
    else if (D.order bd < 1) then
      (if N.order bn >= 1 then failwith "Ill formed rational sequence. Num deg is >= den deg.";
      mul (an, ad) (bn, bd))
    else
      let a_comp = build_comp_matrix ad in
      let b_comp = build_comp_matrix bd in
      let build_init first_row shift coef init_vec = 
        let one_shift = Array.map (fun c -> ConstRing.scalar c) (get_init_vector first_row shift) in
        Array.map2 (fun one_shift_i i -> ConstRing.add (ConstRing.mul one_shift_i coef) i) one_shift init_vec
      in
      let a_init = N.fold (build_init (a_comp.(0))) an (Array.make (Array.length (a_comp.(0))) ConstRing.zero) in
      let b_init = N.fold (build_init (b_comp.(0))) bn (Array.make (Array.length (b_comp.(0))) ConstRing.zero) in
      let transform = kronecker QQ.mul a_comp b_comp in
      let init_m = kronecker ConstRing.mul [|a_init|] [|b_init|] in
      let init = init_m.(0) in
      let sol = solve_mat_rec_rs transform init (Array.make (Array.length init) zero) in
      let n, p = Array.length a_comp, Array.length b_comp in
      sol.(n*p - p - 2) (* Need to check this*)
  
  let had_exp rs e = 
    if e < 0 then failwith "Exponentiating a negative exponent";
    let rec exp_by_squaring y x n = 
      if n = 0 then y
      else if n mod 2 = 0 then
        exp_by_squaring y (had_mult x x) (n/2)
      else
        exp_by_squaring (had_mult x y) (had_mult x x) ((n-1)/2)
    in
    exp_by_squaring one rs e

  
  type block =
  { blk_transform : QQ.t array array;
    blk_add : QQXs.t array }

  let solve_rec_rs sp : t array = 
    let size = List.fold_left (+) 0 (List.map (fun blk -> Array.length blk.blk_transform) sp) in
    let cf = Array.make size zero in
    let translate_blk_add p = 
      QQXs.fold (
        fun m coef rs ->
          let mon_rs = BatEnum.fold (
            fun acc (dim, pow) ->
              had_mult acc (had_exp (cf.(dim)) pow)
          ) one (Monomial.enum m) in
          add (mul (lift (N.scalar (ConstRing.scalar coef))) mon_rs) rs
      ) p zero
    in
    let rec aux blocks offset = 
      match blocks with
      | [] -> ()
      | blk :: blks ->
        let blk_size = Array.length (blk.blk_add) in
        let blk_add = Array.map translate_blk_add blk.blk_add in
        let init = Array.mapi (fun i _ -> ConstRing.of_dim (i + offset)) blk.blk_add in
        let sol = solve_mat_rec_rs blk.blk_transform init blk_add in
        for i = 0 to blk_size - 1 do
          cf.(i + offset) <- sol.(i)
        done;
        aux blks (offset + blk_size)
    in
    aux sp 0;
    cf

end

module RatEP = ExpPolynomial.MakeEP(QQ)(struct include ConstRing let lift = ConstRing.scalar end)(struct include ConstRingX let pp = ConstRingX.pp ConstRing.pp end)


(*let pp_rat_pow f (n, (d, e)) = 
  if QQX.equal d QQX.one then
    Format.fprintf f "@[%a@]" (ConstRingX.pp ConstRing.pp) n
  else
    Format.fprintf f "@[(%a)/(%a)^%d@]" (ConstRingX.pp ConstRing.pp) n QQX.pp d e*)


let translate_rs (sols : RatSeq.t array) = 
  let sols_fact = Array.map (
    fun (n, d) ->
      let content, den_facts = QQX.factor d in
      let n = ConstRingX.scalar_mul (ConstRing.scalar (QQ.inverse content)) n in
      RatSeq.partial_fraction n den_facts
  ) sols in
  (*let pl = Format.pp_print_list ~pp_sep:(fun fo () -> Format.pp_print_string fo " +"; Format.pp_print_space fo ()) pp_rat_pow in
  Array.iteri (
    fun i rs ->
      logf ~level:`always "Dim %d : %a" i pl rs
  ) sols_fact;*)
  let translate_term (n, (den, power)) = 
    if QQX.order den > 1 then failwith "TODO handle IIFs"
    else 
      if ConstRingX.order n > 0 then failwith "Numerator should be constant unless IIF";
      let num = ConstRingX.coeff 0 n in
      if QQX.order den = 0 then
        let coe = QQ.exp (QQX.coeff 0 den) (-power) in
        RatEP.scalar (ConstRing.scalar_mul coe num)
      else
        let den_root = QQ.negate (QQ.div (QQX.coeff 0 den) (QQX.coeff 1 den)) in
        if QQ.equal den_root QQ.one then
          let p = QQX.choose power in
          RatEP.scalar_mul num (RatEP.of_polynomial (lift_qqx_to_constfofx p))
        else
          let rec aux c = 
            if c = 1 then 
              let ep_den = ConstRing.scalar (QQ.inverse (QQ.sub den_root QQ.one)) in
              let ep = RatEP.add (RatEP.of_exponential den_root) (RatEP.negate RatEP.one) in
              RatEP.scalar_mul ep_den ep (*(k^n - 1)/(k-1)*)
            else
              let ep_den = ConstRing.scalar (QQ.inverse (QQ.sub den_root QQ.one)) in
              let expo = RatEP.of_exponential den_root in
              let poly = QQX.scalar_mul (QQ.exp den_root (-c + 1)) (QQX.choose (c-1)) in (*(n choose c-1) a^{-c+1}*)
              let term = RatEP.mul expo (RatEP.of_polynomial (lift_qqx_to_constfofx poly)) in
              let rhs = aux (c-1) in
              RatEP.scalar_mul ep_den (RatEP.add term (RatEP.negate rhs)) (*1/(a-1) ((n choose c-1) a^{-c+1}a^n - aux (c-1))*)
          in
          RatEP.scalar_mul num (aux power)
  in
  Array.map (
    List.fold_left (
      fun acc rat_t -> RatEP.add acc (translate_term rat_t)
    ) RatEP.zero) sols_fact
  




        







  (*let (irreducible_den_factors_prod, rational_roots) = 
    Array.fold_left (
      fun (irred, roots) (_, factors) ->
        let irred_facts, lin_facts = List.partition (fun (f, _) -> QQX.order f > 1) factors in
        let irred_facts, lin_facts = fst (List.split irred_facts), fst (List.split lin_facts) in
        let extract_root_from_linear p = QQ.div (QQX.coeff 0 p) (QQ.negate (QQX.coeff 1 p)) in
        List.fold_left QQX.mul irred irred_facts, (List.map extract_root_from_linear lin_facts) @ roots
    ) (QQX.one, []) sols_fact in
  let splitting_field, rational_roots, irrational_roots = 
    if QQX.order irreducible_den_factors_prod <= 1 then QQX.zero, BatList.of_enum (BatEnum.uniq_by (QQ.equal) (BatList.enum rational_roots)), []
    else 
      let sp, irred_roots = NumberField.splitting_field irreducible_den_factors_prod in
      sp, BatList.of_enum (BatEnum.uniq_by (QQ.equal) (BatList.enum rational_roots)), (fst (List.split irred_roots))
  in
  let module NF = NumberField.MakeNF(struct let min_poly = splitting_field end) in
  let module RootMap = BatMap.Make(struct type t = NF.elem let compare = NF.compare end) in (*Maybe not the most efficient*)
  let module NFXs = MakeMultivariate(struct include NF type t = elem end) in
  let module ConstFoFNF = MakeFoF(
    struct 
      include NFXs 
      let int_mul i a = NFXs.scalar_mul (NF.int_mul i NF.one) a 
      let pp = NFXs.pp NF.pp (fun f dim -> Format.pp_print_string f ("x_" ^ (string_of_int dim)))
    end) in
  let module ConstFoFNFX = MakeEuclidean(ConstFoFNF) in
  let module Rat = MakeRat(struct include ConstFoFNFX let pp = ConstFoFNFX.pp ConstFoFNF.pp end) in
  let roots_e = (List.map (fun e -> NF.make_elem e) irrational_roots) @ (List.map (fun q -> NF.of_rat q) rational_roots) in
  let offset = Array.length sols in
  let rm = List.fold_left (fun (i, m) e -> i+1, RootMap.add e i m) (offset, RootMap.empty) roots_e in
  let lift_constfof_to_constfofnf ((n, d) : ConstFoF.t) : ConstFoFNF.t = 
    let qqxs_to_nfxs a = 
      NFXs.of_enum (BatEnum.map (fun (c, m) -> NF.of_rat c, m) (QQXs.enum a))
    in
    (qqxs_to_nfxs n, qqxs_to_nfxs d)
  in
  let translate_rat_seq ((num, den_fact_list) : (ConstFoFX.t * (QQX.t * int) list)) = 
    let num_fofnfx = ConstFoFNFX.of_enum (BatEnum.map (fun (c, d) -> lift_constfof_to_constfofnf c, d) (ConstFoFX.enum num)) in
    let translate_den (coef, new_den_list) (den, power) = 
      let dennf = NF.X.lift den in
      let roots = List.filter (fun r -> NF.is_zero (NF.X.eval dennf r)) roots_e in
      if List.length roots <> NF.X.order dennf then failwith "A root has not been accounted for";
      let root_polys = List.map (fun r -> NF.X.sub NF.X.identity (NF.X.scalar r)) roots in
      let min_poly = List.fold_left NF.X.mul NF.X.one root_polys in
      let (const_p, _) = NF.X.qr dennf min_poly in
      if NF.X.order const_p > 0 then failwith "Dennf and min_poly are off by more than a constant";
      let const_mult = NF.X.coeff 0 const_p in
      let root_polys_nfxs = List.map (fun p -> ConstFoFNFX.of_enum (BatEnum.map (fun (c, d) -> ConstFoFNF.lift (NFXs.scalar c), d) (NF.X.enum p))) root_polys in
      (NF.mul coef (NF.exp const_mult power), new_den_list @ (List.map (fun rp -> rp, power) root_polys_nfxs))
    in
    let coef, new_den_list = List.fold_left translate_den (NF.one, []) den_fact_list in
    let new_num = ConstFoFNFX.scalar_mul (ConstFoFNF.lift (NFXs.scalar (NF.inverse coef))) num_fofnfx in
    Rat.partial_fraction new_num new_den_list
  in
  let translated_rs = Array.map translate_rat_seq sols_fact in (*Each element should be a sum of terms of the form c/(p(x))^k where p(x) is a linear polynomial*)
  let translate_to_exp_poly rs = 
    let translate_term_to_exp_poly (num, (den, power)) =
      let rec aux (d, c) = 
        if ConstFoFNFX.order d <> 1 then failwith "Denominator is not of the form (x-a)^c";
        let an, ad = ConstFoFNF.mul (ConstFoFNF.negate (ConstFoFNFX.coeff 0 d)) (ConstFoFNF.inverse (ConstFoFNFX.coeff 1 d)) in*)
  
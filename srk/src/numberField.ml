open Polynomial

include Log.Make(struct let name = "srk.numberField" end)

let make_multivariate dim p = 
  QQXs.of_enum (BatEnum.map (fun (coef, pow) -> coef, Monomial.singleton dim pow) (QQX.enum p))

let make_univariate p = 
  QQX.of_enum (
    BatEnum.map (
      fun (coef, m) -> 
        if Monomial.equal m Monomial.one then
          (coef, 0)
        else if BatEnum.count (Monomial.enum m) > 1 then
          failwith "Trying to convert a multivariate polynomial to a univariate polynomial"
        else
          (coef, Monomial.total_degree m)
      ) (QQXs.enum p))


let primitive_elem mp0 mp1 v0 v1 = 
  (*let v0, v1 = 0, 1 in
  let mp0, mp1 = make_multivariate v0 mp0x, make_multivariate v1 mp1x in*)
  let mp0d, mp1d = QQXs.degree mp0, QQXs.degree mp1 in
  if mp0d = 0 then make_univariate mp1, QQX.zero, QQX.identity
  else if mp1d = 0 then make_univariate mp0, QQX.identity, QQX.zero
  else
    let needed_deg = (QQXs.degree mp0) * (QQXs.degree mp1) in
    let v2 = (max v0 v1) + 1 in
    let rec aux i = 
      (* v0 + iv1 - v2*)
      let lin_comb = QQXs.of_list [Q.one, Monomial.singleton v0 1; Q.of_int i, Monomial.singleton v1 1; Q.minus_one, Monomial.singleton v2 1] in
      let gb = FGb.grobner_basis [v0; v1] [v2] [mp0; mp1; lin_comb] in
      let v2_poly = 
        List.find (
          fun p -> 
            let dims = QQXs.dimensions p in
            SrkUtil.Int.Set.is_singleton dims && SrkUtil.Int.Set.mem v2 dims) gb in
      if QQXs.degree v2_poly = needed_deg then v2_poly, Rewrite.mk_rewrite (FGb.get_mon_order [v0;v1] [v2]) gb
      else if i > needed_deg then failwith "Unable to find primitive element, which breaks the primitive element theorem."
      else aux (i+1)
    in
    let prim, r = aux 1 in
    let v0_in_prim = make_univariate (Rewrite.reduce r (QQXs.of_dim v0)) in
    let v1_in_prim = make_univariate (Rewrite.reduce r (QQXs.of_dim v1)) in
    make_univariate prim, v0_in_prim, v1_in_prim

module MakeNF (A : sig val min_poly : QQX.t end) = struct





  type elem = QQX.t

  let compute_min_poly_p el p = 
    let open Linear in
    let p_deg = QQX.order p in
    if p_deg = 0 then el
    else
      let m = Array.make_matrix p_deg (p_deg+1) QQ.zero in (*m is a matrix to hold onto the powers of el*)
      (*m.(0).(0) <- QQ.one; (* The zero'th power of el is 1; 0; ...*)*)
      for i = 0 to p_deg do
        let r = snd (QQX.qr (QQX.exp el i) p) in
        BatEnum.iter (
          fun (c, d) -> 
            m.(d).(i) <- c
        ) (QQX.enum r)
      done;
      (*In general I don't think null is guarenteed to be reduced with respect to powers of el. However,
         I think it is do to how nullspace is implemented.*)
      let null = nullspace (QQMatrix.of_dense m) (List.init (p_deg + 1) (fun i -> i)) in
      let min = snd (List.fold_left (
        fun (min_deg, min_p) vec ->
          let poly = QQX.of_enum (QQVector.enum vec) in
          if QQX.order poly < min_deg then (QQX.order poly, poly)
          else (min_deg, min_p)
      ) (p_deg + 2, QQX.one) null) in
      let lc = QQX.coeff (QQX.order min) min in
      QQX.map (fun _ c -> QQ.div c lc) min


  let min_poly_den_lcm = 
    QQX.fold (
      fun _ c l ->
        ZZ.lcm (QQ.denominator c) l
    ) A.min_poly (QQ.numerator (QQX.coeff (QQX.order A.min_poly) A.min_poly))

  let int_poly = compute_min_poly_p (QQX.scalar_mul (QQ.of_zz min_poly_den_lcm) QQX.identity) A.min_poly


  let compute_min_poly e = compute_min_poly_p e int_poly

  let deg = QQX.order int_poly

  let reduce a = 
    if QQX.is_zero int_poly then a
    else snd (QQX.qr a int_poly)

  (*let r = 
    Rewrite.mk_rewrite (Monomial.degrevlex) [make_multivariate 0 A.min_poly]*)

  let make_elem p = reduce (QQX.map (fun d c -> QQ.div c (QQ.exp (QQ.of_zz min_poly_den_lcm) d)) p)

  let mul a b = 
    reduce (QQX.mul a b)

  let add = 
    QQX.add
  
  let sub = 
    QQX.sub

  let inverse a = 
    let (_, u, _) = QQX.ex_euc a int_poly in
    u

  let exp a i = 
    if i < 0 then
      inverse (reduce (QQX.exp a i))
    else
      reduce (QQX.exp a i)

  let equal a b = 
    QQX.equal (reduce a) (reduce b)

  let is_zero a = 
    QQX.equal (QQX.zero) (reduce a)

  let one = QQX.one

  let zero = QQX.zero

  let negate = QQX.negate


  let pp f e = 
    QQX.pp f e;
    Format.fprintf f "Where x is a root of @[%a@]" QQX.pp int_poly

  module E = struct let one = one let mul = mul let negate = negate let exp = exp end

  module X = struct 
    include MakeEuclidean(
      struct 
        type t = elem
        let equal = equal
        let add = add
        let zero = zero
        let one = one
        let mul = mul
        let negate = negate
        let pp = pp
        let inverse = inverse
        let int_mul i x = QQX.scalar_mul (QQ.of_int i) x
      end)
    let pp formatter p = 
      let pp_monomial formatter (coeff, order) = 
        if order = 0 then
          QQX.pp formatter coeff
        else if QQX.equal coeff QQX.one then
          Format.fprintf formatter "@[z^%d@]" order
        else if QQX.equal coeff (QQX.negate QQX.one) then
          Format.fprintf formatter "@[-z^%d@]" order
        else 
          Format.fprintf formatter "@[(%a)*z^%d@]" QQX.pp coeff order
        in
        SrkUtil.pp_print_enum
          ~pp_sep:(fun formatter () -> Format.fprintf formatter "@ + ")
          pp_monomial
          formatter
          (enum p)
      
    let lift (p : QQX.t) = 
      of_enum (BatEnum.map (fun (c, d) -> QQX.scalar c, d) (QQX.enum p))

    let de_lift (p : t) : QQXs.t = 
      fold (
        fun m coef acc ->
          QQXs.add (QQXs.mul_monomial (Monomial.singleton 1 m) (make_multivariate 0 coef)) acc
      ) p QQXs.zero

    let factor_square_free_poly p =
      if QQX.is_zero int_poly then
        let p_uni = make_univariate (de_lift p) in
        let lc, facts = QQX.factor p_uni in
        make_elem (QQX.scalar lc), List.map (fun (f, d) -> lift f, d) facts
      else
        let lc = coeff (order p) p in
        let pmonic = scalar_mul (inverse lc) p in
        let pmonicxs = de_lift pmonic in (* p is a multivariate polynomial in 0, the variable of the field, and 1 the variable of the polynomial.*)
        let prim, v0_in_prim, v1_in_prim = primitive_elem (make_multivariate 0 int_poly) pmonicxs 0 1 in
        let primxs = make_multivariate 0 prim in
        let v1_term = QQXs.sub (make_multivariate 1 (QQX.identity)) (make_multivariate 0 v0_in_prim) in 
        let v2_term = QQXs.sub (make_multivariate 2 (QQX.identity)) (make_multivariate 0 v1_in_prim) in
        (*let gb = FGb.grobner_basis [0] [1;2] [primxs; v1_term; v2_term] in*)
        let mon_order = FGb.get_mon_order [0;2] [1] in
        (*let r = Rewrite.grobner_basis (Rewrite.mk_rewrite mon_order gb) in*)
        let (_, factors) = QQX.factor prim in
        let find_factor (fact, deg) = 
          if deg > 1 then failwith "Primitive element contains square factor?";
          let factxs = make_multivariate 0 fact in
          let ps = FGb.grobner_basis [0;2] [1] [primxs; v1_term; v2_term; factxs] in
          (*let pv fo v = if v = 0 then Format.pp_print_string fo "z" else if v = 1 then Format.pp_print_string fo "y" else Format.pp_print_string fo "x" in
          Log.log ~level:`always "Searching for factor in";
          Log.log_pp ~level:`always (Format.pp_print_list ~pp_sep:(fun fo () -> Format.pp_print_newline fo ()) (QQXs.pp pv)) ps;*)
          let v2ps = 
            List.filter (
              fun p -> 
                let dims = QQXs.dimensions p in
                if SrkUtil.Int.Set.mem 2 dims && not (SrkUtil.Int.Set.mem 0 dims) then true
                else false
            ) ps in
          if List.length v2ps <> 1 then failwith "Unable to find factor in reduced ring";
          let poly = List.hd v2ps in
          let poly_lc, _, _ = QQXs.split_leading mon_order poly in
          let poly = QQXs.of_enum (BatEnum.map (fun (c, m) -> QQ.div c poly_lc, m) (QQXs.enum poly)) in 
          QQXs.fold (
            fun m coef acc ->
              let var_part, coef_part = 
                BatEnum.fold (
                  fun (var_part, coef_part) (var, deg) ->
                    if var = 2 then mul (exp identity deg) var_part, coef_part
                    else var_part, QQX.mul (QQX.exp QQX.identity deg) coef_part
                    ) (one, QQX.one) (Monomial.enum m) in
              let coe = QQX.scalar_mul coef coef_part in
              add (scalar_mul coe var_part) acc
          ) poly zero, deg
        in
        (lc, List.map find_factor factors)


    let factor (p : t) = 
      let square_free_facts = square_free_factor p in
      List.fold_left (
        fun (coef, factors) (square_free_fact, deg) ->
          let (lc, facts) = factor_square_free_poly square_free_fact in
          let new_facts = List.map (fun (f, d) -> (f, d * deg)) facts in
          E.mul (E.exp lc deg) coef, new_facts @ factors
      ) (E.one, []) square_free_facts

    let extract_root_from_linear p = 
      if order p <> 1 then failwith "Trying to extract root from non-linear polynomial"
      else
        let lc = coeff 1 p in
        let const = E.negate (coeff 0 p) in
        E.mul (inverse lc) const 

  end
   

  module O = struct
    module ZZV = Ring.MakeVector(ZZ)
    module ZZM = Ring.MakeMatrix(ZZ)

    let rank = deg

    let mult_table = ref None

    let get_mult_table () = 
      match !mult_table with
      | Some x -> x
      | None ->
        let m = Array.make_matrix (deg * deg) deg ZZ.zero in
        for i = 0 to deg - 1 do
          for j = 0 to deg - 1 do
            let mult = mul (QQX.exp QQX.identity i) (QQX.exp QQX.identity j) in
            for k = 0 to deg - 1 do
              let e = QQX.coeff k mult 
              in
              if not (ZZ.equal (QQ.denominator e) ZZ.one) then failwith "Failed constructing order";
              m.((deg-1-i)*deg + (deg-1-j)).(deg - 1 - k) <- QQ.numerator e
            done;
          done;
        done;
        mult_table := Some (m);
        m

    let mult_table_m () = 
      ZZM.of_dense (get_mult_table ())

    let mult i j = 
      if i >= rank || j >= rank then Array.make rank ZZ.zero
      else
        let m = get_mult_table () in
        m.(i*rank + j)
    
    let zzmify = ZZM.of_dense

    let unzzmify matrix = 
      ZZM.dense_of matrix (ZZM.nb_rows matrix) (ZZM.nb_columns matrix)

    type pre_ideal = Red of ZZM.t | UnRed of ZZM.t

    type ideal = pre_ideal ref

    type o = ZZ.t array

    let pp_o f o = 
      let strs = Array.mapi (
        fun i coef ->
            (ZZ.show coef)^ "x^" ^ (string_of_int (deg - 1 - i))
        ) o in
      let str = String.concat " + " (List.rev (Array.to_list strs)) in
      Format.fprintf f "@[%s@]  where x is a root of @[%a@]" str QQX.pp int_poly
      

    let make_o_el e = 
      let lcm = QQX.fold (
        fun _ coe acc ->
          ZZ.lcm acc (QQ.denominator coe)
      ) e ZZ.one in
      let order_e = Array.make rank ZZ.zero in
      BatEnum.iter (
        fun (coef, d) ->
          order_e.(deg - 1 - d) <- QQ.numerator (QQ.mul coef (QQ.of_zz lcm))
      ) (QQX.enum e);
      lcm, order_e

    let order_el_to_f_elem (den, o_el) = 
      QQX.of_enum (BatArray.enum (Array.mapi (
        fun i coef ->
          (QQ.div (QQ.of_zz coef) (QQ.of_zz den)), (deg - 1 - i)
      ) o_el))

    let get_mat i = match !i with Red m | UnRed m -> m

    let idealify aa = 
      ref (UnRed (zzmify aa))


    let dense_hermite_normal_form matrix =
      let mat = Normalizffi.Flint.new_matrix matrix in
      Normalizffi.Flint.hermitize mat;
      let rank = Normalizffi.Flint.rank mat in
      let basis =
        Normalizffi.Flint.denom_matrix_of_rational_matrix mat
        |> snd
        |> BatList.take rank (* The rows after rank should be all zeros *)
      in
      basis

    let hermite_normal_form mat = 
      let matrix = Array.to_list (Array.map (fun r -> Array.to_list (Array.map ZZ.mpz_of r)) (unzzmify mat)) in
      let m = ZZM.nb_rows mat in
      let n = ZZM.nb_columns mat in
      let mapper i row = 
        let pad = List.init m (fun j -> if i = j then Mpzf.of_int 1 else Mpzf.of_int 0) in
        row @ pad
      in
      let hu = dense_hermite_normal_form (List.mapi mapper matrix) in
      let splitter hurow = 
        let rec aux i prev rest = 
          if i >= n then
            Array.of_list (List.rev prev), Array.of_list (List.map ZZ.of_mpz rest)
          else
            match rest with
            | [] -> failwith "Didn't find u matrix?"
            | x :: xs -> aux (i+1) (ZZ.of_mpz x :: prev) xs
        in
        aux 0 [] hurow
      in
      let h, u = Array.split (Array.of_list (List.map splitter hu)) in
      zzmify h, zzmify u

    let get_reduced i = 
      match !i with 
      | Red m -> m 
      | UnRed m -> 
        let red = fst (hermite_normal_form m) in
        i := Red red;
        red

    let stack a b =
      let am = ZZM.nb_rows a in
      let brs = ZZM.rowsi b in
      BatEnum.fold (fun acc (i, brow) -> ZZM.add_row (i+am) brow acc) a brs

    let kronecker a b = 
      let am, an = ZZM.nb_rows a, ZZM.nb_columns a in
      let bm, bn = ZZM.nb_rows b, ZZM.nb_columns b in
      let aa, ba = unzzmify a, unzzmify b in
      let m = Array.make_matrix (am * bm) (an * bn) ZZ.zero in
      for i = 0 to am * an - 1 do
        for j = 0 to bm * bn - 1 do
          m.(i).(j) <- ZZ.mul aa.(i / bm).(j / bn) ba.(i mod bm).(j mod bn)
        done
      done;
      zzmify m



    let get_smallest_int i = 
      ZZM.entry (rank - 1) (rank - 1) (get_reduced i)

    let pp_i f i = 
      ZZM.pp ZZ.pp f (get_reduced i)

    let equal_i a b = 
      ZZM.equal (get_reduced a) (get_reduced b)


    let sum_i a b =
      ref (UnRed (stack (get_mat a) (get_mat b)))

    let mul_i a b = 
      ref (UnRed (ZZM.mul (kronecker (get_reduced a) (get_reduced b)) (mult_table_m ())))

    let mul_v_by_basis_v v basis_i = 
      fst (Array.fold_left (
        fun (acc, j) vj ->
          let x = Array.map (fun y -> ZZ.mul vj y) (mult basis_i j) in
          Array.map2 ZZ.add acc x, j+1
      ) (Array.make rank ZZ.zero, 0) v)

    let ideal_generated_by a = 
      let m = Array.make rank (Array.make rank ZZ.zero) in
      for i = 0 to rank - 1 do
        m.(i) <- mul_v_by_basis_v a i
      done;
      ref (UnRed (zzmify m))

    let one_i = ref (Red (ZZM.identity (List.init rank (fun i -> i))))


    let get_lower_left_corner a = 
      let m = ZZM.nb_rows a in
      let aa = unzzmify a in
      let r = Array.make_matrix rank rank ZZ.zero in
      for i = 0 to rank - 1 do
        r.(i) <- Array.sub (aa.(i + (m-rank))) 0 rank
      done;
      zzmify r


    let intersect_i a b = 
      let a_red, b_red = get_reduced a, get_reduced b in
      let (_, u) = hermite_normal_form (stack a_red b_red) in
      let u_sub = get_lower_left_corner u in
      ref (UnRed (ZZM.mul u_sub a_red))

    
    let quotient_i a b = 
      let ba = unzzmify (get_reduced b) in
      let neg_aa = unzzmify (ZZM.scalar_mul (ZZ.of_int (-1)) (get_reduced a)) in
      let top_part = Array.of_list (List.init rank (
        fun i ->
          Array.concat (List.init rank (
            fun j ->
              mul_v_by_basis_v ba.(j) i
          ))
      )) in
      let bot_part = Array.concat (List.init rank (
        fun i ->
          let r = List.init rank (
            fun j ->
              if i = j then neg_aa
              else Array.make_matrix rank rank ZZ.zero
          ) in
          List.fold_left (
            fun acc sr ->
              Array.map2 Array.append acc sr
          ) (List.hd r) (List.tl r)
      )) in
      let (_, u) = hermite_normal_form (stack (zzmify top_part) (zzmify bot_part)) in
      ref (UnRed (get_lower_left_corner u))


    let get_matrix_gcd i = 
      BatEnum.fold (
        fun g (_, _, e) -> ZZ.gcd g e) ZZ.zero (ZZM.entries (get_reduced i))

    let scalar_mul_i a i =
      match !i with
      | UnRed m -> ref (UnRed (ZZM.scalar_mul a m))
      | Red m -> ref (Red (ZZM.scalar_mul a m))

    let divide_common_factor common_factor i = 
      match !i with
      | Red m ->
        ref (Red (ZZM.map_rows (
          fun r ->
            ZZV.map (fun _ e -> ZZ.div e common_factor) r
        ) m))
      | UnRed m ->
        ref (UnRed (ZZM.map_rows (
          fun r ->
            ZZV.map (fun _ e -> ZZ.div e common_factor) r
        ) m))

    type pre_frac_ideal = Norm of ZZ.t * ideal | UnNorm of ZZ.t * ideal

    type frac_ideal = pre_frac_ideal ref


    let one = ref (Norm (ZZ.one, one_i))

    let get_normalized (i : frac_ideal) = 
      match !i with
      | Norm (d, a) -> (d, a)
      | UnNorm (d, a) ->
        let matrix_factor = get_matrix_gcd a in
        let common_factor = ZZ.gcd d matrix_factor in
        if ZZ.equal common_factor ZZ.one then 
          (i := Norm (d, a);
          d, a)
        else
          (let new_d, new_a = ZZ.div d common_factor, divide_common_factor common_factor a in
          i := Norm (new_d, new_a);
          new_d, new_a)

    let get_den_and_ideal (i : frac_ideal) = 
      match !i with | Norm (d, id) | UnNorm (d, id) -> (d, id)

    let sum ai bi = 
      let (d1, a) = get_den_and_ideal ai in
      let (d2, b) = get_den_and_ideal bi in
      let new_d = ZZ.lcm d1 d2 in
      ref (UnNorm (new_d, sum_i (scalar_mul_i (ZZ.div new_d d1) a) (scalar_mul_i (ZZ.div new_d d2) b)))

    let intersect ai bi = 
      let (d1, a) = get_den_and_ideal ai in
      let (d2, b) = get_den_and_ideal bi in
      let new_d = ZZ.lcm d1 d2 in
      ref (UnNorm (new_d, intersect_i (scalar_mul_i (ZZ.div new_d d1) a) (scalar_mul_i (ZZ.div new_d d2) b)))

    let mul ai bi = 
      match !ai, !bi with
      | Norm (d1, a), Norm (d2, b) -> ref (Norm ((ZZ.mul d1 d2), mul_i a b))
      | Norm(d1, a), UnNorm(d2, b) | UnNorm(d1, a), Norm(d2, b) | UnNorm(d1, a), UnNorm(d2, b) -> ref (UnNorm (ZZ.mul d1 d2, mul_i a b))

    let exp ai i = 
      let rec aux acc j = 
        if j = 0 then acc
        else
          aux (mul ai acc) (j-1)
        in
      aux one i


    let quotient ai bi = 
      let (d1, a) = get_den_and_ideal ai in
      let (d2, b) = get_den_and_ideal bi in
      let smallest_int = get_smallest_int b in
      let new_d = ZZ.mul d1 smallest_int in
      let new_m = quotient_i (scalar_mul_i (ZZ.mul d2 smallest_int) a) b in
      ref (UnNorm (new_d, new_m))

    let pp f i = 
      let (d, a) = get_normalized i in
      Format.fprintf f "@[1/(%a)@]" ZZ.pp d;
      pp_i f a
    
    let equal ai bi = 
      let (d1, a) = get_normalized ai in
      let (d2, b) = get_normalized bi in
      ZZ.equal d1 d2 && equal_i a b

    let subset a b = 
      equal b (sum a b)

    let make_frac_ideal d i = 
      ref (UnNorm (d, i))


    let compute_overorder o i = 
      let rec aux c j =
        let c_div_j = quotient c j in
        let x = quotient c_div_j c_div_j in
        if equal x c then (c, j)
        else aux x (mul c j)
      in
      aux o i

    module IM = SrkUtil.Int.Map

    let factor_refinement is = 
      let init_c = List.fold_left (fun acc i -> fst (compute_overorder acc i)) one is in
      let js = List.map (fun i -> mul i init_c, 1) is in
      let rec aux next_index worklist c l = 
        match worklist with
        | [] -> c, l
        | (m, n) :: rest ->
          let (jm, jme), (jn, jne) = IM.find m l, IM.find n l in
          let h = sum jm jn in
          if equal c h then aux next_index rest c l
          else
            let new_c, h = compute_overorder c h in
            let new_worklist = List.filter (fun (a, b) -> a <> m && a <> n && b <> m && b <> n) worklist in
            let new_l = IM.remove m (IM.remove n l) in
            let new_l = IM.map (fun (j, e) -> mul j new_c, e) new_l in
            let jmp = quotient jm h in
            let jnp = quotient jn h in
            let active_indices = IM.keys new_l in
            let new_worklist, new_l, next_index, active_indices = 
              if not (equal jmp new_c) then
                let new_l = IM.add next_index (jmp, jme) new_l in
                let new_pairs = BatEnum.map (fun i -> (i, next_index)) active_indices in
                (new_worklist @ (BatList.of_enum new_pairs), new_l, next_index + 1, BatEnum.icons next_index active_indices)
              else
                new_worklist, new_l, next_index, active_indices
            in
            let new_worklist, new_l, next_index, active_indices = 
              if not (equal jnp new_c) then
                let new_l = IM.add next_index (jnp, jne) new_l in
                let new_pairs = BatEnum.map (fun i -> (i, next_index)) active_indices in
                (new_worklist @ (BatList.of_enum new_pairs), new_l, next_index + 1, BatEnum.icons next_index active_indices)
              else
                new_worklist, new_l, next_index, active_indices
            in
            let new_l = IM.add next_index (h, jme + jne) new_l in
            let new_pairs = BatEnum.map (fun i -> (i, next_index)) active_indices in
            let new_worklist = new_worklist @ (BatList.of_enum new_pairs) in
            aux (next_index + 1) new_worklist new_c new_l
      in
      let indices = List.mapi (fun i _ -> i) js in
      let next_index = List.length js in
      let l = List.fold_left (fun l i -> IM.add i (List.nth js i) l) IM.empty indices in
      let get_pairs l = List.filter (fun (x, y) -> x<>y) (fst(List.fold_left (fun (acc, l1) x -> (acc @ (List.map (fun y -> (x, y)) l1),List.tl l1)) ([],l) l)) in
      let c, gcd_basis = aux next_index (get_pairs indices) init_c l in
      c, BatList.of_enum (IM.values gcd_basis)

    let compute_factorization is = 
      let over, gcd_basis = factor_refinement is in
      let is = List.map (fun i -> mul over i) is in
      List.map (
        fun i ->
          let fact_list, _ = 
            List.fold_left (
              fun (flist, curr_h) (j, _) ->
                let rec aux h fj = 
                  if subset h j then
                    aux (quotient h j) (fj + 1)
                  else
                    fj :: flist, h
                in
                aux curr_h 0
            ) ([], i) gcd_basis in
          List.rev fact_list
      ) is, fst (List.split gcd_basis), over

    let find_unit_basis l = 
      let is = List.map (fun a -> make_frac_ideal ZZ.one (ideal_generated_by a)) l in
      let exps, _, _ = compute_factorization is in
      let exps_m = zzmify (
        Array.of_list (
          List.map (
            fun r ->
              Array.of_list (List.map ZZ.of_int r)
          ) exps        
        )) in
      let (h, u) = hermite_normal_form exps_m in
      let h_size = ZZM.nb_rows h in
      let basis_size = (ZZM.nb_rows exps_m) - h_size in
      let indices_to_grab = List.init basis_size (fun i -> h_size + i) in
      List.map (
        fun i ->
          let r = ZZM.row i u in
          let int_rows = BatEnum.map (
            fun (c, _) ->
              match ZZ.to_int c with
              | None -> failwith "Exponent overflow"
              | Some i -> i
          ) (ZZV.enum r) in
          BatList.of_enum int_rows
      ) indices_to_grab
  end

end

let splitting_field p_with_squares = 
  let square_free_facts = QQX.square_free_factor p_with_squares in
  let p = List.fold_left (fun acc (f, _) -> QQX.mul acc f) QQX.one square_free_facts in 
  let rec aux min_poly = 
    let module NF = MakeNF(struct let min_poly = min_poly end) in
    let (_, facts) = NF.X.factor (NF.X.lift p) in (*Can probably be made more efficient.*)
    let (lin_facts, non_lin_facts) = List.partition (fun (x, _) -> NF.X.order x = 1) facts in
    if List.length non_lin_facts = 0 then
      min_poly, (List.map (fun (x, d) -> NF.X.extract_root_from_linear x, d) lin_facts)
    else
      let non_lin_fact, _ = List.hd non_lin_facts in
      let new_min_poly, _, _ = primitive_elem (make_multivariate 0 min_poly) (NF.X.de_lift non_lin_fact) 0 1 in
      aux new_min_poly
  in
  aux QQX.zero
  



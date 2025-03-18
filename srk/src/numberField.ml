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


let primitive_elem needed_deg mp0 mp1 v0 v1 = 
  let mp0d, mp1d = QQXs.degree mp0, QQXs.degree mp1 in
  if mp0d = 0 then make_univariate mp1, QQX.zero, QQX.identity
  else if mp1d = 0 then make_univariate mp0, QQX.identity, QQX.zero
  else
    let v2 = (max v0 v1) + 1 in
    let rec aux i =
      (* v0 + iv1 - v2*)
      let lin_comb =
        QQXs.of_list [Q.one, Monomial.singleton v0 1
                    ; Q.of_int i, Monomial.singleton v1 1
                    ; Q.minus_one, Monomial.singleton v2 1]
      in
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


module type NF = sig  
  val deg : int
  val int_poly : QQX.t
  type t
  val make_elem : QQX.t -> t
  val get_poly : t -> QQX.t
  val of_rat : QQ.t -> t
  val compute_min_poly : t -> QQX.t
  val mul : t -> t -> t
  val int_mul : int -> t -> t
  val add : t -> t -> t
  val sub : t -> t -> t
  val inverse : t -> t
  val exp : t -> int -> t
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val is_zero : t -> bool
  val one : t
  val zero : t
  val negate : t -> t
  val pp : Format.formatter -> t -> unit
  module X : 
    sig
      include Euclidean with type scalar = t
      val pp : Format.formatter -> t -> unit
      val lift : QQX.t -> t
      val de_lift : t -> QQXs.t
      val factor_square_free_poly : t -> (scalar * (t list))
      val factor : t -> (scalar * ((t * int) list))
      val extract_root_from_linear : t -> scalar
    end
  module O : sig
    type ideal
    type o
    val pp_o : Format.formatter -> o -> unit
    val make_o_el : t -> ZZ.t * o
    val order_el_to_f_elem : ZZ.t * o -> t
    val idealify : ZZ.t array array -> ideal
    val pp_i : Format.formatter -> ideal -> unit
    val equal_i : ideal -> ideal -> bool
    val sum_i : ideal -> ideal -> ideal
    val mul_i : ideal -> ideal -> ideal
    val ideal_generated_by : o -> ideal
    val one_i : ideal
    val intersect_i : ideal -> ideal -> ideal
    val quotient_i : ideal -> ideal -> ideal
    val get_smallest_int : ideal -> ZZ.t
    type frac_ideal
    val one : frac_ideal
    val sum : frac_ideal -> frac_ideal -> frac_ideal
    val intersect : frac_ideal -> frac_ideal -> frac_ideal
    val mul : frac_ideal -> frac_ideal -> frac_ideal
    val exp : frac_ideal -> int -> frac_ideal
    val quotient : frac_ideal -> frac_ideal -> frac_ideal
    val pp : Format.formatter -> frac_ideal -> unit
    val equal : frac_ideal -> frac_ideal -> bool
    val subset : frac_ideal -> frac_ideal -> bool
    val make_frac_ideal : ZZ.t -> ideal -> frac_ideal
    val compute_overorder : frac_ideal -> frac_ideal -> frac_ideal * frac_ideal
    val factor_refinement : frac_ideal list -> frac_ideal * (frac_ideal * int) list
    val compute_factorization : frac_ideal list -> int list list * frac_ideal list * frac_ideal
    val find_unit_basis : o list -> int list list
  end
  val find_relations : t list -> int list list
end

module M = Linear.MakeLinearMap(QQ)(SrkUtil.Int)(
  struct
    include QQX

    let split_leading v =
      try
        let (d, b) = min_support v in
        let v' = set d QQ.zero v in
        Some (d, b, v')
      with Not_found ->
        None
  end
)(QQX)

let compute_min_poly_p el p =
  let e i = snd (QQX.qr (QQX.exp el i) p) in
  let rec aux app_res m i =
    match app_res with
   | Some p -> QQX.add_term QQ.one i p
   | None ->
     let new_m = M.add_exn (e i) (QQX.negate (QQX.exp (QQX.identity) i)) m in
       aux (M.apply new_m (e (i+1))) new_m (i+1)
  in
  aux None M.empty 0


module MakeNF (A : sig val min_poly : QQX.t end) = struct

  type t = QQX.t (* elements of the field are polynomials of degree < the degree of the field*)


  (* Let p be A.min_poly divided by the lc of A.min_poly. Then min_poly_den_multiple is a multiple
     of the denominators of p.*)
  let min_poly_den_multiple = 
    QQX.fold (
      fun _ c l ->
        ZZ.lcm (QQ.denominator c) l
    ) A.min_poly (QQ.numerator (QQX.coeff (QQX.order A.min_poly) A.min_poly))

  (* Let min_poly = p(x), and let d be the smallest integer such that dp(x) has integer coefficients.
     Then the element dx in Q[x]/p(x) is an algebraic integer. Let q(x) be the minimal polynomial
     of dx. Then Q[x]/p(x) iso Q[x]/q(x) with q(x) an integer polynomial. For constructing
     an order later we need such an integer polynomial. Therefore, rather than using Q[x]/p(x) as
     a representation of the field we use Q[x]/q(x). The isomorphism is recognized by x --> 1/d x.*)
  let int_poly = 
    if QQX.is_zero A.min_poly then QQX.identity
    else if QQX.order A.min_poly < 1 then
      failwith ("Creating a trivial field A.min_poly = " ^ ((SrkUtil.mk_show QQX.pp) A.min_poly))
    else compute_min_poly_p (QQX.scalar_mul (QQ.of_zz min_poly_den_multiple) QQX.identity) A.min_poly


  let compute_min_poly e = compute_min_poly_p e int_poly

  let deg = QQX.order int_poly

  let reduce a = 
    if QQX.is_zero int_poly then a
    else snd (QQX.qr a int_poly)

  (*The isomorphism is recognized by x --> 1/d x.*)
  let make_elem p = reduce (QQX.map (fun d c -> QQ.div c (QQ.exp (QQ.of_zz min_poly_den_multiple) d)) p)

  let get_poly e = e

  let of_rat = QQX.scalar

  let mul a b = 
    reduce (QQX.mul a b)

  let add = 
    QQX.add
  
  let sub = 
    QQX.sub

  let inverse a = 
    let (_, u, _) = QQX.gcdext a int_poly in
    u

  let pos_exp = SrkUtil.exp mul QQX.one 

  let exp a i = 
    if i >= 0 then pos_exp a i
    else inverse (pos_exp a (-i))

  let equal a b = 
    QQX.equal (reduce a) (reduce b)

  let compare a b =
    QQX.compare QQ.compare (reduce a) (reduce b)

  let is_zero a = 
    QQX.equal (QQX.zero) (reduce a)

  let one = QQX.one

  let zero = QQX.zero

  let negate = QQX.negate


  let pp formatter p = 
    let pp_monomial formatter (coeff, order) = 
      if order = 0 then
        QQ.pp formatter coeff
      else if order = 1 && QQ.equal coeff QQ.one then
        Format.fprintf formatter "@[z@]"
      else if order = 1 && QQ.equal coeff (QQ.negate QQ.one) then
        Format.fprintf formatter "@[-z@]"
      else if order = 1 then
        Format.fprintf formatter "@[%az@]" QQ.pp coeff
      else if QQ.equal coeff QQ.one then
        Format.fprintf formatter "@[z^%d@]" order
      else if QQ.equal coeff (QQ.negate QQ.one) then
        Format.fprintf formatter "@[-z^%d@]" order
      else 
        Format.fprintf formatter "@[%az^%d@]" QQ.pp coeff order
    in
    SrkUtil.pp_print_enum
      ~pp_sep:(fun formatter () -> Format.fprintf formatter "@ + ")
      pp_monomial
      formatter
      (QQX.enum p)

  

  let int_mul i x = QQX.scalar_mul (QQ.of_int i) x

  module E = struct 
    type nonrec t = t
    let zero = zero
    let int_mul = int_mul
    let one = one 
    let mul = mul 
    let negate = negate 
    let exp = exp 
    let pp = pp 
    let equal = equal
    let add = add
    let inverse = inverse
  end

  (*Polynonials in the number field.*)
  module X = struct 
    include MakeEuclidean(E)

    let pp = pp E.pp
      
    let lift (p : QQX.t) = 
      of_enum (BatEnum.map (fun (c, d) -> QQX.scalar c, d) (QQX.enum p))

    let de_lift (p : t) : QQXs.t = 
      fold (
        fun m coef acc ->
          QQXs.add (QQXs.mul_monomial (Monomial.singleton 1 m) (make_multivariate 0 coef)) acc
      ) p QQXs.zero

    (* Factoring polynomials via Trager's method*)
    let factor_square_free_poly p =
      if QQX.is_zero int_poly then
        let p_uni = make_univariate (de_lift p) in
        let content, facts = QQX.factor p_uni in
        make_elem (QQX.scalar content), List.map (fun (f, _) -> lift f) facts
      else
        (*let lc = coeff (order p) p in
        let pmonic = scalar_mul (inverse lc) p in
        let pmonic_deg = order pmonic in
        let pmonicxs = de_lift pmonic in (* p is a multivariate polynomial in 0, the variable of the field, and 1 the variable of the polynomial.*)*)
        let prim, v0_in_prim, v1_in_prim =
          primitive_elem
            ((order p) * deg)
            (make_multivariate 0 int_poly)
            (de_lift p)
            0
            1
        in
        let primxs = make_multivariate 0 prim in
        let v1_term = QQXs.sub (make_multivariate 1 (QQX.identity)) (make_multivariate 0 v0_in_prim) in 
        let v2_term = QQXs.sub (make_multivariate 2 (QQX.identity)) (make_multivariate 0 v1_in_prim) in
        let mon_order = FGb.get_mon_order [0;2] [1] in
        let (_, factors) = QQX.factor prim in (*Is the content needed somewhere?*)
        let find_factor (fact, deg) = 
          if deg > 1 then failwith "Primitive element contains square factor?";
          let factxs = make_multivariate 0 fact in
          let ps = FGb.grobner_basis [0;2] [1] [primxs; v1_term; v2_term; factxs] in
          let v2ps = 
            List.filter (
                fun p -> 
                let dims = QQXs.dimensions p in
                if (SrkUtil.Int.Set.mem 2 dims) && not (SrkUtil.Int.Set.mem 0 dims) then
                  true
                else false
              ) ps
          in
          let poly =
            match v2ps with
            | [] -> failwith "Unable to find factor in reduced ring";
            | p::ps ->
               List.fold_left (fun p q ->
                   if QQXs.degree p < QQXs.degree q then p else q)
                 p
                 ps
          in
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
          ) poly zero
        in
        (E.one, List.map find_factor factors)


    let factor (p : t) = 
      let square_free_facts = square_free_factor p in
      List.fold_left (
        fun (coef, factors) (square_free_fact, deg) ->
          let (lc, facts) = factor_square_free_poly square_free_fact in
          let new_facts = List.map (fun f -> (f, deg)) facts in
          E.mul (E.exp lc deg) coef, new_facts @ factors
      ) (E.one, []) square_free_facts

    let extract_root_from_linear p = 
      if order p <> 1 then failwith "Trying to extract root from non-linear polynomial"
      else
        let lc = coeff 1 p in
        let const = E.negate (coeff 0 p) in
        E.mul (inverse lc) const 

  end
   

  module FMPZ_mat = Flint.FMPZ_mat
  module ACB = Flint.ACB
  module FMPZ_poly = Flint.FMPZ_poly
  module ARB_FMPZ_poly = Flint.ARB_FMPZ_poly
  module MAG = Flint.MAG
  module ARB = Flint.ARB
  module ARF = Flint.ARF
  module ZZV = Ring.MakeVector(ZZ)
  module ZZM = Ring.MakeMatrix(ZZ)

  let zzmify a = 
    let m = Array.length a in
    if m = 0 then
      FMPZ_mat.zero 0 0 
    else
      let n = Array.length a.(0) in
      FMPZ_mat.init ~rows:m ~columns:n (fun i j -> a.(i).(j))

  let unzzmify matrix = 
    let m, n = FMPZ_mat.rows matrix, FMPZ_mat.columns matrix in
    Array.init_matrix m n (FMPZ_mat.entry matrix)

  (*The number field is Q[x]/q(x) for an integer polynomial q(x). The order O is Z[x]/q(x).*)
  module O = struct

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
      zzmify (get_mult_table ())

    let mult i j = 
      if i >= rank || j >= rank then Array.make rank ZZ.zero
      else
        let m = get_mult_table () in
        m.(i*rank + j)
  

    type pre_ideal = Red of FMPZ_mat.t | UnRed of FMPZ_mat.t

    (*ideals are flint matrices of rank x rank. Internally to this module they are mutable and can be reduced or
       unreduced. Reduced ideals are in HNF and unreduced matrices are not necessarily in HNF.*)
    type ideal = pre_ideal ref

    (*An element of the order is an integer vector of size rank.*)
    type o = ZZ.t array

    let pp_o f o = 
      let strs = Array.mapi (
        fun i coef ->
            (ZZ.show coef)^ "x^" ^ (string_of_int (deg - 1 - i))
        ) o in
      let str = String.concat " + " (List.rev (Array.to_list strs)) in
      Format.fprintf f "@[%s@]  where x is a root of @[%a@]" str QQX.pp int_poly
    
    (*hermite a = h*)
    let hermite a = 
      (*Log.time "HNF"*) FMPZ_mat.hnf a

    (*hermite a = (h, u) where u*a = h and hermite a = h.*)
    let hermite_transform a = 
      (*Log.time "HNF"*) FMPZ_mat.hnf_transform a

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

    (* Get the matrix representation of the ideal reduced or unreduced.*)
    let get_mat i = match !i with Red m | UnRed m -> m


    let idealify aa = 
      ref (UnRed (zzmify aa))

    let _pp_ez fmt r =
      Format.fprintf
        fmt
        "[[%a, %a]; [%a, %a]]"
        ZZ.pp (FMPZ_mat.entry r 0 0)
        ZZ.pp (FMPZ_mat.entry r 0 1)
        ZZ.pp (FMPZ_mat.entry r 1 0)
        ZZ.pp (FMPZ_mat.entry r 1 1)

    (* Get the reduced matrix representation of the ideal*)
    let get_reduced i = 
      match !i with 
      | Red m -> m 
      | UnRed m ->
         let red =
           (* I think this should work... *)
           FMPZ_mat.window (hermite m) ~top:0 ~left:0 ~bottom:rank ~right:rank
         in
        i := Red red;
        red

    let get_smallest_int i =
      FMPZ_mat.entry (get_reduced i) (rank - 1) (rank - 1)

    let pp_i f i =
      ZZM.pp ZZ.pp f (ZZM.of_dense (unzzmify (get_reduced i)))


    let equal_i a b =
      FMPZ_mat.equal (get_reduced a) (get_reduced b)


    let sum_i a b =
      ref (UnRed (FMPZ_mat.concat_vertical (get_mat a) (get_mat b)))

    let mul_i a b = 
      ref (UnRed (FMPZ_mat.mul (FMPZ_mat.kronecker_product (get_reduced a) (get_reduced b)) (mult_table_m ())))

    (* Given an element o, comptues o * e_i, where e_i is the i'th basis vector of the order. *)
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

    let one_i = ref (Red (FMPZ_mat.one rank rank))


    let get_lower_left_corner a = 
      let m = FMPZ_mat.rows a in
      FMPZ_mat.window a ~top:(m-rank) ~left:0 ~bottom:m ~right:rank


    let intersect_i a b = 
      let a_red, b_red = get_reduced a, get_reduced b in
      let (_, u) = hermite_transform (FMPZ_mat.concat_vertical a_red b_red) in
      let u_sub = get_lower_left_corner u in
      ref (UnRed (FMPZ_mat.mul u_sub a_red))

    
    let quotient_i a b = 
      let ba = unzzmify (get_reduced b) in
      let top_part = Array.of_list (List.init rank (
        fun i ->
          Array.concat (List.init rank (
            fun j ->
              mul_v_by_basis_v ba.(j) i
          ))
      )) in
      let bot_part =
        FMPZ_mat.kronecker_product
          (FMPZ_mat.one rank rank)
          (FMPZ_mat.neg (get_reduced a))
      in
      let (_, u) =
        hermite_transform (FMPZ_mat.concat_vertical (zzmify top_part) bot_part)
      in
      ref (UnRed (get_lower_left_corner u))

    let scalar_mul_i a i =
      match !i with
      | UnRed m -> ref (UnRed (FMPZ_mat.scalar_mul m a))
      | Red m -> ref (Red (FMPZ_mat.scalar_mul m a))

    let divide_common_factor common_factor i = 
      match !i with
      | Red m ->
        ref (Red (FMPZ_mat.scalar_divexact m common_factor))
      | UnRed m ->
        ref (UnRed (FMPZ_mat.scalar_divexact m common_factor))

    type pre_frac_ideal = Norm of ZZ.t * ideal | UnNorm of ZZ.t * ideal

    (*fractional ideals consist of an integer and an ideal. Internally to this module they are mutable and can be normalized or
       unnormalized. Normalized fractional ideals (d, i) are such that gcd(d, get_reduced i) = 1. That is, d does not share a common
       factor with the matrix representation of i.*)
    type frac_ideal = pre_frac_ideal ref


    let one = ref (Norm (ZZ.one, one_i))

    let get_normalized (i : frac_ideal) = 
      match !i with
      | Norm (d, a) -> (d, a)
      | UnNorm (d, a) ->
        let matrix_factor = FMPZ_mat.content (get_reduced a) in
        let common_factor = ZZ.gcd d matrix_factor in
        if ZZ.equal common_factor ZZ.one then 
          (i := Norm (d, a);
          d, a)
        else (
          let new_a = divide_common_factor common_factor a in
          let new_d = ZZ.div d common_factor in
          i := Norm (new_d, new_a);
          new_d, new_a
        )

    let get_den_and_ideal (i : frac_ideal) = 
      match !i with | Norm (d, id) | UnNorm (d, id) -> (d, id)

    let sum ai bi = 
      let (d1, a) = get_den_and_ideal ai in
      let (d2, b) = get_den_and_ideal bi in
      let new_d = ZZ.lcm d1 d2 in
      ref (UnNorm (new_d, sum_i (scalar_mul_i (ZZ.div new_d d1) a) (scalar_mul_i (ZZ.div  new_d d2) b)))

    let intersect ai bi = 
      let (d1, a) = get_den_and_ideal ai in
      let (d2, b) = get_den_and_ideal bi in
      let new_d = ZZ.lcm d1 d2 in
      ref (UnNorm (new_d, intersect_i (scalar_mul_i (ZZ.div new_d d1) a) (scalar_mul_i (ZZ.div new_d d2) b)))

    let mul ai bi = 
      let timer () = 
        let (d1, a) = get_den_and_ideal ai in
        let (d2, b) = get_den_and_ideal bi in
        ref (UnNorm (ZZ.mul d1 d2, mul_i a b))
      in
      (*Log.time "Ideal mul"*) timer ()

    let exp ai i = 
      let timer () = 
        let rec aux acc j = 
          if j = 0 then acc
          else
            aux (mul ai acc) (j-1)
          in
        aux one i
      in
      (*Log.time "Ideal Exp"*) timer ()


    let quotient ai bi = 
      let timer () = 
        let (d1, a) = get_den_and_ideal ai in
        let (d2, b) = get_den_and_ideal bi in
        let smallest_int = get_smallest_int b in
        let new_d = ZZ.mul d1 smallest_int in
        let new_m = quotient_i (scalar_mul_i (ZZ.mul d2 smallest_int) a) b in
        ref (UnNorm (new_d, new_m))
      in
      (*Log.time "Ideal Quotient"*) timer ()


    let pp f i = 
      let (d, a) = get_normalized i in
      Format.fprintf f "@[1/(%a)@]" ZZ.pp d;
      pp_i f a
    
    let equal ai bi = 
      let timer () = 
        let (d1, a) = get_normalized ai in
        let (d2, b) = get_normalized bi in
        ZZ.equal d1 d2 && equal_i a b
      in
      (*Log.time "Ideal equal"*) timer ()

    let subset a b = 
      equal b (sum a b)

    let make_frac_ideal_internal d i = 
      ref (UnNorm (d, i))

    let make_frac_ideal d i = 
      make_frac_ideal_internal d i

    (*Algorithm 3.17 of Ge*)
    let compute_overorder o i =
      let rec aux c j =
        let c_div_j = quotient c j in
        let x = quotient c_div_j c_div_j in
        if equal x c then (c, j)
        else aux x (mul x j)
      in
      aux o i

    module IM = SrkUtil.Int.Map

    (*Worklist implementation of Algorithm 3.19 of Ge*)
    let factor_refinement is = 
      let is = List.filter (fun i -> not (equal i one)) is in
      let init_c = List.fold_left (fun acc i -> fst (compute_overorder acc i)) one is in
      let js = List.map (fun i -> mul i init_c, 1) is in
      let rec aux next_index worklist c l = 
        match worklist with
        | [] -> c, l
        | (m, n) :: rest ->
          let (jm, jme), (jn, jne) = IM.find m l, IM.find n l in
          let h = sum jm jn in (*Check if jm jn are coprime*)
          if equal c h then aux next_index rest c l (*If coprime*)
          else (*If they share a common factor h*)
            let new_c, h = compute_overorder c h in (*Enlarge the overorder so h is invertible*)
            let new_worklist = List.filter (fun (a, b) -> a <> m && a <> n && b <> m && b <> n) worklist in (*Remove jm jn from the worklist*)
            let new_l = IM.remove m (IM.remove n l) in
            let new_l = IM.map (fun (j, e) -> mul j new_c, e) new_l in (*The ideals need to now be w.r.t. the new overorder*)
            let jm, jn = (mul new_c jm, mul new_c jn) in
            let jmp = quotient jm h in
            let jnp = quotient jn h in
            let active_indices = IM.keys new_l in
            let new_worklist, new_l, next_index, active_indices = 
              if not (equal jmp new_c) then (*If the new jm is not trivial. I.e. 1*)
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

    let find_unit_basis_f l =
      let dens, nums = List.split l in 
      let is = List.map (fun a -> make_frac_ideal_internal ZZ.one (ideal_generated_by a)) nums in
      let dens_i = List.map (
        fun a -> 
          let a_el = Array.make rank ZZ.zero in
          a_el.(rank-1) <- a;
          make_frac_ideal_internal ZZ.one (ideal_generated_by a_el)
        ) dens in
      let exps, _, _ = compute_factorization (is @ dens_i) in
      let num_is = List.length l in
      let num_den_equal_constr = List.init (2* num_is) (
        fun index ->
          List.init num_is (
            fun j -> 
              if index mod num_is = j then 1
              else 0
          )
      ) in
      let exps_m = zzmify (
        Array.of_list (
          List.map (
            fun r ->
              Array.of_list (List.map ZZ.of_int r)
          ) (List.map2 (@) exps num_den_equal_constr)       
        )) in
      let (h, u) = hermite_transform exps_m in
      let h_nb_non_zero_rows = 
        let rec outer i rows =
          if i >= (FMPZ_mat.rows h) then rows
          else
            let rec inner j not_zero = 
              if j >= (FMPZ_mat.columns h) then
                if not_zero then outer (i+1) (rows + 1)
                else outer (i+1) rows
              else
                let is_entry_zero = ZZ.equal (FMPZ_mat.entry h i j) ZZ.zero in
                inner (j + 1) ((not is_entry_zero) || not_zero)
            in
            inner 0 false
          in
          outer 0 0
        in
      let basis_size = (FMPZ_mat.rows exps_m) - h_nb_non_zero_rows in
      let indices_to_grab = List.init basis_size (fun i -> h_nb_non_zero_rows + i) in
      let js = List.init num_is (fun i -> i) in
      let basis = List.map (
        fun i ->
          List.map (
            fun j ->
            match ZZ.to_int (FMPZ_mat.entry u i j) with
            | Some i -> i
            | None -> assert false
          ) js
      ) indices_to_grab in
      List.map (
        fun r ->
          match List.find_opt (fun e -> e <> 0) r with
          | None -> failwith "Basis with zero vector"
          | Some lc -> if lc < 0 then List.map ( ( * ) (-1)) r else r
      ) basis

    let find_unit_basis l = 
      find_unit_basis_f (List.map (fun i -> ZZ.one, i) l)


  end

  let find_unit_basis l = 
    O.find_unit_basis_f (List.map O.make_o_el l)

  let calc_needed_prec n s b c lambda = 
    let nq, sq, bq, cq = QQ.of_int n, QQ.of_int s, QQ.of_zz b, QQ.of_int c in
    let operand2 = QQ.exp (QQ.div (QQ.mul (QQ.add nq QQ.one) bq) lambda) (2 * n) in (* ((n+1)B/lambda)^{2n}*)
    let operand1 = QQ.add QQ.one (QQ.mul nq (QQ.mul sq (QQ.exp cq 2))) in (* 1 + nsc^2 *)
    let m = QQ.ceiling (QQ.mul sq (QQ.mul operand1 operand2)) in
    let two_to_s_minus_1_sqrt = Mpfr.of_int 2 Mpfr.Up in
    let _ = Mpfr.pow_si two_to_s_minus_1_sqrt two_to_s_minus_1_sqrt (s-1) Mpfr.Up in
    let _ = Mpfr.sqrt two_to_s_minus_1_sqrt two_to_s_minus_1_sqrt Mpfr.Up in (* 2^((s-1)/2)*)
    let msn_sqrt = Mpfr.of_mpz (ZZ.mpz_of (ZZ.mul m (ZZ.mul (ZZ.of_int s) (ZZ.of_int n)))) Mpfr.Up in 
    let _ = Mpfr.sqrt msn_sqrt msn_sqrt Mpfr.Up in (* sqrt(Msn) *)
    let m_sqrt = Mpfr.of_mpz (ZZ.mpz_of m) Mpfr.Up in 
    let _ = Mpfr.sqrt m_sqrt m_sqrt Mpfr.Up in (* sqrt(M) *)
    let summand1, (_, summand2), res = Mpfr.init (), Mpfr.init_set_si c Mpfr.Up, Mpfr.init () in
    let _ = Mpfr.mul summand1 two_to_s_minus_1_sqrt m_sqrt Mpfr.Up in (* 2^((s-1)/2) sqrt(M)*)
    let _ = Mpfr.mul summand2 summand2 two_to_s_minus_1_sqrt Mpfr.Up in
    let _ = Mpfr.mul summand2 summand2 msn_sqrt Mpfr.Up in (* 2^((s-1)/2)c sqrt(Msn)*)
    let _ = Mpfr.add res summand1 summand2 Mpfr.Up in
    let lambda_mpq = Mpq.init_set_z (ZZ.mpz_of (QQ.numerator lambda)) in
    let _ = Mpq.div lambda_mpq lambda_mpq (Mpq.init_set_z (ZZ.mpz_of (QQ.denominator lambda))) in
    let _ = Mpfr.div res res (Mpfr.of_mpq lambda_mpq Mpfr.Up) Mpfr.Up in
    let _ = Mpfr.log2 res res Mpfr.Up in
    let _ = Mpfr.ceil res res in 
    let t_mpq = Mpfr.to_mpq res in
    let t_mpz = Mpz.init () in
    let _ = Mpq.get_num t_mpz t_mpq in
    match ZZ.to_int (ZZ.of_mpz (Mpzf.of_mpz t_mpz)) with
    | None -> failwith "Requiring more than max int bits of precision"
    | Some x -> x, m

  (*Given an element of the number field e = p(x), a conjugate r of the integer polynomial, computes 1/2pi ln(p(r)) using
     the given precision.*)
  let get_conj_div_2pi e r prec = 
    let conj =
      QQX.fold (fun d coef acc ->
          let coef_acb = ACB.of_q coef prec in
          let t = ACB.mul coef_acb (ACB.pow_si r d prec) prec in (* could increase prec? *)
          ACB.add t acc prec)
        e
        ACB.zero
    in
    let log_conj = ACB.log conj prec in
    ACB.trim (ACB.div
                (ACB.div log_conj (ACB.pi prec) prec)
                (ACB.of_int 2)
                prec)

  let acb_get_real_imag_mag_upper acb =
    let a = MAG.get_z (ARB.get_mag (ACB.real acb)) in
    let b = MAG.get_z (ARB.get_mag (ACB.imag acb)) in
    (a, b)

  let arb_mid_2exp arb = ARF.to_2exp (ARB.mid arb)

  let find_relations_of_units (units : t list) = 
    let arb_poly = FMPZ_poly.init (deg+1) (fun i -> (QQ.numerator (QQX.coeff i int_poly))) in
    let n = 2 * deg in
    let s = (List.length units) + deg in
    let b_guess = ZZ.of_int 5 in
    let t_guess, _ = calc_needed_prec n s b_guess 1 (QQ.of_frac 1 16) in
    logf ~level:`trace "Initial guess for required bits of precision: %d" t_guess;
    let build_cross_matrix prec = 
      let prec = prec + 5 in (* Guess plus a few extra bits. *)
      let roots =
        List.rev (ARB_FMPZ_poly.fold_complex_roots (fun xs r -> r::xs) [] arb_poly prec)
      in
      List.map (
        fun u ->
          List.map (
            fun r ->
              get_conj_div_2pi u r prec
          ) roots
      ) units 
    in
    let u_r_cross_matrix = build_cross_matrix t_guess in
    let real_b = List.fold_left (
      fun maximum row -> 
        let b_row = List.fold_left (
          fun sum conj ->
            let (c, d) = acb_get_real_imag_mag_upper conj in
            ZZ.add (ZZ.add c d) sum
        ) ZZ.zero row in
        ZZ.max maximum b_row
    ) (ZZ.of_int (-1)) u_r_cross_matrix in
    let t_req, m = calc_needed_prec n s real_b 1 (QQ.of_frac 1 16) in
    let fmpz_mat = FMPZ_mat.zero s (n+s) in
    let t = 
      let rec aux mat prec = 
        let is_precise_enough = List.for_all (
          fun row -> 
            List.for_all (fun conj -> ACB.rel_accuracy_bits conj > t_req) row
        ) mat in
        if is_precise_enough then
          let used_t, rev_mat = List.fold_left (
            fun (max_t, ac) row ->
              let t_row, r = List.fold_left (
                fun (mx_t, acc) c ->
                  let (ureal, ereal) = arb_mid_2exp (ACB.real c) in
                  let (uimag, eimag) = arb_mid_2exp (ACB.imag c) in
                  let er, ei = 
                    match (ZZ.to_int ereal, ZZ.to_int eimag) with
                    | None, _ | _, None -> failwith "Exponents of fmpz is larger than maxint"
                    | Some er, Some ei -> er, ei
                  in
                  let temp = min er ei in
                  if temp < (-1) * mx_t then (-1) * temp,(uimag, ei) :: (ureal, er) :: acc
                  else mx_t, (uimag, ei) :: (ureal, er) :: acc
              ) (max_t, []) row in
              t_row, (List.rev r) :: ac
          ) (t_req, []) mat
          in
          let int_mat = List.rev rev_mat in
          for i = 0 to s - 1 do
            for j = 0 to (n+s) - 1 do
              if i = j then 
                FMPZ_mat.set_entry fmpz_mat i j ZZ.one
              else if (i >= List.length units && j >= s && (j-s) / 2 = (i - List.length units) && (j-s) mod 2 = 1) then 
                let entry = Z.shift_left ZZ.one used_t in
                FMPZ_mat.set_entry fmpz_mat i j entry
              else if i < List.length units && j >= s then
                let uij, eij = (List.nth (List.nth int_mat i) (j-s)) in
                FMPZ_mat.set_entry fmpz_mat i j (Z.shift_left uij (used_t+eij))
              else 
                FMPZ_mat.set_entry fmpz_mat i j ZZ.zero
            done;
          done;
          used_t
        else
          (logf ~level:`trace "Trying to build matrix with %d bits of precision" (2*prec);
          aux (build_cross_matrix (2 * prec)) (2*prec))
      in
      aux u_r_cross_matrix t_guess
    in
    logf ~level:`trace "Using t = %d, reducing matrix" t;
    FMPZ_mat.lll fmpz_mat (QQ.of_frac 3 4) (QQ.of_frac 51 100); (* Using lll_storjohann here seemed to crash sometimes.*)
    let rec find_relations i basis =
      if i >= s then basis
      else
        let row_zz = List.init (n+s) (FMPZ_mat.entry fmpz_mat i) in
        let norm_squared = List.fold_left (fun acc x -> ZZ.add acc (ZZ.mul x x)) ZZ.zero row_zz in
        if ZZ.compare norm_squared (ZZ.mul (Z.pow (ZZ.of_int 2) (s-1)) m) <= 0 then
          let int_i = 
            List.mapi (
              fun ind z ->
                if ind >= List.length units then ind, 0
                else
                  match ZZ.to_int z with
                  | None -> failwith "Unit relation basis requires bigger than max int"
                  | Some x -> ind, x
          ) row_zz in
          let relation = List.filter_map (
            fun (ind, x) -> if ind >= List.length units then None
                            else Some x
          ) int_i in
          find_relations (i+1) (relation :: basis)
        else find_relations (i+1) basis
    in
    find_relations 0 []


  let find_relations elems = 
    let unit_basis = (*Log.time "Finding Unit basis"*) find_unit_basis elems in
    let (ones, units_but_not_one) = List.partition_map (
      fun expl ->
        let unit = List.fold_left2 (
            fun acc elem e ->
              mul acc (exp elem e)
          ) one elems expl
          in
        if equal unit one then
          Left expl
        else
          Right (unit, expl)
    ) unit_basis in
    let res = 
      if List.length units_but_not_one = 0 then ones
      else
        let unit_relations = (*Log.time "Finding relations of Units"*) find_relations_of_units (fst (List.split units_but_not_one)) in
        let relations = List.map (
          fun unit_relation ->
            List.fold_left2 (
              fun acc m relation_to_give_unit ->
                let x = List.map (( * ) m) relation_to_give_unit in
                List.map2 (+) acc x
            ) (List.init (List.length elems) (fun _ -> 0)) unit_relation (snd (List.split units_but_not_one))
        ) unit_relations in
        ones @ relations in
    let res_a = Array.of_list (List.map (fun r -> Array.of_list (List.map ZZ.of_int r)) res) in
    let h = FMPZ_mat.hnf (zzmify res_a) in
    let h_a = unzzmify h in
    let z_to_int z = 
      match ZZ.to_int z with
      | None -> failwith "Multiplicative relation is requiring more than max int"
      | Some x -> x
    in
    Array.to_list (Array.map (fun r -> Array.to_list (Array.map z_to_int r)) h_a)





end

type sf = Sf : (module NF with type t = 'a) * (('a * int) list) -> sf

(*See the wikipedia entry on splitting field for more information on this method.*)
let splitting_field p_with_squares : sf = 
  let square_free_facts = QQX.square_free_factor p_with_squares in
  let p = List.fold_left (fun acc (f, _) -> QQX.mul acc f) QQX.one square_free_facts in
  let rec aux min_poly = 
    let module NF = MakeNF(struct let min_poly = min_poly end) in
    let (_, facts) = NF.X.factor (NF.X.lift p) in (*Can probably be made more efficient.*)
    let (lin_facts, non_lin_facts) = List.partition (fun (x, _) -> NF.X.order x <= 1) facts in
    if List.length non_lin_facts = 0 then
      let nf = (module NF : NF with type t = QQX.t) in
      Sf (nf, (List.map (fun (x, d) -> NF.X.extract_root_from_linear x, d) lin_facts))
    else
      let non_lin_fact, _ = List.hd non_lin_facts in
      let new_min_poly, _, _ = primitive_elem (NF.deg * NF.X.order non_lin_fact) (make_multivariate 0 NF.int_poly) (NF.X.de_lift non_lin_fact) 0 1 in
      aux new_min_poly
  in
  aux QQX.zero
  



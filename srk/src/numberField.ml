open Polynomial

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

  let reduce a = 
    if QQX.is_zero A.min_poly then a
    else snd (QQX.qr a A.min_poly)

  (*let r = 
    Rewrite.mk_rewrite (Monomial.degrevlex) [make_multivariate 0 A.min_poly]*)

  let make_elem p = reduce p

  let mul a b = 
    reduce (QQX.mul a b)

  let add = 
    QQX.add
  
  let sub = 
    QQX.sub

  let inverse a = 
    let (_, u, _) = QQX.ex_euc a A.min_poly in
    u

  let exp a i = 
    reduce (QQX.exp a i)

  let equal a b = 
    QQX.equal (reduce a) (reduce b)

  let is_zero a = 
    QQX.equal (QQX.zero) (reduce a)

  let one = QQX.one

  let zero = QQX.zero

  let negate = QQX.negate


  let pp = 
    QQX.pp

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
      if QQX.is_zero A.min_poly then
        let p_uni = make_univariate (de_lift p) in
        let lc, facts = QQX.factor p_uni in
        make_elem (QQX.scalar lc), List.map (fun (f, d) -> lift f, d) facts
      else
        let lc = coeff (order p) p in
        let pmonic = scalar_mul (inverse lc) p in
        let pmonicxs = de_lift pmonic in (* p is a multivariate polynomial in 0, the variable of the field, and 1 the variable of the polynomial.*)
        let prim, v0_in_prim, v1_in_prim = primitive_elem (make_multivariate 0 A.min_poly) pmonicxs 0 1 in
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
  



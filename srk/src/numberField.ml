open Polynomial

type pseudo_uni = QQXs.t * Monomial.dim

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


let primitive_elem mp0x mp1x = 
  let v0, v1 = 0, 1 in
  let mp0, mp1 = make_multivariate v0 mp0x, make_multivariate v1 mp1x in
  let needed_deg = (QQXs.degree mp0) * (QQXs.degree mp1) in
  let v2 = (max v0 v1) + 1 in
  let rec aux i = 
    (* v0 + iv1 - v2*)
    let lin_comb = QQXs.of_list [Q.one, Monomial.singleton v0 1; Q.of_int i, Monomial.singleton v1 1; Q.minus_one, Monomial.singleton v2 1] in
    let gb = FGb.grobner_basis [0; 1] [2] [mp0; mp1; lin_comb] in
    let v2_poly = 
      List.find (
        fun p -> 
          let dims = QQXs.dimensions p in
          SrkUtil.Int.Set.is_singleton dims && SrkUtil.Int.Set.mem v2 dims) gb in
    if QQXs.degree v2_poly = needed_deg then v2_poly, Rewrite.mk_rewrite (FGb.get_mon_order [0;1] [2]) gb
    else if i > needed_deg then failwith "Unable to find primitive element, which breaks the primitive element theorem."
    else aux (i+1)
  in
  let prim, r = aux 1 in
  let v0_in_prim = make_univariate (Rewrite.reduce r (QQXs.of_dim v0)) in
  let v1_in_prim = make_univariate (Rewrite.reduce r (QQXs.of_dim v1)) in
  make_univariate prim, v0_in_prim, v1_in_prim

module MakeNF (A : sig val min_poly : QQX.t end) = struct

  type t = QQX.t

  type elem = QQXs.t

  let r = 
    Rewrite.mk_rewrite (Monomial.degrevlex) [make_multivariate 0 A.min_poly]

  let make_elem p = Rewrite.reduce r (make_multivariate 0 p)

  let mul a b = 
    Rewrite.reduce r (QQXs.mul a b)

  let add = 
    QQXs.add
  
  let sub = 
    QQXs.sub

  let exp a i = 
    Rewrite.reduce r (QQXs.exp a i)

  let equal a b = 
    QQXs.equal (Rewrite.reduce r a) (Rewrite.reduce r b)

  let is_zero a = 
    QQXs.equal (QQXs.zero) (Rewrite.reduce r a)


  module PNF = struct 
    include MakeUnivariate(
      struct 
        type t = QQXs.t
        let equal = equal
        let add = add
        let zero = QQXs.zero
        let one = QQXs.one
        let mul = mul
        let negate = QQXs.negate
      end)
    let pp formatter p = 
      let pp_monomial formatter (coeff, order) = 
        if order = 0 then
          QQXs.pp (fun fo _ -> Format.pp_print_string fo "z") formatter coeff
        else if QQXs.equal coeff QQXs.one then
          Format.fprintf formatter "@[x^%d@]" order
        else if QQXs.equal coeff (QQXs.negate QQXs.one) then
          Format.fprintf formatter "@[-x^%d@]" order
        else 
          Format.fprintf formatter "@[(%a)*x^%d@]" (QQXs.pp (fun fo _ -> Format.pp_print_string fo "z")) coeff order
        in
        SrkUtil.pp_print_enum
          ~pp_sep:(fun formatter () -> Format.fprintf formatter "@ + ")
          pp_monomial
          formatter
          (enum p)
      
    let lift (p : QQX.t) = 
      of_enum (BatEnum.map (fun (c, d) -> QQXs.scalar c, d) (QQX.enum p))
  end

  

  (** Need to square free factor p*)
  let factor p = 
    let lc, _, _ = QQXs.split_leading Monomial.degrevlex (make_multivariate 1 p) in
    let p = QQX.map (fun _ c -> QQ.div c lc) p in
    let prim, v1_in_prim, v2_in_prim = primitive_elem A.min_poly p in
    let primxs = make_multivariate 0 prim in
    let v1_term = QQXs.sub (make_multivariate 1 (QQX.identity)) (make_multivariate 0 v1_in_prim) in
    let v2_term = QQXs.sub (make_multivariate 2 (QQX.identity)) (make_multivariate 0 v2_in_prim) in
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
                if var = 2 then PNF.mul (PNF.exp PNF.identity deg) var_part, coef_part
                else var_part, QQX.mul (QQX.exp QQX.identity deg) coef_part
                ) (PNF.one, QQX.one) (Monomial.enum m) in
          let coe = make_multivariate 0 (QQX.scalar_mul coef coef_part) in
          PNF.add (PNF.scalar_mul coe var_part) acc
      ) poly PNF.zero, deg
    in
    (lc, List.map find_factor factors)
end






open BatPervasives

include Log.Make(struct let name = "ark.polynomial" end)

module type Ring = Linear.Ring

module type Univariate = sig
  include Linear.Vector with type dim = int
  val order : t -> int
  val mul : t -> t -> t
  val one : t
  val scalar : scalar -> t
  val compose : t -> t -> t
  val identity : t
  val eval : t -> scalar -> scalar
  val exp : t -> int -> t
end

module Int = struct
  type t = int [@@deriving show,ord]
  let tag k = k
end

module Uvp(R : Ring) = struct
  module IntMap = ArkUtil.Int.Map

  include Linear.RingMap(IntMap)(R)

  let order p = IntMap.fold (fun power _ hi -> max hi power) p 0

  let scalar k = of_term k 0

  let one = scalar R.one

  let identity = of_term R.one 1

  let monomial_mul coeff power p =
    (IntMap.enum p)
    /@ (fun (power',coeff') -> (power * power', R.mul coeff coeff'))
    |> IntMap.of_enum

  let mul p q =
    BatEnum.fold
      (fun r ((pp,pc), (qp,qc)) -> add_term (R.mul pc qc) (pp + qp) r)
      zero
      (ArkUtil.cartesian_product (IntMap.enum p) (IntMap.enum q))

  let exp = ArkUtil.exp mul one

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
    ArkUtil.pp_print_enum
      ~pp_sep:(fun formatter () -> Format.fprintf formatter "@ + ")
      pp_monomial
      formatter
      (IntMap.enum p)

  let show = ArkUtil.mk_show pp

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

module Monomial = struct
  module IntMap = BatMap.Make(Int)

  type dim = int
  type t = dim IntMap.t

  let pp pp_dim formatter monomial =
    if IntMap.is_empty monomial then
      Format.pp_print_string formatter "1"
    else
      ArkUtil.pp_print_enum_nobox
        ~pp_sep:(fun formatter () -> Format.fprintf formatter "*")
        (fun formatter (dim, power) ->
           if power = 1 then
             pp_dim formatter dim
           else
             Format.fprintf formatter "%a^%d"
               pp_dim dim
               power)
        formatter
        (IntMap.enum monomial)

  let one = IntMap.empty

  let mul =
    let f _ a b =
      match a, b with
      | Some a, Some b ->
        if a + b = 0 then None else Some (a + b)
      | Some x, None | None, Some x -> Some x
      | None, None -> assert false
    in
    IntMap.merge f

  let mul_term dim power monomial =
    if power = 0 then monomial else begin
      try
        let power' = power + (IntMap.find dim monomial) in
        if power' = 0 then
          IntMap.remove dim monomial
        else
          IntMap.add dim power' monomial
      with Not_found -> IntMap.add dim power monomial
    end

  let power dim monomial = try IntMap.find dim monomial with Not_found -> 0

  let enum = IntMap.enum

  let of_enum = BatEnum.fold (fun monomial (x,y) -> mul_term x y monomial) one

  let equal = IntMap.equal (=)

  let compare = IntMap.compare Pervasives.compare

  let singleton dim power = mul_term dim power one

  let pivot dim monomial =
    (power dim monomial, IntMap.remove dim monomial)

  exception Undefined
  let div m n =
    try
      Some (IntMap.fold
              (fun dim n_power m ->
                 let m_power = power dim m in
                 if n_power > m_power then
                   raise Undefined
                 else if n_power = m_power then
                   IntMap.remove dim m
                 else
                   IntMap.add dim (m_power - n_power) m)
              n
              m)
    with Undefined -> None

  let lcm =
    let f _ a b =
      match a, b with
      | Some a, Some b -> Some (max a b)
      | Some x, None | None, Some x -> Some x
      | None, None -> assert false
    in
    IntMap.merge f

  let gcd =
    let f _ a b =
      match a, b with
      | Some a, Some b -> Some (min a b)
      | Some x, None | None, Some x -> None
      | None, None -> assert false
    in
    IntMap.merge f

  let total_degree m =
    IntMap.fold (fun _ degree total -> degree + total) m 0

  let graded partial total m n =
    match partial m n with
    | `Gt -> `Gt
    | `Lt -> `Lt
    | `Pass -> total m n

  let compare_degree m n =
    let deg_diff = (total_degree m) - (total_degree n) in
    if deg_diff = 0 then `Pass
    else if deg_diff > 0 then `Gt
    else `Lt

  let lex m n =
    let mlist = BatList.of_enum (enum m) in
    let nlist = BatList.of_enum (enum n) in
    let rec go m n =
      match m, n with
      | ([], []) -> `Eq
      | ([], n) -> `Lt
      | (m, []) -> `Gt
      | ((x, a)::m', (y, b)::n') ->
        if x = y then
          if a = b then go m' n'
          else if a < b then `Lt
          else `Gt
        else if x < y then `Gt
        else `Lt
    in
    go mlist nlist

  let deglex = graded compare_degree lex
  let degrevlex =
    let revlex m n = match lex m n with
      | `Eq -> `Eq
      | `Lt -> `Gt
      | `Gt -> `Lt
    in
    graded compare_degree revlex

  let split_block p m =
    IntMap.fold (fun dim pow (t,f) ->
        if p dim then
          (IntMap.add dim pow t, f)
        else
          (t, IntMap.add dim pow f))
      m
      (IntMap.empty, IntMap.empty)

  let block blocks compare_block =
    let rec compare blocks m n =
      match blocks with
      | [] -> compare_block m n
      | (block::blocks) ->
        let (m1,m2) = split_block block m in
        let (n1,n2) = split_block block n in
        match compare_block m1 n1 with
        | `Eq -> compare blocks m2 n2
        | cmp -> cmp
    in
    compare blocks

  let term_of ark dim_term m =
    IntMap.fold (fun dim pow product ->
        (Syntax.mk_pow ark (dim_term dim) pow)::product)
      m
      []
    |> Syntax.mk_mul ark
end

module Mvp = struct
  module MM = BatMap.Make(Monomial)
  include Linear.RingMap(MM)(QQ)

  let pp pp_dim formatter p =
    if MM.is_empty p then
      Format.pp_print_string formatter "0"
    else
      ArkUtil.pp_print_enum_nobox
        ~pp_sep:(fun formatter () -> Format.fprintf formatter "@ + ")
        (fun formatter (coeff, m) ->
           if QQ.equal coeff QQ.one then
             Format.fprintf formatter "@[%a@]" (Monomial.pp pp_dim) m
           else if QQ.lt coeff QQ.zero then
             Format.fprintf formatter "@[(%a)*%a@]"
               QQ.pp coeff
               (Monomial.pp pp_dim) m
         else
           Format.fprintf formatter "@[%a*%a@]" QQ.pp coeff (Monomial.pp pp_dim) m)
        formatter
        (enum p)

  let monomial_scalar_mul coeff monomial p =
    if QQ.equal coeff QQ.zero then
      zero
    else
      (MM.enum p)
      /@ (fun (monomial', coeff') ->
          (Monomial.mul monomial monomial', QQ.mul coeff coeff'))
      |> MM.of_enum

  let monomial_mul = monomial_scalar_mul QQ.one

  let mul p q =
    BatEnum.fold
      (fun r (monomial, coeff) ->
         add r (monomial_scalar_mul coeff monomial q))
      zero
      (MM.enum p)

  let sub p q = add p (scalar_mul (QQ.of_int (-1)) q)

  let scalar k = of_term k Monomial.one

  let one = of_term QQ.one Monomial.one

  let of_dim dim =
    of_term QQ.one (Monomial.singleton dim 1)

  module V = Linear.QQVector
  let of_vec ?(const=Linear.const_dim) vec =
    let (const_coeff, vec) = V.pivot const vec in
    V.enum vec
    /@ (fun (coeff, id) -> scalar_mul coeff (of_dim id))
    |> BatEnum.fold add (scalar const_coeff)

  let split_linear ?(const=Linear.const_dim) p =
    MM.fold (fun monomial coeff (vec, poly) ->
        match BatList.of_enum (Monomial.enum monomial) with
        | [] -> (V.add_term coeff const vec, poly)
        | [(x,1)] -> (V.add_term coeff x vec, poly)
        | _ -> (vec, add_term coeff monomial poly))
      p
      (V.zero, zero)

  let vec_of ?(const=Linear.const_dim) p =
    let (vec, q) = split_linear ~const p in
    if equal q zero then
      Some vec
    else
      None

  let term_of ark dim_term p =
    MM.fold (fun monomial coeff sum ->
        (Syntax.mk_mul ark [Syntax.mk_real ark coeff;
                            Monomial.term_of ark dim_term monomial])::sum)
      p
      []
    |> Syntax.mk_add ark

  let compare = MM.compare QQ.compare

  let exp = ArkUtil.exp mul one

  let substitute subst p =
    MM.fold (fun monomial coeff p ->
        let q =
          Monomial.IntMap.fold (fun dim pow q ->
              mul q (exp (subst dim) pow))
            monomial
            one
        in
        add p (scalar_mul coeff q))
      p
      zero

  let div_monomial p m =
    MM.fold (fun n coeff p ->
        match p with
        | Some p ->
          begin match Monomial.div n m with
            | Some q -> Some (add_term coeff q p)
            | None -> None
          end
        | None -> None)
      p
      (Some zero)

  let dimensions p =
    let module S = ArkUtil.Int.Set in
    MM.fold (fun m _ set ->
        Monomial.IntMap.fold (fun dim _ set -> S.add dim set) m set)
      p
      S.empty
    |> S.enum
end

module Rewrite = struct
  (* An ordered polynomial (coefficient, monomial) pairs such that the
     monomials *descend* in some admissible order. *)
  type op = (QQ.t * Monomial.t) list

  module P = BatSet.Make(Mvp)

  type t =
    { rules : (Monomial.t * op * P.t) list;
      order : Monomial.t -> Monomial.t -> [ `Eq | `Lt | `Gt ] }

  let pp_op pp_dim formatter op =
    match op with
    | [] -> Format.pp_print_string formatter "0"
    | _ ->
    ArkUtil.pp_print_enum_nobox
      ~pp_sep:(fun formatter () -> Format.fprintf formatter "@ + ")
      (fun formatter (coeff, monomial) ->
         if QQ.equal coeff QQ.one then
           Format.fprintf formatter "(%a)"
             (Monomial.pp pp_dim) monomial
         else
           Format.fprintf formatter "%a*(%a)"
             QQ.pp coeff
             (Monomial.pp pp_dim) monomial)
      formatter
      (BatList.enum op)

  let pp pp_dim formatter rewrite =
    ArkUtil.pp_print_enum_nobox
      ~pp_sep:(fun formatter () -> Format.fprintf formatter "@;")
      (fun formatter (lhs, rhs, _) ->
         Format.fprintf formatter "%a --> @[<hov 2>%a@]"
           (Monomial.pp pp_dim) lhs
           (pp_op pp_dim) rhs)
      formatter
      (BatList.enum rewrite.rules)

  let rec op_add order p q =
    match p, q with
    | ([], q) -> q
    | (p, []) -> p
    | ((a, m)::p', (b, n)::q') ->
      match order m n with
      | `Eq ->
        let c = QQ.add a b in
        let rest = op_add order p' q' in
        if QQ.equal c QQ.zero then rest
        else (c, m)::rest
      | `Gt -> (a,m)::(op_add order p' q)
      | `Lt -> (b,n)::(op_add order p q')

  let op_monomial_scalar_mul coeff monomial =
    List.map
      (fun (coeff', monomial') ->
        (QQ.mul coeff coeff', Monomial.mul monomial monomial'))

  let op_of_mvp order p =
    Mvp.enum p
    |> BatList.of_enum
    |> BatList.sort (fun (_, m) (_, n) -> match order m n with
        | `Eq -> 0
        | `Lt -> 1
        | `Gt -> -1)

  let mvp_of_op p =
    List.fold_left (fun q (c, m) -> Mvp.MM.add m c q) Mvp.zero p

  let rec reduce_op rewrite polynomial =
    match polynomial with
    | [] -> ([], P.empty)
    | (c, m)::polynomial' ->
      try
        let (reduced, provenance) =
          BatList.find_map (fun (n, p, provenance) ->
              match Monomial.div m n with
              | Some remainder ->
                Some (op_monomial_scalar_mul c remainder p, provenance)
              | None -> None)
            rewrite.rules
        in
        let (reduced', provenance') =
          reduce_op rewrite (op_add rewrite.order reduced polynomial')
        in
        (reduced', P.union provenance provenance')
      with Not_found ->
        let (reduced, provenance) = reduce_op rewrite polynomial' in
        (op_add rewrite.order [(c, m)] reduced, provenance)

  let preduce rewrite polynomial =
    let (reduced, provenance) =
      reduce_op rewrite (op_of_mvp rewrite.order polynomial)
    in
    (mvp_of_op reduced, P.elements provenance)

  let reduce rewrite polynomial =
    let (reduced, _) =
      reduce_op rewrite (op_of_mvp rewrite.order polynomial)
    in
    mvp_of_op reduced

  let mk_rewrite order polynomials =
    let rules =
      List.fold_left (fun rules polynomial ->
          let (op, provenance) =
            op_of_mvp order polynomial
            |> reduce_op { rules; order }
          in
          match op with
          | [] -> rules (* reduced to 0 *)
          | (c, m)::rest ->
            assert (not (QQ.equal c QQ.zero));
            let rhs =
              op_monomial_scalar_mul (QQ.negate (QQ.inverse c)) Monomial.one rest
            in
            let new_rule = (m, rhs, P.add polynomial provenance) in
            let rules =
              let rewrite = { rules = [new_rule]; order = order } in
              List.map (fun (n, p, provenance) ->
                  let (p',provenance') = reduce_op rewrite p in
                  (n, p', P.union provenance provenance')) rules
            in
            new_rule::rules)
        []
        polynomials
    in
    { rules; order }

  let insert_rule order rule rules =
    let rec insert (m,rhs,provenance) rules =
      match rules with
      | [] -> [(m,rhs,provenance)]
      | (m',rhs',provenance')::rules' ->
        if Monomial.total_degree m <= Monomial.total_degree m' then
          (m,rhs,provenance)::rules
        else
          (m',rhs',provenance')::(insert (m,rhs,provenance) rules')
    in
    let reduce_rule (m, rhs, provenance) =
      let reduced =
        reduce_op {order = order; rules = [rule] } ((QQ.negate QQ.one, m)::rhs)
      in
      match reduced with
      | ([], _) -> None
      | ([(c,m)], provenance') when Monomial.equal m Monomial.one ->
        (* Inconsistent -- return (1 = 0) *)
        assert (not (QQ.equal c QQ.zero));
        Some (Monomial.one, [], P.union provenance provenance')
      | ((c,m)::rest, provenance') ->
        assert (not (QQ.equal c QQ.zero));
        let rhs =
          op_monomial_scalar_mul (QQ.negate (QQ.inverse c)) Monomial.one rest
        in
        Some (m, rhs, P.union provenance provenance')
    in
    insert rule (BatList.filter_map reduce_rule rules)

  let buchberger order rules pairs =
    (* Suppose m1 = rhs1 and m2 = rhs1.  Let m be the least common multiple of
       m1 and m2, and let m1*r1 = m = m2*r2.  Then we have m = rhs1*r1 and m =
       rhs2*r1.  It follows that rhs1*r1 - rhs2*r2 = 0.  spoly computes this
       polynomial. *)
    let spoly (m1, rhs1, provenance1) (m2, rhs2, provenance2) =
      let m = Monomial.lcm m1 m2 in
      let r1 = BatOption.get (Monomial.div m m1) in
      let r2 = BatOption.get (Monomial.div m m2) in
      (op_add
         order
         (op_monomial_scalar_mul QQ.one r1 rhs1)
         (op_monomial_scalar_mul (QQ.of_int (-1)) r2 rhs2),
       P.union provenance1 provenance2)
    in
    let pp_dim formatter i =
      Format.pp_print_string formatter (Char.escaped (Char.chr (65 + i)))
    in
    let lhs (x, _, _) = x in
    let rhs (_, x, _) = x in
    let rec go rules pairs =
      match pairs with
      | [] -> rules
      | (r1, r2)::pairs ->
        logf ~level:`trace  "Pair:";
        logf ~level:`trace  "  @[%a@] --> @[<hov 2>%a@]"
          (Monomial.pp pp_dim) (lhs r1)
          (pp_op pp_dim) (rhs r1);
        logf ~level:`trace  "  @[%a@] --> @[<hov 2>%a@]"
          (Monomial.pp pp_dim) (lhs r2)
          (pp_op pp_dim) (rhs r2);
        let (sp, provenance) = spoly r1 r2 in
        match reduce_op { order = order; rules = rules } sp with
        | ([], _) -> go rules pairs
        | ([(c,m)], provenance') when Monomial.equal m Monomial.one ->
          (* Inconsistent -- return (1 = 0) *)
          assert (not (QQ.equal c QQ.zero));
          [(Monomial.one, [], P.union provenance provenance')]
        | ((c,m)::rest, provenance') ->
          assert (not (QQ.equal c QQ.zero));
          let rhs =
            op_monomial_scalar_mul (QQ.negate (QQ.inverse c)) Monomial.one rest
          in
          logf ~level:`trace "Result:";
          logf ~level:`trace "  @[%a@] --> @[<hov 2>%a@]"
            (Monomial.pp pp_dim) m
            (pp_op pp_dim) rhs;
          let new_rule = (m,rhs,P.union provenance provenance') in
          let new_pairs =
            BatList.filter_map (fun (m',rhs',provenance') ->
                if Monomial.equal (Monomial.gcd m m') Monomial.one then
                  None
                else
                  Some (new_rule, (m',rhs',provenance')))
              rules
          in
          go
            (insert_rule order new_rule rules)
            (pairs@new_pairs)
    in
    go rules pairs

  let buchberger order rules pairs =
    Log.time "buchberger" (buchberger order rules) pairs

  let add_saturate_op rewrite op provenance =
    match reduce_op rewrite op with
    | ([], _) -> rewrite
    | ([(c,m)], provenance') when Monomial.equal m Monomial.one ->
      (* Inconsistent -- return (1 = 0) *)
      assert (not (QQ.equal c QQ.zero));
      { order = rewrite.order;
        rules = [(Monomial.one, [], P.union provenance provenance')] }
    | ((c,m)::rest, provenance') ->
      assert (not (QQ.equal c QQ.zero));
      let rhs =
        op_monomial_scalar_mul (QQ.negate (QQ.inverse c)) Monomial.one rest
      in
      let new_rule = (m, rhs, P.union provenance provenance') in
      let pairs = List.map (fun r -> (new_rule, r)) rewrite.rules in
      { order = rewrite.order;
        rules = buchberger rewrite.order (new_rule::rewrite.rules) pairs }

  let add_saturate rewrite p =
    add_saturate_op rewrite (op_of_mvp rewrite.order p) (P.singleton p)

  let grobner_basis rewrite =
    List.fold_left (fun rewrite (m,rhs,provenance) ->
        add_saturate_op rewrite ((QQ.negate QQ.one, m)::rhs) provenance)
      { order = rewrite.order; rules = [] }
      rewrite.rules

  let generators rewrite =
    List.map
      (fun (lt, op, _) -> mvp_of_op ((QQ.of_int (-1), lt)::op))
      rewrite.rules
end

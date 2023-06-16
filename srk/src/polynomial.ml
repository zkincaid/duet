open BatPervasives

include Log.Make(struct let name = "srk.polynomial" end)

let pp_ascii_dim formatter i =
  let rec to_string i =
    if i < 26 then
      Char.escaped (Char.chr (97 + i))
    else
      (to_string (i/26)) ^ (Char.escaped (Char.chr (97 + (i mod 26))))
  in
  Format.pp_print_string formatter (to_string i)

let pp_numeric_dim base formatter i =
  Format.fprintf formatter "%s_{%d}" base i

module type Univariate = sig
  include Ring.Vector with type dim = int
  val order : t -> int
  val mul : t -> t -> t
  val one : t
  val scalar : scalar -> t
  val compose : t -> t -> t
  val identity : t
  val eval : t -> scalar -> scalar
  val exp : t -> int -> t
  val mul_monomial : scalar -> int -> t -> t
end

module MakeUnivariate(R : Algebra.Ring) = struct
  include Ring.RingMap(SrkUtil.Int)(R)

  let order p = fold (fun power _ hi -> max hi power) p 0

  let scalar k = of_term k 0

  let one = scalar R.one

  let identity = of_term R.one 1

  let mul_monomial coeff power p =
    (enum p)
    /@ (fun (coeff',power') -> (R.mul coeff coeff', power * power'))
    |> of_enum

  let mul p q =
    BatEnum.fold
      (fun r ((pc,pp), (qc,qp)) -> add_term (R.mul pc qc) (pp + qp) r)
      zero
      (SrkUtil.cartesian_product (enum p) (enum q))

  let exp = SrkUtil.exp mul one

  let compose p q =
    let rec go n = function
      | [] -> zero
      | (coeff,k)::xs ->
        let multiplier = exp q (k-n) in
        mul multiplier (add_term coeff 0 (go k xs))
    in
    enum p
    |> BatList.of_enum
    |> BatList.sort (fun x y -> Stdlib.compare (snd x) (snd y))
    |> go 0

  let scalar k = add_term k 0 zero

  let eval p k = fst (pivot 0 (compose p (scalar k)))
end

module type Euclidean = sig
  include Univariate

  val qr : t -> t -> t * t

  val ex_euc : t -> t -> t * t * t

  val square_free_factor : t -> (t * int) list
end

module MakeEuclidean (
  F : sig
    include Algebra.Field
    val int_mul : int -> t -> t (*Mathematically this isn't needed ix = x + x + ... + x. But there could be faster implementations.*)
  end) = struct
  include MakeUnivariate(F)

  let qr a b = 
    if is_zero b then failwith "Divide by 0";
    let d = order b in
    let c = coeff d b in
    if d = 0 then 
      (scalar_mul (F.inverse c) a, zero)
    else
      let rec aux q r =
        let rd = order r in
        if rd = 0 || rd < d then (q, r)
        else
          let s = (of_term (F.mul (coeff rd r) (F.inverse c)) (rd - d)) in
          aux (add q s) (sub r (mul s b))
        in
      aux zero a
  
  let ex_euc a b = 
    let rec aux r0 r1 s0 s1 t0 t1 = 
      if is_zero r1 then 
        let lcri = F.inverse (coeff (order r0) r0) in
        (scalar_mul lcri r0, scalar_mul lcri s0, scalar_mul lcri t0)
      else
        let q = fst (qr r0 r1) in
        aux r1 (sub r0 (mul q r1)) s1 (sub s0 (mul q s1)) t1 (sub t0 (mul q t1))
    in
    aux a b one zero zero one
  
  let derivative f = 
    of_list (fold (
      fun deg coef acc ->
        if deg = 0 then (F.zero, 0) :: acc
        else
         (F.int_mul deg coef, deg - 1) :: acc
    ) f [])

  let square_free_factor p = 
    let rec aux b d i facts = 
      if equal b one then
        facts
      else
        let a, _, _ = ex_euc b d in
        let new_b = fst (qr b a) in
        let c = fst (qr d a) in
        let new_d = sub c (derivative new_b) in
        if equal a one then 
          aux new_b new_d (i+1) facts
        else
          aux new_b new_d (i+1) ((a, i) :: facts)
      in
    let p_p = derivative p in
    let a_0, _, _ = ex_euc p p_p in
    let b_1 = fst (qr p a_0) in
    let c_1 = fst (qr p_p a_0) in
    let d_1 = sub c_1 (derivative b_1) in
    aux b_1 d_1 1 []
end


module QQX = struct
  include MakeEuclidean(struct include QQ let int_mul i x = QQ.mul (QQ.of_int i) x end)

  let pp formatter p =
    let pp_monomial formatter (coeff, order) =
      if order = 0 then
        QQ.pp formatter coeff
      else if QQ.equal coeff QQ.one then
        Format.fprintf formatter "@[x^%d@]" order
      else if QQ.equal coeff (QQ.negate QQ.one) then
        Format.fprintf formatter "@[-x^%d@]" order
      else
        Format.fprintf formatter "@[%a*x^%d@]" QQ.pp coeff order
    in
    SrkUtil.pp_print_enum
      ~pp_sep:(fun formatter () -> Format.fprintf formatter "@ + ")
      pp_monomial
      formatter
      (enum p)

  let show = SrkUtil.mk_show pp

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

  let factor p =
    let denominator =
      BatEnum.fold (fun d (coeff, _) ->
          ZZ.lcm d (QQ.denominator coeff))
        ZZ.one
        (enum p)
    in
    let zzx =
      (enum p) /@ (fun (coeff, d) ->
          let (num, den) = QQ.to_zzfrac coeff in
          (d, Ntl.ZZ.of_mpz (ZZ.mpz_of (ZZ.div (ZZ.mul num denominator) den))))
      |> BatList.of_enum
      |> Ntl.ZZX.of_list
    in
    let (c, factors) = Ntl.ZZX.factor zzx in
    let content = QQ.of_zzfrac (ZZ.of_mpz (Ntl.ZZ.mpz_of c)) denominator in
    let factors =
      List.map (fun (zzx, n) ->
          let qqx =
            BatList.enum (Ntl.ZZX.list_of zzx)
            /@ (fun (degree, coeff) ->
                (QQ.of_zz (ZZ.of_mpz (Ntl.ZZ.mpz_of coeff)), degree))
            |> of_enum
          in
          (qqx, n))
        factors
    in
    (content, factors)

  let content p =
    fold (fun _ coeff content ->
        QQ.gcd coeff content)
      p
      QQ.zero

  let choose k =
    assert (k >= 0);
    let rec go i next p =
      if i = k then
        p
      else
        let next' =
          add_term (QQ.of_int (-1)) 0 next
        in
        go (i + 1) next' (mul next p)
    in
    let rec factorial = function
      | 0 -> 1
      | k -> k*(factorial (k-1))
    in
    scalar_mul (QQ.of_frac 1 (factorial k)) (go 0 identity one)

  let term_of srk term p =
    fold (fun pow coeff product ->
        let term =
          Syntax.mk_mul srk [Syntax.mk_real srk coeff; Syntax.mk_pow srk term pow]
        in
        term::product)
      p
      []
    |> Syntax.mk_add srk


end

module Monomial = struct
  module IntMap = SrkUtil.Int.Map

  type dim = int
  type t = int IntMap.t

  let pp pp_dim formatter monomial =
    if IntMap.is_empty monomial then
      Format.pp_print_string formatter "1"
    else
      SrkUtil.pp_print_enum_nobox
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

  let compare = IntMap.compare Stdlib.compare

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
      | Some _, None | None, Some _ -> None
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
      | ([], _) -> `Lt
      | (_, []) -> `Gt
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

  let term_of srk dim_term m =
    IntMap.fold (fun dim pow product ->
        (Syntax.mk_pow srk (dim_term dim) pow)::product)
      m
      []
    |> Syntax.mk_mul srk

  let destruct_var monomial =
    let e = enum monomial in
    match BatEnum.get e with
    | Some (v, 1) ->
      if BatEnum.is_empty e then
        Some v
      else
        None
    | _ -> None
end

module type Multivariate = sig
  type t
  type scalar
  type dim = Monomial.t
  val equal : t -> t -> bool
  val add : t -> t -> t
  val negate : t -> t
  val mul : t -> t -> t
  val zero : t
  val one : t
  val is_zero : t -> bool
  val sub : t -> t -> t
  val pp : (Format.formatter -> scalar -> unit) ->
           (Format.formatter -> int -> unit) ->
           Format.formatter ->
           t ->
           unit
  val add_term : scalar -> Monomial.t -> t -> t
  val scalar : scalar -> t
  val of_dim : int -> t
  val scalar_mul : scalar -> t -> t
  val coeff : Monomial.t -> t -> scalar
  val pivot : Monomial.t -> t -> scalar * t
  val enum : t -> (scalar * Monomial.t) BatEnum.t
  val of_enum : (scalar * Monomial.t) BatEnum.t -> t
  val of_list : (scalar * Monomial.t) list -> t
  val exp : t -> int -> t
  val substitute : (int -> t) -> t -> t
  val mul_monomial : Monomial.t -> t -> t
  val div_monomial : t -> Monomial.t -> t option
  val qr_monomial : t -> Monomial.t -> t * t
  val dimensions : t -> SrkUtil.Int.Set.t
  val degree : t -> int
  val fold : (dim -> scalar -> 'a -> 'a) -> t -> 'a -> 'a
end

module MakeMultivariate(R : Algebra.Ring) = struct
  include Ring.RingMap(Monomial)(R)

  let pp pp_scalar pp_dim formatter p =
    if is_zero p then
      Format.pp_print_string formatter "0"
    else
      SrkUtil.pp_print_enum_nobox
        ~pp_sep:(fun formatter () -> Format.fprintf formatter "@ + ")
        (fun formatter (coeff, m) ->
           if R.equal coeff R.one then
             Format.fprintf formatter "@[%a@]" (Monomial.pp pp_dim) m
           else
             Format.fprintf formatter "@[%a*%a@]" pp_scalar coeff (Monomial.pp pp_dim) m)
        formatter
        (enum p)

  let mul_monomial_scalar coeff monomial p =
    if R.equal coeff R.zero then
      zero
    else
      (enum p)
      /@ (fun (coeff', monomial') ->
          (R.mul coeff coeff', Monomial.mul monomial monomial'))
      |> of_enum

  let mul_monomial = mul_monomial_scalar R.one

  let mul p q =
    BatEnum.fold
      (fun r (coeff, monomial) ->
         add r (mul_monomial_scalar coeff monomial q))
      zero
      (enum p)

  let sub p q = add p (scalar_mul (R.negate R.one) q)

  let scalar k = of_term k Monomial.one

  let one = of_term R.one Monomial.one

  let of_dim dim =
    of_term R.one (Monomial.singleton dim 1)

  let exp = SrkUtil.exp mul one

  let substitute subst p =
    fold (fun monomial coeff p ->
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
    fold (fun n coeff p ->
        match p with
        | Some p ->
          begin match Monomial.div n m with
            | Some q -> Some (add_term coeff q p)
            | None -> None
          end
        | None -> None)
      p
      (Some zero)

  let qr_monomial p m =
    fold (fun n coeff (q, r) ->
        match Monomial.div n m with
        | Some qn -> (add_term coeff qn q, r)
        | None -> (q, add_term coeff n r))
      p
      (zero, zero)

  let dimensions p =
    let module S = SrkUtil.Int.Set in
    fold (fun m _ set ->
        Monomial.IntMap.fold (fun dim _ set -> S.add dim set) m set)
      p
      S.empty

  let degree p =
    fold (fun m _ d -> max (Monomial.total_degree m) d) p 0
end

module QQXs = struct
  include MakeMultivariate(QQ)
  module V = Linear.QQVector
  module IntSet = SrkUtil.Int.Set

  let pp pp_dim formatter p =
    if is_zero p then
      Format.pp_print_string formatter "0"
    else
      SrkUtil.pp_print_enum
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

  let of_vec ?(const=Linear.const_dim) vec =
    let (const_coeff, vec) = V.pivot const vec in
    V.enum vec
    /@ (fun (coeff, id) -> scalar_mul coeff (of_dim id))
    |> BatEnum.fold add (scalar const_coeff)

  let split_linear ?(const=Linear.const_dim) p =
    fold (fun monomial coeff (vec, poly) ->
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

  let term_of srk dim_term p =
    fold (fun monomial coeff sum ->
        (Syntax.mk_mul srk [Syntax.mk_real srk coeff;
                            Monomial.term_of srk dim_term monomial])::sum)
      p
      []
    |> Syntax.mk_add srk

  let of_term srk term =
    let qq_of poly =
      if (degree poly) > 0 then failwith "Cannot convert non-const term to qq (cannot handle modulo involving variables)"
      else coeff Monomial.one poly
    in
    let nonzero_qq_of poly =
      let qq = qq_of poly in
      if QQ.equal qq QQ.zero then failwith "Cannot divide or modulo zero" else qq
    in
    let alg = function
      | `Real qq -> scalar qq
      | `App (k, []) -> of_dim (Syntax.int_of_symbol k)
      | `Var (_, _) | `App (_, _) -> failwith "Cannot convert functions term to polynomials"
      | `Add sum -> BatList.fold_left add zero sum
      | `Mul prod -> BatList.fold_left mul one prod
      | `Binop (`Div, x, y) -> scalar_mul (QQ.inverse (nonzero_qq_of y)) x
      | `Binop (`Mod, x, y) -> scalar (QQ.modulo (qq_of x) (nonzero_qq_of y))
      | `Unop (`Floor, x) -> scalar (QQ.of_zz (QQ.floor (qq_of x)))
      | `Unop (`Neg, x) -> negate x
      | `Select _ -> assert false
      | `Ite (_, _, _) -> failwith "Cannot convert ite term to polynomials"
    in
    Syntax.ArithTerm.eval srk alg term

  let compare = compare QQ.compare

  let content p =
    fold (fun _ coeff content ->
        QQ.gcd coeff content)
      p
      QQ.zero

  let factor_gcd p =
    if is_zero p then
      (QQ.one, Monomial.one, p)
    else
      let ((m, c), p') = pop p in
      let (c, m) =
        fold (fun monomial coeff (c, m) ->
            (QQ.gcd coeff c, Monomial.gcd m monomial))
          p'
          (c, m)
      in
      let q =
        fold (fun n coeff q ->
            match Monomial.div n m with
            | Some r -> add_term (QQ.div coeff c) r q
            | None -> assert false)
          p
          zero
      in
      (c, m, q)

  let split_leading ord p =
    let leading_monomial =
      fold (fun n _ m ->
          if ord n m = `Gt then n
          else m)
        p
        Monomial.one
    in
    let (coeff, rest) = pivot leading_monomial p in
    (coeff, leading_monomial, rest)
end

module LinearQQXs = struct
  include Linear.MakeDenseConversion(Monomial)(struct
      include QQXs
      let split_leading p =
        match BatEnum.get (enum p) with
        | None -> None
        | Some (_, m) ->
          let (a, p') = pivot m p in
          Some (m, a, p')
      let pp = QQXs.pp (pp_numeric_dim "x")
    end)
  let densify_affine ctx p =
    let (a, p) = QQXs.pivot Monomial.one p in
    Linear.QQVector.set Linear.const_dim a (densify ctx p)
  let sparsify_affine ctx v =
    let (a, v) = Linear.QQVector.pivot Linear.const_dim v in
    QQXs.set Monomial.one a (sparsify ctx v)
end

module OrderedPolynomial = struct
  type t = (QQ.t * Monomial.t) list [@@deriving ord]
  let pp pp_dim formatter op =
    match op with
    | [] -> Format.pp_print_string formatter "0"
    | _ ->
    SrkUtil.pp_print_enum_nobox
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

  let rec add order p q =
    match p, q with
    | ([], q) -> q
    | (p, []) -> p
    | ((a, m)::p', (b, n)::q') ->
      match order m n with
      | `Eq ->
        let c = QQ.add a b in
        let rest = add order p' q' in
        if QQ.equal c QQ.zero then rest
        else (c, m)::rest
      | `Gt -> (a,m)::(add order p' q)
      | `Lt -> (b,n)::(add order p q')

  let monomial_scalar_mul coeff monomial =
    List.map
      (fun (coeff', monomial') ->
         (QQ.mul coeff coeff', Monomial.mul monomial monomial'))

  let of_qqxs order p =
    QQXs.enum p
    |> BatList.of_enum
    |> BatList.sort (fun (_, m) (_, n) -> match order m n with
        | `Eq -> 0
        | `Lt -> 1
        | `Gt -> -1)

  let qqxs_of p =
    List.fold_left (fun q (c, m) -> QQXs.add_term c m q) QQXs.zero p

  let fold f acc xs =
    List.fold_left (fun acc (c, m) -> f acc c m) acc xs

  let split_leading _ = function
    | [] -> None
    | (c, m)::xs -> Some (c, m, xs)

  let add_term order c m p = add order [(c,m)] p

  let zero = []
  let is_zero = function
    | [] -> true
    | _ -> false
end

module MakeRewrite
    (K : Algebra.Field)
    (P : sig
       type t
       type scalar = K.t
       val zero : t
       val compare : t -> t -> int
       val fold : ('a -> scalar -> Monomial.t -> 'a) -> 'a -> t -> 'a
       val add : (Monomial.t -> Monomial.t -> [`Eq | `Lt | `Gt]) -> t -> t -> t
       val add_term : (Monomial.t -> Monomial.t -> [`Eq | `Lt | `Gt]) -> scalar -> Monomial.t -> t -> t
       val monomial_scalar_mul : scalar -> Monomial.t -> t -> t
       val split_leading : (Monomial.t -> Monomial.t -> [`Eq | `Lt | `Gt]) -> t -> (scalar * Monomial.t * t) option
       val pp : (Format.formatter -> int -> unit) -> Format.formatter -> t -> unit
     end) = struct

  type rule = Monomial.t * P.t [@@deriving ord]

  (* Priority queue of pairs of polynomials, ordered by total degree of the
     LCM of their leading monomials *)
  module PairQueue = struct
    type pair = int * rule * rule [@@deriving ord]

    module H = BatHeap.Make(struct
        type t = pair [@@deriving ord]
      end)
    let insert queue (x, y) =
      let (m, _) = x in
      let (m', _) = y in
      let deg = Monomial.total_degree (Monomial.lcm m m') in
      if compare_rule x y < 0 then
        H.insert queue (deg, x, y)
      else
        H.insert queue (deg, y, x)
    let pop queue =
      if queue = H.empty then
        None
      else
        let (_, x, y) = H.find_min queue in
        Some ((x, y), H.del_min queue)
    let empty = H.empty

    let mem queue (x, y) =
      let (m, _) = x in
      let (m', _) = y in
      let deg = Monomial.total_degree (Monomial.lcm m m') in
      let elt =
        if compare_rule x y < 0 then
          (deg, x, y)
        else
          (deg, y, x)
      in
      BatEnum.exists ((=) 0 % compare_pair elt) (H.enum queue)
  end

  module IntSet = SrkUtil.Int.Set

  (* Rule set *)
  module RS = struct
    type t = rule FeatureTree.t
    let enum = FeatureTree.enum
    let features ft m = FeatureTree.features ft (m, P.zero)
    let find_leq_map = FeatureTree.find_leq_map
    let insert = FeatureTree.insert
    let remove = FeatureTree.remove (fun x y -> compare_rule x y = 0)
    let of_list rules =
      let () = Random.init 63864283 in
      let nb_dimensions =
        let max_dim m =
          Monomial.IntMap.fold (fun d _ m -> max d m) m 0
        in
        List.fold_left (fun nb_dimensions (n,p) ->
            P.fold
              (fun x _ y -> max x (max_dim y))
              (max nb_dimensions (max_dim n))
              p)
          0
          rules
      in
      let rec log2 n =
        if n == 1 then
          0
        else
          log2 (n / 2) + 1
      in
      let nb_features = (log2 (8 + nb_dimensions)) in
      let feature_sets =
        Array.init nb_features (fun _ ->
            BatEnum.fold (fun set d ->
                if Random.bool () then
                  IntSet.add d set
                else
                  set)
              IntSet.empty
              (0 -- nb_dimensions))
      in
      let features (m,_) =
        let fv = Array.make nb_features 0 in
        m |> Monomial.IntMap.iter (fun d p ->
            for i = 0 to (nb_features - 1) do
              if IntSet.mem d feature_sets.(i) then
                fv.(i) <- fv.(i) + p
            done);
        fv
      in
      FeatureTree.of_list features rules
  end

  module VarMap = SrkUtil.Int.Map

  type t =
    { rules : RS.t;
      linear : P.t VarMap.t;
      order : Monomial.t -> Monomial.t -> [ `Eq | `Lt | `Gt ] }

  let polynomial_of_rule order (lhs, rhs) =
    P.add_term order (K.negate K.one) lhs rhs

  (* Add a rule to a rewrite.  **Assumes that the rule is reduced**.  Do not
     export. *)
  let _insert_rule (lhs, rhs) rewrite =
    match Monomial.destruct_var lhs with
    | Some v -> { rewrite with linear = VarMap.add v rhs rewrite.linear }
    | None -> { rewrite with rules = RS.insert (lhs, rhs) rewrite.rules }

  (* Try to find a linear rule (v -> rhs) such that v divides the monomial
     m.  If yes, return the pair (m/v, rhs)  *)
  let _reduce_lin _order linear monomial =
    try
      let var =
        BatEnum.find (fun var -> VarMap.mem var linear) (Monomial.IntMap.keys monomial)
      in
      let remainder =
        Monomial.IntMap.modify_opt
          var
          (fun deg -> match deg with
             | Some n when n >= 2 -> Some (n - 1)
             | _ -> None)
          monomial
      in
      Some (remainder, VarMap.find var linear)
    with Not_found ->
      (* No key in linear divides monomial *)
      None

  let rec reduce rewrite polynomial =
    match P.split_leading rewrite.order polynomial with
    | None -> polynomial
    | Some (c, m, polynomial') ->
      (* Preferentially reduce using linear polynomials, since pattern
         matching is faster.  This speeds up the linear case.
         TODO: can do multiple steps of linear reduction at once, e.g.,
               if x -> p, then x^2 -> p^2 *)
      match _reduce_lin rewrite.order rewrite.linear m with
      | Some (m, q) ->
        reduce rewrite
          (P.add rewrite.order (P.monomial_scalar_mul c m q) polynomial')
      | None ->
        try
          let reduced =
            RS.find_leq_map (RS.features rewrite.rules m) (fun (n, p) ->
                match Monomial.div m n with
                | Some remainder ->
                  Some (P.monomial_scalar_mul c remainder p)
                | None -> None)
              rewrite.rules
          in
          reduce rewrite (P.add rewrite.order reduced polynomial')
        with Not_found ->
          let reduced = reduce rewrite polynomial' in
          P.add_term rewrite.order c m reduced

  (* Buchberger's second criterion *)
  let _criterion2 r r' pairs rules =
    let lcm =
      let (m, _) = r in
      let (m', _) = r' in
      Monomial.lcm m m'
    in
    BatEnum.exists (fun rule ->
        let (m, _) = rule in
        (Monomial.div m lcm) != None
        && not (PairQueue.mem pairs (r, rule))
        && not (PairQueue.mem pairs (r', rule)))
      rules

  let mk_inconsistent order rhs =
    { order = order
    ; linear = VarMap.empty
    ; rules = RS.of_list [(Monomial.one, rhs)]}

  let buchberger rewrite pairs =
    (* Suppose m1 = rhs1 and m2 = rhs1.  Let m be the least common multiple of
       m1 and m2, and let m1*r1 = m = m2*r2.  Then we have m = rhs1*r1 and m =
       rhs2*r1.  It follows that rhs1*r1 - rhs2*r2 = 0.  spoly computes this
       polynomial. *)
    let spoly (m1, rhs1) (m2, rhs2) =
      let m = Monomial.lcm m1 m2 in
      let r1 = BatOption.get (Monomial.div m m1) in
      let r2 = BatOption.get (Monomial.div m m2) in
      P.add
        rewrite.order
        (P.monomial_scalar_mul K.one r1 rhs1)
        (P.monomial_scalar_mul (K.negate K.one) r2 rhs2)
    in
    let lhs (x, _) = x in
    let rhs (_, x) = x in
    let rec go rewrite pairs =
      match PairQueue.pop pairs with
      | None -> rewrite
      | Some ((r1, r2), pairs) ->
        logf ~level:`trace  "Pair:";
        logf ~level:`trace  "  @[%a@] --> @[<hov 2>%a@]"
          (Monomial.pp pp_ascii_dim) (lhs r1)
          (P.pp pp_ascii_dim) (rhs r1);
        logf ~level:`trace  "  @[%a@] --> @[<hov 2>%a@]"
          (Monomial.pp pp_ascii_dim) (lhs r2)
          (P.pp pp_ascii_dim) (rhs r2);
        let sp = reduce rewrite (spoly r1 r2) in
        match P.split_leading rewrite.order sp with
        | None -> go rewrite pairs
        | Some (c, m, p') when Monomial.equal m Monomial.one ->
          (* Inconsistent -- return (1 = 0) *)
          assert (not (K.equal c K.zero));
          let rhs =
            P.monomial_scalar_mul (K.negate (K.inverse c)) Monomial.one p'
          in
          mk_inconsistent rewrite.order rhs
        | Some (c, m, rest) ->
          assert (not (K.equal c K.zero));
          let rhs =
            P.monomial_scalar_mul (K.negate (K.inverse c)) Monomial.one rest
          in
          logf ~level:`trace "Result:";
          logf ~level:`trace "  @[%a@] --> @[<hov 2>%a@]"
            (Monomial.pp pp_ascii_dim) m
            (P.pp pp_ascii_dim) rhs;
          let new_rule = (m, rhs) in
          let pairs =
            BatEnum.fold (fun pairs rule ->
                match rule with
                | (m', _) when Monomial.equal (Monomial.gcd m m') Monomial.one ->
                  pairs
                | _ ->
                  PairQueue.insert pairs (new_rule, rule))
              pairs
              (RS.enum rewrite.rules)
          in
          go (_insert_rule new_rule rewrite) pairs
    in
    go rewrite pairs

  let buchberger rewrite pairs =
    Log.time "Buchberger" (buchberger rewrite) pairs

  (* Ensure that every basis polynomial is irreducible w.r.t. every other
     basis polynomial *)
  let reduce_rewrite rewrite =
    let rewrite =
      (* Leading term of linear rewrite is irreducible -- only RHS needs to be
         reduced. *)
      { rewrite with
        linear = VarMap.map (fun rhs -> reduce rewrite rhs) rewrite.linear }
    in
    BatEnum.fold (fun rewrite rule ->
        let rewrite' = { rewrite with rules = RS.remove rule rewrite.rules } in
        let p =
          polynomial_of_rule rewrite.order rule
          |> reduce rewrite'
        in
        match P.split_leading rewrite.order p with
        | None -> rewrite'
        | Some (c, m, p') when Monomial.equal m Monomial.one ->
          (* Inconsistent -- return (1 = 0) *)
          assert (not (K.equal c K.zero));
          let rhs =
            P.monomial_scalar_mul (K.negate (K.inverse c)) Monomial.one p'
          in
          mk_inconsistent rewrite.order rhs
        | Some (c, m, rest) ->
          assert (not (K.equal c K.zero));
          let rhs =
            P.monomial_scalar_mul (K.negate (K.inverse c)) Monomial.one rest
          in
          _insert_rule (m, rhs) rewrite')
      rewrite
      (RS.enum rewrite.rules)


  let add_saturate rewrite p =
    let p = reduce rewrite p in
    match P.split_leading rewrite.order p with
    | None -> rewrite
    | Some (c, m, p') when Monomial.equal m Monomial.one ->
      (* Inconsistent -- return (1 = 0) *)
      assert (not (K.equal c K.zero));
      let rhs =
        P.monomial_scalar_mul (K.negate (K.inverse c)) Monomial.one p'
      in
      mk_inconsistent rewrite.order rhs
    | Some (c, m, rest) ->
      assert (not (K.equal c K.zero));
      let rhs =
        P.monomial_scalar_mul (K.negate (K.inverse c)) Monomial.one rest
      in
      let new_rule = (m, rhs) in
      let pairs =
        BatEnum.fold (fun pairs rule ->
            match rule with
            | (m', _) when Monomial.equal (Monomial.gcd m m') Monomial.one ->
              pairs
            | _ ->
              PairQueue.insert pairs (new_rule, rule))
          PairQueue.empty
          (RS.enum rewrite.rules)
      in
      buchberger (_insert_rule new_rule rewrite) pairs

  let add_saturate rewrite p =
    Log.time "Buchberger" (add_saturate rewrite) p

  let generators rewrite =
    let linear =
      VarMap.fold
        (fun v rhs rules ->
           (polynomial_of_rule rewrite.order (Monomial.singleton v 1, rhs))::rules)
        rewrite.linear
        []
    in
    BatEnum.fold
      (fun rules rule ->
         (polynomial_of_rule rewrite.order rule)::rules)
      linear
      (RS.enum rewrite.rules)

  let pp pp_dim formatter rewrite =
    Format.pp_open_vbox formatter 0;
    SrkUtil.pp_print_enum_nobox
      ~pp_sep:Format.pp_print_cut
      (fun formatter (lhs, rhs) ->
         Format.fprintf formatter "%a --> @[<hov 2>%a@]"
           (Monomial.pp pp_dim) lhs
           (P.pp pp_dim) rhs)
      formatter
      (RS.enum rewrite.rules);
    SrkUtil.pp_print_enum_nobox
      ~pp_sep:Format.pp_print_cut
      (fun formatter (lhs, rhs) ->
         Format.fprintf formatter "%a --> @[<hov 2>%a@]"
           pp_dim lhs
           (P.pp pp_dim) rhs)
      formatter
      (VarMap.enum rewrite.linear);
    Format.pp_close_box formatter ()

  let grobner_basis rewrite =
    logf ~level:`trace "Compute a Grobner basis for:@\n@[<v 0>%a@]"
      (pp pp_ascii_dim) rewrite;

    let rewrite = reduce_rewrite rewrite in

    logf ~level:`trace "After reduction:@\n@[<v 0>%a@]"
      (pp pp_ascii_dim) rewrite;

    let pairs =
      BatEnum.fold (fun pairs (rule, rule') ->
          let (m, _) = rule in
          let (m', _) = rule' in
          if Monomial.equal (Monomial.gcd m m') Monomial.one then
            pairs
          else
            PairQueue.insert pairs (rule, rule'))
        PairQueue.empty
        (SrkUtil.distinct_pairs (RS.enum rewrite.rules))
    in

    let grobner =
      buchberger rewrite pairs 
    in
    logf ~level:`trace "Grobner basis:@\n@[<v 0>%a@]"
      (pp pp_ascii_dim) grobner;
    grobner

  module type LinearSpace = Linear.LinearSpace
    with type scalar = K.t
     and type vector = P.t

  let mk_space order =
    (module (Linear.MakeLinearSpace
               (K)
               (Monomial)
               (struct
                 type t = P.t
                 type dim = Monomial.t
                 type scalar = K.t
                 let scalar_mul k p = P.monomial_scalar_mul k Monomial.one p
                 let zero = P.zero
                 let add = P.add order
                 let split_leading p =
                   match P.split_leading order p with
                   | Some (a,b,c) -> Some (b,a,c)
                   | None -> None
                 let pp = P.pp pp_ascii_dim
                 let rec fold f p a =
                   match P.split_leading order p with
                   | Some (c,m,p') ->
                     fold f p' (f m c a)
                   | None -> a
                 let add_term = P.add_term order
               end)) : LinearSpace)

  let mk_rewrite order polynomials =
    let module L = ((val mk_space order) : LinearSpace) in
    let polynomials =
      L.basis (L.span (BatList.enum polynomials))
    in
    let rec loop (rule_list, linear) =
      match BatEnum.get polynomials with
      | None ->
        { rules = RS.of_list rule_list
        ; linear = linear
        ; order = order }
      | Some polynomial ->
        match P.split_leading order polynomial with
        | None -> loop (rule_list, linear)
        | Some (c, m, p') when Monomial.equal m Monomial.one ->
          (* Inconsistent *)
          assert (not (K.equal c K.zero));
          let rhs =
            P.monomial_scalar_mul (K.negate (K.inverse c)) Monomial.one p'
          in
          mk_inconsistent order rhs
        | Some (c, m, rest) ->
          assert (not (K.equal c K.zero));
          let rhs =
            P.monomial_scalar_mul (K.negate (K.inverse c)) Monomial.one rest
          in
          match Monomial.destruct_var m with
          | Some v -> loop (rule_list, VarMap.add v rhs linear)
          | None ->
            assert (not (Monomial.equal m Monomial.one));
            loop ((m, rhs)::rule_list, linear)
    in
    loop ([], VarMap.empty)


  let get_monomial_ordering rewrite = rewrite.order

  let restrict p rewrite =
    let rules =
      RS.enum rewrite.rules
      |> BatEnum.filter (fun (m, _) -> p m)
      |> BatList.of_enum
      |> RS.of_list
    in
    let linear =
      VarMap.filter (fun v _ -> p (Monomial.singleton v 1)) rewrite.linear
    in
    { order = rewrite.order
    ; rules = rules
    ; linear = linear }
end

module Rewrite = struct
  module OP = OrderedPolynomial
  module P = BatSet.Make(QQXs)
  module R = MakeRewrite(QQ)(struct
      type t = OP.t * P.t
      type scalar = QQ.t
      let zero = (OP.zero, P.empty)
      let add order (p1, w1) (p2, w2) = (OP.add order p1 p2, P.union w1 w2)
      let add_term order c m (p, w) = (OP.add_term order c m p, w)
      let monomial_scalar_mul c m (p, w) = (OP.monomial_scalar_mul c m p, w)
      let fold f acc (p, _) = OP.fold f acc p
      let split_leading order (p, w) =
        match OP.split_leading order p with
        | None -> None
        | Some (c, m, p') -> Some (c, m, (p', w))
      let pp pp_dim formatter (p, _) = OP.pp pp_dim formatter p
      let compare (p1, _) (p2, _) = OP.compare p1 p2
    end)
  type t = R.t

  let reduce rewrite p =
    (OP.of_qqxs (R.get_monomial_ordering rewrite) p, P.empty)
    |> R.reduce rewrite
    |> fst
    |> OP.qqxs_of

  let pp = R.pp

  let mk_rewrite order generators =
    R.mk_rewrite
      order
      (List.map (fun p -> (OP.of_qqxs order p, P.singleton p)) generators)

  let add_saturate rewrite p =
    R.add_saturate
      rewrite
      (OP.of_qqxs (R.get_monomial_ordering rewrite) p, P.singleton p)

  let preduce rewrite p =
    let (p', w) =
      (OP.of_qqxs (R.get_monomial_ordering rewrite) p, P.empty)
      |> R.reduce rewrite
    in
    (OP.qqxs_of p', P.elements w)

  let grobner_basis = R.grobner_basis
  let generators rewrite =
    R.generators rewrite
    |> List.map (fun (p, _) -> OP.qqxs_of p)

  let restrict = R.restrict
  let reduce_zero rewrite p =
    let (p', _) =
      (OP.of_qqxs (R.get_monomial_ordering rewrite) p, P.empty)
      |> R.reduce rewrite
    in
    OP.is_zero p'

  let subset j k =
    BatList.for_all
      (fun q ->
         let (p, _) = R.reduce k q in
         OP.is_zero p)
      (R.generators j)

  let equal j k = subset j k && subset k j

  let reorder_groebner order p =
    (* Trivial conversion now.  TODO: implement Groebner walk *)
    grobner_basis (mk_rewrite order (generators p))

  let get_monomial_ordering = R.get_monomial_ordering
  let reduce_rewrite = R.reduce_rewrite
end


module FGb = struct
  type fmon = Z.t * (int list)
  type fpoly = fmon list

  let () = Faugere_zarith.Fgb_int_zarith.set_number_of_threads 2

  
  let mon_to_fmon vs m = 
    List.map (
      fun v -> 
        match Monomial.IntMap.find_opt v m with
          | None -> 0
          | Some d -> d)
      vs

  let convert_to_faugere (vs : Monomial.dim list) (p : QQXs.t) : fpoly = 
    let (clearing_denom, rat_fmon) = 
      BatEnum.fold (
        fun (cd, ml) (c, m)  -> 
          let new_cd = Z.lcm (Q.den c) cd in 
          (new_cd, (c, mon_to_fmon vs m) :: ml)
       ) (Z.one, []) (QQXs.enum p)        
      in
    List.map (
      fun (c, m) -> Q.num (Q.mul (Q.of_bigint clearing_denom) c), m
    ) rat_fmon

  let convert_from_faugere (vs : Monomial.dim list) (p : fpoly) : QQXs.t =
    let convert_fmon_to_mon (c, fm) = 
      Q.of_bigint c, Monomial.of_enum (BatList.enum (List.mapi (fun i deg -> List.nth vs i, deg) fm)) in
    QQXs.of_list (List.map convert_fmon_to_mon p)

  let grobner_basis (blk1 : Monomial.dim list) (blk2 : Monomial.dim list) (polys : QQXs.t list) = 
    let non_zero = List.filter (fun p -> not (QQXs.is_zero p)) polys in 
    if List.length non_zero = 0 then [QQXs.zero]
    else
      let fpolys = List.map (convert_to_faugere (blk1 @ blk2)) non_zero in
      let gb = Faugere_zarith.Fgb_int_zarith.fgb fpolys (List.map string_of_int blk1) (List.map string_of_int blk2) in
      List.map (convert_from_faugere (blk1 @ blk2)) gb

  (* Is this right? *)
  let get_mon_order (blk1 : Monomial.dim list) (blk2 : Monomial.dim list) a b = 
    let ablk1, ablk2 = Monomial.split_block (fun v -> if (List.mem v blk1) then true else false) a in
    let bblk1, bblk2 = Monomial.split_block (fun v -> if (List.mem v blk1) then true else false) b in
    let compare_by_block fmon1 fmon2 = 
      let diff_rev = List.rev (List.map2 (-) fmon1 fmon2) in
      match List.find_opt ((<>) 0) diff_rev with
      | None -> `Eq
      | Some x -> 
        if x < 0 then `Gt
        else `Lt
    in
    let ablk1_total, bblk1_total = Monomial.total_degree ablk1, Monomial.total_degree bblk1 in
    if ablk1_total > bblk1_total then `Gt
    else if ablk1_total < bblk1_total then `Lt
    else
      let blk_comp = compare_by_block (mon_to_fmon blk1 ablk1) (mon_to_fmon blk1 bblk1) in
      match blk_comp with
      | `Gt | `Lt -> blk_comp
      | `Eq ->
        let ablk2_total, bblk2_total = Monomial.total_degree ablk2, Monomial.total_degree bblk2 in
        if ablk2_total > bblk2_total then `Gt
        else if ablk2_total < bblk2_total then `Lt
        else
          compare_by_block (mon_to_fmon blk2 ablk2) (mon_to_fmon blk2 bblk2)

end


module Ideal = struct
  type t = Rewrite.t
  open Rewrite

  (* Common monomial ordering *)
  let order = Monomial.degrevlex

  let add_saturate ideal p = Rewrite.add_saturate ideal p

  let reduce ideal p =
    Rewrite.reduce ideal p

  (* Projection of the ideal generated by a set of polynomials *)
  let project_impl p generators =
    let elim_order = Monomial.block [not % p] order in
    let rewrite =
      mk_rewrite elim_order generators
      |> grobner_basis
    in
    restrict
      (fun m ->
         BatEnum.for_all (fun (d, _) -> p d) (Monomial.enum m))
      rewrite

  let project p j = project_impl p (generators j)

  let intersect j k =
    let j = generators j in
    let k = generators k in
    let t =
      1 + (List.fold_left
             (fun m p ->
                try max m (SrkUtil.Int.Set.max_elt (QQXs.dimensions p))
                with Not_found -> m)
             0
             (j @ k))
    in
    (* { tp : p in j } *)
    let j' = List.map (QQXs.mul (QQXs.of_dim t)) j in
    (* { (1-t)p : p in k } *)
    let k' =
      List.map (QQXs.mul (QQXs.sub (QQXs.scalar QQ.one) (QQXs.of_dim t))) k
    in
    project_impl (not % (=) t) (j' @ k')

  let mem p j = reduce_zero j p

  let subset = subset

  let equal = equal

  let make generators =
    grobner_basis (mk_rewrite order generators)

  let generators = generators

  let product j k =
    let j_generators = generators j in
    List.fold_left (fun gen p ->
        List.fold_left (fun gen q ->
            (QQXs.mul p q)::gen)
          gen
          j_generators)
      []
      (generators k)
    |> make

  let sum j k =
    List.fold_left (fun rewrite q ->
        add_saturate rewrite q)
      j
      (generators k)

  let pp = pp
end

module Witness = struct
  include Ring.RingMap(SrkUtil.Int)(QQXs)
  let monomial_scalar_mul c m w =
    scalar_mul (QQXs.of_list [(c, m)]) w
  let pp pp_dim formatter w =
    let pp_elt formatter (p, i) =
      Format.fprintf formatter "%a * x_%d" (QQXs.pp pp_dim) p i
    in
    SrkUtil.pp_print_enum pp_elt formatter (enum w)
end

module RewriteWitness = struct
  module OP = OrderedPolynomial
  include MakeRewrite(QQ)(struct
      type t = OP.t * Witness.t
      type scalar = QQ.t
      let zero = (OP.zero, Witness.zero)
      let add order (p1, w1) (p2, w2) = (OP.add order p1 p2, Witness.add w1 w2)
      let add_term order c m (p, w) = (OP.add_term order c m p, w)
      let monomial_scalar_mul c m (p, w) = (OP.monomial_scalar_mul c m p,
                                            Witness.monomial_scalar_mul c m w)
      let fold f acc (p, _) = OP.fold f acc p
      let split_leading order (p, w) =
        match OP.split_leading order p with
        | None -> None
        | Some (c, m, p') -> Some (c, m, (p', w))
      let pp pp_dim formatter (p, w) =
        Format.fprintf formatter "%a ~ %a" (OP.pp pp_dim) p (Witness.pp pp_dim) w
      let compare (p1, _) (p2, _) = OP.compare p1 p2
    end)
  let mk_rewrite order generators =
    mk_rewrite order (List.map (fun (p, w) -> (OP.of_qqxs order p, w)) generators)
  let add_saturate rewrite p w =
    add_saturate rewrite (OP.of_qqxs rewrite.order p, w)
  let zero_witness rewrite p =
    let (p, w) = reduce rewrite (OP.of_qqxs rewrite.order p, Witness.zero) in
    if OP.is_zero p then Some w else None

  let reducew rewrite (p, w) =
    let (p, w) = reduce rewrite (OP.of_qqxs rewrite.order p, w) in
    (OP.qqxs_of p, w)

  let reduce rewrite p =
    let (p, w) = reduce rewrite (OP.of_qqxs rewrite.order p, Witness.zero) in
    (OP.qqxs_of p, w)

  let generators rewrite =
    generators rewrite
    |> List.map (fun (p, m) -> (OP.qqxs_of p, m))

  let forget rewrite =
    Rewrite.mk_rewrite
      rewrite.order
      (List.map fst (generators rewrite))
end

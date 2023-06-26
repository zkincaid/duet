open Polynomial

exception Divide_by_zero

include Log.Make(struct let name = "rational" end)

module type RationalFunc = sig
  type num
  type den
  type t
  val zero : t
  val one : t
  val of_n_d : num * den -> t
  val equal : t -> t -> bool
  val equal_syn : t -> t -> bool
  val add : t -> t -> t
  val negate : t -> t
  val lift : num -> t
  val mul : t -> t -> t
  val int_mul : int -> t -> t
  val pp : Format.formatter -> t -> unit
  val partial_fraction : num -> (den * int) list -> (num * (den * int)) list
end



(*The given ring should be an integral domain. There is no way to enforce this in code.*)
module MakeRat (D : sig 
  include Euclidean
  val pp : Format.formatter -> t -> unit
end) = struct

  type num = D.t

  type den = D.t

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
      if D.equal n D.zero then 
        (a := Norm (D.zero, D.one);
        (D.zero, D.one))
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

module IM = SrkUtil.Int.Map

module MakeEPWithHeavy(B : sig 
  include Algebra.Field 
  val compare : t -> t -> int 
  val exp : t -> int -> t 
  val pp : Format.formatter -> t -> unit
end)
(C : sig
  include Algebra.Ring
  val lift : B.t -> t
  val int_mul : int -> t -> t
  val pp : Format.formatter -> t -> unit
end)
(CX : sig
  include Univariate with type scalar = C.t
  val pp : Format.formatter -> t -> unit
end) = struct
  module E = ExpPolynomial.MakeEP(B)(C)(CX)

  type t = {
    ep : E.t;
    heaviside : C.t IM.t
  }

  let zero = {ep = E.zero; heaviside = IM.empty}

  let one = {ep = E.one; heaviside = IM.empty}

  let scalar a = {ep = E.scalar a; heaviside = IM.empty}

  let of_polynomial p = {ep = E.of_polynomial p; heaviside = IM.empty}

  let of_exponential e = {ep = E.of_exponential e; heaviside = IM.empty}

  let of_exponential_poly e p = {ep = E.mul (E.of_exponential e) (E.of_polynomial p); heaviside = IM.empty}

  let of_heavy shift c = {ep = E.zero; heaviside = IM.add shift c IM.empty}

  let scalar_mul c term = 
    let ep = E.scalar_mul c term.ep in
    let heaviside = IM.map (C.mul c) term.heaviside in
    {ep; heaviside}

  let add a b =
    let ep = E.add a.ep b.ep in
    let unioner _ x y = 
      let coef_add = C.add x y in
      if C.equal coef_add C.zero then None
      else Some coef_add
    in
    let heaviside = IM.union unioner a.heaviside b.heaviside in
    {ep; heaviside}

  let negate a = 
    let ep = E.negate a.ep in
    let heaviside = IM.map (C.negate) a.heaviside in
    {ep; heaviside}


  let equal a b = 
    if E.equal a.ep b.ep = true then
      IM.equal C.equal a.heaviside b.heaviside
    else
      false

  let eval a i = 
    let ep_eval = E.eval a.ep i in
    let heavy_eval shift c sum = 
      if i>= shift then C.add sum c
      else sum
    in
    IM.fold heavy_eval a.heaviside ep_eval

  let shift n e = 
    let shift_poly p =
      BatEnum.fold (
        fun acc (c, pow) ->
          CX.add acc (CX.scalar_mul c (CX.exp (CX.add CX.identity (CX.scalar (C.int_mul n C.one))) pow)) (*Add or sub? p(k+n)*) 
      ) CX.zero (CX.enum p)
    in
    let shift_ep_add acc (p, b) = 
      let shifted_p = shift_poly p in
      add acc (of_exponential_poly b (CX.scalar_mul (C.lift (B.exp b (-n))) shifted_p)) (*-n or n?*)
    in
    let shifted_ep = BatEnum.fold shift_ep_add zero (E.enum e.ep) in
    let shift_heavy_add acc (shift, c) = 
      if n >= shift then add acc (scalar c)
      else add acc (of_heavy (shift-n) c)
    in
    BatEnum.fold shift_heavy_add shifted_ep (IM.enum e.heaviside)
    

  let shift_remove_heavys earr = 
    let biggest_heavy e = 
      if IM.is_empty e.heaviside then 0 
      else fst (IM.max_binding e.heaviside)
    in
    let biggest = Array.fold_left (fun acc e -> max acc (biggest_heavy e)) (-1) earr in
    let transient = List.init biggest (fun i -> Array.map (fun e -> eval e i) earr) in
    transient, biggest, Array.map (shift biggest) earr


  (*TODO mul*)

  let enum_ep e = E.enum e.ep

  let enum_heavy e = IM.enum e.heaviside

  let pp f a = 
    let pp_heaviside formatter (offset, coef) =
      if C.equal coef C.one then
        Format.fprintf formatter "[x >= %d]" offset
      else
        Format.fprintf formatter "(%a)[x >= %d]" C.pp coef offset
    in
    let pp_sep formatter () =
      Format.fprintf formatter "@ + "
    in
    let is_ep_zero = E.equal a.ep E.zero in
    let is_heaviside_zero = IM.is_empty a.heaviside in
    if is_ep_zero && is_heaviside_zero then Format.pp_print_string f "0"
    else
      if not is_ep_zero && is_heaviside_zero then E.pp f a.ep
      else 
        if not is_ep_zero then (E.pp f a.ep; pp_sep f ());
        SrkUtil.pp_print_enum_nobox ~pp_sep pp_heaviside f (IM.enum a.heaviside)

end

module type ExpPolyNF = sig
  module NF : NumberField.NF

  module ConstRing : Multivariate with type scalar = NF.elem

  module ConstRingX : Univariate with type scalar = ConstRing.t

  type t 
  val zero : t

  val one : t

  val scalar : ConstRing.t -> t

  val of_polynomial : ConstRingX.t -> t

  val of_exponential : NF.elem -> t

  val of_exponential_poly : NF.elem -> ConstRingX.t -> t

  val of_heavy : int -> ConstRing.t -> t
  
  val scalar_mul : ConstRing.t -> t -> t

  val add : t -> t -> t

  val negate : t -> t
  
  val equal : t -> t -> bool

  val eval : t -> int -> ConstRing.t

  val enum_ep : t -> (ConstRingX.t * NF.elem) BatEnum.t

  val enum_heavy : t -> (int * ConstRing.t) BatEnum.t

  val pp : Format.formatter -> t -> unit

  val get_rec_sols : unit -> t array

  val base_relations : unit -> QQXs.t list * (NF.elem * int) BatEnum.t

  val algebraic_relations : unit -> QQXs.t list

  val shift_remove_heavys : unit -> QQXs.t array list * int * t array

  val long_run_algebraic_relations : unit -> QQXs.t array list * int * QQXs.t list

  (*TODO mul*)
end

module MakeConstRing (
  R : sig 
    include Algebra.Ring 
    val lift : QQ.t -> t
  end) = struct
  include MakeMultivariate(R)
  
  let int_mul i = scalar_mul (R.lift (QQ.of_int i))

end

open Polynomial

module MakeEPNF(NF : NumberField.NF) (*: ExpPolyNF with module NF = NF*) = struct
  module NF = NF

  module ConstRing = MakeConstRing(struct include NF type t = elem let lift = NF.of_rat end)

  
  module ConstRingX = MakeUnivariate(ConstRing)

  include MakeEPWithHeavy
    (struct include NF type t = elem end)
    (struct include ConstRing let lift = ConstRing.scalar let pp = ConstRing.pp NF.pp (fun fo d -> Format.pp_print_string fo ("x_" ^ (string_of_int d))) end)
    (struct include ConstRingX let pp = ConstRingX.pp (ConstRing.pp NF.pp (fun fo d -> Format.pp_print_string fo ("x_" ^ (string_of_int d)))) end)


  module BM = BatMap.Make(struct type t = NF.elem let compare = NF.compare end)

  let rec_sols = ref (Array.make 0 zero)

  let bases_in_rec = ref (BM.empty, IM.empty)

  let set_rec_sols rs = 
    rec_sols := rs;
    let (bm, im, _) = 
      Array.fold_left (
        fun (bm, im, i) ep ->          
          BatEnum.fold (
            fun (basem, dimm, j) (_, b)->
              try 
                let  _ = BM.find b basem in
                (basem, dimm, j)
              with Not_found -> 
                (BM.add b j basem, IM.add j b dimm, j+1)
          ) (bm, im, i) (enum_ep ep)
        ) (BM.empty, IM.empty, 0) rs in
    bases_in_rec := bm, im
  


  let base_relations : QQXs.t list ref = ref []

  let get_rec_sols () = !rec_sols

  let shift_remove_heavys () = 
    let transient, shift, sols = shift_remove_heavys (get_rec_sols ()) in
    let const_ring_to_qqxs p = 
      QQXs.of_enum (BatEnum.map (
        fun (c, d) ->
          let cp = NF.get_poly c in
          if QQX.order cp <> 0 then failwith "Map has non-rational entries";
          QQX.coeff 0 cp, d
      ) (ConstRing.enum p)) in
    List.map (Array.map const_ring_to_qqxs) transient, shift, sols

  let base_relations () = 
    if List.length !base_relations <> 0 then !base_relations, BM.enum (fst (!bases_in_rec))
    else
      let roots = List.init (IM.cardinal (snd !bases_in_rec)) (fun i -> IM.find i (snd !bases_in_rec)) in
      let relations = NF.find_relations roots in
      let exp_rel_to_poly exp = 
        let (poss, negs, _) = List.fold_left (
          fun (pos, neg, i) e ->
            if e = 0 then pos, neg, i+1
            else if e > 0 then
              QQXs.mul (QQXs.exp (QQXs.of_dim i) e) pos, neg, i+1
            else
              pos, QQXs.mul (QQXs.exp (QQXs.of_dim i) (-e)) neg, i+1
        ) (QQXs.one, QQXs.one, 0) exp in
        QQXs.sub poss negs
      in
      List.map exp_rel_to_poly relations, BM.enum (fst (!bases_in_rec))
        

  let algebraic_relations_in sols = 
    let root_rels = fst (base_relations ()) in
    let post_offset = Array.length sols in
    let iter_var = 2 * post_offset in
    let field_var = iter_var + 1 in
    let root_offset = field_var + 1 in
    let translate_coeff c = 
      let translate_m sum (nf, m) = 
        let nf_p = NF.get_poly nf in
        let nf_poly = NumberField.make_multivariate field_var nf_p in
        QQXs.add sum (QQXs.mul_monomial m nf_poly)
      in
      BatEnum.fold translate_m QQXs.zero (ConstRing.enum c)
    in
    let translate_poly p = 
      let translate_t sum (coef, deg) = 
        QQXs.add sum (QQXs.mul (translate_coeff coef) (QQXs.exp (QQXs.of_dim iter_var) deg))
      in
      BatEnum.fold translate_t QQXs.zero (ConstRingX.enum p)
    in
    let translate_sol i ep = 
      if not (BatEnum.is_empty (enum_heavy ep)) then failwith "Unable to get algebraic relations for recurrences with an eigenvalue of 0";
      let translate_power_poly sum (poly, base) =
        let base_var = QQXs.of_dim ((BM.find base (fst !bases_in_rec)) + root_offset) in
        QQXs.add sum (QQXs.mul (translate_poly poly) base_var)
      in
      let rhs = BatEnum.fold translate_power_poly QQXs.zero (enum_ep ep) in
      QQXs.sub (QQXs.of_dim (i+post_offset)) rhs
    in
    let cl = Array.to_list (Array.mapi translate_sol sols) in
    let field_poly = NumberField.make_multivariate field_var NF.int_poly in
    let offset_root_rel p = 
      let offset_mon (c, m) = 
        let offsetter (dim, pow) = 
          (dim + root_offset, pow)
        in
        c, Monomial.of_enum (BatEnum.map offsetter (Monomial.enum m))
      in
      QQXs.of_enum (BatEnum.map offset_mon (QQXs.enum p))
    in
    let root_rels_off = List.map offset_root_rel root_rels in
    let ideal = field_poly :: (cl @ root_rels_off) in
    logf ~level:`trace "Algebraic Relations : Pre_vars %d - %d, Post_vars %d - %d, iter_var %d, field_var %d, root_vars >= %d" 0 (post_offset - 1) post_offset (iter_var - 1) iter_var field_var root_offset;
    let pp_i = Format.pp_print_list ~pp_sep:(fun f () -> Format.pp_print_newline f ()) (QQXs.pp (fun f i -> Format.fprintf f "x_%d" i)) in
    log_pp ~level:`trace pp_i ideal;
    let biggest_root_i, _ = IM.max_binding (snd !bases_in_rec) in
    let gb = FGb.grobner_basis (List.init ((biggest_root_i + root_offset) - field_var + 1) (fun i -> i + field_var)) (List.init (iter_var + 1) (fun i -> i)) ideal in
    log ~level:`trace "After gb";
    log_pp ~level:`trace pp_i gb;
    List.filter (
      fun p ->
        let ds = QQXs.dimensions p in
        SrkUtil.Int.Set.disjoint ds (SrkUtil.Int.Set.of_list (List.init ((biggest_root_i + root_offset) - field_var + 1) (fun i -> i + field_var)))
    ) gb

  let algebraic_relations () = 
    algebraic_relations_in (get_rec_sols ())


  let long_run_algebraic_relations () = (*Should I resubsitute for K?*)
    let (transient, shift, shifted) = shift_remove_heavys () in
    let rels = algebraic_relations_in shifted in
    let loop_counter = 2 * (Array.length (get_rec_sols ())) in
    let deshifted = List.map (QQXs.substitute (fun d -> if d = loop_counter then QQXs.sub (QQXs.of_dim loop_counter) (QQXs.scalar (QQ.of_int shift)) else QQXs.of_dim d)) rels in
    (transient, shift, deshifted)


end 

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

  type num = N.t

  type den = D.t

  type t = N.t * D.t

  let equal (p, q) (r, s) = 
    N.equal (N.mul p (I.lift s)) (N.mul r (I.lift q))

  let equal_syn (p, q) (r, s) = 
    N.equal p r && D.equal q s

  let of_n_d (p, q) = (p, q)
  
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


module ConstRing = struct 
  include QQXs

  let pp = pp (fun fo d -> Format.pp_print_string fo ("x_" ^ (string_of_int d)))

  let int_mul i a = QQXs.scalar_mul (QQ.of_int i) a

  end

module ConstRingX = struct
  include MakeUnivariate(ConstRing)

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


type block = TransitionIdeal.block




module RS = struct 
  type nonrec t = t 
  let add = add 
  let zero = zero 
  let one = one

  let mul = mul
end

module RatEP = struct

  module RE = MakeEPWithHeavy(QQ)(struct include ConstRing let lift = ConstRing.scalar end)(N)

  type iif = QQX.t

  module IIFS = BatMap.Make(
    struct 
      type t = iif * int 
      let compare (a, offa) (b, offb)= 
        let q_c = QQX.compare QQ.compare a b in 
        if q_c <> 0 then q_c
        else
          Int.compare offa offb
    end)

  type t = {
    e : RE.t;
    iifs : ConstRing.t IIFS.t
  }

  let equal a b = 
    if RE.equal a.e b.e = true then
      IIFS.equal (ConstRing.equal) a.iifs b.iifs
    else false

  let pp f a = 
    let pp_iif formatter ((den, shift), coef) =
      if ConstRing.equal coef ConstRing.one then
        if shift = 0 then
          Format.fprintf formatter "IIF(%a)[x]" QQX.pp den
        else
          Format.fprintf formatter "IIF(%a)[x + %d]" QQX.pp den shift
      else
        if shift = 0 then
          Format.fprintf formatter "(%a)IIF(%a)[x]" ConstRing.pp coef QQX.pp den
        else
          Format.fprintf formatter "(%a)IIF(%a)[x + %d]" ConstRing.pp coef QQX.pp den shift
    in
    let pp_sep formatter () =
      Format.fprintf formatter "@ + "
    in
    let is_ep_zero = RE.equal a.e RE.zero in
    let is_iifs_zero = IIFS.is_empty a.iifs in
    if is_ep_zero && is_iifs_zero then Format.pp_print_string f "0"
    else
      if not is_ep_zero && is_iifs_zero then RE.pp f a.e
      else 
        if not is_ep_zero then (RE.pp f a.e; pp_sep f ());
        SrkUtil.pp_print_enum_nobox ~pp_sep pp_iif f (IIFS.enum a.iifs)

  let zero = {e = RE.zero; iifs = IIFS.empty}

  let one = {e = RE.one; iifs = IIFS.empty}

  let eval a i = 
    if not (IIFS.is_empty a.iifs) then failwith "TODO eval an IIF at a point";
    RE.eval a.e i

  let scalar a = {e = RE.scalar a; iifs = IIFS.empty}

  let of_polynomial p = {e = RE.of_polynomial p; iifs = IIFS.empty}

  let of_exponential e = {e = RE.of_exponential e; iifs = IIFS.empty}

  let enum_ep e = RE.enum_ep e.e

  let enum_heavy e = RE.enum_heavy e.e

  let enum_iif e = IIFS.enum e.iifs
  

  let scalar_mul c term = 
    let e = RE.scalar_mul c term.e in
    let iifs = IIFS.map (ConstRing.mul c) term.iifs in
    {e; iifs}

  let add a b =
    let e = RE.add a.e b.e in
    let unioner _ x y = 
      let coef_add = ConstRing.add x y in
      if ConstRing.is_zero coef_add then None
      else Some coef_add
    in
    let iifs = IIFS.union unioner a.iifs b.iifs in
    {e; iifs}

  let negate a = 
    let e = RE.negate a.e in
    let iifs = IIFS.map (ConstRing.negate) a.iifs in
    {e; iifs}


  

  let translate_term (n, (den, power)) = 
    if QQX.order den > 1 then(
      (*let size = BatList.length (BatList.of_enum (QQX.enum den)) in
      if size = 1 then(
        let heaviside = ConstRingX.fold (
          fun deg coef heavies -> 
            IM.add (power - deg) coef heavies
        ) n IM.empty in
        {ep = RE.zero; iifs = IIFS.empty; heaviside})
      else*)
        let iif_den = QQX.exp den power in
        let iifs = ConstRingX.fold (
          fun deg coef iif ->
            IIFS.add (iif_den, deg) coef iif
        ) n IIFS.empty in
        {zero with iifs})
    else( 
      if N.order n > 0 then failwith "Numerator should be constant unless IIF";
      let num = N.coeff 0 n in
      if QQX.order den = 0 then
        let coe = QQ.exp (QQX.coeff 0 den) (-power) in
        scalar (ConstRing.scalar_mul coe num)
      else(
        let den_root = QQ.negate (QQ.div (QQX.coeff 0 den) (QQX.coeff 1 den)) in
        if QQ.equal den_root QQ.zero then
          let heaviside = ConstRingX.fold (
            fun deg coef heavies -> 
              IM.add (power - deg) coef heavies
            ) n IM.empty in
            {e = {RE.zero with heaviside }; iifs = IIFS.empty}
        else if QQ.equal den_root QQ.one then
          let p = QQX.choose power in
          scalar_mul num (of_polynomial (lift_qqx_to_constfofx p))
        else
          let rec aux c = 
            if c = 1 then 
              let ep_den = ConstRing.scalar (QQ.inverse (QQ.sub den_root QQ.one)) in
              let ep = RE.E.add (RE.E.of_exponential den_root) (RE.E.negate RE.E.one) in
              RE.E.scalar_mul ep_den ep (*(k^n - 1)/(k-1)*)
            else
              let ep_den = ConstRing.scalar (QQ.inverse (QQ.sub den_root QQ.one)) in
              let expo = RE.E.of_exponential den_root in
              let poly = QQX.scalar_mul (QQ.exp den_root (-c + 1)) (QQX.choose (c-1)) in (*(n choose c-1) a^{-c+1}*)
              let term = RE.E.mul expo (RE.E.of_polynomial (lift_qqx_to_constfofx poly)) in
              let rhs = aux (c-1) in
              RE.E.scalar_mul ep_den (RE.E.add term (RE.E.negate rhs)) (*1/(a-1) ((n choose c-1) a^{-c+1}a^n - aux (c-1))*)
          in
          {e = {RE.zero with ep = RE.E.scalar_mul num (aux power)}; iifs = IIFS.empty}))

  let translate_rs (n, d) = 
    let content, den_facts = QQX.factor d in
    let n = ConstRingX.scalar_mul (ConstRing.scalar (QQ.inverse content)) n in
    let decomp = partial_fraction n den_facts in
    List.fold_left (
      fun acc rat_t -> add acc (translate_term rat_t)
    ) zero decomp


  let translate_ep_term (xc, xb) = 
    let choose_int n k = 
      if k < 0 || k > n then QQ.zero
      else if k = 0 || k = n then QQ.one
      else
        let k = min k (n-k) in
        let rec aux acc i = 
          if i > k then acc
          else
            aux (QQ.mul acc (QQ.of_frac (n+1-i) (i))) (i + 1)
        in
        aux (QQ.of_int 1) 1
    in
    let binomial_trans p = 
      let d = ConstRingX.order p in
      let kth_coef k = 
        let l = List.map (
          fun i ->
            let rat_piece = QQ.mul (QQ.exp (QQ.of_int (-1)) (k-i)) (choose_int k i) in
            ConstRing.scalar_mul rat_piece (ConstRingX.eval p (ConstRing.scalar (QQ.of_int i)))
        ) (List.init (k+1) (fun i -> i)) in
        List.fold_left ConstRing.add ConstRing.zero l in
      List.init (d + 1) kth_coef
    in
    let xc_binom = binomial_trans xc in
    if QQ.equal xb QQ.one then
      let add_l = List.mapi (fun i coef -> (ConstRingX.scalar coef), QQX.exp (QQX.sub QQX.identity QQX.one) i) xc_binom in
      List.fold_left RS.add RS.zero add_l
    else
      let add_l = List.mapi (
        fun i coef -> 
          let num = ConstRingX.scalar_mul (ConstRing.scalar_mul (QQ.exp xb i) coef) (ConstRingX.sub ConstRingX.identity ConstRingX.one) in
          num, QQX.exp (QQX.sub QQX.identity (QQX.scalar xb)) (i + 1)) xc_binom in
      List.fold_left RS.add RS.zero add_l

        
  let translate_iif ((iifa, shift), coef) : RS.t = 
    ConstRingX.scalar_mul coef (ConstRingX.of_term ConstRing.one shift), iifa          

  let translate_heaviside (shift, coef) : RS.t = 
    ConstRingX.scalar coef, QQX.of_term QQ.one shift

  let mul a b = 
    if IIFS.is_empty a.iifs && IIFS.is_empty b.iifs && IM.is_empty a.e.heaviside && IM.is_empty b.e.heaviside then {zero with e = {RE.zero with ep = RE.E.mul a.e.ep b.e.ep}}
    else (*probably a much more efficient way to due this*)
      let a_ep_rs, b_ep_rs = BatEnum.map translate_ep_term (RE.enum_ep a.e), BatEnum.map translate_ep_term (RE.enum_ep b.e) in
      let a_iifs_rs, b_iifs_rs = BatEnum.map translate_iif (IIFS.enum a.iifs), BatEnum.map translate_iif (IIFS.enum b.iifs) in
      let a_heavy_rs, b_heavy_rs = BatEnum.map translate_heaviside (RE.enum_heavy a.e), BatEnum.map translate_heaviside (RE.enum_heavy b.e) in
      let a_rs = BatEnum.fold RS.add RS.zero (BatEnum.append (BatEnum.append a_ep_rs a_iifs_rs) a_heavy_rs) in
      let b_rs = BatEnum.fold RS.add RS.zero (BatEnum.append (BatEnum.append b_ep_rs b_iifs_rs) b_heavy_rs) in
      translate_rs (had_mult a_rs b_rs)


  let to_nf eps = 
    let all_iifs = Array.fold_left (fun acc ep -> BatEnum.append acc (IIFS.keys ep.iifs)) (BatEnum.empty ()) eps in
    let sf, roots = 
      if BatEnum.is_empty all_iifs then QQX.zero, []
      else
        let irreds = BatEnum.uniq_by (fun (den1, _) (den2, _) -> QQX.equal den1 den2) all_iifs in
        let root_poly = BatEnum.fold (fun rp (irred, _) -> QQX.mul rp irred) QQX.one irreds in
        NumberField.splitting_field root_poly
    in
    let module NF = NumberField.MakeNF(struct let min_poly = sf end) in
    let roots_e = List.map (fun (r, _) -> NF.make_elem r) roots in
    let module EP = MakeEPNF(NF) in
    let lift_nfx_to_constnfx d =   
      let e = BatEnum.map (
        fun (c, deg) ->
          EP.ConstRing.scalar c, deg
        ) (EP.NF.X.enum d) in
      EP.ConstRingX.of_enum e
    in
    let module RatNF = 
      MakeRatDiff(
        struct 
          include EP.ConstRingX
          let pp = pp (EP.ConstRing.pp EP.NF.pp (fun fo d -> Format.pp_print_string fo ("x_" ^ (string_of_int d))))
          let int_mul i e = scalar_mul (EP.ConstRing.scalar (EP.NF.of_rat (QQ.of_int i))) e
        end)
        (EP.NF.X)(
        struct
          let lift = lift_nfx_to_constnfx
          let qr a b = 
            if EP.NF.X.is_zero b then failwith "Divide by 0";
            let d = EP.NF.X.order b in
            let c = EP.NF.X.coeff d b in
            if d = 0 then 
              (EP.ConstRingX.scalar_mul (EP.ConstRing.scalar (EP.NF.inverse c)) a, EP.ConstRingX.zero)
            else
              let rec aux q r =
                let rd = EP.ConstRingX.order r in
                if rd = 0 || rd < d then (q, r)
                else
                  let s = (EP.ConstRingX.of_term (EP.ConstRing.scalar_mul (EP.NF.inverse c) (EP.ConstRingX.coeff rd r)) (rd - d)) in
                  aux (EP.ConstRingX.add q s) (EP.ConstRingX.sub r (EP.ConstRingX.mul s (lift b)))
                in
              aux EP.ConstRingX.zero a
        end) in
    let lift_const_to_constnf c = 
      EP.ConstRing.of_enum (BatEnum.map (fun (c, m) -> EP.NF.of_rat c, m) (ConstRing.enum c))
    in
    let lift_constx_to_constnfx p = 
      EP.ConstRingX.of_enum (BatEnum.map (fun (c, d) -> lift_const_to_constnf c, d) (ConstRingX.enum p))
    in
    let translate_ep ep = 
      let ep_with_e_and_heavy = BatEnum.fold (
        fun e (coef, b) ->
          EP.add e (EP.of_exponential_poly (EP.NF.of_rat b) (lift_constx_to_constnfx coef))
        ) (BatEnum.fold (fun e (heavy, coef) -> EP.add e (EP.of_heavy heavy (lift_const_to_constnf coef))) EP.zero (RE.enum_heavy ep.e)) (RE.enum_ep ep.e)
      in
      let iif_to_rat_pow ((iif, shift), coef) = 
        let square_free_iif = QQX.square_free_factor iif in
        let process_square_free (new_c, den_facts) (den_fact, multi) = 
          let den_e = EP.NF.X.lift den_fact in
          let roos = List.filter (fun r -> EP.NF.is_zero (EP.NF.X.eval den_e r)) roots_e in
          if EP.NF.X.order den_e <> List.length roos then failwith "Missing root";
          let roos_facts = List.map (fun r -> EP.NF.X.sub EP.NF.X.identity (EP.NF.X.scalar r)) roos in
          let (const_p, rem) = EP.NF.X.qr den_e (List.fold_left EP.NF.X.mul EP.NF.X.one roos_facts) in
          if NF.X.order const_p > 0 || not (NF.X.is_zero rem) then failwith "The root poly should be a constant factor of den_e";
          let const_mult = NF.X.coeff 0 const_p in
          (EP.ConstRingX.scalar_mul (EP.ConstRing.scalar (EP.NF.inverse const_mult)) new_c, den_facts @ (List.map (fun rp -> rp, multi) roos_facts))
        in
        List.fold_left process_square_free (EP.ConstRingX.scalar_mul (lift_const_to_constnf coef) (EP.ConstRingX.of_term (EP.ConstRing.one) shift), []) square_free_iif
      in
      let iifs_rat_pow = BatEnum.map iif_to_rat_pow (IIFS.enum ep.iifs) in
      let translate_and_add sum (numerator, den_fact_list) = 
        let terms = RatNF.partial_fraction numerator den_fact_list in
        let translate_term (num, (den, power)) = 
          if NF.X.order den > 1 then failwith "Everything should be factored to linear polys";
          if EP.ConstRingX.order num > 0 then failwith "Numerator should be a constant with linear denominator";
          let n = EP.ConstRingX.coeff 0 num in
          if NF.X.order den = 0 then
            let coe = NF.inverse (NF.exp (NF.X.coeff 0 den) power) in
            EP.scalar (EP.ConstRing.scalar_mul coe n)
          else
            let den_root = NF.negate (NF.mul (NF.X.coeff 0 den) (NF.inverse (NF.X.coeff 1 den))) in
            if NF.equal den_root NF.zero then
              EP.ConstRingX.fold (
                fun deg coef heavies ->
                  EP.add (EP.of_heavy (power - deg) coef) heavies
              ) num EP.zero
            else if NF.equal den_root NF.one then (*This should have already been handled*)
              let p = NF.X.lift (QQX.choose power) in
              EP.scalar_mul n (EP.of_polynomial (lift_nfx_to_constnfx p))
            else
              let rec aux c = 
                if c = 1 then 
                  let ep_den = EP.ConstRing.scalar (NF.inverse (NF.sub den_root NF.one)) in
                  let ep = EP.add (EP.of_exponential den_root) (EP.negate EP.one) in
                  EP.scalar_mul ep_den ep (*(k^n - 1)/(k-1)*)
                else
                  let ep_den = EP.ConstRing.scalar (NF.inverse (NF.sub den_root NF.one)) in
                  let poly = NF.X.scalar_mul (NF.exp den_root (-c + 1)) (NF.X.lift (QQX.choose (c-1))) in (*(n choose c-1) a^{-c+1}*)
                  let term = EP.of_exponential_poly den_root (lift_nfx_to_constnfx poly) in
                  let rhs = aux (c-1) in
                  EP.scalar_mul ep_den (EP.add term (EP.negate rhs)) (*1/(a-1) ((n choose c-1) a^{-c+1}a^n - aux (c-1))*)
              in
              EP.scalar_mul n (aux power)
        in
        List.fold_left (fun acc t -> EP.add acc (translate_term t)) sum terms
      in
      BatEnum.fold translate_and_add ep_with_e_and_heavy iifs_rat_pow
    in
    let eps_nf = Array.map translate_ep eps in
    EP.set_rec_sols eps_nf;
    let ep = (module EP : ExpPolyNF) in
    ep
  


  let solve_rec_rs initial sp : RS.t array = 
    let size = List.fold_left (+) 0 (List.map (fun (blk : block) -> Array.length blk.blk_transform) sp) in
    let cf = Array.make size RS.zero in
    let translate_blk_add p = (*Might be better to work with ep's and use that mult rather than had mult.*)
      QQXs.fold (
        fun m coef rs ->
          let mon_rs = BatEnum.fold (
            fun acc (dim, pow) ->
              had_mult acc (had_exp (cf.(dim)) pow)
          ) RS.one (Monomial.enum m) in
          RS.add (RS.mul (lift (N.scalar (ConstRing.scalar coef))) mon_rs) rs
      ) p RS.zero
    in
    let rec aux blocks offset = 
      match blocks with
      | [] -> ()
      | (blk : block) :: blks ->
        let blk_size = Array.length (blk.blk_add) in
        let blk_add = Array.map translate_blk_add blk.blk_add in
        let init = Array.sub initial offset blk_size in
          (*match initial with
          | None -> Array.mapi (fun i _ -> ConstRing.of_dim (i + offset)) blk.blk_add
          | Some ini ->
            Array.mapi (
              fun i ini_v ->
                match ini_v with 
                | None -> ConstRing.of_dim (i + offset)
                | Some v -> ConstRing.scalar v
            ) ini
        in*)
        let sol = solve_mat_rec_rs blk.blk_transform init blk_add in
        for i = 0 to blk_size - 1 do
          cf.(i + offset) <- sol.(i)
        done;
        aux blks (offset + blk_size)
    in
    aux sp 0;
    cf

  let solve_rec ?(initial = None) recs = 
    let size = List.fold_left (+) 0 (List.map (fun (blk : block) -> Array.length blk.blk_transform) recs) in
    let init_opt = 
      match initial with
      | None -> Array.make size None
      | Some x -> x
    in
    let init = Array.mapi (
      fun i ini_opt ->
        match ini_opt with
        | None -> ConstRing.of_dim i
        | Some v -> ConstRing.scalar v
    ) init_opt in
    Array.map translate_rs (solve_rec_rs init recs)

end
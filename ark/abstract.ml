open Syntax
open Linear
open BatPervasives
open Apak

include Log.Make(struct let name = "ark.abstract" end)


(* Sets & maps of constants symbols *)
module K = struct
  type t = const_sym
  let compare = Pervasives.compare
end
module KS = BatSet.Make(K)
module KM = BatMap.Make(K)

exception Nonlinear

(* Affine expressions over constant symbols.  dim_of_const, const_dim, and
   const_of_dim are used to translate between constant symbols and the
   dimensions of the coordinate space. *)
module V = Linear.QQVector
module VS = Putil.Set.Make(Linear.QQVector)
module VM = Putil.Map.Make(Linear.QQVector)

let const_of_dim dim =
  if dim == 0 then None
  else if dim > 0 then Some (Obj.magic (dim - 1))
  else Some (Obj.magic dim)

let dim_of_const k =
  let id = Obj.magic k in
  if id >= 0 then id + 1
  else id

let const_dim = 0

let const_linterm k = Linear.QQVector.of_term k const_dim

let linterm_size linterm = BatEnum.count (V.enum linterm)

let const_of_linterm v =
  let (k, rest) = V.pivot const_dim v in
  if V.equal rest V.zero then Some k
  else None

let linterm_of ark term =
  let open Linear.QQVector in
  let real qq = of_term qq const_dim in
  let pivot_const = pivot const_dim in
  let qq_of term =
    let (k, rest) = pivot_const term in
    if equal rest zero then k
    else raise Nonlinear
  in
  let mul x y =
    try scalar_mul (qq_of x) y
    with Nonlinear -> scalar_mul (qq_of y) x
  in
  let alg = function
    | `Real qq -> real qq
    | `Const k -> of_term QQ.one (dim_of_const k)
    | `Var (_, _) -> raise Nonlinear
    | `Add sum -> List.fold_left add zero sum
    | `Mul sum -> List.fold_left mul (real QQ.one) sum
    | `Binop (`Div, x, y) -> scalar_mul (QQ.inverse (qq_of y)) x
    | `Binop (`Mod, x, y) -> real (QQ.modulo (qq_of x) (qq_of y))
    | `Unop (`Floor, x) -> real (QQ.of_zz (QQ.floor (qq_of x)))
    | `Unop (`Neg, x) -> negate x
  in
  Term.eval ark alg term

let of_linterm ark linterm =
  let open Linear.QQVector in
  enum linterm
  /@ (fun (coeff, dim) ->
      match const_of_dim dim with
      | Some k ->
        if QQ.equal coeff QQ.one then mk_const ark k
        else mk_mul ark [mk_real ark coeff; mk_const ark k]
      | None -> mk_real ark coeff)
  |> BatList.of_enum
  |> mk_add ark

let pp_linterm ark formatter linterm =
  Term.pp ark formatter (of_linterm ark linterm)

let evaluate_term ark interp ?(env=Env.empty) term =
  let f = function
    | `Real qq -> qq
    | `Const k -> interp k
    | `Var (i, _) ->
      begin match Env.find env i with
        | `Real qq -> qq
        | _ -> invalid_arg "evaluate_term"
      end
    | `Add xs -> List.fold_left QQ.add QQ.zero xs
    | `Mul xs -> List.fold_left QQ.mul QQ.one xs
    | `Binop (`Div, dividend, divisor) -> QQ.div dividend divisor
    | `Binop (`Mod, t, modulus) -> QQ.modulo t modulus
    | `Unop (`Floor, t) -> QQ.of_zz (QQ.floor t)
    | `Unop (`Neg, t) -> QQ.negate t
  in
  Term.eval ark f term

let evaluate_linterm interp term =
  (V.enum term)
  /@ (fun (coeff, dim) ->
      match const_of_dim dim with
      | Some const -> QQ.mul (interp const) coeff
      | None -> coeff)
  |> BatEnum.fold QQ.add QQ.zero

(* Compute the GCD of all coefficients in an affine term (with integral
   coefficients) *)
let coefficient_gcd term =
  BatEnum.fold (fun gcd (qq, _) ->
      match QQ.to_zz qq with
      | None -> assert false
      | Some zz -> ZZ.gcd zz gcd)
    ZZ.zero
    (V.enum term)

(* Mapping from constant symbols to appropriately-typed constant values. *)
module Interpretation = struct
  type 'a interpretation =
    { ark : 'a context;
      map : [ `Bool of bool | `Real of QQ.t ] KM.t }

  let empty ark =
    { ark = ark;
      map = KM.empty }

  let add_real k v interp =
    match typ_symbol interp.ark k with
    | `TyReal | `TyInt -> { interp with map = KM.add k (`Real v) interp.map }
    | _ -> invalid_arg "add_real: constant symbol is non-arithmetic"

  let add_bool k v interp =
    match typ_symbol interp.ark k with
    | `TyBool -> { interp with map = KM.add k (`Bool v) interp.map }
    | _ -> invalid_arg "add_boolean: constant symbol is non-boolean"

  let real interp k =
    match KM.find k interp.map with
    | `Real v -> v
    | _ -> invalid_arg "real: constant symbol is not real"

  let bool interp k =
    match KM.find k interp.map with
    | `Bool v -> v
    | _ -> invalid_arg "bool: constant symbol is not Boolean"

  let value interp k = KM.find k interp.map

  let pp formatter interp =
    let pp_val formatter = function
      | `Bool true -> Format.pp_print_string formatter "true"
      | `Bool false -> Format.pp_print_string formatter "false"
      | `Real q -> QQ.pp formatter q
    in
    let pp_elt formatter (key, value) =
      Format.fprintf formatter "@[%a@ => %a@]"
        (pp_symbol interp.ark) key
        pp_val value
    in
    Format.fprintf formatter "[@[%a@]]"
      (ApakEnum.pp_print_enum pp_elt) (KM.enum interp.map)

  let of_model ark model symbols =
    List.fold_left
      (fun interp k ->
         match typ_symbol ark k with
         | `TyReal | `TyInt ->
           add_real
             k
             (model#eval_real (mk_const ark k))
             interp
         | `TyBool ->
           add_bool
             k
             (model#sat (mk_const ark k))
             interp
         | `TyFun _ -> assert false)
      (empty ark)
      symbols

  let enum interp = KM.enum interp.map
end

(* Counter-example based extraction of the affine hull of a formula.  This
   works by repeatedly posing new (linearly independent) equations; each
   equation is either implied by the formula (and gets added to the affine
   hull) or there is a counter-example point which shows that it is not.
   Counter-example points are collecting in a system of linear equations where
   the variables are the coefficients of candidate equations. *)
let affine_hull (smt_ctx : 'a Smt.smt_context) phi constants =
  let ark = smt_ctx#ark in
  let solver = smt_ctx#mk_solver () in
  solver#add [phi];
  let next_row =
    let n = ref (-1) in
    fun () -> incr n; (!n)
  in
  let vec_one = QQVector.of_term QQ.one 0 in
  let rec go equalities mat = function
    | [] -> equalities
    | (k::ks) ->
      let dim = dim_of_const k in
      let row_num = next_row () in
      (* Find a candidate equation which is satisfied by all previously
         sampled points, and where the coefficient of k is 1 *)
      let mat' = QQMatrix.add_row row_num (QQVector.of_term QQ.one dim) mat in
      match Linear.solve mat' (QQVector.of_term QQ.one row_num) with
      | None -> go equalities mat ks
      | Some candidate ->
        solver#push ();
        let candidate_term =
          QQVector.enum candidate
          /@ (fun (coeff, dim) ->
              match const_of_dim dim with
              | Some const -> mk_mul ark [mk_real ark coeff; mk_const ark const]
              | None -> mk_real ark coeff)
          |> BatList.of_enum
          |> mk_add ark
        in
        solver#add [
          mk_not ark (mk_eq ark candidate_term (mk_real ark QQ.zero))
        ];
        match solver#get_model () with
        | `Unknown -> (* give up; return the equalities we have so far *)
          logf ~level:`warn
            "Affine hull timed out (%d equations)"
            (List.length equalities);
          equalities
        | `Unsat -> (* candidate equality is implied by phi *)
          solver#pop 1;
          (* We never choose the same candidate equation again, because the
             system of equations mat' x = 0 implies that the coefficient of k is
             zero *)
          go (candidate_term::equalities) mat' ks
        | `Sat point -> (* candidate equality is not implied by phi *)
          solver#pop 1;
          let point_row =
            List.fold_left (fun row k ->
                QQVector.add_term
                  (point#eval_real (mk_const ark k))
                  (dim_of_const k)
                  row)
              vec_one
              constants
          in
          let mat' = QQMatrix.add_row row_num point_row mat in
          (* We never choose the same candidate equation again, because the
             only solutions to the system of equations mat' x = 0 are
             equations which are satisfied by the sampled point *)
          go equalities mat' (k::ks)
  in
  go [] QQMatrix.zero constants

(* [select_implicant ark m ?env phi] selects an implicant of [phi] such that
   [m,?env |= phi] *)
let select_implicant ark interp ?(env=Env.empty) phi =
  let eval term =
    evaluate_term ark (Interpretation.real interp) ~env term
  in
  let rec go phi =
    match Formula.destruct ark phi with
    | `Tru -> Some []
    | `Fls -> None
    | `Or disjuncts ->
      (* Find satisfied disjunct *)
      let f disjunct phi =
        match disjunct with
        | None -> go phi
        | _ -> disjunct
      in
      List.fold_left f None disjuncts
    | `And conjuncts ->
      (* All conjuncts must be satisfied *)
      let f phi =
        match go phi with
        | Some x -> x
        | None -> raise Not_found
      in
      (try Some (BatList.concat (List.map f conjuncts))
       with Not_found -> None)
    | `Atom (`Eq, s, t) when QQ.equal (eval s) (eval t) -> Some [phi]
    | `Atom (`Leq, s, t) when QQ.leq (eval s) (eval t) -> Some [phi]
    | `Atom (`Lt, s, t) when QQ.lt (eval s) (eval t) -> Some [phi]
    | `Atom (_, _, _) -> None
    | `Proposition (`Const p) ->
      if Interpretation.bool interp p then Some [phi]
      else None
    | `Proposition (`Var v) ->
      begin match Env.find env v with
        | `Bool true -> Some [phi]
        | `Bool false -> None
        | _ -> invalid_arg "select_implicant"
      end
    | `Not psi -> go_not psi
    | `Quantify _ -> invalid_arg "select_implicant"
  and go_not phi =
    match Formula.destruct ark phi with
    | `Tru -> None
    | `Fls -> Some []
    | `Or disjuncts ->
      (* All disjuncts must be unsatisfied *)
      let f phi =
        match go_not phi with
        | Some x -> x
        | None -> raise Not_found
      in
      (try Some (BatList.concat (List.map f disjuncts))
       with Not_found -> None)
    | `And conjuncts ->
      (* Find unsatisfied conjunct *)
      let f conjunct phi =
        match conjunct with
        | None -> go_not phi
        | _ -> conjunct
      in
      List.fold_left f None conjuncts
    | `Atom (`Eq, s, t) when QQ.equal (eval s) (eval t) -> None
    | `Atom (`Leq, s, t) when QQ.leq (eval s) (eval t) -> None
    | `Atom (`Lt, s, t) when QQ.lt (eval s) (eval t) -> None
    | `Atom (_, _, _) -> Some [phi]
    | `Proposition (`Const p) ->
      if Interpretation.bool interp p then None
      else Some [mk_not ark phi]
    | `Proposition (`Var v) ->
      begin match Env.find env v with
        | `Bool true -> None
        | `Bool false -> Some [mk_not ark phi]
        | _ -> invalid_arg "select_implicant"
      end
    | `Not psi -> go psi
    | `Quantify _ -> invalid_arg "select_implicant"
  in
  match go phi with
  | Some phis -> Some (mk_and ark phis)
  | None -> None

let boxify smt_ctx phi terms =
  let ark = smt_ctx#ark in
  let mk_box t ivl =
    let lower =
      match Interval.lower ivl with
      | Some lo -> [mk_leq ark (mk_real ark lo) t]
      | None -> []
    in
    let upper =
      match Interval.upper ivl with
      | Some hi -> [mk_leq ark t (mk_real ark hi)]
      | None -> []
    in
    lower@upper
  in
  match smt_ctx#optimize_box phi terms with
  | `Sat intervals ->
    mk_and ark (List.concat (List.map2 mk_box terms intervals))
  | `Unsat -> mk_false ark
  | `Unknown -> assert false

let map_atoms ark f phi =
  let alg = function
    | `And conjuncts -> mk_and ark conjuncts
    | `Or disjuncts -> mk_or ark disjuncts
    | `Tru -> mk_true ark
    | `Fls -> mk_false ark
    | `Atom (op, s, zero) -> f op s zero
    | `Proposition _ | `Not _ | `Quantify (_, _, _, _) ->
      invalid_arg "map_atoms"
  in
  Formula.eval ark alg phi

(* floor(term/divisor) + offset *)
type int_virtual_term =
  { term : V.t;
    divisor : int;
    offset : ZZ.t }
  [@@ deriving ord]

let pp_int_virtual_term ark formatter vt =
  begin
    if vt.divisor = 1 then
      pp_linterm ark formatter vt.term
    else
      Format.fprintf formatter "@[floor(@[%a@ / %d@])@]"
        (pp_linterm ark) vt.term
        vt.divisor
  end;
  if not (ZZ.equal vt.offset ZZ.zero) then
    Format.fprintf formatter " + %a@]" ZZ.pp vt.offset
  else
    Format.fprintf formatter "@]"

type virtual_term =
  | MinusInfinity
  | PlusEpsilon of V.t
  | Term of V.t
        [@@deriving ord]

let pp_virtual_term ark formatter =
  function
  | MinusInfinity -> Format.pp_print_string formatter "-oo"
  | PlusEpsilon t ->
    Format.fprintf formatter "%a + epsilon" (pp_linterm ark) t
  | Term t -> pp_linterm ark formatter t

(* Loos-Weispfenning virtual substitution *) 
let virtual_substitution ark x virtual_term phi =
  let pivot_term x term =
    V.pivot (dim_of_const x) (linterm_of ark term)
  in
  let replace_atom op s zero =
    assert (Term.equal zero (mk_real ark QQ.zero));

    (* s == s' + ax, x not in fv(s') *)
    let (a, s') = pivot_term x s in
    if QQ.equal a QQ.zero then
      match op with
      | `Eq -> mk_eq ark s zero
      | `Lt -> mk_lt ark s zero
      | `Leq -> mk_leq ark s zero
    else
      let soa = V.scalar_mul (QQ.inverse (QQ.negate a)) s' (* -s'/a *) in
      let mk_sub s t = of_linterm ark (V.add s (V.negate t)) in
      match op, virtual_term with
      | (`Eq, Term t) ->
        (* -s'/a = x = t <==> -s'/a = t *)
        mk_eq ark (mk_sub soa t) zero
      | (`Leq, Term t) ->
        if QQ.lt a QQ.zero then
          (* -s'/a <= x = t <==> -s'/a <= t *)
          mk_leq ark (mk_sub soa t) zero
        else
          (* t = x <= -s'/a <==> t <= -s'/a *)
          mk_leq ark (mk_sub t soa) zero
      | (`Lt, Term t) ->
        if QQ.lt a QQ.zero then
          (* -s'/a < x = t <==> -s'/a < t *)
          mk_lt ark (mk_sub soa t) zero
        else
          (* t = x < -s'/a <==> t < -s'/a *)
          mk_lt ark (mk_sub t soa) zero
      | `Eq, _ -> mk_false ark
      | (_, PlusEpsilon t) ->
        if QQ.lt a QQ.zero then
          (* -s'/a < x = t + eps <==> -s'/a <= t *)
          (* -s'/a <= x = t + eps <==> -s'/a <= t *)
          mk_leq ark (mk_sub soa t) zero
        else
          (* t + eps = x < -s'/a <==> t < -s'/a *)
          (* t + eps = x <= -s'/a <==> t < -s'/a *)
          mk_lt ark (mk_sub t soa) zero
      | (_, MinusInfinity) ->
        if QQ.lt a QQ.zero then
          (* -s'/a < x = -oo <==> false *)
          mk_false ark
        else
          (* -oo = x < -s'/a <==> true *)
          mk_true ark
  in
  map_atoms ark replace_atom phi


(* Model based projection, as in described in Anvesh Komuravelli, Arie
   Gurfinkel, Sagar Chaki: "SMT-based Model Checking for Recursive Programs".
   Given a structure m, a constant symbol x, and a set of
   linear terms T, find a virtual term vt such that
   - vt is -t/a (where ax + t in T) and m |= x = -t/a
   - vt is -t/a + epsilon (where ax + t in T) and m |= -t/a < x and
                          m |= 's/b < x ==> (-s/b <= s/a) for all bx + s in T
   - vt is -oo otherwise *)
let mbp_virtual_term ark m x terms =
  (* The set { -t/a : ax + t in T } *)
  let x_terms =
    let f t terms =
      let (coeff, t') = V.pivot (dim_of_const x) t in
      if QQ.equal coeff QQ.zero then
        terms
      else begin
        VS.add (V.scalar_mul (QQ.negate (QQ.inverse coeff)) t') terms
      end
    in
    VS.fold f terms VS.empty
  in
  let x_val = V.dot m (V.of_term QQ.one (dim_of_const x)) in

  (* First try to find a term t such that m |= x = t *)
  let m_implies_x_eq t =
    QQ.equal x_val (V.dot m t)
  in
  try
    Term (BatEnum.find m_implies_x_eq (VS.enum x_terms))
  with Not_found ->
    (* There is no term t such that m |= x = t.  Try to find a term t such
       that m |= t < x and for all s such that m |= s < x, we have
       m |= s <= t *)
    let f s best =
      let s_val = V.dot m s in
      if QQ.lt s_val x_val then
        match best with
        | Some (t, t_val) when QQ.leq s_val t_val -> Some (t, t_val)
        | Some (_, _) | None -> Some (s, s_val)
      else best
    in
    match VS.fold f x_terms None with
    | Some (t, _) -> PlusEpsilon t
    | None -> MinusInfinity

(* Compute the set of normalized linear terms which appear in a normalized
   formula *)
let terms ark phi =
  let alg = function
    | `And xs | `Or xs -> List.fold_left VS.union VS.empty xs
    | `Atom (_, s, t) ->
      V.add (linterm_of ark s) (V.negate (linterm_of ark t))
      |> VS.singleton
    | `Tru | `Fls -> VS.empty
    | `Proposition _ | `Not _ | `Quantify (_, _, _, _) ->
      invalid_arg "abstract.terms"
  in
  Formula.eval ark alg phi

(* Given a prenex formula phi, compute a pair (qf_pre, psi) such that
   - qf_pre is a quantifier prefix [(Q0, a0);...;(Qn, an)] where each Qi is
     either `Exists or `Forall, and each ai is a Skolem constant
   - psi is negation- and quantifier-free formula, and contains no free
     variables
   - every atom of in psi is either a propositial variable or an arithmetic
     atom of the form t < 0, t <= 0, or t = 0
   - phi is equivalent to Q0 a0.Q1 a1. ... Qn. an. psi
*)
let normalize ark phi =
  let phi = Formula.prenex ark phi in
  let zero = mk_real ark QQ.zero in
  let rec normalize env phi =
    let subst = substitute ark (mk_const ark % Env.find env) in
    match Formula.destruct ark phi with
    | `Not psi -> normalize_not env psi
    | `And conjuncts -> mk_and ark (List.map (normalize env) conjuncts)
    | `Or disjuncts -> mk_or ark (List.map (normalize env) disjuncts)
    | `Tru -> mk_true ark
    | `Fls -> mk_false ark
    | `Atom (`Eq, s, t) -> subst (mk_eq ark (mk_sub ark s t) zero)
    | `Atom (`Leq, s, t) -> subst (mk_leq ark (mk_sub ark s t) zero)
    | `Atom (`Lt, s, t) -> subst (mk_lt ark (mk_sub ark s t) zero)
    | `Proposition (`Var i) -> mk_const ark (Env.find env i)
    | `Proposition (`Const _) -> phi
    | `Quantify (_, _, _, _) -> invalid_arg "normalize: expected prenex"
  and normalize_not env phi =
    let subst = substitute ark (mk_const ark % Env.find env) in
    match Formula.destruct ark phi with
    | `Not psi -> normalize env psi
    | `And conjuncts -> mk_or ark (List.map (normalize_not env) conjuncts)
    | `Or disjuncts -> mk_and ark (List.map (normalize_not env) disjuncts)
    | `Tru -> mk_false ark
    | `Fls -> mk_true ark
    | `Atom (`Eq, s, t) ->
      subst (mk_or ark [mk_lt ark (mk_sub ark s t) zero;
                        mk_lt ark (mk_sub ark t s) zero])
    | `Atom (`Leq, s, t) -> subst (mk_lt ark (mk_sub ark t s) zero)
    | `Atom (`Lt, s, t) -> subst (mk_leq ark (mk_sub ark t s) zero)
    | `Proposition (`Var i) -> mk_not ark (mk_const ark (Env.find env i))
    | `Proposition (`Const _) -> mk_not ark phi
    | `Quantify (_, _, _, _) -> invalid_arg "normalize: expected prenex"
  in
  let rec go env phi =
    match Formula.destruct ark phi with
    | `Quantify (qt, name, typ, psi) ->
      let k = mk_symbol ark ~name (typ :> Syntax.typ) in
      let (qf_pre, psi) = go (Env.push k env) psi in
      ((qt,k)::qf_pre, psi)
    | _ -> ([], normalize env phi)
  in
  go Env.empty phi

(* destruct_normal is safe to apply to a formula that has been normalized *)
let destruct_normal ark phi =
  let zero = mk_real ark QQ.zero in
  let destruct_int term =
    match Term.destruct ark term with
    | `Real q ->
      begin match QQ.to_zz q with
        | Some z -> z
        | None -> invalid_arg "destruct_normal: non-integral value"
      end
    | _ -> invalid_arg "destruct_normal: non-constant"
  in
  match Formula.destruct ark phi with
  | `Quantify (_, _, _, _) -> invalid_arg "destruct_normal: quantification"
  | `And psis -> `And psis
  | `Or psis -> `Or psis
  | `Tru -> `Tru
  | `Fls -> `Fls
  | `Not psi ->
    begin match Formula.destruct ark psi with
      | `Proposition (`Const p) -> `NotProposition p
      | _ -> invalid_arg ("destruct_normal: " ^ (Formula.show ark phi))
    end
  | `Proposition (`Const p) -> `Proposition p
  | `Proposition (`Var _) ->
    invalid_arg "destruct_normal: propositional variable"
  | `Atom (`Eq, s, t) ->
    if not (Term.equal t zero) then invalid_arg "destruct_normal";
    begin match Term.destruct ark s with
    | `Binop (`Mod, dividend, modulus) ->

      (* Divisibility constraint *)
      let modulus = destruct_int modulus in
      `Divides (modulus, linterm_of ark dividend)
    | _ -> `CompareZero (`Eq, linterm_of ark s)
    end
  | `Atom (`Lt, s, t) ->
    if not (Term.equal t zero) then invalid_arg "destruct_normal";
    begin match Term.destruct ark s with
      | `Binop (`Mod, dividend, modulus) ->
        (* Indivisibility constraint: dividend % modulus < 0. *)
        let modulus = destruct_int modulus in
        `NotDivides (modulus, linterm_of ark dividend)

      | `Unop (`Neg, s') ->
        begin match Term.destruct ark s' with
          | `Binop (`Mod, dividend, modulus) ->
            (* Indivisibility constraint: dividend % modulus > 0 *)
            let modulus = destruct_int modulus in
            `NotDivides (modulus, linterm_of ark dividend)
          | _ -> `CompareZero (`Lt, linterm_of ark s)
        end

      | _ -> `CompareZero (`Lt, linterm_of ark s)
    end
  | `Atom (`Leq, s, t) ->
    if not (Term.equal t zero) then invalid_arg "destruct_normal";
    `CompareZero (`Leq, linterm_of ark s)

let destruct_normal ark phi = 
  try destruct_normal ark phi
  with Nonlinear ->
    Log.errorf "Error destructing formula: %a" (Formula.pp ark) phi;
    raise Nonlinear

let mk_divides ark divisor term =
  assert (ZZ.lt ZZ.zero divisor);
  if ZZ.equal divisor ZZ.one then
    mk_true ark
  else
    let gcd = coefficient_gcd term in
    let divisor = QQ.of_zz (ZZ.div divisor gcd) in
    let term = V.scalar_mul (QQ.of_zzfrac ZZ.one gcd) term in

    mk_eq ark
      (mk_mod ark (of_linterm ark term) (mk_real ark divisor))
      (mk_real ark QQ.zero)

let mk_not_divides ark divisor term =
  assert(ZZ.lt ZZ.zero divisor);
  if ZZ.equal divisor ZZ.one then
    mk_false ark
  else
    let gcd = coefficient_gcd term in
    let divisor = QQ.div (QQ.of_zz divisor) (QQ.of_zz gcd) in
    let term = V.scalar_mul (QQ.of_zzfrac ZZ.one gcd) term in

    mk_lt ark
      (mk_neg ark (mk_mod ark (of_linterm ark term) (mk_real ark divisor)))
      (mk_real ark QQ.zero)

let int_virtual_substitution ark x virtual_term phi =
  let zero = mk_real ark QQ.zero in
  (* virtual_term is of the form: floor(t/a) + b *)

  (* Each atom
       (c*x + s) op 0
       [or (b | c*x + s) ]
     Is replaced by a disjunction
       \/_{i=0}^{a-1} (a | t - i) /\ c*(t + a*b - i) + a*s op 0)
       [or (a | t - i) /\ (a*b | c*(t + a*b - i) + a*s) ]

     subst_term i c s is the term c*(t + a*b - i) + a*s)
  *)
  let subst_term i c s =
    let t_plus_ab_minus_i =
      V.add_term
        (QQ.of_zz
           (ZZ.sub
              (ZZ.mul (ZZ.of_int virtual_term.divisor) virtual_term.offset)
              (ZZ.of_int i)))
        const_dim
        virtual_term.term
    in
    V.add
      (V.scalar_mul c t_plus_ab_minus_i)
      (V.scalar_mul (QQ.of_int virtual_term.divisor) s)
  in

  (* Make the divisibility atom (a | t - i) *)
  let divisibility_constraint i =
    if virtual_term.divisor == 1 then
      mk_true ark
    else
      let t_minus_i =
        V.add_term (QQ.of_int (-i)) const_dim virtual_term.term
        |> of_linterm ark
      in
      mk_eq ark
        (mk_mod ark t_minus_i (mk_real ark (QQ.of_int virtual_term.divisor)))
        zero
  in

  let rec subst phi =
    match destruct_normal ark phi with
    | `And psis -> mk_and ark (List.map subst psis)
    | `Or psis -> mk_or ark (List.map subst psis)
    | `Tru -> mk_true ark
    | `Fls -> mk_false ark
    | `Proposition _ | `NotProposition _ -> phi
    | `Divides (delta, s) ->
      let (c, s) = V.pivot (dim_of_const x) s in
      if QQ.equal c QQ.zero then
        mk_divides ark delta s
      else
        (0 -- (virtual_term.divisor - 1))
        /@ (fun i ->
            mk_and ark [mk_divides ark
                          (ZZ.mul (ZZ.of_int virtual_term.divisor) delta)
                          (subst_term i c s);
                        divisibility_constraint i])
        |> BatList.of_enum
        |> mk_or ark

    | `NotDivides (delta, s) ->
      let (c, s) = V.pivot (dim_of_const x) s in
      if QQ.equal c QQ.zero then
        mk_not_divides ark delta s
      else
        (0 -- (virtual_term.divisor - 1))
        /@ (fun i ->
            mk_and ark [mk_not_divides ark
                          (ZZ.mul (ZZ.of_int virtual_term.divisor) delta)
                          (subst_term i c s);
                        divisibility_constraint i])
        |> BatList.of_enum
        |> mk_or ark

    | `CompareZero (op, s) ->
      let (c, s) = V.pivot (dim_of_const x) s in
      let mk_compare =
        match op with
        | `Eq -> mk_eq
        | `Lt -> mk_lt
        | `Leq -> mk_leq
      in
      if QQ.equal c QQ.zero then
        mk_compare ark (of_linterm ark s) zero
      else
        (0 -- (virtual_term.divisor - 1))
        /@ (fun i ->
            mk_and ark [mk_compare ark
                          (of_linterm ark (subst_term i c s))
                          zero;
                        divisibility_constraint i])
        |> BatList.of_enum
        |> mk_or ark
  in
  subst phi

let substitute_real_term ark x t phi =
  begin match typ_symbol ark x with
    | `TyInt | `TyReal -> ()
    | _ -> invalid_arg "substitute_real_term: non-arithmetic constant"
  end;
  let replace_term s =
    let (a, s') = V.pivot (dim_of_const x) s in
    if QQ.equal a QQ.zero then
      s
    else
      V.add s' (V.scalar_mul a t)
  in
  let zero = mk_real ark QQ.zero in
  let rec go phi =
    match destruct_normal ark phi with
    | `And psis -> mk_and ark (List.map go psis)
    | `Or psis -> mk_or ark (List.map go psis)
    | `Tru | `Fls | `Proposition _ | `NotProposition _ -> phi
    | `Divides (delta, s) -> mk_divides ark delta (replace_term s)
    | `NotDivides (delta, s) -> mk_not_divides ark delta (replace_term s)
    | `CompareZero (op, s) ->
      let s = of_linterm ark (replace_term s) in
      match op with
      | `Eq -> mk_eq ark s zero
      | `Lt -> mk_lt ark s zero
      | `Leq -> mk_leq ark s zero
  in
  go phi

let substitute_prop_const ark x x' phi =
  begin match typ_symbol ark x, typ_symbol ark x' with
    | `TyBool, `TyBool -> ()
    | _, _ -> invalid_arg "substitute_prop_const: non-boolean constant"
  end;
  let rec go phi =
    match destruct_normal ark phi with
    | `And psis -> mk_and ark (List.map go psis)
    | `Or psis -> mk_or ark (List.map go psis)
    | `Proposition p -> mk_const ark (if x = p then x' else p)
    | `NotProposition p -> mk_not ark (mk_const ark (if x = p then x' else p))
    | `Divides (_, _) | `NotDivides (_, _) | `CompareZero (_, _)
    | `Tru | `Fls -> phi
  in
  go phi

exception Redundant_path
module Scheme = struct

  type move =
    | MInt of int_virtual_term
    | MReal of V.t
    | MBool of bool
          [@@deriving ord]

  let substitute ark x move phi =
    match move with
    | MInt vt -> int_virtual_substitution ark x vt phi
    | MReal t -> substitute_real_term ark x t phi
    | MBool vb ->
      let replacement = match vb with
        | true -> mk_true ark
        | false -> mk_false ark
      in
      let alg = function
        | `And xs -> mk_and ark xs
        | `Or xs -> mk_or ark xs
        | `Tru -> mk_true ark
        | `Fls -> mk_false ark
        | `Quantify (_, _, _, _) | `Proposition (`Var _) ->
          invalid_arg "substitute"
        | `Not phi -> mk_not ark phi
        | `Atom (`Leq, s, t) -> mk_leq ark s t
        | `Atom (`Lt, s, t) -> mk_lt ark s t
        | `Atom (`Eq, s, t) -> mk_eq ark s t
        | `Proposition (`Const p) when p = x -> replacement
        | `Proposition (`Const p) -> mk_const ark p
      in
      Formula.eval ark alg phi

  let substitute_move ark m x move phi =
    match select_implicant ark m (substitute ark x move phi) with
    | None -> assert false
    | Some x -> x

  let evaluate_move model move =
    match move with
    | MInt vt ->
      begin match QQ.to_zz (evaluate_linterm model vt.term) with
        | None -> assert false
        | Some tv ->
          ZZ.add (Mpzf.fdiv_q tv (ZZ.of_int vt.divisor)) vt.offset
          |> QQ.of_zz
      end
    | MReal t -> evaluate_linterm model t
    | MBool _ -> invalid_arg "evaluate_move"

  let pp_move ark formatter move =
    match move with
    | MInt vt -> pp_int_virtual_term ark formatter vt
    | MReal t -> pp_linterm ark formatter t
    | MBool true -> Format.pp_print_string formatter "true"
    | MBool false -> Format.pp_print_string formatter "false"

  let const_of_move move =
    match move with
    | MReal t -> const_of_linterm t
    | MInt vt ->
      if vt.divisor = 1 then const_of_linterm vt.term
      else None
    | MBool _ -> invalid_arg "const_of_move"

  module MM = BatMap.Make(struct type t = move [@@deriving ord] end)

  type t =
    | SForall of const_sym * const_sym * t
    | SExists of const_sym * (t MM.t)
    | SEmpty

  let pp ark formatter scheme =
    let open Format in
    let rec pp formatter = function
      | SForall (k, sk, t) ->
        fprintf formatter "@[(forall %a:@\n  @[%a@])@]" (pp_symbol ark) sk pp t
      | SExists (k, mm) ->
        let pp_elt formatter (move, scheme) =
          fprintf formatter "%a:@\n  @[%a@]@\n"
            (pp_move ark) move
            pp scheme
        in
        fprintf formatter "@[(exists %a:@\n  @[%a@])@]"
          (pp_symbol ark) k
          (ApakEnum.pp_print_enum pp_elt) (MM.enum mm)
      | SEmpty -> ()
    in
    pp formatter scheme

  let rec size = function
    | SEmpty -> 0
    | SForall (_, _, t) -> 1 + (size t)
    | SExists (_, mm) ->
      MM.enum mm
      /@ (fun (_, t) -> size t)
      |> BatEnum.sum
      |> (+) 1

  let rec nb_paths = function
    | SEmpty -> 1
    | SForall (_, _, t) -> nb_paths t
    | SExists (_, mm) ->
      MM.enum mm
      /@ (fun (_, t) -> nb_paths t)
      |> BatEnum.sum

  let empty = SEmpty

  (* Create a new scheme where the only path is the given path *)
  let mk_path ark path =
    let rec go = function
      | [] -> SEmpty
      | (`Forall k)::path ->
        let sk = mk_symbol ark ~name:(show_symbol ark k) (typ_symbol ark k) in
        SForall (k, sk, go path)
      | (`Exists (k, move))::path ->
        SExists (k, MM.add move (go path) MM.empty)
    in
    go path

  (* Add a path (corresponding to a new instantiation of the existential
     variables of some formula) to a scheme.  Raise Redundant_path if this
     path already belonged to the scheme. *)
  let add_path ark path scheme =

    let rec go path scheme =
      match path, scheme with
      | ([], SEmpty) ->
        (* path was already in scheme *)
        raise Redundant_path

      | (`Forall k::path, SForall (k', sk, scheme)) ->
        assert (k = k');
        SForall (k, sk, go path scheme)

      | (`Exists (k, move)::path, SExists (k', mm)) ->
        assert (k = k');
        let subscheme =
          try go path (MM.find move mm)
          with Not_found -> mk_path ark path
        in
        SExists (k, MM.add move subscheme mm)
      | `Exists (_, _)::_, SForall (_, _, _) | (`Forall _)::_, SExists (_, _) ->
        assert false
      | ([], _) ->
        assert false
      | (_, SEmpty) ->
        assert false
    in
    match scheme with
    | SEmpty -> mk_path ark path
    | _ -> go path scheme

  (* Used for incremental construction of the winning formula:
       (winning_formula scheme phi) = \/_p winning_path_formula p scheme phi *)
  let path_winning_formula ark path scheme phi =
    let rec go path scheme =
      match path, scheme with
      | ([], SEmpty) -> phi
      | (`Forall k::path, SForall (k', sk, scheme)) ->
        assert (k = k');

        let term = V.of_term QQ.one (dim_of_const sk) in
        begin match typ_symbol ark k with
          | `TyBool -> substitute_prop_const ark k sk (go path scheme)
          | _ -> substitute_real_term ark k term (go path scheme)
        end

      | (`Exists (k, move)::path, SExists (k', mm)) ->
        assert (k = k');
        substitute ark k move (go path (MM.find move mm))
      | (_, _) -> assert false
    in
    go path scheme

  (* winning_formula scheme phi is valid iff scheme is a winning scheme for
     the formula phi *)
  let winning_formula ark scheme phi =
    let rec go = function
      | SEmpty -> phi
      | SForall (k, sk, scheme) ->
        let move = V.of_term QQ.one (dim_of_const sk) in
        begin match typ_symbol ark k with
          | `TyBool -> substitute_prop_const ark k sk (go scheme)
          | _ -> substitute_real_term ark k move (go scheme)
        end

      | SExists (k, mm) ->
        MM.enum mm
        /@ (fun (move, scheme) -> substitute ark k move (go scheme))
        |> BatList.of_enum
        |> mk_or ark
    in
    go scheme

  let rec paths = function
    | SEmpty -> [[]]
    | SForall (k, sk, scheme) ->
      List.map (fun path -> (`Forall k)::path) (paths scheme)
    | SExists (k, mm) ->
      BatEnum.fold (fun rest (move, scheme) ->
          (List.map (fun path -> (`Exists (k, move))::path) (paths scheme))
          @rest)
        []
        (MM.enum mm)
end

exception Equal_term of V.t
let select_real_term ark interp x phi =
  let merge (lower1, upper1) (lower2, upper2) =
    let lower =
      match lower1, lower2 with
      | (x, None) | (None, x) -> x
      | (Some (s, s_val, s_strict), Some (t, t_val, t_strict)) ->
        if QQ.lt t_val s_val
        then
          Some (s, s_val, s_strict)
        else
          let strict =
            (QQ.equal t_val s_val && (s_strict || t_strict))
            || t_strict
          in
          Some (t, t_val, strict)
    in
    let upper =
      match upper1, upper2 with
      | (x, None) | (None, x) -> x
      | (Some (s, s_val, s_strict), Some (t, t_val, t_strict)) ->
        if QQ.lt s_val t_val
        then
          Some (s, s_val, s_strict)
        else
          let strict =
            (QQ.equal t_val s_val && (s_strict || t_strict))
            || t_strict
          in
          Some (t, t_val, strict)
    in
    (lower, upper)
  in
  let x_val = Interpretation.real interp x in
  let is_sat op t =
    match op with
    | `Leq -> QQ.leq (evaluate_linterm (Interpretation.real interp) t) QQ.zero
    | `Lt -> QQ.lt (evaluate_linterm (Interpretation.real interp) t) QQ.zero
    | `Eq -> QQ.equal (evaluate_linterm (Interpretation.real interp) t) QQ.zero
  in
  let rec go phi =
    match destruct_normal ark phi with
    | `And xs | `Or xs ->
      List.fold_left (fun a psi -> merge a (go psi)) (None, None) xs
    | `Tru | `Fls | `Proposition _ | `NotProposition _ -> (None, None)
    | `Divides _ | `NotDivides _ -> invalid_arg "select_real_term"
    | `CompareZero (op, t) when (not (is_sat op t)) -> (None, None)
    | `CompareZero (op, t) ->

      let (a, t') = V.pivot (dim_of_const x) t in

      (* Atom is ax + t' op 0 *)
      if QQ.equal QQ.zero a then
        (None, None)
      else
        let toa = V.scalar_mul (QQ.inverse (QQ.negate a)) t' in
        let toa_val = evaluate_linterm (Interpretation.real interp) toa in
        if op = `Eq || (QQ.equal toa_val x_val && op = `Leq) then
          raise (Equal_term toa)
        else if QQ.lt a QQ.zero then
          (* Lower bound *)
          (Some (toa, toa_val, op = `Lt), None)
        else
          (* Upper bound *)
          (None, Some (toa, toa_val, op = `Lt))
  in
  try
    match go phi with
    | (Some (t, _, false), _) | (_, Some (t, _, false)) ->
      (logf ~level:`trace "Found equal(?) term: %a = %a"
         (pp_symbol ark) x
         (pp_linterm ark) t;
       t)
    | (Some (s, _, _), None) ->
      logf ~level:`trace "Found lower bound: %a < %a"
        (pp_linterm ark) s
        (pp_symbol ark) x;
      V.add s (const_linterm (QQ.of_int (1)))
    | (None, Some (t, _, _)) ->
      logf ~level:`trace "Found upper bound: %a < %a"
        (pp_symbol ark) x
        (pp_linterm ark) t;
      V.add t (const_linterm (QQ.of_int (-1)))
    | (Some (s, _, _), Some (t, _, _)) ->
      logf ~level:`trace "Found interval: %a < %a < %a"
        (pp_linterm ark) s
        (pp_symbol ark) x
        (pp_linterm ark) t;
      V.scalar_mul (QQ.of_frac 1 2) (V.add s t)
    | (None, None) -> V.zero (* Value of x is irrelevant *)
  with Equal_term t ->
    (logf ~level:`trace "Found equal term: %a = %a"
       (pp_symbol ark) x
       (pp_linterm ark) t;
     t)

let select_int_term ark interp x phi =
  let merge bound bound' =
    match bound, bound' with
    | (`Lower (s, s_val), `Lower (t, t_val)) ->
        if ZZ.lt t_val s_val then
          `Lower (s, s_val)
        else
          `Lower (t, t_val)
    | (`Lower (t, t_val), _) | (_, `Lower (t, t_val)) -> `Lower (t, t_val)
    | (`Upper (s, s_val), `Upper (t, t_val)) ->
        if ZZ.lt s_val t_val then
          `Upper (s, s_val)
        else
          `Upper (t, t_val)
    | (`Upper (t, t_val), _) | (_, `Upper (t, t_val)) -> `Upper (t, t_val)
    | `None, `None -> `None
  in
  let eval = evaluate_linterm (Interpretation.real interp) in
  let x_val = match QQ.to_zz (Interpretation.real interp x) with
    | Some zz -> zz
    | None -> assert false
  in
  let is_sat op t =
    match op with
    | `Leq -> QQ.leq (eval t) QQ.zero
    | `Lt -> QQ.lt (eval t) QQ.zero
    | `Eq -> QQ.equal (eval t) QQ.zero
  in
  (* delta = gcd { lcm(d,a) : d | ax + t or not(d | ax + t) in atoms }.  If
     [[vt]](m) = [[x]](m) mod delta, then for every divisilibity atom
       d | ax + t
     which appears in phi, we have
       m |= (d | ax + t)   <==>   m |= (d | a(vt) + t *)
  let delta =
    let rec go phi =
      match destruct_normal ark phi with
      | `And xs | `Or xs -> List.fold_left ZZ.lcm ZZ.one (List.map go xs)
      | `Tru | `Fls | `CompareZero (_, _)
      | `Proposition _ | `NotProposition _ ->
        ZZ.one
      | `Divides (divisor, t) | `NotDivides (divisor, t) ->
        let (a, t) = V.pivot (dim_of_const x) t in
        let a = match QQ.to_zz a with
          | None -> assert false
          | Some zz -> ZZ.abs zz
        in
        if ZZ.equal ZZ.zero a then ZZ.one
        else ZZ.lcm divisor a
    in
    go phi
  in
  let evaluate_vt vt =
    let real_val =
      Scheme.evaluate_move (Interpretation.real interp) (Scheme.MInt vt)
    in
    match QQ.to_zz real_val with
    | Some v -> v
    | None -> assert false
  in
  let rec go phi =
    match destruct_normal ark phi with
    | `And xs | `Or xs -> List.fold_left merge `None (List.map go xs)
    | `Tru | `Fls | `Proposition _ | `NotProposition _ -> `None
    | `Divides (_, _) | `NotDivides (_, _) -> `None
    | `CompareZero (op, t) when is_sat op t ->
      let (a, t) = V.pivot (dim_of_const x) t in
      let a = match QQ.to_zz a with
        | None -> assert false
        | Some zz -> match ZZ.to_int zz with
          | None -> assert false
          | Some z -> z
      in
      if a = 0 then
        `None
      else if a > 0 then
        (* ax + t (<|<=) 0 --> upper bound of floor(-t/a) *)
        (* x (<|<=) floor(-t/a) + ([[x - floor(-t/a)]] mod delta) - delta *)
        let numerator =
          if op = `Lt then
            (* a*floor(((numerator-1) / a) < numerator *)
            V.add_term (QQ.of_int (-1)) const_dim (V.negate t)
          else
            V.negate t
        in

        let rhs_val = (* [[floor(numerator / a)]] *)
          match QQ.to_zz (eval numerator) with
          | Some num -> Mpzf.fdiv_q num (ZZ.of_int a)
          | None -> assert false
        in
        let vt =
          { term = numerator;
            divisor = a;
            offset = Mpzf.cdiv_r (ZZ.sub x_val rhs_val) delta }
        in
        let vt_val = evaluate_vt vt in

        assert (ZZ.equal (ZZ.modulo (ZZ.sub vt_val x_val) delta) ZZ.zero);
        assert (ZZ.leq x_val vt_val);
        begin
          let axv = ZZ.mul (ZZ.of_int a) vt_val in
          let tv = match QQ.to_zz (eval t) with
            | Some zz -> ZZ.negate zz
            | None -> assert false
          in
          match op with
          | `Lt -> assert (ZZ.lt axv tv)
          | `Leq -> assert (ZZ.leq axv tv)
          | `Eq -> assert (ZZ.equal axv tv)
        end;
        `Upper (vt, evaluate_vt vt)
      else
        let a = -a in

        (* (-a)x + t <= 0 --> lower bound of ceil(t/a) = floor((t+a-1)/a) *)
        (* (-a)x + t < 0 --> lower bound of ceil(t+1/a) = floor((t+a)/a) *)
        let numerator =
          if op = `Lt then
            V.add_term (QQ.of_int a) const_dim t
          else
            V.add_term (QQ.of_int (a - 1)) const_dim t
        in
        let rhs_val = (* [[floor(numerator / a)]] *)
          match QQ.to_zz (eval numerator) with
          | Some num -> Mpzf.fdiv_q num (ZZ.of_int a)
          | None -> assert false
        in

        let vt =
          { term = numerator;
            divisor = a;
            offset = Mpzf.fdiv_r (ZZ.sub x_val rhs_val) delta }
        in
        let vt_val = evaluate_vt vt in

        assert (ZZ.equal (ZZ.modulo (ZZ.sub vt_val x_val) delta) ZZ.zero);
        assert (ZZ.leq vt_val x_val);
        begin
          let axv = ZZ.mul (ZZ.of_int a) vt_val in
          let tv = match QQ.to_zz (eval t) with
            | Some zz -> zz
            | None -> assert false
          in
          match op with
          | `Lt -> assert (ZZ.lt tv axv)
          | `Leq -> assert (ZZ.leq tv axv)
          | `Eq -> assert (ZZ.equal tv axv)
        end;
        `Lower (vt, evaluate_vt vt)

    | `CompareZero (op, t) -> `None
  in
  let vt_val vt =
    let tval = match QQ.to_zz (eval vt.term) with
      | Some zz -> zz
      | None -> assert false
    in
    ZZ.add (Mpzf.fdiv_q tval (ZZ.of_int vt.divisor)) vt.offset
  in
  match go phi with
  | `Lower (vt, _) ->
    logf ~level:`trace "Found lower bound: %a < %a"
      (pp_int_virtual_term ark) vt
      (pp_symbol ark) x;
    assert (ZZ.equal (Mpzf.fdiv_r x_val delta) (Mpzf.fdiv_r (vt_val vt) delta));
    vt
  | `Upper (vt, _)->
    logf ~level:`trace "Found upper bound: %a < %a"
      (pp_symbol ark) x
      (pp_int_virtual_term ark) vt;
    assert (ZZ.equal (Mpzf.fdiv_r x_val delta) (Mpzf.fdiv_r (vt_val vt) delta));
    vt
  | `None ->
    logf ~level:`trace "Irrelevant: %a" (pp_symbol ark) x;
    (* Value of x is irrelevant *)
    { term = V.zero; divisor = 1; offset = ZZ.zero }

(* Counter-strategy synthesis *)
module CSS = struct

  type 'a ctx =
    { formula : 'a formula;
      not_formula : 'a formula; (* Negated formula *)
      mutable scheme : Scheme.t; (* scheme for formula *)

      (* solver for the *negation* of the winning formula for scheme (unsat
         iff there is a winning SAT strategy for formula which conforms to
         scheme) *)
      solver : 'a Smt.smt_solver;
      smt : 'a Smt.smt_context;
      ark : 'a context;
    }

  let reset ctx =
    ctx.solver#reset ();
    ctx.scheme <- Scheme.SEmpty

  let add_path ctx path =
    let ark = ctx.ark in
    try
      ctx.scheme <- Scheme.add_path ark path ctx.scheme;
      let win =
        Scheme.path_winning_formula ark path ctx.scheme ctx.formula
      in
      ctx.solver#add [mk_not ark win]
    with Redundant_path -> ()

  (* Check if a given scheme is winning.  If not, synthesize a
     counter-strategy. *)
  let get_counter_strategy select_term ?(parameters=None) ctx =
    logf ~level:`trace "%a" (Scheme.pp ctx.ark) ctx.scheme;
    let parameters =
      match parameters with
      | Some p -> p
      | None   -> Interpretation.empty ctx.ark
    in
    match ctx.solver#get_model () with
    | `Unsat ->
      logf "Winning formula is valid";
      `Unsat
    | `Unknown -> `Unknown
    | `Sat m ->
      logf "Winning formula is not valid";

      (* Using the model m, synthesize a counter-strategy which beats the
         strategy scheme.  This is done by traversing the scheme: on the way
         down, we build a model of the *negation* of the formula using the
         labels on the path to the root.  On the way up, we find elimination
         terms for each universally-quantified variable using model-based
         projection.  *)
      let rec counter_strategy path_model scheme =
        let open Scheme in
        logf ~level:`trace "Path model: %a" Interpretation.pp path_model;
        match scheme with
        | SForall (k, sk, scheme) ->
          let path_model =
            match typ_symbol ctx.ark k with
            | `TyReal | `TyInt ->
              Interpretation.add_real
                k
                (m#eval_real (mk_const ctx.ark sk))
                path_model
            | `TyBool ->
              Interpretation.add_bool
                k
                (m#sat (mk_const ctx.ark sk))
                path_model
            | `TyFun _ -> assert false
          in
          logf ~level:`trace "Forall %a (%a)"
            (pp_symbol ctx.ark) k
            (pp_symbol ctx.ark) sk;
          let (counter_phi, counter_paths) =
            counter_strategy path_model scheme
          in
          logf ~level:`trace "Select term from: %a" (Formula.pp ctx.ark) counter_phi;
          let move = select_term path_model k counter_phi in
          logf ~level:`trace "Found move: %a = %a"
            (pp_symbol ctx.ark) k
            (Scheme.pp_move ctx.ark) move;
          let counter_phi =
            Scheme.substitute_move ctx.ark path_model k move counter_phi
          in
          let counter_paths =
            List.map (fun path -> (`Exists (k, move))::path) counter_paths
          in
          (counter_phi, counter_paths)
        | SExists (k, mm) ->
          let (counter_phis, paths) =
            MM.enum mm
            /@ (fun (move, scheme) ->
                let path_model =
                  match move with
                  | Scheme.MBool bool_val ->
                    Interpretation.add_bool k bool_val path_model
                  | _ ->
                    let mv =
                      Scheme.evaluate_move (Interpretation.real path_model) move
                    in
                    Interpretation.add_real k mv path_model
                in
                let (counter_phi, counter_paths) =
                  counter_strategy path_model scheme
                in
                let counter_phi =
                  Scheme.substitute_move ctx.ark path_model k move counter_phi
                in
                let counter_paths =
                  List.map (fun path -> (`Forall k)::path) counter_paths
                in
                (counter_phi, counter_paths))
            |> BatEnum.uncombine
          in
          (mk_and ctx.ark (BatList.of_enum counter_phis),
           BatList.concat (BatList.of_enum paths))
        | SEmpty ->
          let phi_implicant =
            let implicant =
              select_implicant ctx.ark path_model ctx.not_formula
            in
            match implicant with
            | Some x -> x
            | None -> assert false
          in
          logf ~level:`trace "Path model: %a" Interpretation.pp path_model;
          logf ~level:`trace "Implicant: %a" (Formula.pp ctx.ark) phi_implicant;
          (phi_implicant, [[]])
      in
      `Sat (snd (counter_strategy parameters ctx.scheme))

  (* Check to see if the matrix of a prenex formula is satisfiable.  If it is,
     initialize a sat/unsat strategy scheme pair. *)
  let initialize_pair select_term smt_ctx qf_pre phi =
    match smt_ctx#get_model phi with
    | `Unsat -> `Unsat
    | `Unknown -> `Unknown
    | `Sat m ->
      logf "Found initial model";
      let ark = smt_ctx#ark in
      let phi_model = Interpretation.of_model ark m (List.map snd qf_pre) in

      (* Create paths for sat_scheme & unsat_scheme *)
      let f (qt, x) (sat_path, unsat_path, phi) =
        let move = select_term phi_model x phi in
        let (sat_path, unsat_path) = match qt with
          | `Exists ->
            ((`Exists (x, move))::sat_path,
             (`Forall x)::unsat_path)
          | `Forall ->
            ((`Forall x)::sat_path,
             (`Exists (x, move))::unsat_path)
        in
        (sat_path, unsat_path, Scheme.substitute ark x move phi)
      in
      let (sat_path, unsat_path, _) = List.fold_right f qf_pre ([], [], phi) in
      let not_phi = snd (normalize ark (mk_not ark phi)) in
      let sat_ctx =
        let scheme = Scheme.mk_path ark sat_path in
        let win =
          Scheme.path_winning_formula ark sat_path scheme phi
        in
        let solver = smt_ctx#mk_solver () in
        solver#add [mk_not ark win];
        { formula = phi;
          not_formula = not_phi;
          scheme = scheme;
          solver = solver;
          smt = smt_ctx;
          ark = ark }
      in
      let unsat_ctx =
        let scheme = Scheme.mk_path ark unsat_path in
        let win =
          Scheme.path_winning_formula ark unsat_path scheme not_phi
        in
        let solver = smt_ctx#mk_solver () in
        solver#add [mk_not ark win];
        { formula = not_phi;
          not_formula = phi;
          scheme = scheme;
          solver = solver;
          smt = smt_ctx;
          ark = ark }
      in
      logf "Initial SAT strategy:@\n%a"
        (Scheme.pp ark) sat_ctx.scheme;
      logf "Initial UNSAT strategy:@\n%a"
        (Scheme.pp ark) unsat_ctx.scheme;
      `Sat (sat_ctx, unsat_ctx)

  let is_sat select_term sat_ctx unsat_ctx =
    let round = ref 0 in
    let old_paths = ref (-1) in
    let rec is_sat () =
      incr round;
      logf ~level:`trace ~attributes:[`Blue;`Bold] "Round %d: Sat [%d/%d], Unsat [%d/%d]"
        (!round)
        (Scheme.size sat_ctx.scheme)
        (Scheme.nb_paths sat_ctx.scheme)
        (Scheme.size unsat_ctx.scheme)
              (Scheme.nb_paths unsat_ctx.scheme);
      let paths = Scheme.nb_paths sat_ctx.scheme in
      assert (paths > !old_paths);
      old_paths := paths;
      logf ~attributes:[`Blue;`Bold] "Checking if SAT wins (%d)"
        (Scheme.nb_paths sat_ctx.scheme);
      match get_counter_strategy select_term sat_ctx with
      | `Sat paths -> (List.iter (add_path unsat_ctx) paths; is_unsat ())
      | `Unsat -> `Sat
      | `Unknown -> `Unknown
    and is_unsat () =
      logf ~attributes:[`Blue;`Bold] "Checking if UNSAT wins (%d)"
        (Scheme.nb_paths unsat_ctx.scheme);
      match get_counter_strategy select_term unsat_ctx with
      | `Sat paths -> (List.iter (add_path sat_ctx) paths; is_sat ())
      | `Unsat -> `Unsat
      | `Unknown -> `Unknown
    in
    is_sat ()

  let max_improve_rounds = ref 10

  (* Try to find a "good" initial model of phi by solving a non-accumulating
     version of the satisfiability game.  This game can go into an infinite
     loop (paper beats rock beats scissors beats paper...), so we detect
     cycles by saving every strategy we've found and quitting when we get a
     repeat or when we hit max_improve_rounds. *)
  let initialize_pair select_term smt_ctx qf_pre phi =
    let unsat_scheme = ref Scheme.empty in
    let ark = smt_ctx#ark in
    match initialize_pair select_term smt_ctx qf_pre phi with
    | `Unsat -> `Unsat
    | `Unknown -> `Unknown
    | `Sat (sat_ctx, unsat_ctx) ->
      let round = ref 0 in
      let rec is_sat () =
        incr round;
        logf "Improve round: %d" (!round);
        logf ~attributes:[`Blue;`Bold] "Checking if SAT wins (%d)"
          (Scheme.size sat_ctx.scheme);
        if (!round) = (!max_improve_rounds) then
          `Sat (sat_ctx, unsat_ctx)
        else
          match get_counter_strategy select_term sat_ctx with
          | `Sat [path] ->
            begin
              try
                unsat_scheme := Scheme.add_path ark path (!unsat_scheme);
                reset unsat_ctx;
                add_path unsat_ctx path;
                is_unsat ()
              with Redundant_path -> `Sat (sat_ctx, unsat_ctx)
            end
          | `Sat _ -> assert false
          | `Unsat -> `Sat (sat_ctx, unsat_ctx)
          | `Unknown -> `Unknown
      and is_unsat () =
        logf ~attributes:[`Blue;`Bold] "Checking if UNSAT wins (%d)"
          (Scheme.size unsat_ctx.scheme);
        match get_counter_strategy select_term unsat_ctx with
        | `Sat paths -> (reset sat_ctx;
                         List.iter (add_path sat_ctx) paths;
                         is_sat ())
        | `Unsat -> `Unsat
        | `Unknown -> `Unknown
      in
      is_sat ()
end

let aqsat_forward smt_ctx qf_pre phi =
  let ark = smt_ctx#ark in
  let select_term model x phi =
    match typ_symbol ark x with
    | `TyInt -> Scheme.MInt (select_int_term ark model x phi)
    | `TyReal -> Scheme.MReal (select_real_term ark model x phi)
    | `TyBool -> Scheme.MBool (Interpretation.bool model x)
    | `TyFun (_, _) -> assert false
  in

  (* If the quantifier prefix leads with an existential, check satisfiability
     of the negated sentence instead, then negate the result.  We may now
     assume that the outer-most quantifier is universal. *)
  let (qf_pre, phi, negate) =
    match qf_pre with
    | (`Exists, _)::_ ->
      let phi = snd (normalize ark (mk_not ark phi)) in
      let qf_pre =
        List.map (function
            | (`Exists, x) -> (`Forall, x)
            | (`Forall, x) -> (`Exists, x))
          qf_pre
      in
      (qf_pre, phi, true)
    | _ ->
      (qf_pre, phi, false)
  in

  match CSS.initialize_pair select_term smt_ctx qf_pre phi with
  | `Unsat -> if negate then `Sat else `Unsat
  | `Unknown -> `Unknown
  | `Sat (sat_ctx, unsat_ctx) ->
    let not_phi = sat_ctx.CSS.not_formula in
    let param_substitution param_interp =
      substitute_const ark (fun sym ->
          try
            begin match Interpretation.value param_interp sym with
              | `Real qq -> (mk_real ark qq :> ('a, typ) expr)
              | `Bool true -> (mk_true ark :> ('a, typ) expr)
              | `Bool false -> (mk_false ark :> ('a, typ) expr)
            end
          with Not_found -> mk_const ark sym)
    in
    let assert_param_constraints ctx parameter_interp =
      let open CSS in
      BatEnum.iter (function
          | (k, `Real qv) ->
            ctx.solver#add [mk_eq ark (mk_const ark k) (mk_real ark qv)]
          | (k, `Bool false) ->
            ctx.solver#add [mk_not ark (mk_const ark k)]
          | (k, `Bool true) ->
            ctx.solver#add [mk_const ark k])
        (Interpretation.enum parameter_interp)
    in
    let mk_sat_ctx scheme parameter_interp =
      let open CSS in
      let ctx =
        { formula = phi;
          not_formula = not_phi;
          scheme = scheme;
          solver = smt_ctx#mk_solver ();
          smt = smt_ctx;
          ark = ark }
      in
      let win =
        Scheme.winning_formula ark scheme phi
        |> param_substitution parameter_interp
      in
      ctx.solver#add [mk_not ark win];
      assert_param_constraints ctx parameter_interp;
      ctx
    in
    let mk_unsat_ctx scheme parameter_interp =
      let open CSS in
      let ctx =
        { formula = not_phi;
          not_formula = phi;
          scheme = scheme;
          solver = smt_ctx#mk_solver ();
          smt = smt_ctx;
          ark = ark }
      in
      let win =
        Scheme.winning_formula ark scheme not_phi
        |> param_substitution parameter_interp
      in
      ctx.solver#add [mk_not ark win];
      assert_param_constraints ctx parameter_interp;
      ctx
    in

    (* Peel leading existential quantifiers off of a scheme.  Fails if there
       is more than one move for an existential in the prefix.  *)
    let rec existential_prefix = function
      | Scheme.SExists (k, mm) ->
        begin match BatList.of_enum (Scheme.MM.enum mm) with
          | [(move, scheme)] ->
            let (ex_pre, sub_scheme) = existential_prefix scheme in
            ((k, move)::ex_pre, sub_scheme)
          | _ -> assert false
        end
      | scheme -> ([], scheme)
    in
    let rec universal_prefix = function
      | Scheme.SForall (k, _, scheme) -> k::(universal_prefix scheme)
      | _ -> []
    in
    let scheme_of_paths paths =
      List.fold_left
        (fun scheme path ->
           try Scheme.add_path ark path scheme
           with Redundant_path -> scheme)
        Scheme.empty
        paths
    in

    (* Compute a winning strategy for the remainder of the game, after the
       prefix play determined by parameter_interp.  scheme is an initial
       candidate strategy for one of the players, which begins with
       universals. *)
    let rec solve_game polarity param_interp ctx =
      logf ~attributes:[`Green] "Solving game %s (%d/%d)"
        (if polarity then "SAT" else "UNSAT")
        (Scheme.nb_paths ctx.CSS.scheme)
        (Scheme.size ctx.CSS.scheme);
      logf ~level:`trace "Parameters: %a" Interpretation.pp param_interp;
      let res =
        try
          CSS.get_counter_strategy select_term ~parameters:(Some param_interp) ctx
        with Not_found -> assert false
      in
      match res with
      | `Unknown -> `Unknown
      | `Unsat ->
        (* No counter-strategy to the strategy of the active player => active
           player wins *)
        `Sat ctx.CSS.scheme
      | `Sat paths ->
        let unsat_scheme = scheme_of_paths paths in
        let (ex_pre, sub_scheme) = existential_prefix unsat_scheme in
        let param_interp' =
          List.fold_left (fun interp (k, move) ->
              match move with
              | Scheme.MBool bv -> Interpretation.add_bool k bv interp
              | move ->
                Interpretation.add_real
                  k
                  (Scheme.evaluate_move (Interpretation.real interp) move)
                  interp)
            param_interp
            ex_pre
        in
        let sub_ctx =
          if polarity then
            mk_unsat_ctx sub_scheme param_interp'
          else
            mk_sat_ctx sub_scheme param_interp'
        in
        match solve_game (not polarity) param_interp' sub_ctx with
        | `Unknown -> `Unknown
        | `Sat scheme ->
          (* Inactive player wins *)
          let scheme =
            List.fold_right
              (fun (k, move) scheme ->
                 let mm = Scheme.MM.add move scheme Scheme.MM.empty in
                 Scheme.SExists (k, mm))
              ex_pre
              scheme
          in
          `Unsat scheme
        | `Unsat scheme' ->
          (* There is a counter-strategy for the strategy of the inactive
             player => augment strategy for the active player & try again *)
          let open CSS in
          let forall_prefix =
            List.map (fun x -> `Forall x) (universal_prefix ctx.scheme)
          in
          let add_path path =
            try
              let path = forall_prefix@path in
              ctx.scheme <- Scheme.add_path ark path ctx.scheme;
              let win =
                Scheme.path_winning_formula ark path ctx.scheme ctx.formula
                |> param_substitution param_interp
              in
              ctx.solver#add [mk_not ark win]
            with Redundant_path -> ()
          in
          List.iter add_path (Scheme.paths scheme');
          solve_game polarity param_interp ctx
    in
    match solve_game true (Interpretation.empty ark) sat_ctx with
    | `Unknown -> `Unknown
    | `Sat _ -> if negate then `Unsat else `Sat
    | `Unsat _ -> if negate then `Sat else `Unsat

let aqsat_core smt_ctx qf_pre phi =
  let ark = smt_ctx#ark in
  let select_term model x phi =
    match typ_symbol ark x with
    | `TyInt -> Scheme.MInt (select_int_term ark model x phi)
    | `TyReal -> Scheme.MReal (select_real_term ark model x phi)
    | `TyBool -> Scheme.MBool (Interpretation.bool model x)
    | `TyFun (_, _) -> assert false
  in
  match CSS.initialize_pair select_term smt_ctx qf_pre phi with
  | `Unsat -> `Unsat
  | `Unknown -> `Unknown
  | `Sat (sat_ctx, unsat_ctx) ->
    CSS.reset unsat_ctx;
    CSS.is_sat select_term sat_ctx unsat_ctx

let aqsat smt_ctx phi =
  let ark = smt_ctx#ark in
  let constants = fold_constants KS.add phi KS.empty in
  let (qf_pre, phi) = normalize ark phi in
  let qf_pre =
    (List.map (fun k -> (`Exists, k)) (KS.elements constants))@qf_pre
  in
  aqsat_core smt_ctx qf_pre phi

let aqsat_forward smt_ctx phi =
  let ark = smt_ctx#ark in
  let constants = fold_constants KS.add phi KS.empty in
  let (qf_pre, phi) = normalize ark phi in
  let qf_pre =
    (List.map (fun k -> (`Exists, k)) (KS.elements constants))@qf_pre
  in
  aqsat_forward smt_ctx qf_pre phi

let maximize_feasible smt_ctx phi t =
  let ark = smt_ctx#ark in
  let objective_constants = fold_constants KS.add t KS.empty in
  let constants = fold_constants KS.add phi objective_constants in
  let (qf_pre, phi) = normalize ark phi in
  let qf_pre =
    ((List.map (fun k -> (`Exists, k)) (KS.elements constants))@qf_pre)
  in

  (* First, check if the objective function is unbounded.  This is done by
     checking satisfiability of the formula:
       forall i. exists ks. phi /\ t >= i
  *)
  let objective = mk_symbol ark ~name:"objective" `TyReal in
  let qf_pre_unbounded = (`Forall, objective)::qf_pre in
  let phi_unbounded =
    mk_and ark [
      phi;
      mk_leq ark (mk_sub ark (mk_const ark objective) t) (mk_real ark QQ.zero)
    ]
  in
  let not_phi_unbounded =
    snd (normalize ark (mk_not ark phi_unbounded))
  in
  (* Always select [[objective]](m) as the value of objective *)
  let select_term m x phi =
    if x = objective then
      Scheme.MReal (const_linterm (Interpretation.real m x))
    else
      match typ_symbol ark x with
      | `TyInt -> Scheme.MInt (select_int_term ark m x phi)
      | `TyReal -> Scheme.MReal (select_real_term ark m x phi)
      | `TyBool -> Scheme.MBool (Interpretation.bool m x)
      | `TyFun (_, _) -> assert false
  in
  CSS.max_improve_rounds := 1;
  let init =
    CSS.initialize_pair select_term smt_ctx qf_pre_unbounded phi_unbounded
  in
  match init with
  | `Unsat -> `MinusInfinity
  | `Unknown -> `Unknown
  | `Sat (sat_ctx, unsat_ctx) ->
    (* Skolem constant associated with the (universally quantified) objective
       bound *)
    let objective_skolem =
      match sat_ctx.CSS.scheme with
      | Scheme.SForall (_, sk, _) -> sk
      | _ -> assert false
    in
    let rec check_bound bound =
      begin
        match bound with
        | None -> ()
        | Some b ->
          CSS.reset unsat_ctx;
          sat_ctx.CSS.solver#add [
            mk_lt ark (mk_const ark objective_skolem) (mk_real ark b)
          ]
      end;
      match CSS.is_sat select_term sat_ctx unsat_ctx with
      | `Unknown -> `Unknown
      | `Sat ->
        begin match bound with
          | Some b -> `Bounded b
          | None -> `Infinity
        end
      | `Unsat ->

        (* Find the largest constant which has been selected as an (UNSAT)
           move for the objective bound, and the associated sub-scheme *)
        let (opt, opt_scheme) = match unsat_ctx.CSS.scheme with
          | Scheme.SExists (_, mm) ->
            BatEnum.filter (fun (move, scheme) ->
                let move_val = match Scheme.const_of_move move with
                  | Some qq -> qq
                  | None -> assert false
                in
                let win =
                  let win_not_unbounded =
                    Scheme.winning_formula ark scheme not_phi_unbounded
                  in
                  mk_and
                    ark
                    [mk_not ark win_not_unbounded;
                     mk_eq ark (mk_real ark move_val) (mk_const ark objective)]
                in
                smt_ctx#is_sat win = `Unsat)
              (Scheme.MM.enum mm)
            /@ (fun (v, scheme) -> match Scheme.const_of_move v with
                | Some qq -> (qq, scheme)
                | None -> assert false)
            |> BatEnum.reduce (fun (a, a_scheme) (b, b_scheme) ->
                if QQ.lt a b then (b, b_scheme)
                else (a, a_scheme))
          | _ -> assert false
        in

        logf "Objective function is bounded by %a" QQ.pp opt;

        (* Get the negation of the winning formula for SAT corresponding to
           the sub-scheme rooted below all of the constant symbols which
           appear in the objective.  This formula is weaker than phi, and the
           constant symbols in the objective are not bound. *)
        let bounded_phi =
          let open Scheme in
          let rec go scheme =
            match scheme with
            | SEmpty -> SEmpty
            | SForall (k, sk, subscheme) ->
              if KS.mem k objective_constants then go subscheme
              else scheme
            | SExists (_, _) -> scheme
          in
          (Scheme.winning_formula ark (go opt_scheme) not_phi_unbounded)
          |> mk_not ark
        in
        logf "Bounded phi:@\n%a" (Formula.pp ark) bounded_phi;
        begin match smt_ctx#optimize_box bounded_phi [t] with
          | `Unknown ->
            Log.errorf "Failed to optimize - returning conservative bound";
            begin match bound with
              | Some b -> `Bounded b
              | None -> `Infinity
            end
          | `Sat [ivl] ->
            begin match bound, Interval.upper ivl with
              | Some b, Some x ->
                logf "Bound %a --> %a" QQ.pp b QQ.pp x;
                assert (QQ.lt x b)
              | _, None -> assert false
              | None, _ -> ()
            end;
            check_bound (Interval.upper ivl)
          | `Unsat | `Sat _ -> assert false
        end
    in
    check_bound None
let maximize smt_ctx phi t =
  match aqsat smt_ctx phi with
  | `Sat -> maximize_feasible smt_ctx phi t
  | `Unsat -> `MinusInfinity
  | `Unknown -> `Unknown

exception Unknown
let qe_mbp smt_ctx phi =
  let ark = smt_ctx#ark in
  let (qf_pre, phi) = normalize ark phi in
  let exists x phi =
    let solver = smt_ctx#mk_solver () in
    let disjuncts = ref [] in
    let constants = KS.elements (fold_constants KS.add phi KS.empty) in
    let terms = terms ark phi in
    let rec loop () =
      match solver#get_model () with
      | `Sat m ->
        let model =
          List.fold_right
            (fun k v ->
               V.add_term
                 (m#eval_real (mk_const ark k))
                 (dim_of_const k)
                 v)
            constants
            (const_linterm QQ.one)
        in
        let vt = mbp_virtual_term ark model x terms in
        let psi = virtual_substitution ark x vt phi in
        disjuncts := psi::(!disjuncts);
        solver#add [mk_not ark psi];
        loop ()
      | `Unsat -> mk_or ark (!disjuncts)
      | `Unknown -> raise Unknown
    in
    solver#add [phi];
    loop ()
  in
  let qe (qt, x) phi =
    match qt with
    | `Exists ->
      exists x (snd (normalize ark phi))
    | `Forall ->
      mk_not ark (exists x (snd (normalize ark (mk_not ark phi))))
  in
  List.fold_right qe qf_pre phi


let easy_sat smt_ctx phi =
  let ark = smt_ctx#ark in
  let constants = fold_constants KS.add phi KS.empty in
  let (qf_pre, phi) = normalize ark phi in
  let qf_pre =
    (List.map (fun k -> (`Exists, k)) (KS.elements constants))@qf_pre
  in
  let select_term model x phi =
    match typ_symbol ark x with
    | `TyInt -> Scheme.MInt (select_int_term ark model x phi)
    | `TyReal -> Scheme.MReal (select_real_term ark model x phi)
    | `TyBool -> Scheme.MBool (Interpretation.bool model x)
    | `TyFun (_, _) -> assert false
  in
  match CSS.initialize_pair select_term smt_ctx qf_pre phi with
  | `Unsat -> `Unsat
  | `Unknown -> `Unknown
  | `Sat (sat_ctx, unsat_ctx) ->
    match CSS.get_counter_strategy select_term sat_ctx with
    | `Unsat -> `Sat
    | `Unknown -> `Unknown
    | `Sat _ -> `Unknown

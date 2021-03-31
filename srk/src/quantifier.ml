open Syntax
open Linear
open BatPervasives

include Log.Make(struct let name = "srk.quantifier" end)

exception Equal_term of Linear.QQVector.t
 
type quantifier_prefix = ([`Forall | `Exists] * symbol) list

module V = Linear.QQVector
module VS = BatSet.Make(Linear.QQVector)
module VM = BatMap.Make(Linear.QQVector)
module ZZVector = Linear.ZZVector
module IntSet = SrkUtil.Int.Set

let substitute_const srk sigma expr =
  let simplify t = of_linterm srk (linterm_of srk t) in
  rewrite srk ~up:(fun expr ->
      match Expr.refine srk expr with
      | `Formula phi ->
        begin
          try
            match Formula.destruct srk phi with
            | `Atom (`Eq, s, t) ->
              (mk_eq srk (simplify s) (simplify t) :> ('a, typ_fo) expr)
            | `Atom (`Leq, s, t) ->
              (mk_leq srk (simplify s) (simplify t) :> ('a, typ_fo) expr)
            | `Atom (`Lt, s, t) ->
              (mk_lt srk (simplify s) (simplify t) :> ('a, typ_fo) expr)
            | `Proposition (`App (k, [])) ->
              (sigma k :> ('a, typ_fo) expr)
            | _ -> expr
          with Nonlinear -> expr
        end
      | `Term t ->
        begin match Term.destruct srk t with
          | `App (k, []) -> (sigma k :> ('a, typ_fo) expr)
          | `Binop (`Mod, s, t) ->
            begin
              try
                (mk_mod srk (simplify s) (simplify t) :> ('a, typ_fo) expr)
              with Nonlinear -> expr
            end
          | _ -> expr
        end)
    expr

(* Compute the GCD of all coefficients in an affine term (with integral
   coefficients) *)
let coefficient_gcd term =
  BatEnum.fold (fun gcd (qq, _) ->
      match QQ.to_zz qq with
      | None -> assert false
      | Some zz -> ZZ.gcd zz gcd)
    ZZ.zero
    (V.enum term)

let common_denominator term =
  BatEnum.fold (fun den (qq, _) ->
      ZZ.lcm den (QQ.denominator qq))
    ZZ.one
    (V.enum term)

let map_atoms srk f phi =
  let rewriter expr =
    match Expr.refine srk expr with
    | `Formula phi ->
      begin match Formula.destruct srk phi with
        | `Atom (op, s, t) -> (f op s t :> ('a, typ_fo) expr)
        | _ -> expr
      end
    | `Term _ -> expr
  in
  rewrite srk ~up:rewriter phi

(* floor(term/divisor) + offset *)
type int_virtual_term =
  { term : V.t;
    divisor : ZZ.t;
    offset : ZZ.t }
  [@@deriving ord]

exception Equal_int_term of int_virtual_term

let pp_int_virtual_term srk formatter vt =
  begin
    if ZZ.equal vt.divisor ZZ.one then
      pp_linterm srk formatter vt.term
    else
      Format.fprintf formatter "@[floor(@[%a@ / %a@])@]"
        (pp_linterm srk) vt.term
        ZZ.pp vt.divisor
  end;
  if not (ZZ.equal vt.offset ZZ.zero) then
    Format.fprintf formatter " + %a@]" ZZ.pp vt.offset
  else
    Format.fprintf formatter "@]"

type virtual_term =
  | MinusInfinity
  | PlusEpsilon of V.t
  | Term of V.t

let pp_virtual_term srk formatter =
  function
  | MinusInfinity -> Format.pp_print_string formatter "-oo"
  | PlusEpsilon t ->
    Format.fprintf formatter "%a + epsilon" (pp_linterm srk) t
  | Term t -> pp_linterm srk formatter t

(* Loos-Weispfenning virtual substitution *) 
let virtual_substitution srk x virtual_term phi =
  let pivot_term x term =
    V.pivot (dim_of_sym x) (linterm_of srk term)
  in
  let replace_atom op s zero =
    assert (Term.equal zero (mk_real srk QQ.zero));

    (* s == s' + ax, x not in fv(s') *)
    let (a, s') = pivot_term x s in
    if QQ.equal a QQ.zero then
      match op with
      | `Eq -> mk_eq srk s zero
      | `Lt -> mk_lt srk s zero
      | `Leq -> mk_leq srk s zero
    else
      let soa = V.scalar_mul (QQ.inverse (QQ.negate a)) s' (* -s'/a *) in
      let mk_sub s t = of_linterm srk (V.add s (V.negate t)) in
      match op, virtual_term with
      | (`Eq, Term t) ->
        (* -s'/a = x = t <==> -s'/a = t *)
        mk_eq srk (mk_sub soa t) zero
      | (`Leq, Term t) ->
        if QQ.lt a QQ.zero then
          (* -s'/a <= x = t <==> -s'/a <= t *)
          mk_leq srk (mk_sub soa t) zero
        else
          (* t = x <= -s'/a <==> t <= -s'/a *)
          mk_leq srk (mk_sub t soa) zero
      | (`Lt, Term t) ->
        if QQ.lt a QQ.zero then
          (* -s'/a < x = t <==> -s'/a < t *)
          mk_lt srk (mk_sub soa t) zero
        else
          (* t = x < -s'/a <==> t < -s'/a *)
          mk_lt srk (mk_sub t soa) zero
      | `Eq, _ -> mk_false srk
      | (_, PlusEpsilon t) ->
        if QQ.lt a QQ.zero then
          (* -s'/a < x = t + eps <==> -s'/a <= t *)
          (* -s'/a <= x = t + eps <==> -s'/a <= t *)
          mk_leq srk (mk_sub soa t) zero
        else
          (* t + eps = x < -s'/a <==> t < -s'/a *)
          (* t + eps = x <= -s'/a <==> t < -s'/a *)
          mk_lt srk (mk_sub t soa) zero
      | (_, MinusInfinity) ->
        if QQ.lt a QQ.zero then
          (* -s'/a < x = -oo <==> false *)
          mk_false srk
        else
          (* -oo = x < -s'/a <==> true *)
          mk_true srk
  in
  map_atoms srk replace_atom phi

(* Model based projection, as in described in Anvesh Komuravelli, Arie
   Gurfinkel, Sagar Chaki: "SMT-based Model Checking for Recursive Programs".
   Given a structure m, a constant symbol x, and a set of
   linear terms T, find a virtual term vt such that
   - vt is -t/a (where ax + t in T) and m |= x = -t/a
   - vt is -t/a + epsilon (where ax + t in T) and m |= -t/a < x and
                          m |= 's/b < x ==> (-s/b <= s/a) for all bx + s in T
   - vt is -oo otherwise *)
let mbp_virtual_term srk interp x atoms =
  if typ_symbol srk x != `TyReal then
    invalid_arg "mbp: cannot eliminate non-real symbols";

  let x_val =
    try Interpretation.real interp x
    with Not_found ->
      invalid_arg "mbp_virtual_term: no interpretation for constant"
  in
  let merge lower lower' =
    match lower, lower' with
    | None, x | x, None -> x
    | Some (lower, lower_val), Some (lower', lower_val') ->
      if QQ.lt lower_val lower_val' then
        Some (lower', lower_val')
      else
        Some (lower, lower_val)
  in

  let get_vt atom =
    match Interpretation.destruct_atom srk atom with
    | `Literal (_, _) -> None
    | `Comparison (op, s, t) ->
      let t =
        try V.add (linterm_of srk s) (V.negate (linterm_of srk t))
        with Nonlinear -> assert false
      in
      let (a, t') = V.pivot (dim_of_sym x) t in

      (* Atom is ax + t' op 0 *)
      if QQ.equal QQ.zero a then
        None
      else
        let toa = V.scalar_mul (QQ.inverse (QQ.negate a)) t' in
        let toa_val = evaluate_linterm (Interpretation.real interp) toa in
        match op with
        | `Eq -> raise (Equal_term toa)
        | `Leq when QQ.equal toa_val x_val -> raise (Equal_term toa)
        | `Lt | `Leq ->
          if QQ.lt a QQ.zero then
            (* Lower bound *)
            Some (toa, toa_val)
          else
            (* Upper bound: discard *)
            None
  in
  let vt =
    try
      begin match List.fold_left merge None (List.map get_vt atoms) with
      | Some (lower, _) -> PlusEpsilon lower
      | None -> MinusInfinity
      end
    with Equal_term t -> Term t
  in
  logf ~level:`trace "Virtual term for %a: %a"
    (pp_symbol srk) x
    (pp_virtual_term srk) vt;
  vt

(* Given a prenex formula phi, compute a pair (qf_pre, psi) such that
   - qf_pre is a quantifier prefix [(Q0, a0);...;(Qn, an)] where each Qi is
     either `Exists or `Forall, and each ai is a Skolem constant
   - psi is negation- and quantifier-free formula, and contains no free
     variables
   - every atom of in psi is either a propositial variable or an arithmetic
     atom of the form t < 0, t <= 0, or t = 0
   - phi is equivalent to Q0 a0.Q1 a1. ... Qn. an. psi
*)
let normalize srk phi =
  let phi = Formula.prenex srk phi in
  let zero = mk_real srk QQ.zero in
  let rewriter env expr =
    match Expr.refine srk expr with
    | `Formula phi ->
      (begin match Formula.destruct srk phi with
         | `Proposition (`Var i) -> mk_const srk (Env.find env i)
         | `Atom (`Eq, s, t) -> mk_eq srk (mk_sub srk s t) zero
         | `Atom (`Leq, s, t) -> mk_leq srk (mk_sub srk s t) zero
         | `Atom (`Lt, s, t) -> mk_lt srk (mk_sub srk s t) zero
         | _ -> phi
       end :> ('a, typ_fo) expr)
    | `Term t ->
      begin match Term.destruct srk t with
        | `Var (i, _) ->
          begin
            try mk_const srk (Env.find env i)
            with Not_found -> invalid_arg "Quantifier.normalize: free variable"
          end
        | _ -> expr
      end
  in
  let rec go env phi =
    match Formula.destruct srk phi with
    | `Quantify (qt, name, typ, psi) ->
      let k = mk_symbol srk ~name (typ :> Syntax.typ) in
      let (qf_pre, psi) = go (Env.push k env) psi in
      ((qt,k)::qf_pre, psi)
    | _ -> ([], rewrite srk ~down:(nnf_rewriter srk) ~up:(rewriter env) phi)
  in
  go Env.empty phi

let simplify_atom srk op s t =
  let zero = mk_real srk QQ.zero in
  let destruct_int term =
    match Term.destruct srk term with
    | `Real q ->
      begin match QQ.to_zz q with
        | Some z -> z
        | None -> invalid_arg "simplify_atom: non-integral value"
      end
    | _ -> invalid_arg "simplify_atom: non-constant"
  in
  let (s, op) =
    let s =
      if Term.equal t zero then s
      else mk_sub srk s t
    in
    match op with
    | `Lt when (expr_typ srk s = `TyInt) ->
      (SrkSimplify.simplify_term srk (mk_add srk [s; mk_real srk QQ.one]), `Leq)
    | _ -> (SrkSimplify.simplify_term srk s, op)
  in
  (* Scale a linterm with rational coefficients so that all coefficients are
     integral *)
  let zz_linterm term =
    let qq_linterm = linterm_of srk term in
    let multiplier = 
      BatEnum.fold (fun multiplier (qq, _) ->
          ZZ.lcm (QQ.denominator qq) multiplier)
        ZZ.one
        (V.enum qq_linterm)
    in
    (multiplier, V.scalar_mul (QQ.of_zz multiplier) qq_linterm)
  in
  match op with
  | `Eq | `Leq ->
    begin match Term.destruct srk s with
    | `Binop (`Mod, dividend, modulus) ->
      (* Divisibility constraint *)
      let modulus = destruct_int modulus in
      let (multiplier, lt) = zz_linterm dividend in
      `Divides (ZZ.mul multiplier modulus, lt)
    | `Unop (`Neg, s') ->
      begin match Term.destruct srk s' with
        | `Binop (`Mod, dividend, modulus) ->
          if op = `Leq then
            (* trivial *)
            `CompareZero (`Leq, V.zero)
          else
            (* Divisibility constraint *)
            let modulus = destruct_int modulus in
            let (multiplier, lt) = zz_linterm dividend in
            `Divides (ZZ.mul multiplier modulus, lt)
        | _ -> `CompareZero (op, snd (zz_linterm s))
      end
    | `Add [x; y] ->
      begin match Term.destruct srk x, Term.destruct srk y with
        | `Real k, `Binop (`Mod, dividend, modulus)
        | `Binop (`Mod, dividend, modulus), `Real k when QQ.lt k QQ.zero && op = `Eq ->
          let (multiplier, lt) = zz_linterm dividend in
          let modulus = destruct_int modulus in
          if ZZ.equal multiplier ZZ.one && QQ.lt k (QQ.of_zz modulus) then
            let lt = V.add_term k const_dim lt in
            `Divides (modulus, lt)
          else
            `CompareZero (op, snd (zz_linterm s))
        | `Real k, `Unop (`Neg, z) | `Unop (`Neg, z), `Real k when QQ.equal k QQ.one ->
          begin match Term.destruct srk z with
            | `Binop (`Mod, dividend, modulus) ->
              let modulus = destruct_int modulus in
              let (multiplier, lt) = zz_linterm dividend in
              `NotDivides (ZZ.mul multiplier modulus, lt)
            | _ -> `CompareZero (op, snd (zz_linterm s))
          end
        | _, _ -> `CompareZero (op, snd (zz_linterm s))
      end
    | _ -> `CompareZero (op, snd (zz_linterm s))
    end
  | `Lt ->
    begin match Term.destruct srk s with
      | `Binop (`Mod, dividend, modulus) ->
        (* Indivisibility constraint: dividend % modulus < 0. *)
        let modulus = destruct_int modulus in
        let (multiplier, lt) = zz_linterm dividend in
        `NotDivides (ZZ.mul multiplier modulus, lt)

      | `Unop (`Neg, s') ->
        begin match Term.destruct srk s' with
          | `Binop (`Mod, dividend, modulus) ->
            (* Indivisibility constraint: dividend % modulus > 0 *)
            let modulus = destruct_int modulus in
            let (multiplier, lt) = zz_linterm dividend in
            `NotDivides (ZZ.mul multiplier modulus, lt)
          | _ -> `CompareZero (`Lt, snd (zz_linterm s))
        end

      | _ -> `CompareZero (`Lt, snd (zz_linterm s))
    end

let is_presburger_atom srk atom =
  try
    begin match Interpretation.destruct_atom srk atom with
      | `Literal (_, _) -> true
      | `Comparison (op, s, t) ->
        ignore (simplify_atom srk op s t);
        true
    end
  with _ -> false

let mk_divides srk divisor term =
  assert (ZZ.lt ZZ.zero divisor);
  if ZZ.equal divisor ZZ.one || V.is_zero term then
    mk_true srk
  else
    let gcd = ZZ.gcd (coefficient_gcd term) divisor in
    let divisor = QQ.of_zz (ZZ.div divisor gcd) in
    let term = V.scalar_mul (QQ.of_zzfrac ZZ.one gcd) term in
    mk_eq srk
      (mk_mod srk (of_linterm srk term) (mk_real srk divisor))
      (mk_real srk QQ.zero)

let _mk_not_divides srk divisor term =
  assert(ZZ.lt ZZ.zero divisor);
  if ZZ.equal divisor ZZ.one || V.is_zero term then
    mk_false srk
  else
    let gcd = ZZ.gcd (coefficient_gcd term) divisor in
    assert (ZZ.lt ZZ.zero gcd);
    let divisor = QQ.div (QQ.of_zz divisor) (QQ.of_zz gcd) in
    let term = V.scalar_mul (QQ.of_zzfrac ZZ.one gcd) term in

    mk_lt srk
      (mk_neg srk (mk_mod srk (of_linterm srk term) (mk_real srk divisor)))
      (mk_real srk QQ.zero)

let term_of_virtual_term srk vt =
  let term = of_linterm srk vt.term in
  let offset = mk_real srk (QQ.of_zz vt.offset) in
  let term_over_div =
    if ZZ.equal vt.divisor ZZ.one then
      term
    else
      mk_floor srk (mk_div srk term (mk_real srk (QQ.of_zz vt.divisor)))
  in
  mk_add srk [term_over_div; offset]

exception Redundant_path
module Skeleton = struct

  type move =
    | MInt of int_virtual_term
    | MReal of V.t
    | MBool of bool
          [@@deriving ord]

  let pp_move srk formatter move =
    match move with
    | MInt vt -> pp_int_virtual_term srk formatter vt
    | MReal t -> pp_linterm srk formatter t
    | MBool true -> Format.pp_print_string formatter "true"
    | MBool false -> Format.pp_print_string formatter "false"

  let substitute srk x move phi =
    match move with
    | MInt vt ->
      let replacement = term_of_virtual_term srk vt in
      substitute_const
        srk
        (fun p -> if p = x then replacement else mk_const srk p)
        phi
    | MReal t ->
      let replacement = of_linterm srk t in
      substitute_const
        srk
        (fun p -> if p = x then replacement else mk_const srk p)
        phi
    | MBool vb ->
      let replacement = match vb with
        | true -> mk_true srk
        | false -> mk_false srk
      in
      substitute_const srk
        (fun p -> if p = x then replacement else mk_const srk p)
        phi

  let evaluate_move model move =
    match move with
    | MInt vt ->
      begin match QQ.to_zz (evaluate_linterm model vt.term) with
        | None -> assert false
        | Some tv ->
          ZZ.add (Mpzf.fdiv_q tv vt.divisor) vt.offset
          |> QQ.of_zz
      end
    | MReal t -> evaluate_linterm model t
    | MBool _ -> invalid_arg "evaluate_move"

  let substitute_implicant interp x move implicant =
    let srk = Interpretation.get_context interp in
    let is_true phi =
      match Formula.destruct srk phi with
      | `Tru -> true
      | _ -> false
    in
    match move with
    | MInt vt ->
      (* floor(term/div) + offset ~> (term - ([[term]] mod div))/div + offset,
         and add constraint that div | (term - ([[term]] mod div)) *)
      let term_val =
        let term_qq = evaluate_linterm (Interpretation.real interp) vt.term in
        match QQ.to_zz term_qq with
        | None -> assert false
        | Some zz -> zz
      in
      let remainder =
        Mpzf.fdiv_r term_val vt.divisor
      in
      let numerator =
        V.add_term (QQ.of_zz (ZZ.negate remainder)) const_dim vt.term
      in
      let replacement =
        V.scalar_mul (QQ.inverse (QQ.of_zz vt.divisor)) numerator
        |> V.add_term (QQ.of_zz vt.offset) const_dim
        |> of_linterm srk
      in

      assert (QQ.equal
                (Interpretation.evaluate_term interp replacement)
                (evaluate_move (Interpretation.real interp) move));
      let subst =
        substitute_const srk
          (fun p -> if p = x then replacement else mk_const srk p)
      in
      let divides = mk_divides srk vt.divisor numerator in
      BatList.filter (not % is_true) (divides::(List.map subst implicant))
    | _ ->
      BatList.filter_map (fun atom ->
          let atom' = substitute srk x move atom in
          if is_true atom' then None else Some atom')
        implicant

  let const_of_move move =
    match move with
    | MReal t -> const_of_linterm t
    | MInt vt ->
      if ZZ.equal vt.divisor ZZ.one then const_of_linterm vt.term
      else None
    | MBool _ -> invalid_arg "const_of_move"

  module MM = BatMap.Make(struct type t = move [@@deriving ord] end)

  type t =
    | SForall of symbol * symbol * t
    | SExists of symbol * (t MM.t)
    | SEmpty

  let pp srk formatter skeleton =
    let open Format in
    let rec pp formatter = function
      | SForall (_, sk, t) ->
        fprintf formatter "@[<v 2>(forall %a:@;%a)@]" (pp_symbol srk) sk pp t
      | SExists (k, mm) ->
        let pp_elt formatter (move, skeleton) =
          fprintf formatter "%a:@;@[%a@]@\n"
            (pp_move srk) move
            pp skeleton
        in
        let pp_sep formatter () = Format.fprintf formatter "@;" in
        fprintf formatter "@[<v 2>(exists %a:@;@[<v 0>%a@])@]"
          (pp_symbol srk) k
          (SrkUtil.pp_print_enum_nobox ~pp_sep pp_elt) (MM.enum mm)
      | SEmpty -> ()
    in
    pp formatter skeleton

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

  (* Create a new skeleton where the only path is the given path *)
  let mk_path srk path =
    let rec go = function
      | [] -> SEmpty
      | (`Forall k)::path ->
        let sk = mk_symbol srk ~name:(show_symbol srk k) (typ_symbol srk k) in
        SForall (k, sk, go path)
      | (`Exists (k, move))::path ->
        SExists (k, MM.add move (go path) MM.empty)
    in
    go path

  (* Add a path (corresponding to a new instantiation of the existential
     variables of some formula) to a skeleton.  Raise Redundant_path if this
     path already belonged to the skeleton. *)
  let add_path srk path skeleton =

    let rec go path skeleton =
      match path, skeleton with
      | ([], SEmpty) ->
        (* path was already in skeleton *)
        raise Redundant_path

      | (`Forall k::path, SForall (k', sk, skeleton)) ->
        assert (k = k');
        SForall (k, sk, go path skeleton)

      | (`Exists (k, move)::path, SExists (k', mm)) ->
        assert (k = k');
        let subskeleton =
          try go path (MM.find move mm)
          with Not_found -> mk_path srk path
        in
        SExists (k, MM.add move subskeleton mm)
      | `Exists (_, _)::_, SForall (_, _, _) | (`Forall _)::_, SExists (_, _) ->
        assert false
      | ([], _) ->
        assert false
      | (_, SEmpty) ->
        assert false
    in
    match skeleton with
    | SEmpty -> mk_path srk path
    | _ -> go path skeleton

  (* Used for incremental construction of the winning formula:
       (winning_formula skeleton phi)
                                   = \/_p winning_path_formula p skeleton phi *)
  let path_winning_formula srk path skeleton phi =
    let rec go path skeleton =
      match path, skeleton with
      | ([], SEmpty) -> phi
      | (`Forall k::path, SForall (k', sk, skeleton)) ->
        assert (k = k');
        let sk_const = mk_const srk sk in
        substitute_const srk
          (fun sym -> if k = sym then sk_const else mk_const srk sym)
          (go path skeleton)
      | (`Exists (k, move)::path, SExists (k', mm)) ->
        assert (k = k');
        substitute srk k move (go path (MM.find move mm))
      | (_, _) -> assert false
    in
    go path skeleton

  (* winning_formula skeleton phi is valid iff skeleton is a winning skeleton
     for the formula phi *)
  let winning_formula srk skeleton phi =
    let rec go = function
      | SEmpty -> phi
      | SForall (k, sk, skeleton) ->
        let sk_const = mk_const srk sk in
        substitute_const srk
          (fun sym -> if k = sym then sk_const else mk_const srk sym)
          (go skeleton)

      | SExists (k, mm) ->
        MM.enum mm
        /@ (fun (move, skeleton) -> substitute srk k move (go skeleton))
        |> BatList.of_enum
        |> mk_or srk
    in
    go skeleton

  let rec paths = function
    | SEmpty -> [[]]
    | SForall (k, _, skeleton) ->
      List.map (fun path -> (`Forall k)::path) (paths skeleton)
    | SExists (k, mm) ->
      BatEnum.fold (fun rest (move, skeleton) ->
          (List.map (fun path -> (`Exists (k, move))::path) (paths skeleton))
          @rest)
        []
        (MM.enum mm)
end

let select_real_term srk interp x atoms =
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
  let bound_of_atom atom =
    match Interpretation.destruct_atom srk atom with
    | `Literal (_, _) -> (None, None)
    | `Comparison (op, s, t) ->
      let t = V.add (linterm_of srk s) (V.negate (linterm_of srk t)) in

      let (a, t') = V.pivot (dim_of_sym x) t in

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
  let bound_of_atom atom =
    if Symbol.Set.mem x (symbols atom) then
      bound_of_atom atom
    else
      (None, None)
  in
  try
    match List.fold_left merge (None, None) (List.map bound_of_atom atoms) with
    | (Some (t, _, false), _) | (_, Some (t, _, false)) ->
      (logf ~level:`trace "Found equal(?) term: %a = %a"
         (pp_symbol srk) x
         (pp_linterm srk) t;
       t)
    | (Some (s, _, _), None) ->
      logf ~level:`trace "Found lower bound: %a < %a"
        (pp_linterm srk) s
        (pp_symbol srk) x;
      V.add s (const_linterm (QQ.of_int (1)))
    | (None, Some (t, _, _)) ->
      logf ~level:`trace "Found upper bound: %a < %a"
        (pp_symbol srk) x
        (pp_linterm srk) t;
      V.add t (const_linterm (QQ.of_int (-1)))
    | (Some (s, _, _), Some (t, _, _)) ->
      logf ~level:`trace "Found interval: %a < %a < %a"
        (pp_linterm srk) s
        (pp_symbol srk) x
        (pp_linterm srk) t;
      V.scalar_mul (QQ.of_frac 1 2) (V.add s t)
    | (None, None) -> V.zero (* Value of x is irrelevant *)
  with Equal_term t ->
    (logf ~level:`trace "Found equal term: %a = %a"
       (pp_symbol srk) x
       (pp_linterm srk) t;
     t)

let select_int_term srk interp x atoms =
  assert (typ_symbol srk x == `TyInt);
  let merge bound bound' =
    match bound, bound' with
    | (`Lower (s, s_val), `Lower (t, t_val)) ->
        if ZZ.lt t_val s_val then
          `Lower (s, s_val)
        else
          `Lower (t, t_val)
    | (`Upper (s, s_val), `Upper (t, t_val)) ->
        if ZZ.lt s_val t_val then
          `Upper (s, s_val)
        else
          `Upper (t, t_val)
    | (`Lower (t, t_val), _) | (_, `Lower (t, t_val)) -> `Lower (t, t_val)
    | (`Upper (t, t_val), _) | (_, `Upper (t, t_val)) -> `Upper (t, t_val)
    | `None, `None -> `None
  in
  let eval = evaluate_linterm (Interpretation.real interp) in
  let x_val = match QQ.to_zz (Interpretation.real interp x) with
    | Some zz -> zz
    | None -> assert false
  in
  (* delta = gcd { lcm(d,a) : d | ax + t or not(d | ax + t) in atoms }.  If
     [[vt]](m) = [[x]](m) mod delta, then for every divisilibity atom
       d | ax + t
     which appears in phi, we have
       m |= (d | ax + t)   <==>   m |= (d | a(vt) + t *)
  let delta =
    List.fold_left
      (fun delta atom ->
         match Interpretation.destruct_atom srk atom with
         | `Literal (_, _) -> delta
         | `Comparison (op, s, t) ->
           match simplify_atom srk op s t with
           | `Divides (divisor, t) | `NotDivides (divisor, t) ->
             let a = match QQ.to_zz (V.coeff (dim_of_sym x) t) with
               | None -> assert false
               | Some zz -> ZZ.abs zz
             in
             if ZZ.equal ZZ.zero a then delta
             else ZZ.lcm (ZZ.div divisor (ZZ.gcd divisor a)) delta
           | _ -> delta)
      ZZ.one
      atoms
  in
  assert (ZZ.lt ZZ.zero delta);
  let evaluate_vt vt =
    let real_val =
      Skeleton.evaluate_move (Interpretation.real interp) (Skeleton.MInt vt)
    in
    match QQ.to_zz real_val with
    | Some v -> v
    | None -> assert false
  in
  let bound_of_atom atom =
    match Interpretation.destruct_atom srk atom with
    | `Literal (_, _) -> `None
    | `Comparison (op, s, t) ->
      match simplify_atom srk op s t with
      | `CompareZero (op, t) ->
        begin
          let (a, t) = V.pivot (dim_of_sym x) t in
          let a = match QQ.to_zz a with
            | None -> assert false
            | Some zz -> zz
          in
          if ZZ.equal a ZZ.zero then
            `None
          else if ZZ.compare a ZZ.zero > 0 then
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
              | Some num -> Mpzf.fdiv_q num a
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
              let axv = ZZ.mul a vt_val in
              let tv = match QQ.to_zz (eval t) with
                | Some zz -> ZZ.negate zz
                | None -> assert false
              in
              match op with
              | `Lt -> assert (ZZ.lt axv tv)
              | `Leq -> assert (ZZ.leq axv tv)
              | `Eq -> assert (ZZ.equal axv tv)
            end;
            begin match op with
              | `Eq -> raise (Equal_int_term vt)
              | _ ->
                `Upper (vt, evaluate_vt vt)
            end
          else
            let a = ZZ.negate a in

            (* (-a)x + t <= 0 --> lower bound of ceil(t/a) = floor((t+a-1)/a) *)
            (* (-a)x + t < 0 --> lower bound of ceil(t+1/a) = floor((t+a)/a) *)
            let numerator =
              if op = `Lt then
                V.add_term (QQ.of_zz a) const_dim t
              else
                V.add_term (QQ.of_zz (ZZ.sub a ZZ.one)) const_dim t
            in
            let rhs_val = (* [[floor(numerator / a)]] *)
              match QQ.to_zz (eval numerator) with
              | Some num -> Mpzf.fdiv_q num a
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
              let axv = ZZ.mul a vt_val in
              let tv = match QQ.to_zz (eval t) with
                | Some zz -> zz
                | None -> assert false
              in
              match op with
              | `Lt -> assert (ZZ.lt tv axv)
              | `Leq -> assert (ZZ.leq tv axv)
              | `Eq -> assert (ZZ.equal tv axv)
            end;
            begin match op with
              | `Eq -> raise (Equal_int_term vt)
              | _ ->
                `Lower (vt, evaluate_vt vt)
            end
        end
      | _ ->
        `None
  in
  let bound_of_atom atom =
    if Symbol.Set.mem x (symbols atom) then
      bound_of_atom atom
    else
      `None
  in
  let vt_val vt =
    let tval = match QQ.to_zz (eval vt.term) with
      | Some zz -> zz
      | None -> assert false
    in
    ZZ.add (Mpzf.fdiv_q tval vt.divisor) vt.offset
  in
  match List.fold_left merge `None (List.map bound_of_atom atoms) with
  | `Lower (vt, _) ->
    logf ~level:`trace "Found lower bound: %a < %a"
      (pp_int_virtual_term srk) vt
      (pp_symbol srk) x;
    assert (ZZ.equal (Mpzf.fdiv_r x_val delta) (Mpzf.fdiv_r (vt_val vt) delta));
    vt
  | `Upper (vt, _) ->
    logf ~level:`trace "Found upper bound: %a < %a"
      (pp_symbol srk) x
      (pp_int_virtual_term srk) vt;
    assert (ZZ.equal (Mpzf.fdiv_r x_val delta) (Mpzf.fdiv_r (vt_val vt) delta));
    vt
  | `None ->
    (* Value of x is irrelevant *)
    logf ~level:`trace "Irrelevant: %a" (pp_symbol srk) x;
    let value = Linear.const_linterm (QQ.of_zz (ZZ.modulo x_val delta)) in
    { term = value; divisor = ZZ.one; offset = ZZ.zero }

let select_int_term srk interp x atoms =
  try
    select_int_term srk interp x atoms
  with
  | Equal_int_term vt -> vt
  | Nonlinear ->
    Log.errorf "(nonlinear) select_int_term atoms:";
    List.iter (fun atom ->
        if not (is_presburger_atom srk atom) then
          Log.errorf ">%a" (Formula.pp srk) atom)
      atoms;
    assert false
  | Invalid_argument msg ->
    Log.errorf "(inv arg) select_int_term atoms: %s" msg;
    List.iter (fun atom -> Log.errorf ">%a" (Formula.pp srk) atom) atoms;
    assert false


(* Given an interpretation M and a cube C with M |= C, find a cube C'
   such that M |= C' |= C, and C does not contain any floor terms. *)
let specialize_floor_cube srk model cube =
  let div_constraints = ref [] in
  let add_div_constraint divisor term =
    let div =
      mk_eq srk (mk_mod srk term (mk_real srk (QQ.of_zz divisor))) (mk_real srk QQ.zero)
    in
    div_constraints := div::(!div_constraints)
  in
  let replace_floor expr = match destruct srk expr with
    | `Unop (`Floor, t) ->
       let v = linterm_of srk t in
       let divisor = common_denominator v in
       let qq_divisor = QQ.of_zz divisor in
       let dividend = of_linterm srk (V.scalar_mul qq_divisor v) in
       let remainder =
         QQ.modulo (Interpretation.evaluate_term model dividend) qq_divisor
       in
       let dividend' = mk_sub srk dividend (mk_real srk remainder) in
       let replacement =
         V.add_term
           (QQ.negate (QQ.div remainder qq_divisor))
           Linear.const_dim
           v
         |> of_linterm srk
       in
       assert (QQ.equal
                 (Interpretation.evaluate_term model replacement)
                 (QQ.of_zz (QQ.floor (Interpretation.evaluate_term model t))));

       add_div_constraint divisor dividend';
       (replacement :> ('a,typ_fo) expr)
    | `Binop (`Mod, t, m) ->
       begin match destruct srk m with
       | `Real m ->
          let replacement =
            mk_real srk (QQ.modulo (Interpretation.evaluate_term model t) m)
          in
          let m = match QQ.to_zz m with
            | Some m -> m
            | None -> assert false
          in
          add_div_constraint m (mk_sub srk t replacement);
          (replacement :> ('a,typ_fo) expr)
       | _ -> expr
       end
    | _ -> expr
  in
  let cube' = List.map (rewrite srk ~up:replace_floor) cube in
  (!div_constraints)@cube'


let select_implicant srk interp ?(env=Env.empty) phi =
  match Interpretation.select_implicant interp ~env phi with
  | Some atoms ->
    logf ~level:`trace "Implicant Atoms:";
    List.iter
      (fun atom -> logf ~level:`trace ">%a" (Formula.pp srk) atom)
      atoms;
    Some (specialize_floor_cube srk interp atoms)
  | None -> None


(* Counter-strategy synthesis *)
module CSS = struct

  type 'a ctx =
    { formula : 'a formula;
      not_formula : 'a formula; (* Negated formula *)
      mutable skeleton : Skeleton.t; (* skeleton for formula *)

      (* solver for the *negation* of the winning formula for skeleton (unsat
         iff there is a winning SAT strategy for formula which conforms to
         skeleton) *)
      solver : 'a Smt.Solver.t;
      srk : 'a context;
    }

  let reset ctx =
    Smt.Solver.reset ctx.solver;
    ctx.skeleton <- Skeleton.SEmpty

  let add_path ctx path =
    let srk = ctx.srk in
    try
      ctx.skeleton <- Skeleton.add_path srk path ctx.skeleton;
      let win =
        Skeleton.path_winning_formula srk path ctx.skeleton ctx.formula
      in
      Smt.Solver.add ctx.solver [mk_not srk win]
    with Redundant_path -> ()

  (* Check if a given skeleton is winning.  If not, synthesize a
     counter-strategy. *)
  let get_counter_strategy select_term ?(parameters=None) ctx =
    logf ~level:`trace "%a" (Skeleton.pp ctx.srk) ctx.skeleton;
    let parameters =
      match parameters with
      | Some p -> p
      | None   -> Interpretation.empty ctx.srk
    in
    match Smt.Solver.get_model ctx.solver with
    | `Unsat ->
      logf "Winning formula is valid";
      `Unsat
    | `Unknown -> `Unknown
    | `Sat m ->
      logf "Winning formula is not valid";

      (* Using the model m, synthesize a counter-strategy which beats the
         strategy skeleton.  This is done by traversing the skeleton: on the
         way down, we build a model of the *negation* of the formula using the
         labels on the path to the root.  On the way up, we find elimination
         terms for each universally-quantified variable using model-based
         projection.  *)
      let rec counter_strategy path_model skeleton =
        let open Skeleton in
        logf ~level:`trace "Path model: %a" Interpretation.pp path_model;
        match skeleton with
        | SForall (k, sk, skeleton) ->
          let path_model =
            Interpretation.add
              k
              (Interpretation.value m sk)
              path_model
          in
          logf ~level:`trace "Forall %a (%a)"
            (pp_symbol ctx.srk) k
            (pp_symbol ctx.srk) sk;
          let (counter_phi, counter_paths) =
            counter_strategy path_model skeleton
          in
          let move = select_term path_model k counter_phi in
          logf ~level:`trace "Found move: %a = %a"
            (pp_symbol ctx.srk) k
            (Skeleton.pp_move ctx.srk) move;
          let counter_phi =
            Skeleton.substitute_implicant path_model k move counter_phi
          in
          let counter_paths =
            List.map (fun path -> (`Exists (k, move))::path) counter_paths
          in
          (counter_phi, counter_paths)
        | SExists (k, mm) ->
          let (counter_phis, paths) =
            MM.enum mm
            /@ (fun (move, skeleton) ->
                let path_model =
                  match move with
                  | Skeleton.MBool bool_val ->
                    Interpretation.add_bool k bool_val path_model
                  | _ ->
                    let mv =
                      Skeleton.evaluate_move
                        (Interpretation.real path_model)
                        move
                    in
                    Interpretation.add_real k mv path_model
                in
                let (counter_phi, counter_paths) =
                  counter_strategy path_model skeleton
                in
                let counter_phi =
                  Skeleton.substitute_implicant path_model k move counter_phi
                in
                let counter_paths =
                  List.map (fun path -> (`Forall k)::path) counter_paths
                in
                (counter_phi, counter_paths))
            |> BatEnum.uncombine
          in
          (BatList.concat (BatList.of_enum counter_phis),
           BatList.concat (BatList.of_enum paths))
        | SEmpty ->
          logf ~level:`trace "Path model: %a" Interpretation.pp path_model;
          logf ~level:`trace "not_phi: %a" (Formula.pp ctx.srk) ctx.not_formula;
          let phi_implicant =
            match select_implicant ctx.srk path_model ctx.not_formula with
            | Some x -> x
            | None -> assert false
          in
          (phi_implicant, [[]])
      in
      `Sat (snd (counter_strategy parameters ctx.skeleton))

  (* Check to see if the matrix of a prenex formula is satisfiable.  If it is,
     initialize a sat/unsat strategy skeleton pair. *)
  let initialize_pair select_term srk qf_pre phi =
    match Smt.get_model srk phi with
    | `Unsat -> `Unsat
    | `Unknown -> `Unknown
    | `Sat phi_model ->
      logf "Found initial model";
      (* Create paths for sat_skeleton & unsat_skeleton *)
      let f (qt, x) (sat_path, unsat_path, atoms) =
        let move = select_term phi_model x atoms in
        let (sat_path, unsat_path) = match qt with
          | `Exists ->
            ((`Exists (x, move))::sat_path,
             (`Forall x)::unsat_path)
          | `Forall ->
            ((`Forall x)::sat_path,
             (`Exists (x, move))::unsat_path)
        in
        (sat_path,
         unsat_path,
         Skeleton.substitute_implicant phi_model x move atoms)
      in
      let (sat_path, unsat_path, _) =
        match select_implicant srk phi_model phi with
        | Some implicant -> List.fold_right f qf_pre ([], [], implicant)
        | None -> assert false
      in
      let not_phi = snd (normalize srk (mk_not srk phi)) in
      let sat_ctx =
        let skeleton = Skeleton.mk_path srk sat_path in
        let win =
          Skeleton.path_winning_formula srk sat_path skeleton phi
        in
        let solver = Smt.mk_solver srk in
        Smt.Solver.add solver [mk_not srk win];
        { formula = phi;
          not_formula = not_phi;
          skeleton = skeleton;
          solver = solver;
          srk = srk }
      in
      let unsat_ctx =
        let skeleton = Skeleton.mk_path srk unsat_path in
        let win =
          Skeleton.path_winning_formula srk unsat_path skeleton not_phi
        in
        let solver = Smt.mk_solver srk in
        Smt.Solver.add solver [mk_not srk win];
        { formula = not_phi;
          not_formula = phi;
          skeleton = skeleton;
          solver = solver;
          srk = srk }
      in
      logf "Initial SAT strategy:@\n%a"
        (Skeleton.pp srk) sat_ctx.skeleton;
      logf "Initial UNSAT strategy:@\n%a"
        (Skeleton.pp srk) unsat_ctx.skeleton;
      `Sat (sat_ctx, unsat_ctx)

  let is_sat select_term sat_ctx unsat_ctx =
    let round = ref 0 in
    let old_paths = ref (-1) in
    let rec is_sat () =
      incr round;
      logf ~level:`trace ~attributes:[`Blue;`Bold]
        "Round %d: Sat [%d/%d], Unsat [%d/%d]"
        (!round)
        (Skeleton.size sat_ctx.skeleton)
        (Skeleton.nb_paths sat_ctx.skeleton)
        (Skeleton.size unsat_ctx.skeleton)
              (Skeleton.nb_paths unsat_ctx.skeleton);
      let paths = Skeleton.nb_paths sat_ctx.skeleton in
      assert (paths > !old_paths);
      old_paths := paths;
      logf ~attributes:[`Blue;`Bold] "Checking if SAT wins (%d)"
        (Skeleton.nb_paths sat_ctx.skeleton);
      match get_counter_strategy select_term sat_ctx with
      | `Sat paths -> (List.iter (add_path unsat_ctx) paths; is_unsat ())
      | `Unsat -> `Sat
      | `Unknown -> `Unknown
    and is_unsat () =
      logf ~attributes:[`Blue;`Bold] "Checking if UNSAT wins (%d)"
        (Skeleton.nb_paths unsat_ctx.skeleton);
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
  let initialize_pair select_term srk qf_pre phi =
    let unsat_skeleton = ref Skeleton.empty in
    match initialize_pair select_term srk qf_pre phi with
    | `Unsat -> `Unsat
    | `Unknown -> `Unknown
    | `Sat (sat_ctx, unsat_ctx) ->
      let round = ref 0 in
      let rec is_sat () =
        incr round;
        logf "Improve round: %d" (!round);
        logf ~attributes:[`Blue;`Bold] "Checking if SAT wins (%d)"
          (Skeleton.size sat_ctx.skeleton);
        if (!round) = (!max_improve_rounds) then
          `Sat (sat_ctx, unsat_ctx)
        else
          match get_counter_strategy select_term sat_ctx with
          | `Sat [path] ->
            begin
              try
                unsat_skeleton := Skeleton.add_path srk path (!unsat_skeleton);
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
          (Skeleton.size unsat_ctx.skeleton);
        match get_counter_strategy select_term unsat_ctx with
        | `Sat paths -> (reset sat_ctx;
                         List.iter (add_path sat_ctx) paths;
                         is_sat ())
        | `Unsat -> `Unsat
        | `Unknown -> `Unknown
      in
      is_sat ()

  let _minimize_skeleton param_interp ctx =
    let solver = Smt.mk_solver ctx.srk in
    let paths = Skeleton.paths ctx.skeleton in
    let path_guards =
      List.map (fun _ -> mk_const ctx.srk (mk_symbol ctx.srk `TyBool)) paths
    in
    let psis =
      let winning_formula path =
        Skeleton.path_winning_formula ctx.srk path ctx.skeleton ctx.formula
        |> Interpretation.substitute param_interp
      in
      List.map2 (fun path guard ->
          mk_or ctx.srk [mk_not ctx.srk guard;
                         mk_not ctx.srk (winning_formula path)])
        paths
        path_guards
    in
    let path_of_guard guard =
      List.fold_left2 (fun res g path ->
          if Formula.equal g guard then Some path
          else res)
        None
        path_guards
        paths
      |> (function
          | Some x -> x
          | None -> assert false)
    in
    Smt.Solver.add solver psis;
    match Smt.Solver.get_unsat_core solver path_guards with
    | `Sat -> assert false
    | `Unknown -> assert false
    | `Unsat core ->
      List.fold_left
        (fun skeleton core_guard ->
           try Skeleton.add_path ctx.srk (path_of_guard core_guard) skeleton
           with Redundant_path -> skeleton)
        Skeleton.empty
        core
end

let simsat_forward_core srk qf_pre phi =
  let select_term model x atoms =
    match typ_symbol srk x with
    | `TyInt -> Skeleton.MInt (select_int_term srk model x atoms)
    | `TyReal -> Skeleton.MReal (select_real_term srk model x atoms)
    | `TyBool -> Skeleton.MBool (Interpretation.bool model x)
    | `TyFun (_, _) -> assert false
  in

  (* If the quantifier prefix leads with an existential, check satisfiability
     of the negated sentence instead, then negate the result.  We may now
     assume that the outer-most quantifier is universal. *)
  let (qf_pre, phi, negate) =
    match qf_pre with
    | (`Exists, _)::_ ->
      let phi = snd (normalize srk (mk_not srk phi)) in
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
  match CSS.initialize_pair select_term srk qf_pre phi with
  | `Unsat ->
    (* Matrix is unsat -> any unsat strategy is winning *)
    let path =
      qf_pre |> List.map (function
          | `Forall, k ->
            begin match typ_symbol srk k with
              | `TyReal ->
                `Exists (k, Skeleton.MReal (Linear.const_linterm QQ.zero))
              | `TyInt ->
                let vt =
                  { term = Linear.const_linterm QQ.zero;
                    divisor = ZZ.one;
                    offset = ZZ.zero }
                in
                `Exists (k, Skeleton.MInt vt)
              | `TyBool -> `Exists (k, Skeleton.MBool true)
              | _ -> assert false
            end
          | `Exists, k -> `Forall k)
    in
    let skeleton = Skeleton.add_path srk path Skeleton.empty in
    if negate then `Sat skeleton
    else `Unsat skeleton

  | `Unknown -> `Unknown
  | `Sat (sat_ctx, _) ->
    let not_phi = sat_ctx.CSS.not_formula in
    let assert_param_constraints ctx parameter_interp =
      let open CSS in
      BatEnum.iter (function
          | (k, `Real qv) ->
            Smt.Solver.add ctx.solver
              [mk_eq srk (mk_const srk k) (mk_real srk qv)]
          | (k, `Bool false) ->
            Smt.Solver.add ctx.solver [mk_not srk (mk_const srk k)]
          | (k, `Bool true) ->
            Smt.Solver.add ctx.solver [mk_const srk k]
          | (_, `Fun _) -> ())
        (Interpretation.enum parameter_interp)
    in
    let mk_sat_ctx skeleton parameter_interp =
      let open CSS in
      let win =
        Skeleton.winning_formula srk skeleton phi
        |> Interpretation.substitute parameter_interp
      in
      let ctx =
        { formula = phi;
          not_formula = not_phi;
          skeleton = skeleton;
          solver = Smt.mk_solver srk;
          srk = srk }
      in
      Smt.Solver.add ctx.solver [mk_not srk win];
      assert_param_constraints ctx parameter_interp;
      ctx
    in
    let mk_unsat_ctx skeleton parameter_interp =
      let open CSS in
      let win =
        Skeleton.winning_formula srk skeleton not_phi
        |> Interpretation.substitute parameter_interp
      in
      let ctx =
        { formula = not_phi;
          not_formula = phi;
          skeleton = skeleton;
          solver = Smt.mk_solver srk;
          srk = srk }
      in
      Smt.Solver.add ctx.solver [mk_not srk win];
      assert_param_constraints ctx parameter_interp;
      ctx
    in

    (* Peel leading existential quantifiers off of a skeleton.  Fails if there
       is more than one move for an existential in the prefix.  *)
    let rec existential_prefix = function
      | Skeleton.SExists (k, mm) ->
        begin match BatList.of_enum (Skeleton.MM.enum mm) with
          | [(move, skeleton)] ->
            let (ex_pre, sub_skeleton) = existential_prefix skeleton in
            ((k, move)::ex_pre, sub_skeleton)
          | _ -> assert false
        end
      | skeleton -> ([], skeleton)
    in
    let rec universal_prefix = function
      | Skeleton.SForall (k, _, skeleton) -> k::(universal_prefix skeleton)
      | _ -> []
    in
    let skeleton_of_paths paths =
      List.fold_left
        (fun skeleton path ->
           try Skeleton.add_path srk path skeleton
           with Redundant_path -> skeleton)
        Skeleton.empty
        paths
    in

    (* Compute a winning strategy for the remainder of the game, after the
       prefix play determined by parameter_interp.  skeleton is an initial
       candidate strategy for one of the players, which begins with
       universals. *)
    let rec solve_game polarity param_interp ctx =
      logf ~attributes:[`Green] "Solving game %s (%d/%d)"
        (if polarity then "SAT" else "UNSAT")
        (Skeleton.nb_paths ctx.CSS.skeleton)
        (Skeleton.size ctx.CSS.skeleton);
      logf ~level:`trace "Parameters: %a" Interpretation.pp param_interp;
      let res =
        try
          CSS.get_counter_strategy
            select_term
            ~parameters:(Some param_interp)
            ctx
        with Not_found -> assert false
      in
      match res with
      | `Unknown -> `Unknown
      | `Unsat ->
        (* No counter-strategy to the strategy of the active player => active
           player wins *)
        `Sat ctx.CSS.skeleton
      | `Sat paths ->
        let unsat_skeleton = skeleton_of_paths paths in
        let (ex_pre, sub_skeleton) = existential_prefix unsat_skeleton in
        let param_interp' =
          List.fold_left (fun interp (k, move) ->
              match move with
              | Skeleton.MBool bv -> Interpretation.add_bool k bv interp
              | move ->
                Interpretation.add_real
                  k
                  (Skeleton.evaluate_move (Interpretation.real interp) move)
                  interp)
            param_interp
            ex_pre
        in
        let sub_ctx =
          if polarity then
            mk_unsat_ctx sub_skeleton param_interp'
          else
            mk_sat_ctx sub_skeleton param_interp'
        in
        match solve_game (not polarity) param_interp' sub_ctx with
        | `Unknown -> `Unknown
        | `Sat skeleton ->
          (* Inactive player wins *)
          let skeleton =
            List.fold_right
              (fun (k, move) skeleton ->
                 let mm = Skeleton.MM.add move skeleton Skeleton.MM.empty in
                 Skeleton.SExists (k, mm))
              ex_pre
              skeleton
          in
          `Unsat skeleton
        | `Unsat skeleton' ->
          (* There is a counter-strategy for the strategy of the inactive
             player => augment strategy for the active player & try again *)
          let open CSS in
          let forall_prefix =
            List.map (fun x -> `Forall x) (universal_prefix ctx.skeleton)
          in
          let add_path path =
            try
              let path = forall_prefix@path in
              ctx.skeleton <- Skeleton.add_path srk path ctx.skeleton;
              let win =
                Skeleton.path_winning_formula srk path ctx.skeleton ctx.formula
                |> Interpretation.substitute param_interp
              in
              Smt.Solver.add ctx.solver [mk_not srk win]
            with Redundant_path -> ()
          in
          List.iter add_path (Skeleton.paths skeleton');
          solve_game polarity param_interp ctx
    in
    match solve_game true (Interpretation.empty srk) sat_ctx with
    | `Unknown -> `Unknown
    | `Sat skeleton -> if negate then `Unsat skeleton else `Sat skeleton
    | `Unsat skeleton -> if negate then `Sat skeleton else `Unsat skeleton

let simsat_core srk qf_pre phi =
  let select_term model x phi =
    match typ_symbol srk x with
    | `TyInt -> Skeleton.MInt (select_int_term srk model x phi)
    | `TyReal -> Skeleton.MReal (select_real_term srk model x phi)
    | `TyBool -> Skeleton.MBool (Interpretation.bool model x)
    | `TyFun (_, _) -> assert false
  in
  match CSS.initialize_pair select_term srk qf_pre phi with
  | `Unsat -> `Unsat
  | `Unknown -> `Unknown
  | `Sat (sat_ctx, unsat_ctx) ->
    CSS.reset unsat_ctx;
    CSS.is_sat select_term sat_ctx unsat_ctx

let simsat srk phi =
  let constants = fold_constants Symbol.Set.add phi Symbol.Set.empty in
  let (qf_pre, phi) = normalize srk phi in
  let qf_pre =
    (List.map (fun k -> (`Exists, k)) (Symbol.Set.elements constants))@qf_pre
  in
  CSS.max_improve_rounds := 2;
  logf "Quantifier prefix: %s"
    (String.concat "" (List.map (function (`Forall, _) -> "A" | (`Exists, _) -> "E") qf_pre));
  simsat_core srk qf_pre phi

let simsat_forward srk phi =
  let constants = fold_constants Symbol.Set.add phi Symbol.Set.empty in
  let (qf_pre, phi) = normalize srk phi in
  let qf_pre =
    (List.map (fun k -> (`Exists, k)) (Symbol.Set.elements constants))@qf_pre
  in
  match simsat_forward_core srk qf_pre phi with
  | `Sat _ -> `Sat
  | `Unsat _ -> `Unsat
  | `Unknown -> `Unknown

let maximize_feasible srk phi t =
  let objective_constants = fold_constants Symbol.Set.add t Symbol.Set.empty in
  let constants = fold_constants Symbol.Set.add phi objective_constants in
  let (qf_pre, phi) = normalize srk phi in
  let qf_pre =
    ((List.map (fun k -> (`Exists, k)) (Symbol.Set.elements constants))@qf_pre)
  in

  (* First, check if the objective function is unbounded.  This is done by
     checking satisfiability of the formula:
       forall i. exists ks. phi /\ t >= i
  *)
  let objective = mk_symbol srk ~name:"objective" `TyReal in
  let qf_pre_unbounded = (`Forall, objective)::qf_pre in
  let phi_unbounded =
    mk_and srk [
      phi;
      mk_leq srk (mk_sub srk (mk_const srk objective) t) (mk_real srk QQ.zero)
    ]
  in
  let not_phi_unbounded =
    snd (normalize srk (mk_not srk phi_unbounded))
  in
  (* Always select [[objective]](m) as the value of objective *)
  let select_term m x phi =
    if x = objective then
      Skeleton.MReal (const_linterm (Interpretation.real m x))
    else
      match typ_symbol srk x with
      | `TyInt -> Skeleton.MInt (select_int_term srk m x phi)
      | `TyReal -> Skeleton.MReal (select_real_term srk m x phi)
      | `TyBool -> Skeleton.MBool (Interpretation.bool m x)
      | `TyFun (_, _) -> assert false
  in
  CSS.max_improve_rounds := 1;
  let init =
    CSS.initialize_pair select_term srk qf_pre_unbounded phi_unbounded
  in
  match init with
  | `Unsat -> `MinusInfinity
  | `Unknown -> `Unknown
  | `Sat (sat_ctx, unsat_ctx) ->
    (* Skolem constant associated with the (universally quantified) objective
       bound *)
    let objective_skolem =
      match sat_ctx.CSS.skeleton with
      | Skeleton.SForall (_, sk, _) -> sk
      | _ -> assert false
    in
    let rec check_bound bound =
      begin
        match bound with
        | None -> ()
        | Some b ->
          CSS.reset unsat_ctx;
          Smt.Solver.add sat_ctx.CSS.solver [
            mk_lt srk (mk_const srk objective_skolem) (mk_real srk b)
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
           move for the objective bound, and the associated sub-skeleton *)
        let (opt, opt_skeleton) = match unsat_ctx.CSS.skeleton with
          | Skeleton.SExists (_, mm) ->
            BatEnum.filter (fun (move, skeleton) ->
                let move_val = match Skeleton.const_of_move move with
                  | Some qq -> qq
                  | None -> assert false
                in
                let win =
                  let win_not_unbounded =
                    Skeleton.winning_formula srk skeleton not_phi_unbounded
                  in
                  mk_and
                    srk
                    [mk_not srk win_not_unbounded;
                     mk_eq srk (mk_real srk move_val) (mk_const srk objective)]
                in
                Smt.is_sat srk win = `Unsat)
              (Skeleton.MM.enum mm)
            /@ (fun (v, skeleton) -> match Skeleton.const_of_move v with
                | Some qq -> (qq, skeleton)
                | None -> assert false)
            |> BatEnum.reduce (fun (a, a_skeleton) (b, b_skeleton) ->
                if QQ.lt a b then (b, b_skeleton)
                else (a, a_skeleton))
          | _ -> assert false
        in

        logf "Objective function is bounded by %a" QQ.pp opt;

        (* Get the negation of the winning formula for SAT corresponding to
           the sub-skeleton rooted below all of the constant symbols which
           appear in the objective.  This formula is weaker than phi, and the
           constant symbols in the objective are not bound. *)
        let bounded_phi =
          let open Skeleton in
          let rec go skeleton =
            match skeleton with
            | SEmpty -> SEmpty
            | SForall (k, _, subskeleton) ->
              if Symbol.Set.mem k objective_constants then go subskeleton
              else skeleton
            | SExists (_, _) -> skeleton
          in
          (Skeleton.winning_formula srk (go opt_skeleton) not_phi_unbounded)
          |> mk_not srk
        in
        logf "Bounded phi:@\n%a" (Formula.pp srk) bounded_phi;
        begin match SrkZ3.optimize_box srk bounded_phi [t] with
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

let maximize srk phi t =
  match simsat srk phi with
  | `Sat -> maximize_feasible srk phi t
  | `Unsat -> `MinusInfinity
  | `Unknown -> `Unknown

exception Unknown
let qe_mbp srk phi =
  let (qf_pre, phi) = normalize srk phi in
  let phi = eliminate_ite srk phi in
  let exists x phi =
    let solver = Smt.mk_solver srk in
    let disjuncts = ref [] in
    let rec loop () =
      match Smt.Solver.get_model solver with
      | `Sat m ->
        let implicant =
          match select_implicant srk m phi with
          | Some x -> x
          | None -> assert false
        in

        let vt = mbp_virtual_term srk m x implicant in
        let psi = virtual_substitution srk x vt phi in
        disjuncts := psi::(!disjuncts);
        Smt.Solver.add solver [mk_not srk psi];
        loop ()
      | `Unsat -> mk_or srk (!disjuncts)
      | `Unknown -> raise Unknown
    in
    Smt.Solver.add solver [phi];
    loop ()
  in
  List.fold_right
    (fun (qt, x) phi ->
       match qt with
       | `Exists ->
         exists x (snd (normalize srk phi))
       | `Forall ->
         mk_not srk (exists x (snd (normalize srk (mk_not srk phi)))))
    qf_pre
    phi

(* Given a set of dimensions to project and a set of equations, orient
   the equations into a set rewrite rules of the form (a * x) -> t *)
let _orient project eqs =
  let simplify vec =
    let gcd = (* GCD of coefficients *)
      BatEnum.fold (fun gcd (a, _) -> ZZ.gcd gcd a) ZZ.zero (ZZVector.enum vec)
    in
    ZZVector.map (fun _ a -> ZZ.div a gcd) vec
  in
  (* Replace a*dim -> rhs in vec.  a must be positive. *)
  let substitute (a, dim) rhs vec =
    let (b,vec') = ZZVector.pivot dim vec in
    if ZZ.equal ZZ.zero b then
      vec
    else
      let lcm = ZZ.abs (ZZ.lcm a b) in
      let rhs = ZZVector.scalar_mul (ZZ.div lcm a) rhs in
      let vec' = ZZVector.scalar_mul (ZZ.div lcm b) vec' in
      simplify (ZZVector.add rhs vec')
  in
  (* Simplify equations *)
  let eqs =
    eqs
    |> List.map (fun vec ->
           let den = common_denominator vec in
           V.enum vec
           /@ (fun (scalar, dim) ->
             match QQ.to_zz (QQ.mul (QQ.of_zz den) scalar) with
             | Some z -> (z, dim)
             | None -> assert false)
           |> ZZVector.of_enum
           |> simplify)
  in
  let rec go eqs oriented =
    (* Find orientation among all equations that minimizes the leading coefficient *)
    let champion =
      List.fold_left (fun champion vec ->
          BatEnum.fold (fun champion (a, dim) ->
              if  IntSet.mem dim project then
                let candidate =
                  if ZZ.lt a ZZ.zero then
                    Some (ZZ.negate a, dim, snd (ZZVector.pivot dim vec))
                  else
                    Some (a, dim, ZZVector.negate (snd (ZZVector.pivot dim vec)))
                in
                match champion with
                | Some (b, _, _) ->
                   if ZZ.lt (ZZ.abs a) b then candidate
                   else champion
                | None -> candidate
              else
                champion)
            champion
            (ZZVector.enum vec))
        None
        eqs
    in
    match champion with
    | Some (a, dim, rhs) ->
       let reduced_eqs =
         List.filter_map (fun vec ->
             let vec' = substitute (a, dim) rhs vec in
             if ZZVector.equal ZZVector.zero vec' then
               None
             else
               Some vec')
           eqs
       in
       go reduced_eqs ((a, dim, rhs)::oriented)
    | None -> (List.rev oriented, eqs)
  in
  go eqs []

let mbp ?(dnf=false) srk exists phi =
  let phi =
    eliminate_ite srk phi
    |> rewrite srk
         ~down:(nnf_rewriter srk)
         ~up:(SrkSimplify.simplify_terms_rewriter srk)
  in
  let project =
    Symbol.Set.filter (not % exists) (symbols phi)
  in
  let project_int =
    Symbol.Set.fold (fun s set ->
        IntSet.add (Linear.dim_of_sym s) set)
      project
      IntSet.empty
  in
  let solver = Smt.mk_solver ~theory:"QF_LIA" srk in
  let disjuncts = ref [] in
  let is_true phi =
    match Formula.destruct srk phi with
    | `Tru -> true
    | _ -> false
  in
  (* Sequentially compose [subst] with the substitution [symbol -> term] *)
  let seq_subst symbol term subst =
    let subst_symbol =
      substitute_const srk
        (fun s -> if s = symbol then term else mk_const srk s)
    in
    Symbol.Map.add symbol term (Symbol.Map.map subst_symbol subst)
  in
  let rec loop () =
    match Smt.Solver.get_model solver with
    | `Sat interp ->
       let implicant =
         match select_implicant srk interp phi with
         | Some x -> specialize_floor_cube srk interp x
         | None -> assert false
       in
       (* Find substitutions for symbols involved in equations, along
          with divisibility constarints *)
       let (subst, div_constraints) =
         let (oriented_eqs, _) =
           List.filter_map (fun atom ->
               match Interpretation.destruct_atom srk atom with
               | `Comparison (op, s, t) ->
                  begin match simplify_atom srk op s t with
                  | `CompareZero (`Eq, t) -> Some t
                  | _ -> None
                  end
               | _ -> None)
             implicant
           |> _orient project_int
         in
         List.fold_left (fun (subst, div_constraints) (a, dim, rhs) ->
             let rhs_qq =
               ZZVector.enum rhs
               /@ (fun (b, dim) -> (QQ.of_zz b, dim))
               |> V.of_enum
             in
             let sym = match Linear.sym_of_dim dim with
               | Some s -> s
               | None -> assert false
             in
             let sym_div = mk_divides srk a rhs_qq in
             let rhs_term =
               Linear.of_linterm srk
                 (V.scalar_mul (QQ.of_zzfrac (ZZ.of_int 1) a) rhs_qq)
             in
             (seq_subst sym rhs_term subst, sym_div::div_constraints))
           (Symbol.Map.empty, [])
           oriented_eqs
       in
       let implicant =
         List.map (substitute_map srk subst) (div_constraints@implicant)
       in
       (* Add substitituions for symbols *not* involved in equations
          to subst *)
       let subst =
         Symbol.Set.fold (fun s (subst, implicant) ->
             if Symbol.Map.mem s subst then
               (* Skip symbols involved in equations *)
               (subst, implicant)
             else if typ_symbol srk s = `TyInt then
               let vt = select_int_term srk interp s implicant in

               (* floor(term/div) + offset ~> (term - ([[term]] mod div))/div + offset,
               and add constraint that div | (term - ([[term]] mod div)) *)
               let term_val =
                 let term_qq = evaluate_linterm (Interpretation.real interp) vt.term in
                 match QQ.to_zz term_qq with
                 | None -> assert false
                 | Some zz -> zz
               in
               let remainder =
                 Mpzf.fdiv_r term_val vt.divisor
               in
               let numerator =
                 V.add_term (QQ.of_zz (ZZ.negate remainder)) const_dim vt.term
               in
               let replacement =
                 V.scalar_mul (QQ.inverse (QQ.of_zz vt.divisor)) numerator
                 |> V.add_term (QQ.of_zz vt.offset) const_dim
                 |> of_linterm srk
               in
               let subst' =
                 substitute_const srk
                   (fun p -> if p = s then replacement else mk_const srk p)
               in
               let divides = mk_divides srk vt.divisor numerator in
               let implicant =
                 BatList.filter (not % is_true) (divides::(List.map subst' implicant))
               in
               (seq_subst s (term_of_virtual_term srk vt) subst,
                implicant)
             else if typ_symbol srk s = `TyReal then
               let implicant_s =
                 List.filter (fun atom -> Symbol.Set.mem s (symbols atom)) implicant
               in
               let t = Linear.of_linterm srk (select_real_term srk interp s implicant_s) in
               let subst' =
                 substitute_const srk
                   (fun p -> if p = s then t else mk_const srk p)
               in
               let implicant =
                 BatList.filter (not % is_true) (List.map subst' implicant)
               in
               (seq_subst s t subst,
                implicant)
             else assert false)
           project
           (subst, implicant)
         |> fst
       in
       let disjunct =
         substitute_map
           srk
           subst
           (if dnf then (mk_and srk (div_constraints@implicant))
            else (mk_and srk (phi::div_constraints)))
         |> SrkSimplify.simplify_terms srk
       in
       disjuncts := disjunct::(!disjuncts);
       Smt.Solver.add solver [mk_not srk disjunct];
       loop ()
    | `Unsat -> mk_or srk (!disjuncts)
    | `Unknown -> raise Unknown
  in
  Smt.Solver.add solver [phi];
  loop ()

let easy_sat srk phi =
  let constants = fold_constants Symbol.Set.add phi Symbol.Set.empty in
  let (qf_pre, phi) = normalize srk phi in
  let qf_pre =
    (List.map (fun k -> (`Exists, k)) (Symbol.Set.elements constants))@qf_pre
  in
  let select_term model x phi =
    match typ_symbol srk x with
    | `TyInt -> Skeleton.MInt (select_int_term srk model x phi)
    | `TyReal -> Skeleton.MReal (select_real_term srk model x phi)
    | `TyBool -> Skeleton.MBool (Interpretation.bool model x)
    | `TyFun (_, _) -> assert false
  in
  match CSS.initialize_pair select_term srk qf_pre phi with
  | `Unsat -> `Unsat
  | `Unknown -> `Unknown
  | `Sat (sat_ctx, _) ->
    match CSS.get_counter_strategy select_term sat_ctx with
    | `Unsat -> `Sat
    | `Unknown -> `Unknown
    | `Sat _ -> `Unknown


type 'a strategy = Strategy of ('a formula * Skeleton.move * 'a strategy) list

let pp_strategy srk formatter (Strategy xs) =
  let open Format in
  let pp_sep formatter () = Format.fprintf formatter "@;" in
  let rec pp formatter = function
    | (Strategy []) -> ()
    | (Strategy xs) ->
      fprintf formatter "@;  @[<v 0>%a@]"
        (SrkUtil.pp_print_enum_nobox ~pp_sep pp_elt)
        (BatList.enum xs)
  and pp_elt formatter (guard, move, sub_strategy) =
    fprintf formatter "%a --> %a%a"
      (Formula.pp srk) guard
      (Skeleton.pp_move srk) move
      pp sub_strategy
  in
  fprintf formatter "@[<v 0>%a@]"
    (SrkUtil.pp_print_enum_nobox ~pp_sep pp_elt)
    (BatList.enum xs)

let show_strategy srk = SrkUtil.mk_show (pp_strategy srk)

(* Extract a winning strategy from a skeleton *)
let extract_strategy _ _ _ =
  failwith "Quantifier.extract_strategy not implemented"
(*
  let open Skeleton in
  let z3 = Z3.mk_context [] in
  let rec go subst = function
    | SEmpty ->
      let psi = mk_not srk (List.fold_left (fun a f -> f a) phi subst) in
      SrkZ3.z3_of_formula srk z3 psi
    | SForall (k, sk, skeleton) ->
      let sk_const = mk_const srk sk in
      let replace =
        substitute_const srk
          (fun sym -> if k = sym then sk_const else mk_const srk sym)
      in
      go (replace::subst) skeleton
    | SExists (k, mm) ->
      MM.enum mm
      /@ (fun (move, skeleton) ->
          go ((substitute srk k move)::subst) skeleton
          |> Z3.Interpolation.mk_interpolant z3)
      |> BatList.of_enum
      |> Z3.Boolean.mk_and z3
  in
  let pattern = go [] skeleton in
  let params = Z3.Params.mk_params z3 in
  match Z3.Interpolation.compute_interpolant z3 pattern params with
  | (_, Some interp, None) ->
    let rec go interp = function
      | SEmpty -> (interp, Strategy [])
      | SForall (k, sk, skeleton) ->
        let replacement = mk_const srk k in
        let subst x =
          if x = sk then replacement else mk_const srk x
        in
        go (List.map (substitute_const srk subst) interp) skeleton
      | SExists (k, mm) ->
        BatEnum.fold (fun (interp, strategy) (move, skeleton) ->
            match go interp skeleton with
            | ([], _) -> assert false
            | ((guard::interp), sub_strategy) ->
              let guard = mk_not srk guard in
              (interp, (guard, move, sub_strategy)::strategy))
          (interp, [])
          (MM.enum mm)
        |> (fun (interp, xs) -> (interp, Strategy xs))
    in
    let (interp, strategy) =
      go (List.map (SrkZ3.formula_of_z3 srk) interp) skeleton
    in
    assert (interp == []);
    strategy
  | (_, None, Some _) -> assert false
  | (_, _, _) -> assert false
 *)

let winning_strategy srk qf_pre phi =
  match simsat_forward_core srk qf_pre phi with
  | `Sat skeleton ->
    logf "Formula is SAT.  Extracting strategy.";
    `Sat (extract_strategy srk skeleton phi)
  | `Unsat skeleton ->
    logf "Formula is UNSAT.  Extracting strategy.";
    `Unsat (extract_strategy srk skeleton (mk_not srk phi))
  | `Unknown -> `Unknown

let check_strategy srk qf_pre phi strategy =
  (* go qf_pre strategy computes a formula whose models correspond to playing
     phi according to the strategy *)
  let rec go qf_pre (Strategy xs) =
    match qf_pre with
    | [] ->
      assert (xs = []);
      mk_true srk
    | (`Exists, k)::qf_pre ->
      let has_move =
        xs |> List.map (fun (guard, move, sub_strategy) ->
            let move_formula =
              let open Skeleton in
              match move with
              | MInt vt ->
                mk_eq srk (mk_const srk k) (term_of_virtual_term srk vt)
              | MReal linterm ->
                mk_eq srk (mk_const srk k) (of_linterm srk linterm)
              | MBool true -> mk_const srk k
              | MBool false -> mk_not srk (mk_const srk k)
            in
            mk_and srk [guard; move_formula; go qf_pre sub_strategy])
        |> mk_or srk
      in
      let no_move =
        xs |> List.map (fun (guard, _, _) -> mk_not srk guard) |> mk_and srk
      in
      mk_or srk [has_move; no_move]
    | (`Forall, _)::qf_pre -> go qf_pre (Strategy xs)
  in
  let strategy_formula = go qf_pre strategy in
  Smt.is_sat srk (mk_and srk [strategy_formula; mk_not srk phi]) = `Unsat


(* Loos-Weispfenning virtual terms, plus a virtual term CUnknown
   indicating failure of virtual term selection.  Substituting
   CUnknown into an atom replaces it with true, resulting in
   over-approximate quantifier elimination. *)
type 'a cover_virtual_term =
  | CMinusInfinity
  | CPlusEpsilon of 'a term
  | CTerm of 'a term
  | CUnknown

let pp_cover_virtual_term srk formatter =
  function
  | CMinusInfinity -> Format.pp_print_string formatter "-oo"
  | CPlusEpsilon t ->
    Format.fprintf formatter "%a + epsilon" (Term.pp srk) t
  | CTerm t -> Term.pp srk formatter t
  | CUnknown -> Format.pp_print_string formatter "??"

let cover_virtual_term srk interp x atoms =
  let merge lower lower' =
    match lower, lower' with
    | None, x | x, None -> x
    | Some (lower, lower_val), Some (lower', lower_val') ->
      if QQ.lt lower_val lower_val' then
        Some (lower', lower_val')
      else
        Some (lower, lower_val)
  in
  let get_equal_term atom =
    match Interpretation.destruct_atom srk atom with
    | `Literal (_, _) -> None
    | `Comparison (`Lt, _, _) -> None
    | `Comparison (_, s, t) ->
      let sval = Interpretation.evaluate_term interp s in
      let tval = Interpretation.evaluate_term interp t in
      if QQ.equal sval tval then
        match SrkSimplify.isolate_linear srk x (mk_sub srk s t) with
        | Some (a, b) when not (QQ.equal a QQ.zero) ->
          let term =
            mk_mul srk [mk_real srk (QQ.inverse (QQ.negate a)); b]
          in
          if typ_symbol srk x = `TyInt && expr_typ srk term = `TyReal then
            Some (mk_floor srk term)
          else
            Some term
        | _ -> None
      else
        None
  in
  let get_vt atom =
    match Interpretation.destruct_atom srk atom with
    | `Literal (_, _) -> None
    | `Comparison (_, s, t) ->
      match SrkSimplify.isolate_linear srk x (mk_sub srk s t) with
      | None -> raise Nonlinear
      | Some (a, b) when QQ.lt a QQ.zero ->
        let b_over_a = mk_mul srk [mk_real srk (QQ.inverse (QQ.negate a)); b] in
        let b_over_a_val = Interpretation.evaluate_term interp b_over_a in
        Some (b_over_a, b_over_a_val)
      | _ -> None
  in
  try CTerm (BatList.find_map get_equal_term atoms)
  with Not_found ->
    (try
       begin match List.fold_left merge None (List.map get_vt atoms) with
         | Some (lower, _) -> CPlusEpsilon lower
         | None -> CMinusInfinity
       end
     with Nonlinear -> CUnknown)

let cover_virtual_substitution srk x virtual_term phi =
  let zero = mk_real srk QQ.zero in
  let replace_atom op s t =
    assert (Term.equal zero (mk_real srk QQ.zero));
    match op, SrkSimplify.isolate_linear srk x (mk_sub srk s t), virtual_term with
    | (_, None, _) -> mk_true srk
    | (`Leq, Some (a, _), _) when QQ.equal a QQ.zero ->
      mk_leq srk s t
    | (`Lt, Some (a, _), _) when QQ.equal a QQ.zero ->
      mk_lt srk s t
    | (`Eq, Some (a, _), _) when QQ.equal a QQ.zero ->
      mk_eq srk s t
    | (`Eq, Some (_, _), CPlusEpsilon _)
    | (`Eq, Some (_, _), CMinusInfinity) -> mk_false srk
    | (_, Some (a, _), CMinusInfinity) ->
      if QQ.lt a QQ.zero then mk_false srk
      else mk_true srk
    | (_, Some (a, b), CPlusEpsilon t) ->
        (* a(t+epsilon) + b <= 0 *)
      if QQ.lt a QQ.zero then
        mk_leq srk (mk_add srk [mk_mul srk [mk_real srk a; t]; b]) zero
      else
        mk_lt srk (mk_add srk [mk_mul srk [mk_real srk a; t]; b]) zero
    | (_, _, _) -> assert false
  in
  match virtual_term with
  | CTerm term ->
    let subst s =
      if s = x then term else mk_const srk s
    in
    substitute_const srk subst phi
  | CUnknown ->
    let drop expr =
      match destruct srk expr with
      | `Atom (_, _, _) ->
        if Symbol.Set.mem x (symbols expr) then
          (mk_true srk :> ('a, typ_fo) expr)
        else
          expr
      | _ -> expr
    in
    rewrite srk ~up:drop phi
  | _ ->
    map_atoms srk replace_atom phi

let mbp_cover ?(dnf=true) srk exists phi =
  let phi = eliminate_ite srk phi in
  let phi = rewrite srk ~down:(nnf_rewriter srk) phi in
  let project =
    Symbol.Set.filter (not % exists) (symbols phi)
  in
  let phi = eliminate_ite srk phi in
  let solver = Smt.mk_solver srk in
  let disjuncts = ref [] in
  let rec loop () =
    match Smt.Solver.get_model solver with
    | `Sat m ->
      let implicant =
        match select_implicant srk m phi with
        | Some x -> x
        | None -> assert false
      in
      let (_, psi) =
        Symbol.Set.fold (fun s (implicant, disjunct) ->
            let vt = cover_virtual_term srk m s implicant in
            logf "Found %a -> %a" (pp_symbol srk) s (pp_cover_virtual_term srk) vt;
            let implicant' =
              List.map (cover_virtual_substitution srk s vt) implicant
            in
            logf "Implicant' %a" (Formula.pp srk) (mk_and srk implicant');
            (implicant', cover_virtual_substitution srk s vt disjunct))
          project
          (implicant, if dnf then (mk_and srk implicant) else phi)
      in

      disjuncts := psi::(!disjuncts);
      Smt.Solver.add solver [mk_not srk psi];
      loop ()
    | `Unsat -> mk_or srk (!disjuncts)
    | `Unknown -> raise Unknown
  in
  Smt.Solver.add solver [phi];
  loop ()

let local_project_cube srk exists model cube =
  (* Set of symbols to be projected *)
  let project =
    List.fold_left
      (fun set phi -> Symbol.Set.union set (Symbol.Set.filter (not % exists) (symbols phi)))
      Symbol.Set.empty
      cube
  in
  let is_true phi =
    match Formula.destruct srk phi with
    | `Tru -> true
    | _ -> false
  in

  Symbol.Set.fold (fun symbol cube ->
      let vt = cover_virtual_term srk model symbol cube in
      List.map (cover_virtual_substitution srk symbol vt) cube
      |> List.filter (not % is_true))
    project
    cube

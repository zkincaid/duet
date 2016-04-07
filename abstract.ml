open Syntax
open Linear
open BatPervasives
open Apak

include Log.Make(struct let name = "ark.abstract" end)

exception Nonlinear
exception Equal_term of Linear.QQVector.t
exception Divide_by_zero


(* Affine expressions over constant symbols.  dim_of_sym, const_dim, and
   sym_of_dim are used to translate between symbols and the dimensions of the
   coordinate space. *)
module V = Linear.QQVector
module VS = Putil.Set.Make(Linear.QQVector)
module VM = Putil.Map.Make(Linear.QQVector)

let sym_of_dim dim =
  if dim == 0 then None
  else if dim > 0 then Some (symbol_of_int (dim - 1))
  else Some (symbol_of_int dim)

let dim_of_sym k =
  let id = int_of_symbol k in
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
  let nonzero_qq_of term =
    let qq = qq_of term in
    if QQ.equal qq QQ.zero then raise Nonlinear else qq
  in
  let mul x y =
    try scalar_mul (qq_of x) y
    with Nonlinear -> scalar_mul (qq_of y) x
  in
  let alg = function
    | `Real qq -> real qq
    | `Const k | `App (k, []) -> of_term QQ.one (dim_of_sym k)
    | `Var (_, _) | `App (_, _) -> raise Nonlinear
    | `Add sum -> List.fold_left add zero sum
    | `Mul sum -> List.fold_left mul (real QQ.one) sum
    | `Binop (`Div, x, y) -> scalar_mul (QQ.inverse (nonzero_qq_of y)) x
    | `Binop (`Mod, x, y) -> real (QQ.modulo (qq_of x) (nonzero_qq_of y))
    | `Unop (`Floor, x) -> real (QQ.of_zz (QQ.floor (qq_of x)))
    | `Unop (`Neg, x) -> negate x
    | `Ite (_, _, _) -> raise Nonlinear
  in
  Term.eval ark alg term

let of_linterm ark linterm =
  let open Linear.QQVector in
  enum linterm
  /@ (fun (coeff, dim) ->
      match sym_of_dim dim with
      | Some k ->
        if QQ.equal coeff QQ.one then mk_const ark k
        else mk_mul ark [mk_real ark coeff; mk_const ark k]
      | None -> mk_real ark coeff)
  |> BatList.of_enum
  |> mk_add ark

let pp_linterm ark formatter linterm =
  Term.pp ark formatter (of_linterm ark linterm)

let evaluate_linterm interp term =
  (V.enum term)
  /@ (fun (coeff, dim) ->
      match sym_of_dim dim with
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
  module SM = Symbol.Map
  type 'a interpretation =
    { ark : 'a context;
      map : [ `Bool of bool | `Real of QQ.t ] SM.t }

  let empty ark =
    { ark = ark;
      map = SM.empty }

  let add_real k v interp =
    match typ_symbol interp.ark k with
    | `TyReal | `TyInt -> { interp with map = SM.add k (`Real v) interp.map }
    | _ -> invalid_arg "add_real: constant symbol is non-arithmetic"

  let add_bool k v interp =
    match typ_symbol interp.ark k with
    | `TyBool -> { interp with map = SM.add k (`Bool v) interp.map }
    | _ -> invalid_arg "add_boolean: constant symbol is non-boolean"

  let real interp k =
    match SM.find k interp.map with
    | `Real v -> v
    | _ -> invalid_arg "real: constant symbol is not real"

  let bool interp k =
    match SM.find k interp.map with
    | `Bool v -> v
    | _ -> invalid_arg "bool: constant symbol is not Boolean"

  let value interp k = SM.find k interp.map

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
      (ApakEnum.pp_print_enum pp_elt) (SM.enum interp.map)

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

  let enum interp = SM.enum interp.map

  let substitute interpretation =
    let ark = interpretation.ark in
    substitute_const ark (fun sym ->
        try
          begin match value interpretation sym with
            | `Real qq -> (mk_real ark qq :> ('a, typ) expr)
            | `Bool true -> (mk_true ark :> ('a, typ) expr)
            | `Bool false -> (mk_false ark :> ('a, typ) expr)
          end
        with Not_found -> mk_const ark sym)

  let rec evaluate_term interp ?(env=Env.empty) term =
    let f = function
      | `Real qq -> qq
      | `Const k | `App (k, []) -> real interp k
      | `Var (i, _) ->
        begin match Env.find env i with
          | `Real qq -> qq
          | _ -> invalid_arg "evaluate_term: ill-typed variable"
        end
      | `Add xs -> List.fold_left QQ.add QQ.zero xs
      | `Mul xs -> List.fold_left QQ.mul QQ.one xs
      | `Binop (`Div, dividend, divisor) when QQ.equal divisor QQ.zero ->
        raise Divide_by_zero
      | `Binop (`Mod, t, modulus) when QQ.equal modulus QQ.zero ->
        raise Divide_by_zero
      | `Binop (`Div, dividend, divisor) -> QQ.div dividend divisor
      | `Binop (`Mod, t, modulus) -> QQ.modulo t modulus
      | `Unop (`Floor, t) -> QQ.of_zz (QQ.floor t)
      | `Unop (`Neg, t) -> QQ.negate t
      | `App (_, _) -> invalid_arg "evaluate_term: application"
      | `Ite (cond, bthen, belse) ->
        if evaluate_formula interp ~env cond then
          bthen
        else
          belse
    in
    try
      Term.eval interp.ark f term
    with Not_found ->
      invalid_arg "evaluate_term: no interpretation for constant symbol"

  and evaluate_formula interp ?(env=Env.empty) phi =
    let f = function
      | `And xs -> List.for_all (fun x -> x) xs
      | `Or xs -> List.exists (fun x -> x) xs
      | `Tru -> true
      | `Fls -> false
      | `Atom (op, s, t) ->
        begin try
            let s = evaluate_term interp ~env s in
            let t = evaluate_term interp ~env t in
            begin match op with
              | `Leq -> QQ.leq s t
              | `Eq -> QQ.equal s t
              | `Lt -> QQ.lt s t
            end
          with Divide_by_zero -> false
        end
      | `Not v -> not v
      | `Ite (cond, bthen, belse) -> if cond then bthen else belse
      | `Proposition (`Const k) -> bool interp k
      | `Proposition (`Var i) ->
        begin match Env.find env i with
        | `Bool v -> v
        | _ -> invalid_arg "evaluate_formula: ill-typed variable"
        end
      | `Proposition (`App (_, _)) ->
        invalid_arg "evaluate_formula: function application"
      | `Quantify (_, _, _, _) -> invalid_arg "evalutate_formula: quantifier"
    in
    try
      Formula.eval interp.ark f phi
    with Not_found ->
      invalid_arg "evaluate_formula: no interpretation for constant symbol"
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
      let dim = dim_of_sym k in
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
              match sym_of_dim dim with
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
                  (dim_of_sym k)
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

(* [select_implicant ark m ?env phi] selects an implicant [I] of [phi] such
   that [m,?env |= I |= phi].  The implicant [I] is a list of atomic formulas,
   which can be destructed using [destruct_atom]. *)
let select_implicant ark interp ?(env=Env.empty) phi =
  let rec term t =
    match Term.destruct ark t with
    | `Real _ | `Const _ | `App (_, []) | `Var (_, _) -> (t, [])
    | `Add xs ->
      let (summands, implicant) =
        List.fold_right
          (fun x (summands, implicant) ->
             let (x_term, x_implicant) = term x in
             (x_term::summands, x_implicant@implicant))
          xs
          ([], [])
      in
      (mk_add ark summands, implicant)
    | `Mul xs ->
      let (products, implicant) =
        List.fold_right
          (fun x (products, implicant) ->
             let (x_term, x_implicant) = term x in
             (x_term::products, x_implicant@implicant))
          xs
          ([], [])
      in
      (mk_mul ark products, implicant)
    | `Binop (op, s, t) ->
      let (s_term, s_impl) = term s in
      let (t_term, t_impl) = term t in
      let term =
        match op with
        | `Div -> mk_div ark s_term t_term
        | `Mod -> mk_mod ark s_term t_term
      in
      (term, s_impl@t_impl)
    | `Unop (op, t) ->
      let (t_term, t_impl) = term t in
      let term = match op with
        | `Floor -> mk_floor ark t_term
        | `Neg -> mk_neg ark t_term
      in
      (term, t_impl)
    | `App (_, _) -> invalid_arg "select_implicant: application"
    | `Ite (cond, bthen, belse) ->
      begin match formula cond with
        | Some implicant ->
          let (t, t_implicant) = term bthen in
          (t, t_implicant@implicant)
        | None ->
          let not_cond =
            rewrite ark ~down:(nnf_rewriter ark) (mk_not ark cond)
          in
          match formula not_cond with
          | Some implicant ->
            let (t, t_implicant) = term belse in
            (t, t_implicant@implicant)
          | None -> assert false
      end
  and formula phi =
    match Formula.destruct ark phi with
    | `Tru -> Some []
    | `Fls -> None
    | `Or disjuncts ->
      (* Find satisfied disjunct *)
      let f disjunct phi =
        match disjunct with
        | None -> formula phi
        | _ -> disjunct
      in
      List.fold_left f None disjuncts
    | `And conjuncts ->
      (* All conjuncts must be satisfied *)
      let f phi =
        match formula phi with
        | Some x -> x
        | None -> raise Not_found
      in
      (try Some (BatList.concat (List.map f conjuncts))
       with Not_found -> None)
    | `Atom (op, s, t) ->
      let (s_term, s_impl) = term s in
      let (t_term, t_impl) = term t in
      begin
        try
          let s_val = Interpretation.evaluate_term interp ~env s_term in
          let t_val = Interpretation.evaluate_term interp ~env t_term in
          let cons_nontriv phi atoms =
            if (Formula.destruct ark phi) = `Tru then atoms
            else phi::atoms
          in
          begin match op with
            | `Eq when QQ.equal s_val t_val ->
              Some (cons_nontriv (mk_eq ark s_term t_term) (s_impl@t_impl))
            | `Leq when QQ.leq s_val t_val ->
              Some (cons_nontriv (mk_leq ark s_term t_term) (s_impl@t_impl))
            | `Lt when QQ.lt s_val t_val ->
              Some (cons_nontriv (mk_lt ark s_term t_term) (s_impl@t_impl))
            | _ ->
              None
          end
        with Divide_by_zero -> None
      end
    | `Proposition (`Const p) ->
      if Interpretation.bool interp p then Some [phi]
      else None
    | `Proposition (`Var v) ->
      begin match Env.find env v with
        | `Bool true -> Some [phi]
        | `Bool _ -> None
        | _ -> invalid_arg "select_implicant: ill-typed propositional variable"
      end
    | `Not psi ->
      begin match Formula.destruct ark psi with
        | `Proposition (`Const p) ->
          if not (Interpretation.bool interp p) then
            Some [phi]
          else
            None
        | `Proposition (`Var v) ->
          begin match Env.find env v with
            | `Bool false -> Some [phi]
            | `Bool _ -> None
            | _ ->
              invalid_arg "select_implicant: ill-typed propositional variable"
          end
        | _ -> invalid_arg "select_implicant: negation"
      end
    | `Ite (cond, bthen, belse) ->
      begin match formula cond with
        | Some cond_implicant ->
          begin match formula bthen with
            | Some bthen_implicant -> Some (cond_implicant@bthen_implicant)
            | None -> None
          end
        | None ->
          let not_cond =
            rewrite ark ~down:(nnf_rewriter ark) (mk_not ark cond)
          in
          match formula not_cond with
          | Some cond_implicant ->
            begin match formula belse with
              | Some belse_implicant -> Some (cond_implicant@belse_implicant)
              | None -> None
            end
          | None -> None
      end
    | `Proposition (`App (_, _)) | `Quantify _ -> invalid_arg "select_implicant"
  in
  formula phi

let select_implicant ark interp ?(env=Env.empty) phi =
  match select_implicant ark interp phi with
  | Some atoms ->
    logf ~level:`trace "Implicant Atoms:";
    List.iter (fun atom -> logf ~level:`trace ">%a" (Formula.pp ark) atom) atoms;
    Some atoms
  | None -> None

let destruct_atom ark phi =
  match Formula.destruct ark phi with
  | `Atom (op, s, t) -> `Comparison (op, s, t)
  | `Proposition (`Const k) -> `Literal (`Pos, `Const k)
  | `Proposition (`Var i) -> `Literal (`Pos, `Var i)
  | `Not psi ->
    begin match Formula.destruct ark psi with
      | `Proposition (`Const k) -> `Literal (`Neg, `Const k)
      | `Proposition (`Var i) -> `Literal (`Neg, `Var i)
      | _ -> invalid_arg "destruct_atomic: not atomic"
    end
  | _ ->
    invalid_arg "destruct_atomic: not atomic"

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
  let rewriter expr =
    match refine ark expr with
    | `Formula phi ->
      begin match Formula.destruct ark phi with
        | `Atom (op, s, t) -> (f op s t :> ('a, typ_fo) expr)
        | _ -> expr
      end
    | `Term _ -> expr
  in
  rewrite ark ~up:rewriter phi

(* floor(term/divisor) + offset *)
type int_virtual_term =
  { term : V.t;
    divisor : int;
    offset : ZZ.t }
  [@@deriving ord]

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
    V.pivot (dim_of_sym x) (linterm_of ark term)
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
let mbp_virtual_term ark interp x atoms =
  assert (typ_symbol ark x == `TyReal);

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
    match destruct_atom ark atom with
    | `Literal (_, _) -> None
    | `Comparison (op, s, t) ->
      let t =
        try V.add (linterm_of ark s) (V.negate (linterm_of ark t))
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
  try
    begin match List.fold_left merge None (List.map get_vt atoms) with
      | Some (lower, _) -> PlusEpsilon lower
      | None -> MinusInfinity
    end
  with Equal_term t -> Term t

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
  let rewriter env expr =
    match refine ark expr with
    | `Formula phi ->
      (begin match Formula.destruct ark phi with
         | `Proposition (`Var i) -> mk_const ark (Env.find env i)
         | `Atom (`Eq, s, t) -> mk_eq ark (mk_sub ark s t) zero
         | `Atom (`Leq, s, t) -> mk_leq ark (mk_sub ark s t) zero
         | `Atom (`Lt, s, t) -> mk_lt ark (mk_sub ark s t) zero
         | _ -> phi
       end :> ('a, typ_fo) expr)
    | `Term t ->
      begin match Term.destruct ark t with
        | `Var (i, _) -> mk_const ark (Env.find env i)
        | _ -> expr
      end
  in
  let rec go env phi =
    match Formula.destruct ark phi with
    | `Quantify (qt, name, typ, psi) ->
      let k = mk_symbol ark ~name (typ :> Syntax.typ) in
      let (qf_pre, psi) = go (Env.push k env) psi in
      ((qt,k)::qf_pre, psi)
    | _ -> ([], rewrite ark ~down:(nnf_rewriter ark) ~up:(rewriter env) phi)
  in
  go Env.empty phi

let simplify_atom ark op s t =
  let zero = mk_real ark QQ.zero in
  let destruct_int term =
    match Term.destruct ark term with
    | `Real q ->
      begin match QQ.to_zz q with
        | Some z -> z
        | None -> invalid_arg "simplify_atom: non-integral value"
      end
    | _ -> invalid_arg "simplify_atom: non-constant"
  in
  let s =
    if Term.equal t zero then s
    else mk_sub ark s t
  in
  (* Scale a linterm with rational coefficients so that all coefficients are
     integral *)
  let zz_linterm term =
    let qq_linterm = linterm_of ark term in
    let multiplier = 
      BatEnum.fold (fun multiplier (qq, _) ->
          ZZ.lcm (QQ.denominator qq) multiplier)
        ZZ.one
        (V.enum qq_linterm)
    in
    V.scalar_mul (QQ.of_zz multiplier) qq_linterm
  in
  match op with
  | `Eq ->
    begin match Term.destruct ark s with
    | `Binop (`Mod, dividend, modulus) ->

      (* Divisibility constraint *)
      let modulus = destruct_int modulus in
      `Divides (modulus, zz_linterm dividend)
    | _ -> `CompareZero (`Eq, zz_linterm s)
    end
  | `Lt ->
    begin match Term.destruct ark s with
      | `Binop (`Mod, dividend, modulus) ->
        (* Indivisibility constraint: dividend % modulus < 0. *)
        let modulus = destruct_int modulus in
        `NotDivides (modulus, zz_linterm dividend)

      | `Unop (`Neg, s') ->
        begin match Term.destruct ark s' with
          | `Binop (`Mod, dividend, modulus) ->
            (* Indivisibility constraint: dividend % modulus > 0 *)
            let modulus = destruct_int modulus in
            `NotDivides (modulus, zz_linterm dividend)
          | _ -> `CompareZero (`Lt, zz_linterm s)
        end

      | _ -> `CompareZero (`Lt, zz_linterm s)
    end
  | `Leq ->
    `CompareZero (`Leq, zz_linterm s)

let mk_divides ark divisor term =
  assert (ZZ.lt ZZ.zero divisor);
  if ZZ.equal divisor ZZ.one || V.equal term V.zero then
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
  if ZZ.equal divisor ZZ.one || V.equal term V.zero then
    mk_false ark
  else
    let gcd = coefficient_gcd term in
    let divisor = QQ.div (QQ.of_zz divisor) (QQ.of_zz gcd) in
    let term = V.scalar_mul (QQ.of_zzfrac ZZ.one gcd) term in

    mk_lt ark
      (mk_neg ark (mk_mod ark (of_linterm ark term) (mk_real ark divisor)))
      (mk_real ark QQ.zero)

let substitute_real_term ark x t phi =
  let replacement = of_linterm ark t in
  substitute_const ark
    (fun p -> if p = x then replacement else mk_const ark p)
    phi

exception Redundant_path
module Scheme = struct

  type move =
    | MInt of int_virtual_term
    | MReal of V.t
    | MBool of bool
          [@@deriving ord]

  let pp_move ark formatter move =
    match move with
    | MInt vt -> pp_int_virtual_term ark formatter vt
    | MReal t -> pp_linterm ark formatter t
    | MBool true -> Format.pp_print_string formatter "true"
    | MBool false -> Format.pp_print_string formatter "false"

  let substitute ark x move phi =
    match move with
    | MInt vt ->
      let replacement =
        let term = of_linterm ark vt.term in
        let offset = mk_real ark (QQ.of_zz vt.offset) in
        let term_over_div =
          if vt.divisor = 1 then
            term
          else
            mk_floor ark (mk_div ark term (mk_real ark (QQ.of_int vt.divisor)))
        in
        mk_add ark [term_over_div; offset]
      in
      substitute_const
        ark
        (fun p -> if p = x then replacement else mk_const ark p)
        phi
    (*      int_virtual_substitution ark x vt phi*)
    | MReal t ->
      substitute_real_term ark x t phi
    | MBool vb ->
      let replacement = match vb with
        | true -> mk_true ark
        | false -> mk_false ark
      in
      substitute_const ark
        (fun p -> if p = x then replacement else mk_const ark p)
        phi

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

  let substitute_implicant interp x move implicant =
    let ark = interp.Interpretation.ark in
    let is_true phi =
      match Formula.destruct ark phi with
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
        Mpzf.fdiv_r term_val (ZZ.of_int vt.divisor)
      in
      let numerator =
        V.add_term (QQ.of_zz (ZZ.negate remainder)) const_dim vt.term
      in
      let replacement =
        V.scalar_mul (QQ.inverse (QQ.of_int vt.divisor)) numerator
        |> V.add_term (QQ.of_zz vt.offset) const_dim
        |> of_linterm ark
      in

      assert (QQ.equal
                (Interpretation.evaluate_term interp replacement)
                (evaluate_move (Interpretation.real interp) move));
      let subst =
        substitute_const ark
          (fun p -> if p = x then replacement else mk_const ark p)
      in
      let divides = mk_divides ark (ZZ.of_int vt.divisor) numerator in
      BatList.filter (not % is_true) (divides::(List.map subst implicant))
    | _ ->
      BatList.filter_map (fun atom ->
          let atom' = substitute ark x move atom in
          if is_true atom' then None else Some atom')
        implicant


  let const_of_move move =
    match move with
    | MReal t -> const_of_linterm t
    | MInt vt ->
      if vt.divisor = 1 then const_of_linterm vt.term
      else None
    | MBool _ -> invalid_arg "const_of_move"

  module MM = BatMap.Make(struct type t = move [@@deriving ord] end)

  type t =
    | SForall of symbol * symbol * t
    | SExists of symbol * (t MM.t)
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
        let sk_const = mk_const ark sk in
        substitute_const ark
          (fun sym -> if k = sym then sk_const else mk_const ark sym)
          (go path scheme)
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
        let sk_const = mk_const ark sk in
        substitute_const ark
          (fun sym -> if k = sym then sk_const else mk_const ark sym)
          (go scheme)

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

let select_real_term ark interp x atoms =
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
    match destruct_atom ark atom with
    | `Literal (_, _) -> (None, None)
    | `Comparison (op, s, t) ->
      let t = V.add (linterm_of ark s) (V.negate (linterm_of ark t)) in

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
  try
    match List.fold_left merge (None, None) (List.map bound_of_atom atoms) with
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

let select_int_term ark interp x atoms =
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
  (* delta = gcd { lcm(d,a) : d | ax + t or not(d | ax + t) in atoms }.  If
     [[vt]](m) = [[x]](m) mod delta, then for every divisilibity atom
       d | ax + t
     which appears in phi, we have
       m |= (d | ax + t)   <==>   m |= (d | a(vt) + t *)
  let delta =
    List.fold_left
      (fun delta atom ->
         match destruct_atom ark atom with
         | `Literal (_, _) -> delta
         | `Comparison (op, s, t) ->
           match simplify_atom ark op s t with
           | `Divides (divisor, t) | `NotDivides (divisor, t) ->
             let (a, t) = V.pivot (dim_of_sym x) t in
             let a = match QQ.to_zz a with
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
      Scheme.evaluate_move (Interpretation.real interp) (Scheme.MInt vt)
    in
    match QQ.to_zz real_val with
    | Some v -> v
    | None -> assert false
  in
  let bound_of_atom atom =
    match destruct_atom ark atom with
    | `Literal (_, _) -> `None
    | `Comparison (op, s, t) ->
      match simplify_atom ark op s t with
      | `CompareZero (op, t) ->
        begin
          let (a, t) = V.pivot (dim_of_sym x) t in
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
        end
      | _ ->
        `None
  in
  let vt_val vt =
    let tval = match QQ.to_zz (eval vt.term) with
      | Some zz -> zz
      | None -> assert false
    in
    ZZ.add (Mpzf.fdiv_q tval (ZZ.of_int vt.divisor)) vt.offset
  in
  match List.fold_left merge `None (List.map bound_of_atom atoms) with
  | `Lower (vt, _) ->
    logf ~level:`trace "Found lower bound: %a < %a"
      (pp_int_virtual_term ark) vt
      (pp_symbol ark) x;
    assert (ZZ.equal (Mpzf.fdiv_r x_val delta) (Mpzf.fdiv_r (vt_val vt) delta));
    vt
  | `Upper (vt, _) ->
    logf ~level:`trace "Found upper bound: %a < %a"
      (pp_symbol ark) x
      (pp_int_virtual_term ark) vt;
    assert (ZZ.equal (Mpzf.fdiv_r x_val delta) (Mpzf.fdiv_r (vt_val vt) delta));
    vt
  | `None ->
    (* Value of x is irrelevant *)
    logf ~level:`trace "Irrelevant: %a" (pp_symbol ark) x;
    { term = V.zero; divisor = 1; offset = ZZ.zero }

let select_int_term ark interp x atoms =
  try
    select_int_term ark interp x atoms
  with Nonlinear | Invalid_argument _ ->
    Log.errorf "select_int_term atoms:";
    List.iter (fun atom -> Log.errorf ">%a" (Formula.pp ark) atom) atoms;
    assert false

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
          let move = select_term path_model k counter_phi in
          logf ~level:`trace "Found move: %a = %a"
            (pp_symbol ctx.ark) k
            (Scheme.pp_move ctx.ark) move;
          let counter_phi =
            Scheme.substitute_implicant path_model k move counter_phi
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
                  Scheme.substitute_implicant path_model k move counter_phi
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
          logf ~level:`trace "not_phi: %a" (Formula.pp ctx.ark) ctx.not_formula;
          let phi_implicant =
            match select_implicant ctx.ark path_model ctx.not_formula with
            | Some x -> x
            | None -> assert false
          in
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
         Scheme.substitute_implicant phi_model x move atoms)
      in
      let (sat_path, unsat_path, _) =
        match select_implicant ark phi_model phi with
        | Some implicant -> List.fold_right f qf_pre ([], [], implicant)
        | None -> assert false
      in
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

  let minimize_scheme param_interp ctx =
    let solver = ctx.smt#mk_solver () in
    let paths = Scheme.paths ctx.scheme in
    let path_guards =
      List.map (fun _ -> mk_const ctx.ark (mk_symbol ctx.ark `TyBool)) paths
    in
    let psis =
      let winning_formula path =
        Scheme.path_winning_formula ctx.ark path ctx.scheme ctx.formula
        |> Interpretation.substitute param_interp
      in
      List.map2 (fun path guard ->
          mk_or ctx.ark [mk_not ctx.ark guard;
                         mk_not ctx.ark (winning_formula path)])
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
    solver#add [mk_and ctx.ark psis];
    match solver#get_unsat_core path_guards with
    | `Sat -> assert false
    | `Unknown -> assert false
    | `Unsat core ->
      List.fold_left
        (fun scheme core_guard ->
           try Scheme.add_path ctx.ark (path_of_guard core_guard) scheme
           with Redundant_path -> scheme)
        Scheme.empty
        core
end

let simsat_forward smt_ctx qf_pre phi =
  let ark = smt_ctx#ark in
  let select_term model x atoms =
    match typ_symbol ark x with
    | `TyInt -> Scheme.MInt (select_int_term ark model x atoms)
    | `TyReal -> Scheme.MReal (select_real_term ark model x atoms)
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
        |> Interpretation.substitute parameter_interp
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
        |> Interpretation.substitute parameter_interp
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
                |> Interpretation.substitute param_interp
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

let simsat_core smt_ctx qf_pre phi =
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

let simsat smt_ctx phi =
  let ark = smt_ctx#ark in
  let constants = fold_constants Symbol.Set.add phi Symbol.Set.empty in
  let (qf_pre, phi) = normalize ark phi in
  let qf_pre =
    (List.map (fun k -> (`Exists, k)) (Symbol.Set.elements constants))@qf_pre
  in
  simsat_core smt_ctx qf_pre phi

let simsat_forward smt_ctx phi =
  let ark = smt_ctx#ark in
  let constants = fold_constants Symbol.Set.add phi Symbol.Set.empty in
  let (qf_pre, phi) = normalize ark phi in
  let qf_pre =
    (List.map (fun k -> (`Exists, k)) (Symbol.Set.elements constants))@qf_pre
  in
  simsat_forward smt_ctx qf_pre phi

let maximize_feasible smt_ctx phi t =
  let ark = smt_ctx#ark in
  let objective_constants = fold_constants Symbol.Set.add t Symbol.Set.empty in
  let constants = fold_constants Symbol.Set.add phi objective_constants in
  let (qf_pre, phi) = normalize ark phi in
  let qf_pre =
    ((List.map (fun k -> (`Exists, k)) (Symbol.Set.elements constants))@qf_pre)
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
              if Symbol.Set.mem k objective_constants then go subscheme
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
  match simsat smt_ctx phi with
  | `Sat -> maximize_feasible smt_ctx phi t
  | `Unsat -> `MinusInfinity
  | `Unknown -> `Unknown

exception Unknown
let qe_mbp smt_ctx phi =
  let ark = smt_ctx#ark in
  let (qf_pre, phi) = normalize ark phi in
  let phi = eliminate_ite ark phi in
  let exists x phi =
    let solver = smt_ctx#mk_solver () in
    let disjuncts = ref [] in
    let constants =
      fold_constants Symbol.Set.add phi (Symbol.Set.singleton x)
      |> Symbol.Set.elements
    in
    let rec loop () =
      match solver#get_model () with
      | `Sat m ->
        let interp = Interpretation.of_model ark m constants in
        let implicant =
          match select_implicant ark interp phi with
          | Some x -> x
          | None -> assert false
        in
        let vt = mbp_virtual_term ark interp x implicant in
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
  List.fold_right
    (fun (qt, x) phi ->
       match qt with
       | `Exists ->
         exists x (snd (normalize ark phi))
       | `Forall ->
         mk_not ark (exists x (snd (normalize ark (mk_not ark phi)))))
    qf_pre
    phi

let easy_sat smt_ctx phi =
  let ark = smt_ctx#ark in
  let constants = fold_constants Symbol.Set.add phi Symbol.Set.empty in
  let (qf_pre, phi) = normalize ark phi in
  let qf_pre =
    (List.map (fun k -> (`Exists, k)) (Symbol.Set.elements constants))@qf_pre
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

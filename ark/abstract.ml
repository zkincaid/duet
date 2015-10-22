open Syntax
open Linear
open BatPervasives
open Apak

include Log.Make(struct let name = "ark.abstract" end)

module V = Linear.QQVector
module VS = Putil.Set.Make(Linear.QQVector)
module VM = Putil.Map.Make(Linear.QQVector)
module KS = BatSet.Make(struct
    type t = const_sym
    let compare = Pervasives.compare
  end)

module type AbstractionContext = sig

  include Syntax.BuilderContext

  val const_typ : const_sym -> typ
  val pp_const : Format.formatter -> const_sym -> unit
  val mk_sub : term -> term -> term
  val mk_skolem : ?name:string -> typ -> const_sym
  module Term : sig
    type t = term
    val eval : ('a open_term -> 'a) -> t -> 'a
    val pp : Format.formatter -> t -> unit
    val compare : t -> t -> int
    val equal : t -> t -> bool
    val fold_constants : (const_sym -> 'a -> 'a) -> t -> 'a -> 'a
    val destruct : t -> t open_term
  end
  module Formula : sig
    type t = formula
    val eval : (('a, term) open_formula -> 'a) -> t -> 'a    
    val pp : Format.formatter -> t -> unit
    val substitute_const : (const_sym -> term) -> t -> t
    val substitute : (int -> term) -> t -> t
    val destruct : t -> (t, term) open_formula
    val fold_constants : (const_sym -> 'a -> 'a) -> t -> 'a -> 'a
    val prenex : t -> t
  end

  type solver
  type model

  val get_model : formula -> [`Sat of model | `Unknown | `Unsat ]
  val interpolate_seq : formula list ->
    [ `Sat of model | `Unsat of formula list | `Unknown ]

  module Solver : sig
    val mk_solver : unit -> solver
    val add : solver -> formula list -> unit
    val push : solver -> unit
    val pop : solver -> int -> unit
    val reset : solver -> unit
    val check : solver -> formula list -> [ `Sat | `Unsat | `Unknown ]
    val get_model : solver -> [ `Sat of model | `Unsat | `Unknown ]
    val get_unsat_core : solver ->
      formula list ->
      [ `Sat | `Unsat of formula list | `Unknown ]
  end

  module Model : sig
    val eval_int : model -> term -> ZZ.t
    val eval_real : model -> term -> QQ.t
    val sat : model -> formula -> bool
    val to_string : model -> string
  end

  val optimize_box : formula -> term list -> [ `Sat of Interval.t list
                                             | `Unsat
                                             | `Unknown ]
end

exception Nonlinear

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

let const_of_linterm v =
  let (k, rest) = V.pivot const_dim v in
  if V.equal rest V.zero then Some k
  else None

let linterm_of
    (type t)
    (module C : AbstractionContext with type term = t)
    term =
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
    | `Binop (`Div, x, y) -> scalar_mul (QQ.inverse (qq_of y)) y
    | `Binop (`Mod, x, y) -> real (QQ.modulo (qq_of x) (qq_of y))
    | `Unop (`Floor, x) -> real (QQ.of_zz (QQ.floor (qq_of x)))
    | `Unop (`Neg, x) -> negate x
  in
  C.Term.eval alg term

let of_linterm
      (type t)
      (module C : AbstractionContext with type term = t)
      linterm =
  let open Linear.QQVector in
  enum linterm
  /@ (fun (coeff, dim) ->
      match const_of_dim dim with
      | Some k ->
        if QQ.equal coeff QQ.one then C.mk_const k
        else C.mk_mul [C.mk_real coeff; C.mk_const k]
      | None -> C.mk_real coeff)
  |> BatList.of_enum
  |> C.mk_add

let pp_linterm
      (type t)
      (module C : AbstractionContext with type term = t)
      formatter
      v =
    C.Term.pp formatter (of_linterm (module C) v)

(* Counter-example based extraction of the affine hull of a formula.  This
   works by repeatedly posing new (linearly independent) equations; each
   equation is either implied by the formula (and gets added to the affine
   hull) or there is a counter-example point which shows that it is not.
   Counter-example points are collecting in a system of linear equations where
   the variables are the coefficients of candidate equations. *)
let affine_hull
    (type formula)
    (type term)
    (module C : AbstractionContext with type formula = formula
                                    and type term = term)
    phi
    constants =
  let s = C.Solver.mk_solver () in
  C.Solver.add s [phi];
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
        C.Solver.push s;
        let candidate_term =
          QQVector.enum candidate
          /@ (fun (coeff, dim) ->
              match const_of_dim dim with
              | Some const -> C.mk_mul [C.mk_real coeff; C.mk_const const]
              | None -> C.mk_real coeff)
          |> BatList.of_enum
          |> C.mk_add
        in
        C.Solver.add s [C.mk_not (C.mk_eq candidate_term (C.mk_real QQ.zero))];
        match C.Solver.get_model s with
        | `Unknown -> (* give up; return the equalities we have so far *)
          logf ~level:`warn
            "Affine hull timed out (%d equations)"
            (List.length equalities);
          equalities
        | `Unsat -> (* candidate equality is implied by phi *)
          C.Solver.pop s 1;
          (* We never choose the same candidate equation again, because the
             system of equations mat' x = 0 implies that the coefficient of k is
             zero *)
          go (candidate_term::equalities) mat' ks
        | `Sat point -> (* candidate equality is not implied by phi *)
          C.Solver.pop s 1;
          let point_row =
            List.fold_left (fun row k ->
                QQVector.add_term
                  (C.Model.eval_real point (C.mk_const k))
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

let evaluate_term
    (type term)
    (module C : AbstractionContext with type term = term)
    interp
    ?(env=Env.empty)
    term =
  let f = function
    | `Real qq -> qq
    | `Const k -> interp k
    | `Var (i, _) -> Env.find env i
    | `Add xs -> List.fold_left QQ.add QQ.zero xs
    | `Mul xs -> List.fold_left QQ.mul QQ.one xs
    | `Binop (`Div, dividend, divisor) -> QQ.div dividend divisor
    | `Binop (`Mod, t, modulus) -> QQ.modulo t modulus
    | `Unop (`Floor, t) -> QQ.of_zz (QQ.floor t)
    | `Unop (`Neg, t) -> QQ.negate t
  in
  C.Term.eval f term

(* [select_implicant m ?env phi] selects an implicant of [phi] such that
   [m,?env |= phi] *)
let select_implicant
    (type formula)
    (module C : AbstractionContext with type formula = formula)
    interp
    ?(env=Env.empty)
    phi =
  let eval term = evaluate_term (module C) interp ~env term in
  let rec go phi =
    match C.Formula.destruct phi with
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
    | `Quantify _ | `Not _ -> invalid_arg "select_implicant"
  in
  match go phi with
  | Some phis -> Some (C.mk_and phis)
  | None -> None

let boxify
    (type formula)
    (type term)
    (module C : AbstractionContext with type formula = formula
                                    and type term = term)
    phi
    terms =
  let mk_box t ivl =
    let lower =
      match Interval.lower ivl with
      | Some lo -> [C.mk_leq (C.mk_real lo) t]
      | None -> []
    in
    let upper =
      match Interval.upper ivl with
      | Some hi -> [C.mk_leq t (C.mk_real hi)]
      | None -> []
    in
    lower@upper
  in
  match C.optimize_box phi terms with
  | `Sat intervals ->
    C.mk_and (List.concat (List.map2 mk_box terms intervals))
  | `Unsat -> C.mk_false
  | `Unknown -> assert false

let map_atoms
    (type formula)
    (type term)
    (module C : AbstractionContext with type formula = formula
                                    and type term = term)
    f
    phi =
  let alg = function
    | `And conjuncts -> C.mk_and conjuncts
    | `Or disjuncts -> C.mk_or disjuncts
    | `Tru -> C.mk_true
    | `Fls -> C.mk_false
    | `Not _ | `Quantify (_, _, _, _) -> invalid_arg "map_atoms"
    | `Atom (op, s, zero) -> f op s zero
  in
  C.Formula.eval alg phi

(* floor(term/divisor) + offset *)
type int_virtual_term =
  { term : V.t;
    divisor : int;
    offset : ZZ.t }
  [@@ deriving ord]

let pp_int_virtual_term
    (module C : AbstractionContext)
    formatter
    vt =
  begin
    if vt.divisor = 1 then
      pp_linterm (module C) formatter vt.term
    else
      Format.fprintf formatter "@[floor(@[%a@ / %d@])@]"
        (pp_linterm (module C)) vt.term
        vt.divisor
  end;
  if not (ZZ.equal vt.offset ZZ.zero) then
    Format.fprintf formatter "@ + %a@]" ZZ.pp vt.offset
  else
    Format.fprintf formatter "@]"

type virtual_term =
  | MinusInfinity
  | PlusEpsilon of V.t
  | Term of V.t
        [@@deriving ord]

let pp_virtual_term
    (module C : AbstractionContext)
    formatter =
  function
  | MinusInfinity -> Format.pp_print_string formatter "-oo"
  | PlusEpsilon t ->
    Format.fprintf formatter "%a + epsilon" (pp_linterm (module C)) t
  | Term t -> pp_linterm (module C) formatter t

(* Loos-Weispfenning virtual substitution *) 
let virtual_substitution
    (type formula)
    (module C : AbstractionContext with type formula = formula)
    x
    virtual_term
    phi =
  let pivot_term x term =
    V.pivot (dim_of_const x) (linterm_of (module C) term)
  in
  let replace_atom op s zero =
    assert (C.Term.equal zero (C.mk_real QQ.zero));

    (* s == s' + ax, x not in fv(s') *)
    let (a, s') = pivot_term x s in
    if QQ.equal a QQ.zero then
      match op with
      | `Eq -> C.mk_eq s zero
      | `Lt -> C.mk_lt s zero
      | `Leq -> C.mk_leq s zero
    else
      let soa = V.scalar_mul (QQ.inverse (QQ.negate a)) s' (* -s'/a *) in
      let mk_sub s t = of_linterm (module C) (V.add s (V.negate t)) in
      match op, virtual_term with
      | (`Eq, Term t) ->
        (* -s'/a = x = t <==> -s'/a = t *)
        C.mk_eq (mk_sub soa t) zero
      | (`Leq, Term t) ->
        if QQ.lt a QQ.zero then
          (* -s'/a <= x = t <==> -s'/a <= t *)
          C.mk_leq (mk_sub soa t) zero
        else
          (* t = x <= -s'/a <==> t <= -s'/a *)
          C.mk_leq (mk_sub t soa) zero
      | (`Lt, Term t) ->
        if QQ.lt a QQ.zero then
          (* -s'/a < x = t <==> -s'/a < t *)
          C.mk_lt (mk_sub soa t) zero
        else
          (* t = x < -s'/a <==> t < -s'/a *)
          C.mk_lt (mk_sub t soa) zero
      | `Eq, _ -> C.mk_false
      | (_, PlusEpsilon t) ->
        if QQ.lt a QQ.zero then
          (* -s'/a < x = t + eps <==> -s'/a <= t *)
          (* -s'/a <= x = t + eps <==> -s'/a <= t *)
          C.mk_leq (mk_sub soa t) zero
        else
          (* t + eps = x < -s'/a <==> t < -s'/a *)
          (* t + eps = x <= -s'/a <==> t < -s'/a *)
          C.mk_lt (mk_sub t soa) zero
      | (_, MinusInfinity) ->
        if QQ.lt a QQ.zero then
          (* -s'/a < x = -oo <==> false *)
          C.mk_false
        else
          (* -oo = x < -s'/a <==> true *)
          C.mk_true
  in
  map_atoms (module C) replace_atom phi


(* Model based projection, as in described in Anvesh Komuravelli, Arie
   Gurfinkel, Sagar Chaki: "SMT-based Model Checking for Recursive Programs".
   Given a structure m, a constant symbol x, and a set of
   linear terms T, find a virtual term vt such that
   - vt is -t/a (where ax + t in T) and m |= x = -t/a
   - vt is -t/a + epsilon (where ax + t in T) and m |= -t/a < x and
                          m |= 's/b < x ==> (-s/b <= s/a) for all bx + s in T
   - vt is -oo otherwise *)
let mbp_virtual_term
    (type formula)
    (type model)
    (module C : AbstractionContext with type formula = formula
                                    and type model = model)
    m
    x
    terms =
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
let terms
    (type formula)
    (module C : AbstractionContext with type formula = formula)
    phi =
  let alg = function
    | `And xs | `Or xs -> List.fold_left VS.union VS.empty xs
    | `Atom (_, s, t) ->
      V.add (linterm_of (module C) s) (V.negate (linterm_of (module C) t))
      |> VS.singleton
    | `Tru | `Fls -> VS.empty
    | `Not _ | `Quantify (_, _, _, _) -> invalid_arg "abstract.terms"
  in
  C.Formula.eval alg phi

exception Equal_term of V.t
let select_real_term
    (type formula)
    (type model)
    (module C : AbstractionContext with type formula = formula
                                    and type model = model)
    m
    x
    phi =

  let merge (lower1, upper1) (lower2, upper2) =
    let lower =
      match lower1, lower2 with
      | (x, None) | (None, x) -> x
      | (Some (s, s_val), Some (t, t_val)) ->
        if QQ.lt t_val s_val then
          Some (s, s_val)
        else
          Some (t, t_val)
    in
    let upper =
      match upper1, upper2 with
      | (x, None) | (None, x) -> x
      | (Some (s, s_val), Some (t, t_val)) ->
        if QQ.lt s_val t_val then
          Some (s, s_val)
        else
          Some (t, t_val)
    in
    (lower, upper)
  in
  let x_val = V.dot m (V.of_term QQ.one (dim_of_const x)) in
  let alg = function
    | `And xs | `Or xs -> List.fold_left merge (None, None) xs
    | `Atom (op, t, zero) ->
      assert (C.Term.equal zero (C.mk_real QQ.zero));

      let t = linterm_of (module C) t in
      let (a, t') = V.pivot (dim_of_const x) t in

      (* Atom is ax + t' op 0 *)
      if QQ.equal QQ.zero a then
        (None, None)
      else
        let toa = V.scalar_mul (QQ.inverse (QQ.negate a)) t' in
        let toa_val = V.dot m toa in
        if QQ.equal toa_val x_val && (op = `Leq || op = `Eq) then
          raise (Equal_term toa)
        else if QQ.lt a QQ.zero && QQ.lt toa_val x_val then
          (* Lower bound *)
          (Some (toa, toa_val), None)
        else if QQ.lt QQ.zero a && QQ.lt x_val toa_val then
          (* Upper bound *)
          (None, Some (toa, toa_val))
        else
          (None, None)
    | `Tru | `Fls -> (None, None)
    | `Not _ | `Quantify (_, _, _, _) -> invalid_arg "abstract.terms"
  in
  try
    match C.Formula.eval alg phi with
    | (Some (s, _), None) ->
      logf ~level:`trace "Found lower bound: %a < %a"
        (pp_linterm (module C))
        s C.pp_const x;
      V.add s (const_linterm (QQ.of_int (1)))
    | (None, Some (t, _)) ->
      logf ~level:`trace "Found upper bound: %a < %a"
        C.pp_const x
        (pp_linterm (module C)) t;
      V.add t (const_linterm (QQ.of_int (-1)))
    | (Some (s, _), Some (t, _)) ->
      logf ~level:`trace "Found interval: %a < %a < %a"
        (pp_linterm (module C)) s
        C.pp_const x
        (pp_linterm (module C)) t;
      V.scalar_mul (QQ.of_frac 1 2) (V.add s t)
    | (None, None) -> V.zero (* Value of x is irrelevant *)
  with Equal_term t ->
    (logf ~level:`trace "Found equal term: %a = %a"
       C.pp_const x
       (pp_linterm (module C)) t;
     t)

(* Given a prenex formula phi, compute a pair (qf_pre, psi) such that
   - qf_pre is a quantifier prefix [(Q0, a0);...;(Qn, an)] where each Qi is
     either `Exists or `Forall, and each ai is a Skolem constant
   - psi is negation- and quantifier-free formula, and contains no free
     variables
   - every atom of in psi is of the form t < 0, t <= 0, or t = 0
   - phi is equivalent to Q0 a0.Q1 a1. ... Qn. an. psi
*)
let normalize
    (type formula)
    (module C : AbstractionContext with type formula = formula)
    phi =
  let phi = C.Formula.prenex phi in
  let zero = C.mk_real QQ.zero in
  let rec normalize (env : C.term Env.t) phi =
    let subst = C.Formula.substitute (Env.find env) in
    match C.Formula.destruct phi with
    | `Not psi -> normalize_not env psi
    | `And conjuncts -> C.mk_and (List.map (normalize env) conjuncts)
    | `Or disjuncts -> C.mk_or (List.map (normalize env) disjuncts)
    | `Tru -> C.mk_true
    | `Fls -> C.mk_false
    | `Atom (`Eq, s, t) -> subst (C.mk_eq (C.mk_sub s t) zero)
    | `Atom (`Leq, s, t) -> subst (C.mk_leq (C.mk_sub s t) zero)
    | `Atom (`Lt, s, t) -> subst (C.mk_lt (C.mk_sub s t) zero)
    | `Quantify (_, _, _, _) -> invalid_arg "normalize: expected prenex"
  and normalize_not env phi =
    let subst = C.Formula.substitute (Env.find env) in
    match C.Formula.destruct phi with
    | `Not psi -> normalize env psi
    | `And conjuncts -> C.mk_or (List.map (normalize_not env) conjuncts)
    | `Or disjuncts -> C.mk_and (List.map (normalize_not env) disjuncts)
    | `Tru -> C.mk_false
    | `Fls -> C.mk_true
    | `Atom (`Eq, s, t) ->
      subst (C.mk_or [C.mk_lt (C.mk_sub s t) zero; C.mk_lt (C.mk_sub t s) zero])
    | `Atom (`Leq, s, t) -> subst (C.mk_lt (C.mk_sub t s) zero)
    | `Atom (`Lt, s, t) -> subst (C.mk_leq (C.mk_sub t s) zero)
    | `Quantify (_, _, _, _) -> invalid_arg "normalize: expected prenex"
  in
  let rec go env phi =
    match C.Formula.destruct phi with
    | `Quantify (qt, name, typ, psi) ->
      let k = C.mk_skolem ~name (typ :> Syntax.typ) in
      let (qf_pre, psi) = go (Env.push (C.mk_const k) env) psi in
      ((qt,k)::qf_pre, psi)
    | _ -> ([], normalize env phi)
  in
  go Env.empty phi

(* destruct_normal is safe to apply to a formula that has been
   normalized *)
let destruct_normal
    (type formula)
    (module C : AbstractionContext with type formula = formula)
    phi =
  let zero = C.mk_real QQ.zero in
  let destruct_int term =
    match C.Term.destruct term with
    | `Real q ->
      begin match QQ.to_zz q with
        | Some z -> z
        | None -> invalid_arg "destruct_normal"
      end
    | _ -> invalid_arg "destruct_normal"
  in
  match C.Formula.destruct phi with
  | `Not _ | `Quantify (_, _, _, _) -> invalid_arg "destruct_normal"
  | `And psis -> `And psis
  | `Or psis -> `Or psis
  | `Tru -> `Tru
  | `Fls -> `Fls
  | `Atom (`Eq, s, t) ->
    if not (C.Term.equal t zero) then invalid_arg "destruct_normal";
    begin match C.Term.destruct s with
    | `Binop (`Mod, dividend, modulus) ->

      (* Divisibility constraint *)
      let modulus = destruct_int modulus in
      `Divides (modulus, linterm_of (module C) dividend)
    | _ -> `CompareZero (`Eq, linterm_of (module C) s)
    end
  | `Atom (`Lt, s, t) ->
    if not (C.Term.equal t zero) then invalid_arg "destruct_normal";

    begin match C.Term.destruct s with
      | `Binop (`Mod, dividend, modulus) ->
        (* Indivisibility constraint: dividend % modulus < 0. *)
        let modulus = destruct_int modulus in
        `NotDivides (modulus, linterm_of (module C) dividend)

      | `Unop (`Neg, s') ->
        begin match C.Term.destruct s' with
          | `Binop (`Mod, dividend, modulus) ->
            (* Indivisibility constraint: dividend % modulus > 0 *)
            let modulus = destruct_int modulus in
            `NotDivides (modulus, linterm_of (module C) dividend)
          | _ -> `CompareZero (`Lt, linterm_of (module C) s)
        end

      | _ -> `CompareZero (`Lt, linterm_of (module C) s)
    end
  | `Atom (`Leq, s, t) ->
    if not (C.Term.equal t zero) then invalid_arg "destruct_normal";
    `CompareZero (`Leq, linterm_of (module C) s)

let destruct_normal
    (type formula)
    (module C : AbstractionContext with type formula = formula)
    phi =
  try destruct_normal (module C) phi
  with Nonlinear ->
    Log.errorf "Error destructing formula: %a" C.Formula.pp phi;
    raise Nonlinear

let mk_divides
    (type formula)
    (module C : AbstractionContext with type formula = formula)
    divisor
    term =
  assert(ZZ.lt ZZ.zero divisor);
  if ZZ.equal divisor ZZ.one then
    C.mk_true
  else
    let divisor = QQ.of_zz divisor in
    C.mk_eq
      (C.mk_mod (of_linterm (module C) term) (C.mk_real divisor))
      (C.mk_real QQ.zero)

let mk_not_divides
    (type formula)
    (module C : AbstractionContext with type formula = formula)
    divisor
    term =
  assert(ZZ.lt ZZ.zero divisor);
  if ZZ.equal divisor ZZ.one then
    C.mk_false
  else
    let divisor = QQ.of_zz divisor in
    C.mk_lt
      (C.mk_neg (C.mk_mod (of_linterm (module C) term) (C.mk_real divisor)))
      (C.mk_real QQ.zero)

let int_virtual_substitution
    (type formula)
    (module C : AbstractionContext with type formula = formula)
    x
    virtual_term
    phi =
  let zero = C.mk_real QQ.zero in
  (* phi[x -> floor(t/mu) + k]
     == \/_{i=0}^mu mu | t - i /\ phi[mu * x -> t - i + mu*k] *)
  (0 -- (virtual_term.divisor - 1))
  (*  ((-(virtual_term.divisor - 1)) -- (virtual_term.divisor - 1))*)
  /@ (fun i ->
      (* t - i + mu*k *)
      let replace_mux =
        V.add_term
          (QQ.of_zz
             (ZZ.sub
                (ZZ.mul
                   (ZZ.of_int virtual_term.divisor)
                   virtual_term.offset)
                (ZZ.of_int i)))
          const_dim
          virtual_term.term
      in

      let subst_term a s =
        V.add
          (V.scalar_mul a replace_mux)
          (V.scalar_mul (QQ.of_int virtual_term.divisor) s)
      in
      let rec subst phi =
        match destruct_normal (module C) phi with
        | `And psis -> C.mk_and (List.map subst psis)
        | `Or psis -> C.mk_or (List.map subst psis)
        | `Tru -> C.mk_true
        | `Fls -> C.mk_false
        | `Divides (delta, s) ->
          (* The atom is of the form
                delta | ax + s
             Replace with
                mu * delta | a(t - i + mu * k) + mu * s *)
          let (a, s) = V.pivot (dim_of_const x) s in
          if QQ.equal a QQ.zero then
            mk_divides (module C) delta s
          else
            mk_divides (module C)
              (ZZ.mul (ZZ.of_int virtual_term.divisor) delta)
              (subst_term a s)
        | `NotDivides (delta, s) ->
          (* The atom is of the form
                not(delta | ax + s)
             Replace with
                not(mu * delta | a(t - i + mu * k) + mu * s) *)
          let (a, s) = V.pivot (dim_of_const x) s in
          if QQ.equal a QQ.zero then
            mk_not_divides (module C) delta s
          else
            mk_not_divides (module C)
              (ZZ.mul (ZZ.of_int virtual_term.divisor) delta)
              (subst_term a s)
        | `CompareZero (op, s) ->
          (* The atom is of the form
                ax + s >< 0
             Replace with
               a(t - i + mu * k) + mu * s >< 0 *)
          let (a, s) = V.pivot (dim_of_const x) s in
          let mk_compare =
            match op with
            | `Eq -> C.mk_eq
            | `Lt -> C.mk_lt
            | `Leq -> C.mk_leq
          in
          if QQ.equal a QQ.zero then
            mk_compare (of_linterm (module C) s) zero
          else
            mk_compare (of_linterm (module C) (subst_term a s)) zero
      in

      (* mu | t - i *)
      let divisibility_constraint =
        if virtual_term.divisor == 1 then
          C.mk_true
        else
          let t_minus_i =
            V.add_term (QQ.of_int (-i)) const_dim virtual_term.term
            |> of_linterm (module C)
          in
          C.mk_eq
            (C.mk_mod t_minus_i (C.mk_real (QQ.of_int virtual_term.divisor)))
            zero
      in
      C.mk_and [subst phi; divisibility_constraint])
  |> BatList.of_enum
  |> C.mk_or

let substitute_real_term
    (type formula)
    (module C : AbstractionContext with type formula = formula)
    x
    t
    phi =
  let replace_term s =
    let (a, s') = V.pivot (dim_of_const x) s in
    if QQ.equal a QQ.zero then
      s
    else
      V.add s' (V.scalar_mul a t)
  in
  let zero = C.mk_real QQ.zero in
  let rec go phi =
    match destruct_normal (module C) phi with
    | `And psis -> C.mk_and (List.map go psis)
    | `Or psis -> C.mk_or (List.map go psis)
    | `Tru | `Fls -> phi
    | `Divides (delta, s) -> mk_divides (module C) delta (replace_term s)
    | `NotDivides (delta, s) -> mk_not_divides (module C) delta (replace_term s)
    | `CompareZero (op, s) ->
      let s = of_linterm (module C) (replace_term s) in
      match op with
      | `Eq -> C.mk_eq s zero
      | `Lt -> C.mk_lt s zero
      | `Leq -> C.mk_leq s zero
  in
  go phi

exception Redundant_path
module Scheme = struct

  type move =
    | MInt of int_virtual_term
    | MReal of V.t
          [@@deriving ord]

  let substitute
    (type formula)
    (module C : AbstractionContext with type formula = formula)
    x
    move
    phi =
    match move with
    | MInt vt -> int_virtual_substitution (module C) x vt phi
    | MReal t -> substitute_real_term (module C) x t phi

  let evaluate_move model move =
    match move with
    | MInt vt ->
      begin match QQ.to_zz (V.dot vt.term model) with
        | None -> assert false
        | Some tv ->
          ZZ.add (Mpzf.fdiv_q tv (ZZ.of_int vt.divisor)) vt.offset
          |> QQ.of_zz
      end
    | MReal t -> V.dot t model

  let pp_move
      (module C : AbstractionContext)
      formatter
      move =
    match move with
    | MInt vt -> pp_int_virtual_term (module C) formatter vt
    | MReal t -> pp_linterm (module C) formatter t

  let const_of_move move =
    match move with
    | MReal t -> const_of_linterm t
    | MInt vt ->
      if vt.divisor = 1 then const_of_linterm vt.term
      else None

  module MM = BatMap.Make(struct type t = move [@@deriving ord] end)

  type t =
    | SForall of const_sym * const_sym * t
    | SExists of const_sym * (t MM.t)
    | SEmpty

  let pp
      (module C : AbstractionContext)
      formatter
      scheme =
    let open Format in
    let rec pp formatter = function
      | SForall (k, sk, t) ->
        fprintf formatter "@[(forall %a:@\n  @[%a@])@]" C.pp_const sk pp t
      | SExists (k, mm) ->
        let pp_elt formatter (move, scheme) =
          fprintf formatter "%a:@\n  @[%a@]@\n"
            (pp_move (module C)) move
            pp scheme
        in
        fprintf formatter "@[(exists %a:@\n  @[%a@])@]"
          C.pp_const k
          (ApakEnum.pp_print_enum pp_elt) (MM.enum mm)
      | SEmpty -> ()
    in
    pp formatter scheme

  let rec size = function
    | SEmpty -> 1
    | SForall (_, _, t) -> size t
    | SExists (_, mm) ->
      MM.enum mm
      /@ (fun (_, t) -> size t)
      |> BatEnum.sum

  let empty = SEmpty

  (* Create a new scheme where the only path is the given path *)
  let mk_path
      (module C : AbstractionContext)
      path =
    let rec go = function
      | [] -> SEmpty
      | (`Forall k)::path ->
        let sk =
          C.mk_skolem ~name:(Putil.mk_show C.pp_const k) (C.const_typ k)
        in
        SForall (k, sk, go path)
      | (`Exists (k, move))::path ->
        SExists (k, MM.add move (go path) MM.empty)
    in
    go path

  (* Add a path (corresponding to a new instantiation of the existential
     variables of some formula) to a scheme.  Raise Redundant_path if this
     path already belonged to the scheme. *)
  let add_path
      (module C : AbstractionContext)
      path
      scheme =

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
          with Not_found -> mk_path (module C) path
        in
        SExists (k, MM.add move subscheme mm)
      | (_, _) -> assert false
    in
    match scheme with
    | SEmpty -> mk_path (module C) path
    | _ -> go path scheme

  (* Used for incremental construction of the winning formula:
       (winning_formula scheme phi) = \/_p winning_path_formula p scheme phi *)
  let path_winning_formula
      (type formula)
      (module C : AbstractionContext with type formula = formula)
      path
      scheme
      phi =
    let rec go path scheme =
      match path, scheme with
      | ([], SEmpty) -> phi
      | (`Forall k::path, SForall (k', sk, scheme)) ->
        assert (k = k');

        let term = V.of_term QQ.one (dim_of_const sk) in
        substitute_real_term (module C) k term (go path scheme)

      | (`Exists (k, move)::path, SExists (k', mm)) ->
        assert (k = k');
        substitute (module C) k move (go path (MM.find move mm))
      | (_, _) -> assert false
    in
    go path scheme

  (* winning_formula scheme phi is valid iff scheme is a winning scheme for
     the formula phi *)
  let winning_formula
      (type formula)
      (module C : AbstractionContext with type formula = formula)
      scheme
      phi =
    let rec go = function
      | SEmpty -> phi
      | SForall (k, sk, scheme) ->
        let move = V.of_term QQ.one (dim_of_const sk) in
        substitute_real_term (module C) k move (go scheme)
      | SExists (k, mm) ->
        MM.enum mm
        /@ (fun (move, scheme) -> substitute (module C) k move (go scheme))
        |> BatList.of_enum
        |> C.mk_or
    in
    go scheme
end

let select_int_term
    (type formula)
    (module C : AbstractionContext with type formula = formula)
    m
    x
    phi =
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
  let x_val = match QQ.to_zz (V.coeff (dim_of_const x) m) with
    | Some zz -> zz
    | None -> assert false
  in
  let is_sat op t =
    match op with
    | `Leq -> QQ.leq (V.dot m t) QQ.zero
    | `Lt -> QQ.lt (V.dot m t) QQ.zero
    | `Eq -> QQ.equal (V.dot m t) QQ.zero
  in
  (* delta = gcd { lcm(d,a) : d | ax + t or not(d | ax + t) in atoms }.  If
     [[vt]](m) = [[x]](m) mod delta, then for every divisilibity atom
       d | ax + t
     which appears in phi, we have
       m |= (d | ax + t)   <==>   m |= (d | a(vt) + t *)
  let delta =
    let rec go phi =
      match destruct_normal (module C) phi with
      | `And xs | `Or xs -> List.fold_left ZZ.gcd ZZ.one (List.map go xs)
      | `Tru | `Fls | `CompareZero (_, _) -> ZZ.one
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
    match QQ.to_zz (Scheme.evaluate_move m (Scheme.MInt vt)) with
    | Some v -> v
    | None -> assert false
  in
  let rec go phi =
    match destruct_normal (module C) phi with
    | `And xs | `Or xs -> List.fold_left merge `None (List.map go xs)
    | `Tru | `Fls -> `None
    | `Divides (_, _) | `NotDivides (_, _) -> `None
    | `CompareZero (op, t) when is_sat op t ->
      let (a, t) = V.pivot (dim_of_const x) t in
      let a = match QQ.to_zz a with
        | None -> assert false
        | Some zz -> match ZZ.to_int zz with
          | None -> assert false
          | Some z -> z
      in
      let t_val = match QQ.to_zz (V.dot m t) with
        | Some zz -> zz
        | None -> assert false
      in
      if a = 0 then
        `None
      else if a > 0 then
        (* ax + t (<|<=) 0 --> upper bound of floor(-t/a) *)
        (* x (<|<=) floor(-t/a) + ([[x - floor(-t/a)]] mod delta) - delta *)
        let rhs_val = Mpzf.fdiv_q (ZZ.negate t_val) (ZZ.of_int a) in
        let vt =
          { term = V.negate t;
            divisor = a;
            offset =
              let res = Mpzf.fdiv_r (ZZ.sub x_val rhs_val) delta in
              if ZZ.equal res ZZ.zero && op != `Lt then
                ZZ.zero
              else
                ZZ.sub res delta
          }
        in
        `Upper (vt, evaluate_vt vt)
      else
        (* (-a)x + t (<|<=) 0 --> lower bound of ceil(t/a) = floor((t+a-1)/2) *)
        let rhs =
          V.add_term (QQ.negate (QQ.add (QQ.of_int a) QQ.one)) const_dim t
        in
        let t_val = match QQ.to_zz (V.dot m rhs) with
          | Some zz -> zz
          | None -> assert false
        in

        let rhs_val = Mpzf.fdiv_q (ZZ.negate t_val) (ZZ.of_int a) in
        let vt =
          { term = rhs;
            divisor = -a;
            offset =
              let res = Mpzf.fdiv_r (ZZ.sub x_val rhs_val) delta in
              if ZZ.equal res ZZ.zero && op = `Lt then
                delta
              else
                res }
        in
        `Lower (vt, evaluate_vt vt)

    | `CompareZero (op, t) -> `None
  in
  let vt_val vt =
    let tval = match QQ.to_zz (V.dot m vt.term) with
      | Some zz -> zz
      | None -> assert false
    in
    ZZ.add (Mpzf.fdiv_q tval (ZZ.of_int vt.divisor)) vt.offset
  in
  match go phi with
  | `Lower (vt, _) ->
    logf ~level:`trace "Found lower bound: %a < %a"
      (pp_int_virtual_term (module C)) vt
      C.pp_const x;
    assert (ZZ.equal (Mpzf.fdiv_r x_val delta) (Mpzf.fdiv_r (vt_val vt) delta));
    vt
  | `Upper (vt, _)->
    logf ~level:`trace "Found upper bound: %a < %a"
      C.pp_const x
      (pp_int_virtual_term (module C)) vt;
    assert (ZZ.equal (Mpzf.fdiv_r x_val delta) (Mpzf.fdiv_r (vt_val vt) delta));
    vt
  | `None ->
    logf ~level:`trace "Irrelevant: %a" C.pp_const x;
    (* Value of x is irrelevant *)
    { term = V.zero; divisor = 1; offset = ZZ.zero }

module CounterStrategySynthesis (C : AbstractionContext) = struct

  type ctx =
    { formula : C.formula;
      not_formula : C.formula; (* Negated formula *)
      mutable scheme : Scheme.t; (* scheme for formula *)
      solver : C.solver (* solver for the *negation* of the winning formula
                           for scheme (unsat iff there is a winning SAT
                           strategy for formula which conforms to scheme) *)
    }

  let add_path ctx path =
    try
      ctx.scheme <- Scheme.add_path (module C) path ctx.scheme;
      let win =
        Scheme.path_winning_formula (module C) path ctx.scheme ctx.formula
      in
      C.Solver.add ctx.solver [C.mk_not win]
    with Redundant_path -> ()

  (* Check if a given scheme is winning.  If not, synthesize a
     counter-strategy. *)
  let get_counter_strategy select_term ctx =
    logf "%a" (Scheme.pp (module C)) ctx.scheme;
    match C.Solver.get_model ctx.solver with
    | `Unsat -> `Unsat
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
        logf "Path model: %a" (pp_linterm (module C)) path_model;
        let open Scheme in
        match scheme with
        | SForall (k, sk, scheme) ->
          let path_model =
            V.add_term
              (C.Model.eval_real m (C.mk_const sk))
              (dim_of_const k)
              path_model
          in
          logf ~level:`trace "Forall %a" C.pp_const k;
          let (counter_phi, counter_paths) =
            counter_strategy path_model scheme
          in
          let move = select_term path_model k counter_phi in
          logf ~level:`trace "Found move: %a = %a"
            C.pp_const k
            (Scheme.pp_move (module C)) move;
          let counter_phi = Scheme.substitute (module C) k move counter_phi in
          let counter_paths =
            List.map (fun path -> (`Exists (k, move))::path) counter_paths
          in
          (counter_phi, counter_paths)
        | SExists (k, mm) ->
          let (counter_phis, paths) =
            MM.enum mm
            /@ (fun (move, scheme) ->
                let path_model =
                  V.add_term
                    (Scheme.evaluate_move path_model move)
                    (dim_of_const k)
                    path_model
                in
                let (counter_phi, counter_paths) =
                  counter_strategy path_model scheme
                in
                let counter_phi =
                  Scheme.substitute (module C) k move counter_phi
                in
                let counter_paths =
                  List.map (fun path -> (`Forall k)::path) counter_paths
                in
                (counter_phi, counter_paths))
            |> BatEnum.uncombine
          in
          (C.mk_and (BatList.of_enum counter_phis),
           BatList.concat (BatList.of_enum paths))
        | SEmpty ->
          let phi_implicant =
            let interp x = V.coeff (dim_of_const x) path_model in
            let implicant =
              select_implicant (module C) interp ctx.not_formula
            in
            match implicant with
            | Some x -> x
            | None -> assert false
          in
          logf ~level:`trace "Implicant: %a" C.Formula.pp phi_implicant;
          (phi_implicant, [[]])
      in
      `Sat (snd (counter_strategy (const_linterm QQ.one) ctx.scheme))

  (* Check to see if the matrix of a prenex formula is satisfiable.  If it is,
     initialize a sat/unsat strategy scheme pair. *)
  let initialize_pair select_term qf_pre phi =
    match C.get_model phi with
    | `Unsat -> `Unsat
    | `Unknown -> `Unknown
    | `Sat m ->
      logf "Found initial model";

      let phi_model =
        List.fold_left
          (fun v (_, k) ->
             V.add_term (C.Model.eval_real m (C.mk_const k)) (dim_of_const k) v)
          (const_linterm QQ.one)
          qf_pre
      in

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
        (sat_path, unsat_path, Scheme.substitute (module C) x move phi)
      in
      let (sat_path, unsat_path, _) = List.fold_right f qf_pre ([], [], phi) in
      let not_phi = snd (normalize (module C) (C.mk_not phi)) in
      let sat_ctx =
        let scheme = Scheme.mk_path (module C) sat_path in
        let win =
          Scheme.path_winning_formula (module C) sat_path scheme phi
        in
        let solver = C.Solver.mk_solver () in
        C.Solver.add solver [C.mk_not win];
        { formula = phi;
          not_formula = not_phi;
          scheme = scheme;
          solver = solver }
      in
      let unsat_ctx =
        let scheme = Scheme.mk_path (module C) unsat_path in
        let win =
          Scheme.path_winning_formula (module C) unsat_path scheme not_phi
        in
        let solver = C.Solver.mk_solver () in
        C.Solver.add solver [C.mk_not win];
        { formula = not_phi;
          not_formula = phi;
          scheme = scheme;
          solver = solver }
      in
      logf "Initial SAT strategy:@\n%a"
        (Scheme.pp (module C)) sat_ctx.scheme;
      logf "Initial UNSAT strategy:@\n%a"
        (Scheme.pp (module C)) unsat_ctx.scheme;
      `Sat (sat_ctx, unsat_ctx)

  let is_sat select_term sat_ctx unsat_ctx =
    let rec is_sat () =
      logf ~attributes:[`Blue;`Bold] "Checking if SAT wins";
      match get_counter_strategy select_term sat_ctx with
      | `Sat paths -> (List.iter (add_path unsat_ctx) paths; is_unsat ())
      | `Unsat -> `Sat
      | `Unknown -> `Unknown
    and is_unsat () =
      logf ~attributes:[`Blue;`Bold] "Checking if UNSAT wins";
      match get_counter_strategy select_term unsat_ctx with
      | `Sat paths -> (List.iter (add_path sat_ctx) paths; is_sat ())
      | `Unsat -> `Unsat
      | `Unknown -> `Unknown
    in
    is_sat ()

  let reset ctx =
    C.Solver.reset ctx.solver;
    ctx.scheme <- Scheme.SEmpty
end

let aqsat
    (type formula)
    (module C : AbstractionContext with type formula = formula)
    phi =
  let module CSS = CounterStrategySynthesis(C) in
  let constants = C.Formula.fold_constants KS.add phi KS.empty in
  let (qf_pre, phi) = normalize (module C) phi in
  let qf_pre =
    (List.map (fun k -> (`Exists, k)) (KS.elements constants))@qf_pre
  in
  let select_term model x phi =
    match C.const_typ x with
    | `TyInt -> Scheme.MInt (select_int_term (module C) model x phi)
    | `TyReal -> Scheme.MReal (select_real_term (module C) model x phi)
    | `TyBool | `TyFun (_, _) -> assert false
  in
  match CSS.initialize_pair select_term qf_pre phi with
  | `Unsat -> `Unsat
  | `Unknown -> `Unknown
  | `Sat (sat_ctx, unsat_ctx) -> CSS.is_sat select_term sat_ctx unsat_ctx

let aqopt
    (type formula)
    (type term)
    (module C : AbstractionContext with type formula = formula
                                    and type term = term)
    phi
    t =
  let module CSS = CounterStrategySynthesis(C) in
  let objective_constants = C.Term.fold_constants KS.add t KS.empty in
  let constants = C.Formula.fold_constants KS.add phi objective_constants in
  let (qf_pre, phi) = normalize (module C) phi in
  let qf_pre =
    ((List.map (fun k -> (`Exists, k)) (KS.elements constants))@qf_pre)
  in

  (* First, check if the objective function is unbounded.  This is done by
     checking satisfiability of the formula:
       forall i. exists ks. phi /\ t >= i
  *)
  let objective = C.mk_skolem ~name:"objective" `TyReal in
  let qf_pre_unbounded =
    (`Forall, objective)::qf_pre
  in
  let phi_unbounded =
    C.mk_and [phi;
              C.mk_leq (C.mk_sub (C.mk_const objective) t) (C.mk_real QQ.zero)]
  in
  let not_phi_unbounded =
    snd (normalize (module C) (C.mk_not phi_unbounded))
  in
  (* Always select [[objective]](m) as the value of objective *)
  let select_term m x phi =
    if x = objective then
      Scheme.MReal (const_linterm (V.coeff (dim_of_const x) m))
    else
      match C.const_typ x with
      | `TyInt -> Scheme.MInt (select_int_term (module C) m x phi)
      | `TyReal -> Scheme.MReal (select_real_term (module C) m x phi)
      | `TyBool | `TyFun (_, _) -> assert false
  in
  match CSS.initialize_pair select_term qf_pre_unbounded phi_unbounded with
  | `Unsat -> `Unsat
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
          C.Solver.add sat_ctx.CSS.solver [
            C.mk_lt (C.mk_const objective_skolem) (C.mk_real b)
          ]
      end;
      match CSS.is_sat select_term sat_ctx unsat_ctx with
      | `Unknown -> `Unknown
      | `Sat -> `Sat (Interval.make None bound)
      | `Unsat ->

        (* Find the largest constant which has been selected as an (UNSAT)
           move for the objective bound, and the associated sub-scheme *)
        let (opt, opt_scheme) = match unsat_ctx.CSS.scheme with
          | Scheme.SExists (_, mm) ->
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
          let win =
            Scheme.winning_formula (module C) (go opt_scheme) not_phi_unbounded
          in
          C.mk_not win
        in
        begin match C.optimize_box bounded_phi [t] with
          | `Unknown ->
            Log.errorf "Failed to optimize - returning conservative bound";
            `Sat (Interval.make None bound)
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

exception Unknown
let qe_mbp
    (type formula)
    (module C : AbstractionContext with type formula = formula)
    phi =
  let (qf_pre, phi) = normalize (module C) phi in
  let exists x phi =
    let solver = C.Solver.mk_solver () in
    let disjuncts = ref [] in
    let constants =
      KS.elements (C.Formula.fold_constants KS.add phi KS.empty)
    in
    let terms = terms (module C) phi in
    let rec loop () =
      match C.Solver.get_model solver with
      | `Sat m ->
        let model =
          List.fold_right
            (fun k v ->
               V.add_term
                 (C.Model.eval_real m (C.mk_const k))
                 (dim_of_const k)
                 v)
            constants
            (const_linterm QQ.one)
        in
        let vt = mbp_virtual_term (module C) model x terms in
        let psi = virtual_substitution (module C) x vt phi in
        disjuncts := psi::(!disjuncts);
        C.Solver.add solver [C.mk_not psi];
        loop ()
      | `Unsat -> C.mk_or (!disjuncts)
      | `Unknown -> raise Unknown
    in
    C.Solver.add solver [phi];
    loop ()
  in
  let qe (qt, x) phi =
    match qt with
    | `Exists ->
      exists x (snd (normalize (module C) phi))
    | `Forall ->
      C.mk_not (exists x (snd (normalize (module C) (C.mk_not phi))))
  in
  List.fold_right qe qf_pre phi

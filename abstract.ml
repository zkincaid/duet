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

(** [select_disjunct m phi] selects a clause [psi] in the disjunctive normal
      form of [psi] such that [m |= psi] *)
let select_disjunct
    (type formula)
    (type model)
    (module C : AbstractionContext with type formula = formula
                                    and type model = model)
    phi
    m =
  let eval = C.Model.eval_real m in
  let f = function
    | `Tru -> Some C.mk_true
    | `Fls -> None

    | `Atom (`Eq, s, t) when QQ.equal (eval s) (eval t) -> Some (C.mk_eq s t)
    | `Atom (`Leq, s, t) when QQ.leq (eval s) (eval t) -> Some (C.mk_eq s t)
    | `Atom (`Lt, s, t) when QQ.lt (eval s) (eval t) -> Some (C.mk_lt s t)
    | `Atom (_, _, _) -> None

    | `Or disjuncts ->
      (* Find satisfied disjunct *)
      let f old = function
        | Some phi -> Some phi
        | None -> old
      in
      List.fold_left f None disjuncts

    | `And conjuncts ->
      (* All conjuncts must be satisfied *)
      let f = function
        | Some x -> x
        | None -> raise Not_found
      in
      (try Some (C.mk_and (List.map f conjuncts))
       with Not_found -> None)

    | `Quantify (_, _, _, _) | `Not _ -> invalid_arg "select_disjunct"
  in
  C.Formula.eval f phi

(* As [select_disjunct], except the model m is represented as a vector and all
   terms are assumed to be linear (so that a term t may be evaluated with
   V.dot m t) *)
let select_disjunct_linear
    (type formula)
    (type model)
    (module C : AbstractionContext with type formula = formula
                                    and type model = model)
    phi
    m =
  let eval t = V.dot m (linterm_of (module C) t) in
  let f = function
    | `Tru -> Some []
    | `Fls -> None

    | `Atom (`Eq, s, t) when QQ.equal (eval s) (eval t) -> Some [C.mk_eq s t]
    | `Atom (`Leq, s, t) when QQ.leq (eval s) (eval t) -> Some [C.mk_eq s t]
    | `Atom (`Lt, s, t) when QQ.lt (eval s) (eval t) -> Some [C.mk_lt s t]
    | `Atom (_, _, _) -> None

    | `Or disjuncts ->
      (* Find satisfied disjunct *)
      let f old = function
        | Some phi -> Some phi
        | None -> old
      in
      List.fold_left f None disjuncts

    | `And conjuncts ->
      (* All conjuncts must be satisfied *)
      let f = function
        | Some x -> x
        | None -> raise Not_found
      in
      (try Some (BatList.concat (List.map f conjuncts))
       with Not_found -> None)

    | `Quantify (_, _, _, _) | `Not _ -> invalid_arg "select_disjunct"
  in
  match C.Formula.eval f phi with
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
    | `Not _ | `Quantify (_, _, _, _) -> invalid_arg "aq_sat"
    | `Atom (op, s, zero) -> f op s zero
  in
  C.Formula.eval alg phi

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

module VirtualTerm = struct
  module Inner = struct
    type t = virtual_term [@@deriving ord]
  end
  include Inner
  module Set = BatSet.Make(Inner)
end

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

(* Compute the set of normalized linear terms which appear in a aq_normalized
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
let mbp_term
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
          (logf ~level:`trace "LB: %a < %a" (pp_linterm (module C)) toa C.pp_const x;
          (Some (toa, toa_val), None))
        else if QQ.lt QQ.zero a && QQ.lt x_val toa_val then
          (* Upper bound *)
          (logf ~level:`trace "UB: %a < %a" C.pp_const x (pp_linterm (module C)) toa;
          (None, Some (toa, toa_val)))
        else
          (None, None)
    | `Tru | `Fls -> (None, None)
    | `Not _ | `Quantify (_, _, _, _) -> invalid_arg "abstract.terms"
  in
  try
    match C.Formula.eval alg phi with
    | (Some (s, _), None) ->
      logf ~level:`trace "Found lower bound: %a < %a" (pp_linterm (module C)) s C.pp_const x;
      V.add s (const_linterm (QQ.of_int (1)))
    | (None, Some (t, _)) ->
      logf ~level:`trace "Found upper bound: %a < %a" C.pp_const x (pp_linterm (module C)) t;
      V.add t (const_linterm (QQ.of_int (-1)))
    | (Some (s, _), Some (t, _)) ->
      logf ~level:`trace "Found interval: %a < %a < %a" (pp_linterm (module C)) s C.pp_const x (pp_linterm (module C)) t;
      V.scalar_mul (QQ.of_frac 1 2) (V.add s t)
    | (None, None) -> V.zero (* Value of x is irrelevant *)
  with Equal_term t ->
    (logf ~level:`trace "Found equal term: %a = %a" C.pp_const x (pp_linterm (module C)) t;
     t)

module CT = BatHashtbl.Make(struct
    type t = const_sym
    let equal = (=)
    let hash = Hashtbl.hash
  end)

(* Given a prenex formula phi, compute a pair (qf_pre, psi) such that
   - qf_pre is a quantifier prefix [(Q0, a0);...;(Qn, an)] where each Qi is
     either `Exists or `Forall, and each ai is a Skolem constant
   - psi is negation- and quantifier-free formula, and contains no free
     variables
   - every atom of in psi is of the form t < 0, t <= 0, or t = 0
   - phi is equivalent to Q0 a0.Q1 a1. ... Qn. an. psi
*)
let aq_normalize
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
    | `Quantify (_, _, _, _) -> invalid_arg "aq_normalize: expected prenex"
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
    | `Quantify (_, _, _, _) -> invalid_arg "aq_normalize: expected prenex"
  in
  let rec go env phi =
    match C.Formula.destruct phi with
    | `Quantify (qt, name, typ, psi) ->
      let k = C.mk_skolem ~name `TyReal in
      let (qf_pre, psi) = go (Env.push (C.mk_const k) env) psi in
      ((qt,k)::qf_pre, psi)
    | _ -> ([], normalize env phi)
  in
  go Env.empty phi

let negate_quantifier_prefix =
  List.map (function
      | (`Exists, a) -> (`Forall, a)
      | (`Forall, a) -> (`Exists, a))

(* Substitute t for x in phi *)
let substitute_one
    (type formula)
    (module C : AbstractionContext with type formula = formula)
    x
    t
    phi =
  let f op s zero =
    let s = linterm_of (module C) s in
    let (a, s') = V.pivot (dim_of_const x) s in
    let replacement =
      if QQ.equal a QQ.zero then
        s
      else
        V.add s' (V.scalar_mul a t)
    in
    let replacement_term = of_linterm (module C) replacement in
    match op with
    | `Eq -> C.mk_eq replacement_term zero
    | `Leq -> C.mk_leq replacement_term zero
    | `Lt -> C.mk_lt replacement_term zero
  in
  map_atoms (module C) f phi


exception Redundant_path
module Scheme = struct
  type t =
    | STExists of const_sym * const_sym * t
    | STForall of const_sym * (t VM.t)
    | STLeaf

  let pp
      (module C : AbstractionContext)
      formatter
      scheme =
    let open Format in
    let rec pp formatter = function
      | STExists (k, sk, t) ->
        fprintf formatter "@[(exists %a:@\n  @[%a@])@]" C.pp_const sk pp t
      | STForall (k, vm) ->
        let pp_elt formatter (move, scheme) =
          fprintf formatter "%a:@\n  @[%a@]@\n"
            (pp_linterm (module C)) move
            pp scheme
        in
        fprintf formatter "@[(forall %a:@\n  @[%a@])@]"
          C.pp_const k
          (ApakEnum.pp_print_enum pp_elt) (VM.enum vm)
      | STLeaf -> ()
    in
    pp formatter scheme

  let rec size = function
    | STLeaf -> 1
    | STExists (_, _, t) -> size t
    | STForall (_, vm) ->
      VM.enum vm
      /@ (fun (_, t) -> size t)
      |> BatEnum.sum

  let empty = STLeaf

  let fold_paths f acc scheme =
    let rec go acc path = function
      | STLeaf -> f acc (List.rev path)
      | STExists (k, sk, scheme) ->
        go acc (`Exists (k, sk)::path) scheme
      | STForall (k, vm) ->
        BatEnum.fold (fun acc (term, scheme) ->
            go acc ((`Forall (k, term))::path) scheme)
          acc
          (VM.enum vm)
    in
    go acc [] scheme

  let fold_substitutions f acc scheme =
    let rec go acc path = function
      | STLeaf -> f acc (List.rev path)
      | STExists (k, sk, scheme) ->
        let term = V.of_term QQ.one (dim_of_const sk) in
        go acc ((k, term)::path) scheme
      | STForall (k, vm) ->
        BatEnum.fold (fun acc (term, scheme) ->
            go acc ((k, term)::path) scheme)
          acc
          (VM.enum vm)
    in
    go acc [] scheme

  let fold_skolem f acc scheme =
    let rec go acc = function
      | STLeaf -> acc
      | STExists (k, sk, scheme) -> go (f acc sk) scheme
      | STForall (k, vm) ->
        BatEnum.fold
          (fun acc (_, scheme) -> go acc scheme)
          acc
          (VM.enum vm)
    in
    go acc scheme

  let mk_empty
      (module C : AbstractionContext)
      path =
    let rec go = function
      | [] -> STLeaf
      | (`Exists k)::path ->
        let sk = C.mk_skolem ~name:(Putil.mk_show C.pp_const k) `TyReal in
        STExists (k, sk, go path)
      | (`Forall (k, t))::path -> STForall (k, VM.empty)
    in
    go path

  (* Given an input path, create pair consisting of (1) a substitution
     corresponding to the path and (2) a new scheme where the only path is
     the path *)
  let mk_path
      (module C : AbstractionContext)
      path =
    let rec go = function
      | [] -> ([], STLeaf)
      | (`Exists k)::path ->
        let sk = C.mk_skolem ~name:(Putil.mk_show C.pp_const k) `TyReal in
        let term = V.of_term QQ.one (dim_of_const sk) in
        let (subst, result_scheme) = go path in
        ((k, term)::subst, STExists (k, sk, result_scheme))
      | (`Forall (k, move))::path ->
        let (subst, result_scheme) = go path in
        ((k, move)::subst, STForall (k, VM.add move result_scheme VM.empty))
    in
    go path

  (* Given an input path and a scheme, create a pair consisting of (1) a
     substitution corresponding to the path and (2) the result of adding the
     path to the input scheme *)
  let add_path
      (module C : AbstractionContext)
      path
      scheme =

    let rec go path scheme =
      match path, scheme with
      | ([], STLeaf) ->
        (* path was already in scheme *)
        raise Redundant_path

      | (`Exists k::path, STExists (k', sk, scheme)) ->
        assert (k = k');
        let (subst, child) = go path scheme in
        let term = V.of_term QQ.one (dim_of_const sk) in
        ((k, term)::subst, STExists (k, sk, child))

      | (`Forall (k, move)::path, STForall (k', vm)) ->
        assert (k = k');
        let (subst, child) =
          try go path (VM.find move vm)
          with Not_found -> mk_path (module C) path
        in
        ((k, move)::subst, STForall (k, VM.add move child vm))
      | (_, _) -> assert false
    in
    go path scheme

  let formula_of_scheme
      (type formula)
      (module C : AbstractionContext with type formula = formula)
      scheme
      phi =
    let f constraints subst =
      let new_constraint =
        List.fold_right
          (fun (k, move) phi -> substitute_one (module C) k move phi)
          subst
          phi
      in
      new_constraint::constraints
    in
    fold_substitutions f [] scheme
    |> C.mk_and
end

let aqsat_impl
    (type formula)
    (type solver)
    (module C : AbstractionContext with type formula = formula
                                    and type solver = solver)
    mbp_term
    (sat_scheme, sat_solver, phi)
    (unsat_scheme, unsat_solver, not_phi) =

  (* Synthesize a winning strategy for SAT, if one exists.  If so, update
     unsat_solver and unsat_scheme so in the next round a counter-strategy will
     be synthesized. *)
  let find_strategy
      (sat_scheme, sat_solver, phi)
      (unsat_scheme, unsat_solver, not_phi) =

    logf "%a" (Scheme.pp (module C)) sat_scheme;
    logf "Checking sat... %d" (Scheme.size sat_scheme);
    match C.Solver.get_model sat_solver with
    | `Sat m ->
      logf "Strategy formula is SAT!";

      (* Using the model m, synthesize a counter-strategy which beats the
         strategy unsat-strategy.  This is done by traversing the SAT strategy
         scheme: on the way down, we build a model of phi from the labels on
         the path to the root.  On the way up, we find elimination terms for
         each variable using model-based projection.  *)
      let rec counter_strategy path_model scheme =
        let open Scheme in
        match scheme with
        | STExists (k, sk, scheme) ->
          let path_model =
            V.add_term
              (C.Model.eval_real m (C.mk_const sk))
              (dim_of_const k)
              path_model
          in
          let (counter_phi, counter_paths) =
            counter_strategy path_model scheme
          in
          let move = mbp_term path_model k counter_phi in
          logf ~level:`trace "Found move: %a = %a"
            C.pp_const k
            (pp_linterm (module C)) move;
          let counter_phi = substitute_one (module C) k move counter_phi in
          let counter_paths =
            List.map (fun path -> (`Forall (k, move))::path) counter_paths
          in
          (counter_phi, counter_paths)
        | STForall (k, vm) ->
          let (counter_phis, paths) =
            VM.enum vm
            /@ (fun (move, scheme) ->
                let path_model =
                  V.add_term
                    (V.dot move path_model)
                    (dim_of_const k)
                    path_model
                in
                let (counter_phi, counter_paths) =
                  counter_strategy path_model scheme
                in
                let counter_phi =
                  substitute_one (module C) k move counter_phi
                in
                let counter_paths =
                  List.map (fun path -> (`Exists k)::path) counter_paths
                in
                (counter_phi, counter_paths))
            |> BatEnum.uncombine
          in
          (C.mk_and (BatList.of_enum counter_phis),
           BatList.concat (BatList.of_enum paths))
        | STLeaf ->
          let phi_core =
            match select_disjunct_linear (module C) phi path_model with
            | Some x -> x
            | None -> assert false
          in
          logf ~level:`trace "Core: %a" C.Formula.pp phi_core;
          (phi_core, [[]])
      in
      let unsat_scheme =
        let add_counter_path unsat_scheme path =
          try
            let (subst, unsat_scheme) =
              Scheme.add_path (module C) path unsat_scheme
            in
            C.Solver.add
              unsat_solver
              [List.fold_right
                 (fun (x, move) phi -> substitute_one (module C) x move phi)
                 subst
                 not_phi];
            unsat_scheme
          with Redundant_path -> unsat_scheme
        in
        List.fold_left
          add_counter_path
          unsat_scheme
          (snd (counter_strategy (const_linterm QQ.one) sat_scheme))
      in
      `Sat unsat_scheme
    | `Unsat -> `Unsat
    | `Unknown -> `Unknown
  in
  let rec is_sat (sat_scheme, unsat_scheme) =
    logf ~attributes:[`Blue;`Bold] "Synthesizing SAT strategy";
    match find_strategy (sat_scheme, sat_solver, phi) (unsat_scheme, unsat_solver, not_phi) with
    | `Sat unsat_scheme -> is_unsat (sat_scheme, unsat_scheme)
    | `Unsat -> `Unsat (sat_scheme, unsat_scheme)
    | `Unknown -> `Unknown
  and is_unsat (sat_scheme, unsat_scheme) =
    logf ~attributes:[`Red;`Bold] "Synthesizing UNSAT strategy";
    match find_strategy (unsat_scheme, unsat_solver, not_phi) (sat_scheme, sat_solver, phi) with
    | `Sat sat_scheme -> is_sat (sat_scheme, unsat_scheme)
    | `Unsat -> `Sat (sat_scheme, unsat_scheme)
    | `Unknown -> `Unknown
  in
  is_unsat (sat_scheme, unsat_scheme)

let aqsat_init
    (type formula)
    (module C : AbstractionContext with type formula = formula)
    qf_pre
    phi =
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
      let move = mbp_term (module C) phi_model x phi in
      logf "Initial move: %a = %a"
        C.pp_const x
        (pp_linterm (module C)) move;
      let (sat_path, unsat_path) = match qt with
        | `Exists ->
          ((`Exists x)::sat_path,
           (`Forall (x, move))::unsat_path)
        | `Forall ->
          ((`Forall (x, move))::sat_path,
           (`Exists x)::unsat_path)
      in
      (sat_path, unsat_path, substitute_one (module C) x move phi)
    in
    let (sat_path, unsat_path, _) = List.fold_right f qf_pre ([], [], phi) in
    let (sat_subst, sat_scheme) = Scheme.mk_path (module C) sat_path in
    let (unsat_subst, unsat_scheme) = Scheme.mk_path (module C) unsat_path in
    `Sat (sat_scheme, unsat_scheme)

let aqsat
    (type formula)
    (module C : AbstractionContext with type formula = formula)
    phi =
  let constants = C.Formula.fold_constants KS.add phi KS.empty in
  let (qf_pre, phi) = aq_normalize (module C) phi in
  let qf_pre =
    (List.map (fun k -> (`Exists, k)) (KS.elements constants))@qf_pre
  in
  let not_phi = snd (aq_normalize (module C) (C.mk_not phi)) in

  match aqsat_init (module C) qf_pre phi with
  | `Unsat -> `Unsat
  | `Unknown -> `Unknown
  | `Sat (sat_scheme, unsat_scheme) ->
    let sat_solver = C.Solver.mk_solver () in
    let unsat_solver = C.Solver.mk_solver () in

    C.Solver.add unsat_solver
      [Scheme.formula_of_scheme (module C) unsat_scheme not_phi];
    C.Solver.add sat_solver
      [Scheme.formula_of_scheme (module C) sat_scheme phi];

    let result =
      aqsat_impl
        (module C)
        (mbp_term (module C))
        (sat_scheme, sat_solver, phi)
        (unsat_scheme, unsat_solver, not_phi)
    in
    match result with
    | `Sat (_, _) -> `Sat
    | `Unsat (_, _) -> `Unsat
    | `Unknown -> `Unknown

let aqopt
    (type formula)
    (type term)
    (module C : AbstractionContext with type formula = formula
                                    and type term = term)
    phi
    t =

  let objective_constants = C.Term.fold_constants KS.add t KS.empty in
  let constants = C.Formula.fold_constants KS.add phi objective_constants in
  let (qf_pre, phi) = aq_normalize (module C) phi in
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
    snd (aq_normalize (module C) (C.mk_not phi_unbounded))
  in

  let mbp_term m x phi =
    if x = objective then const_linterm (V.coeff (dim_of_const x) m)
    else mbp_term (module C) m x phi
  in

  let sat_scheme_initial = ref Scheme.empty in
  let unsat_scheme_initial = ref Scheme.empty in
  let rec improve_bound bound unsat_scheme =
    let unsat_scheme = !unsat_scheme_initial in
    let constrain =
      match unsat_scheme, bound with
      | (Scheme.STExists (_, objective, _), Some x) ->
        logf "Trying to improve bound: %a" QQ.pp x;
        C.mk_lt (C.mk_const objective) (C.mk_real x)
      | (_, _) ->
        logf "Checking for unbounded objective@\n%a" C.Formula.pp phi_unbounded;
        C.mk_true
    in

    let sat_solver = C.Solver.mk_solver () in
    let unsat_solver = C.Solver.mk_solver () in

    C.Solver.add unsat_solver
      [constrain;
       Scheme.formula_of_scheme (module C) unsat_scheme not_phi_unbounded];
    C.Solver.add sat_solver
      [Scheme.formula_of_scheme (module C) (!sat_scheme_initial) phi_unbounded];

    let result =
      aqsat_impl
        (module C)
        mbp_term
        (!sat_scheme_initial, sat_solver, phi_unbounded)
        (unsat_scheme, unsat_solver, not_phi_unbounded)
    in
    match result with
    | `Sat (sat_scheme, unsat_scheme) -> `Sat bound
    | `Unknown -> `Unknown
    | `Unsat (Scheme.STLeaf, Scheme.STLeaf) -> `Unsat
    | `Unsat (sat_scheme, unsat_scheme) ->
      let (opt, opt_scheme) = match sat_scheme with
        | Scheme.STForall (_, vm) ->
          (VM.enum vm)
          /@ (fun (v, scheme) -> match const_of_linterm v with
              | Some qq -> (qq, scheme)
              | None -> assert false)
          |> BatEnum.reduce (fun (a, a_scheme) (b, b_scheme) ->
              if QQ.lt a b then (b, b_scheme)
              else (a, a_scheme))
        | _ -> assert false
      in
      logf "Objective function is bounded by %a" QQ.pp opt;

      let bounded_phi =
        let f constraints subst =
          let new_constraint =
            List.fold_right (fun (x, move) phi ->
                if KS.mem x objective_constants then
                  phi
                else
                  substitute_one (module C) x move phi)
              subst
              phi
          in
          new_constraint::constraints
        in
        Scheme.fold_substitutions f [] opt_scheme
        |> C.mk_and
      in
      (*      logf "Bounded: %a" C.Formula.pp bounded_phi;*)
      begin match C.optimize_box bounded_phi [t] with
       | `Unknown ->
         Log.errorf "Failed to optimize - returning conservative bound";
         `Sat bound
       | `Sat [ivl] ->
         begin match bound, Interval.upper ivl with
           | Some b, Some x ->
             logf "Bound %a --> %a" QQ.pp b QQ.pp x;
             assert (QQ.lt x b)
           | _, None -> assert false
           | None, _ -> ()
         end;
         improve_bound (Interval.upper ivl) unsat_scheme
       | `Unsat | `Sat _ -> assert false
      end
  in
  match aqsat_init (module C) qf_pre_unbounded phi_unbounded with
  | `Sat (sat_scheme, unsat_scheme) ->
    sat_scheme_initial := sat_scheme;
    unsat_scheme_initial := unsat_scheme;
    begin match improve_bound None unsat_scheme with
      | `Sat upper -> `Sat (Interval.make None upper)
      | `Unsat -> `Unsat
      | `Unknown -> `Unknown
    end
  | `Unsat -> `Unsat
  | `Unknown -> `Unknown

exception Unknown
let qe_mbp
    (type formula)
    (module C : AbstractionContext with type formula = formula)
    phi =
  let (qf_pre, phi) = aq_normalize (module C) phi in
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
      exists x (snd (aq_normalize (module C) phi))
    | `Forall ->
      C.mk_not (exists x (snd (aq_normalize (module C) (C.mk_not phi))))
  in
  List.fold_right qe qf_pre phi

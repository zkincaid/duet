(*pp camlp4find deriving.syntax *)

open Apak
open Term
open ArkPervasives
open BatPervasives

module type FormulaBasis = sig
  type t
  include Putil.Hashed.S with type t := t
  include Putil.OrderedMix with type t := t

  module T : Term.Term

  val eval : ('a,T.t) formula_algebra -> t -> 'a
  val view : t -> (t, T.t) open_formula
  val to_smt : t -> Smt.ast
  val subst : (T.V.t -> T.t) -> t -> t

  val top : t
  val bottom : t

  val conj : t -> t -> t
  val disj : t -> t -> t

  val leqz : T.t -> t
  val eqz : T.t -> t
  val ltz : T.t -> t
  val eq : T.t -> T.t -> t
  val leq : T.t -> T.t -> t
  val geq : T.t -> T.t -> t
  val lt : T.t -> T.t -> t
  val gt : T.t -> T.t -> t

  val log_stats : unit -> unit
end
module type Formula = sig
  include FormulaBasis

  val negate : t -> t
  val exists : T.V.t list -> t -> t
  val of_smt : Smt.ast -> t
  val implies : t -> t -> bool
  val equiv : t -> t -> bool

  val select_disjunct : (T.V.t -> QQ.t) -> t -> t option

  val big_conj : t BatEnum.t -> t
  val big_disj : t BatEnum.t -> t

  val of_abstract : 'a T.D.t -> t
  val abstract : 'a Apron.Manager.t -> t -> 'a T.D.t

  module Syntax : sig
    val ( && ) : t -> t -> t
    val ( || ) : t -> t -> t
    val ( == ) : T.t -> T.t -> t
    val ( < ) : T.t -> T.t -> t
    val ( > ) : T.t -> T.t -> t
    val ( <= ) : T.t -> T.t -> t
    val ( >= ) : T.t -> T.t -> t
  end
end

module MakeHashconsedBasis (T : Term) : FormulaBasis with module T = T = struct
  open Hashcons

  module F = struct
    type t =
    | Or of t Hset.t
    | And of t Hset.t
    | LeqZ of T.t
    | EqZ of T.t
    | LtZ of T.t

    let hash = function
      | Or xs  -> Hashtbl.hash (Hset.hash xs, 0)
      | And xs -> Hashtbl.hash (Hset.hash xs, 1)
      | LeqZ t -> Hashtbl.hash (T.hash t, 2)
      | EqZ t  -> Hashtbl.hash (T.hash t, 3)
      | LtZ t  -> Hashtbl.hash (T.hash t, 4)

    let equal x y = match x,y with
      | Or xs, Or ys   -> Hset.equal xs ys
      | And xs, And ys -> Hset.equal xs ys
      | LeqZ s, LeqZ t -> T.equal s t
      | EqZ s, EqZ t   -> T.equal s t
      | LtZ s, LtZ t   -> T.equal s t
      | _, _ -> false
  end

  open F
  module HC = Hashcons.Make(F)
  let formula_tbl = HC.create 200003
  let hashcons x = Log.time "formula:hashcons" (HC.hashcons formula_tbl) x

  let term_zero = T.int ZZ.zero
  let term_one = T.int ZZ.one

  type t = F.t hash_consed
  module T = T

  include Putil.MakeFmt(struct
    type a = t
    let rec format_in formatter phi = match phi with
      | Or xs -> Format.fprintf formatter "Or %a" (Hset.format format_in) xs
      | And xs -> Format.fprintf formatter "And %a" (Hset.format format_in) xs
      | LeqZ t -> Format.fprintf formatter "%a <= 0" T.format t
      | EqZ t -> Format.fprintf formatter "%a == 0" T.format t
      | LtZ t -> Format.fprintf formatter "%a < 0" T.format t
    let rec format formatter phi = format_in formatter phi.node
  end)
  module Compare_t = struct
    type a = t
    let compare x y = Pervasives.compare x.tag y.tag
  end
  let compare = Compare_t.compare
  let equal x y = x.tag == y.tag
  let hash x = x.hkey

  let top = hashcons (LeqZ term_zero)
  let bottom = hashcons (LeqZ term_one)

  let mk_and xs =
    if Hset.is_empty xs then top
    else if Hset.mem bottom xs then bottom
    else hashcons (And xs)

  let mk_or xs =
    if Hset.is_empty xs then bottom
    else if Hset.mem top xs then top
    else hashcons (Or xs)

  let conj phi psi =
    if phi.tag == top.tag then psi
    else if psi.tag == top.tag then phi
    else if phi.tag == bottom.tag || psi.tag == bottom.tag then bottom
    else begin match phi.node, psi.node with
    | (And xs, And ys) -> hashcons (And (Hset.union xs ys))
    | (And xs, _) -> hashcons (And (Hset.add psi xs))
    | (_, And xs) -> hashcons (And (Hset.add phi xs))
    | (Or xs, Or ys) ->
      let common = Hset.inter xs ys in
      if Hset.is_empty common
      then hashcons (And (Hset.add phi (Hset.singleton psi)))
      else begin
	let phi = mk_or (Hset.diff xs common) in
	let psi = mk_or (Hset.diff ys common) in
	mk_and (Hset.add (mk_or (Hset.add phi (Hset.singleton psi))) common)
      end
    | (_, _) -> hashcons (And (Hset.add phi (Hset.singleton psi)))
    end

  let disj phi psi =
    if phi.tag == bottom.tag then psi
    else if psi.tag == bottom.tag then phi
    else if phi.tag == top.tag || psi.tag == top.tag then top
    else begin match phi.node, psi.node with
    | (Or xs, Or ys) -> hashcons (Or (Hset.union xs ys))
    | (Or xs, _) -> hashcons (Or (Hset.add psi xs))
    | (_, Or xs) -> hashcons (Or (Hset.add phi xs))
    | (And xs, And ys) ->
      let common = Hset.inter xs ys in
      if Hset.is_empty common
      then hashcons (Or (Hset.add phi (Hset.singleton psi)))
      else begin
	let phi = mk_and (Hset.diff xs common) in
	let psi = mk_and (Hset.diff ys common) in
	mk_and (Hset.add (mk_or (Hset.add phi (Hset.singleton psi))) common)
      end
    | (_, _) -> hashcons (Or (Hset.add phi (Hset.singleton psi)))
    end

  let leqz term =
    match T.get_const term with
    | Some k -> if QQ.leq k QQ.zero then top else bottom
    | _ -> hashcons (LeqZ term)
  let eqz term =
    match T.get_const term with
    | Some k -> if QQ.equal k QQ.zero then top else bottom
    | _ -> hashcons (EqZ term)
  let ltz term =
    match T.get_const term with
    | Some k -> if QQ.lt k QQ.zero then top else bottom
    | _ -> hashcons (LtZ term)


  let eq s t = eqz (T.sub s t)
  let leq s t = leqz (T.sub s t)
  let geq s t = leqz (T.sub t s)
  let lt s t = ltz (T.sub s t)
  let gt s t = ltz (T.sub t s)

  module M = Memo.Make(struct
    type t = F.t hash_consed
    let hash t = t.hkey
    let equal s t = s.tag == t.tag
  end)

  let eval alg =
    M.memo_recursive ~size:991 (fun eval x ->
      match x.node with
      | Or xs ->
	let e = Hset.enum xs in
	begin match BatEnum.get e with
	| Some elt ->
	  BatEnum.fold (fun x y -> alg (OOr (x, eval y))) (eval elt) e
	| None -> alg (OLeqZ term_one)
	end
      | And xs ->
	let e = Hset.enum xs in
	begin match BatEnum.get e with
	| Some elt ->
	  BatEnum.fold (fun x y -> alg (OAnd (x, eval y))) (eval elt) e
	| None -> alg (OLeqZ term_zero)
	end
      | LeqZ t -> alg (OLeqZ t)
      | EqZ t -> alg (OEqZ t)
      | LtZ t -> alg (OLtZ t))

  let view t = match t.node with
    | LeqZ t -> OLeqZ t
    | EqZ t -> OEqZ t
    | LtZ t -> OLtZ t
    | And xs ->
      (* todo: skip enumerations; write functions in hset to make this more
	 efficient *)
      let e = Hset.enum xs in
      begin match BatEnum.count e with
      | 0 -> OLeqZ term_zero
      | 1 -> assert false (* this should have been promoted! *)
      | 2 -> OAnd (BatEnum.get_exn e, BatEnum.get_exn e)
      | _ -> OAnd (BatEnum.get_exn e, hashcons (And (Hset.of_enum e)))
      end
    | Or xs ->
      let e = Hset.enum xs in
      begin match BatEnum.count e with
      | 0 -> OLeqZ term_one
      | 1 -> assert false (* this should have been promoted! *)
      | 2 -> OOr (BatEnum.get_exn e, BatEnum.get_exn e)
      | _ -> OOr (BatEnum.get_exn e, hashcons (Or (Hset.of_enum e)))
      end

  let to_smt =
    let alg = function
      | OLeqZ t -> Smt.mk_le (T.to_smt t) (Smt.const_int 0)
      | OLtZ t -> Smt.mk_lt (T.to_smt t) (Smt.const_int 0)
      | OEqZ t -> Smt.mk_eq (T.to_smt t) (Smt.const_int 0)
      | OAnd (x, y) -> Smt.conj x y
      | OOr (x, y) -> Smt.disj x y
    in
    eval alg

  let subst sigma =
    let term_subst = T.subst sigma in (* Build memo table here *)
    let alg = function
      | OLeqZ t -> leqz (term_subst t)
      | OEqZ t -> eqz (term_subst t)
      | OLtZ t -> ltz (term_subst t)
      | OAnd (x, y) -> conj x y
      | OOr (x, y) -> disj x y
    in
    eval alg

  let log_stats () =
    let (length, count, total, min, median, max) = HC.stats formula_tbl in
    Log.log 0 "----------------------------\n Formula stats";
    Log.logf 0 "Length:\t\t%d" length;
    Log.logf 0 "Count:\t\t%d" count;
    Log.logf 0 "Total size:\t%d" total;
    Log.logf 0 "Min bucket:\t%d" min;
    Log.logf 0 "Median bucket:\t%d" median;
    Log.logf 0 "Max bucket:\t%d" max
end

module MakeBasis (T : Term) : FormulaBasis with module T = T =
struct

  module rec F : sig
    type t =
    | Or of ESet.t
    | And of ESet.t
    | LeqZ of T.t
    | EqZ of T.t
    | LtZ of T.t
    include Putil.Ordered with type t := t
  end = struct
    type t =
    | Or of ESet.t
    | And of ESet.t
    | LeqZ of T.t
    | EqZ of T.t
    | LtZ of T.t
	deriving (Show,Compare)
    let format = Show_t.format
    let show = Show_t.show
    let compare = Compare_t.compare
  end
  and ESet : Putil.Set.S with type elt = F.t = Putil.Set.Make(F)

  include F
  module T = T

  let equal x y = compare x y = 0
  let top = LeqZ T.zero
  let bottom = LeqZ T.one
  let mk_and xs =
    if ESet.is_empty xs then top
    else if ESet.mem bottom xs then bottom
    else And xs

  let mk_or xs =
    if ESet.is_empty xs then bottom
    else if ESet.mem top xs then top
    else Or xs

  let conj phi psi =
    if equal phi top then psi
    else if equal psi top then phi
    else if equal phi bottom || equal psi bottom then bottom
    else begin match phi, psi with
    | (And xs, And ys) -> And (ESet.union xs ys)
    | (And xs, y) | (y, And xs) -> And (ESet.add y xs)
    | (Or xs, Or ys) ->
      let common = ESet.inter xs ys in
      if ESet.is_empty common then And (ESet.add phi (ESet.singleton psi))
      else begin
	let phi = mk_or (ESet.diff xs common) in
	let psi = mk_or (ESet.diff ys common) in
	mk_and (ESet.add (mk_or (ESet.add phi (ESet.singleton psi))) common)
      end
    | (_, _) -> And (ESet.add phi (ESet.singleton psi))
    end

  let disj phi psi =
    if equal phi bottom then psi
    else if equal psi bottom then phi
    else if equal phi top || equal psi top then top
    else begin match phi, psi with
    | (Or xs, Or ys) -> Or (ESet.union xs ys)
    | (Or xs, y) | (y, Or xs) -> Or (ESet.add y xs)
    | (And xs, And ys) ->
      let common = ESet.inter xs ys in
      if ESet.is_empty common then Or (ESet.add phi (ESet.singleton psi))
      else begin
	let phi = mk_and (ESet.diff xs common) in
	let psi = mk_and (ESet.diff ys common) in
	mk_and (ESet.add (mk_or (ESet.add phi (ESet.singleton psi))) common)
      end
    | (_, _) -> Or (ESet.add phi (ESet.singleton psi))
    end
  let leqz term = match T.get_const term with
    | Some k -> if QQ.leq k QQ.zero then top else bottom
    | None -> LeqZ term
  let eqz term = match T.get_const term with
    | Some k -> if QQ.equal k QQ.zero then top else bottom
    | None -> EqZ term
  let ltz term = match T.get_const term with
    | Some k -> if QQ.lt k QQ.zero then top else bottom
    | None -> LtZ term

  let eq s t = eqz (T.sub s t)
  let leq s t = leqz (T.sub s t)
  let geq s t = leqz (T.sub t s)

  let lt s t = ltz (T.sub s t)
  let gt s t = ltz (T.sub t s)

  let term_zero = T.zero
  let term_one = T.one

  let rec eval alg = function
    | Or xs ->
      let e = ESet.enum xs in
      begin match BatEnum.get e with
      | Some elt ->
	BatEnum.fold (fun x y -> alg (OOr (x, eval alg y))) (eval alg elt) e
      | None -> alg (OLeqZ term_one)
      end
    | And xs ->
      let e = ESet.enum xs in
      begin match BatEnum.get e with
      | Some elt ->
	BatEnum.fold (fun x y -> alg (OAnd (x, eval alg y))) (eval alg elt) e
      | None -> alg (OLeqZ term_zero)
      end
    | LeqZ t -> alg (OLeqZ t)
    | EqZ t -> alg (OEqZ t)
    | LtZ t -> alg (OLtZ t)

  let view t = match t with
    | LeqZ t -> OLeqZ t
    | LtZ t -> OLtZ t
    | EqZ t -> OEqZ t
    | And xs ->
      (* todo: skip enumerations; write functions in hset to make this more
	 efficient *)
      let e = ESet.enum xs in
      begin match BatEnum.count e with
      | 0 -> OLeqZ term_zero
      | 1 -> assert false (* this should have been promoted! *)
      | 2 -> OAnd (BatEnum.get_exn e, BatEnum.get_exn e)
      | _ -> OAnd (BatEnum.get_exn e, And (ESet.of_enum e))
      end
    | Or xs ->
      let e = ESet.enum xs in
      begin match BatEnum.count e with
      | 0 -> OLeqZ term_one
      | 1 -> assert false (* this should have been promoted! *)
      | 2 -> OOr (BatEnum.get_exn e, BatEnum.get_exn e)
      | _ -> OOr (BatEnum.get_exn e, Or (ESet.of_enum e))
      end


  let rec to_smt = function
    | LeqZ t -> Smt.mk_le (T.to_smt t) (Smt.const_int 0)
    | LtZ t -> Smt.mk_lt (Smt.mk_real2int (T.to_smt t)) (Smt.const_int 0)
    | EqZ t -> Smt.mk_eq (T.to_smt t) (Smt.const_int 0)
    | And phi -> Smt.big_conj (BatEnum.map to_smt (ESet.enum phi))
    | Or phi -> Smt.big_disj (BatEnum.map to_smt (ESet.enum phi))
      
  let rec subst sigma = function
    | LeqZ term -> leqz (T.subst sigma term)
    | LtZ term -> ltz (T.subst sigma term)
    | EqZ term -> eqz (T.subst sigma term)
    | And phi ->
      let phi = ESet.remove top (ESet.map (subst sigma) phi) in
      if ESet.mem bottom phi then bottom
      else begin match ESet.cardinal phi with
      | 0 -> top
      | 1 -> ESet.choose phi
      | _ -> BatEnum.reduce conj (ESet.enum phi)
      end
    | Or phi ->
      let phi = ESet.remove bottom (ESet.map (subst sigma) phi) in
      if ESet.mem top phi then top
      else begin match ESet.cardinal phi with
      | 0 -> bottom
      | 1 -> ESet.choose phi
      | _ -> BatEnum.reduce disj (ESet.enum phi)
      end

  let hash =
    let alg = function
      | OLeqZ t -> Hashtbl.hash (T.hash t, 0)
      | OEqZ t -> Hashtbl.hash (T.hash t, 1)
      | OAnd (x, y) -> Hashtbl.hash (x, y, 2)
      | OOr (x, y) -> Hashtbl.hash (x, y, 3)
      | OLtZ t -> Hashtbl.hash (T.hash t, 4)
    in
    eval alg

  let log_stats () = ()
end

module Defaults (F : FormulaBasis) = struct
  include F

  let negate =
    let alg = function
    | OOr (x, y) -> conj x y
    | OAnd (x, y) -> disj x y
    | OLeqZ t -> gt t T.zero
    | OEqZ t -> disj (gt t T.zero) (lt t T.zero)
    | OLtZ t -> geq t T.zero
    in
    eval alg

  let of_smt ast =
    let open Z3 in
    let ctx = Smt.get_context () in
    let smt_term vs = T.of_smt (List.nth vs) in
    let rec of_smt vars ast =
      match get_ast_kind ctx ast with
      | APP_AST -> begin
	let app = to_app ctx ast in
	let decl = get_app_decl ctx app in
	let args =
	  (0 -- (get_app_num_args ctx app - 1)) /@ (get_app_arg ctx app)
	in
	match get_decl_kind ctx decl with
	| OP_TRUE -> F.top
	| OP_FALSE -> F.bottom
	| OP_AND ->
	  BatEnum.fold F.conj F.top (BatEnum.map (of_smt vars) args)
	| OP_OR ->
	  BatEnum.fold F.disj F.bottom (BatEnum.map (of_smt vars) args)
	| OP_NOT -> begin
	  match BatList.of_enum (BatEnum.map (of_smt vars) args) with
	  | [phi] -> negate phi
	  | _ -> assert false
	end
	| OP_EQ -> begin
	  match BatList.of_enum (BatEnum.map (smt_term vars) args) with
	  | [x;y] -> F.eq x y
	  | _ -> assert false
	end
	| OP_LE -> begin
	  match BatList.of_enum (BatEnum.map (smt_term vars) args) with
	  | [x;y] -> F.leq x y
	  | _ -> assert false
	end
	| OP_GE -> begin
	  match BatList.of_enum (BatEnum.map (smt_term vars) args) with
	  | [x;y] -> F.geq x y
	  | _ -> assert false
	end
	| OP_LT -> begin
	  match BatList.of_enum (BatEnum.map (smt_term vars) args) with
	  | [x;y] -> F.lt x y
	  | _ -> assert false
	end
	| OP_GT -> begin
	  match BatList.of_enum (BatEnum.map (smt_term vars) args) with
	  | [x;y] -> F.gt x y
	  | _ -> assert false
	end
	| _ -> assert false
      end
      | QUANTIFIER_AST ->
	let num_vars = Z3.get_quantifier_num_bound ctx ast in
	let new_vars =
	  BatEnum.map
	    (T.V.of_smt % Z3.get_quantifier_bound_name ctx ast)
	    (0--(num_vars-1))
	in
	let vars = List.append (BatList.of_enum new_vars) vars in
	of_smt vars (Z3.get_quantifier_body ctx ast)
      | NUMERAL_AST
      | VAR_AST
      | FUNC_DECL_AST
      | SORT_AST
      | UNKNOWN_AST -> assert false
    in
    of_smt [] ast

  let of_goal g =
    let ctx = Smt.get_context() in
    let subgoal_formula n = of_smt (Z3.goal_formula ctx g n) in
    let formulae =
      BatEnum.map subgoal_formula (0 -- (Z3.goal_size ctx g - 1))
    in
    BatEnum.fold F.conj F.top formulae

  let of_apply_result result =
    let ctx = Smt.get_context() in
    let goal_formula n = of_goal (Z3.apply_result_get_subgoal ctx result n) in
    let formulae =
      BatEnum.map
	goal_formula
	(0 -- (Z3.apply_result_get_num_subgoals ctx result - 1))
    in
    BatEnum.fold F.conj F.top formulae

  let exists vars phi =
    let ctx = Smt.get_context() in
    let solve = Z3.mk_tactic ctx "qe" in
    let simpl = Z3.mk_tactic ctx "simplify" in
    let qe = Z3.tactic_and_then ctx solve simpl in
    let g = Z3.mk_goal ctx false false false in
    Z3.goal_assert ctx g
      (Z3.mk_exists_const
	 ctx
	 (List.length vars)
	 (Array.of_list (List.map (Z3.to_app ctx % T.V.to_smt) vars))
	 [||]
	 (to_smt phi));
    of_apply_result (Z3.tactic_apply ctx qe g)

  let implies phi psi =
    let s = new Smt.solver in
    s#assrt (to_smt phi);
    s#assrt (Smt.mk_not (to_smt psi));
    match s#check () with
    | Smt.Sat   -> false
    | Smt.Unsat -> true
    | Smt.Undef -> assert false

  let equiv phi psi =
    let s = new Smt.solver in
    let phi = to_smt phi in
    let psi = to_smt psi in
    s#assrt (Smt.disj
	       (Smt.conj phi (Smt.mk_not psi))
	       (Smt.conj (Smt.mk_not phi) psi));
    match s#check () with
    | Smt.Sat   -> false
    | Smt.Unsat -> true
    | Smt.Undef -> assert false

  let big_disj = BatEnum.fold disj bottom 
  let big_conj = BatEnum.fold conj top

  (** [select_disjunct m phi] selects a clause [psi] in the disjunctive normal
      form of [psi] such that [m |= psi] *)
  let select_disjunct m phi =
    let f = function
      | OLeqZ t ->
	if QQ.leq (T.evaluate m t) QQ.zero then Some (F.leqz t) else None
      | OLtZ t ->
	if QQ.lt (T.evaluate m t) QQ.zero then Some (F.ltz t) else None
      | OEqZ t ->
	if QQ.equal (T.evaluate m t) QQ.zero then Some (F.eqz t) else None
      | OAnd (Some phi, Some psi) -> Some (F.conj phi psi)
      | OAnd (_, _) -> None
      | OOr (x, None) | OOr (_, x) -> x
    in
    F.eval f phi

  module VarSet = Putil.Set.Make(T.V)
  module D = T.D
  open Apron

  let term_free_vars term =
    let f = function
      | OVar v -> VarSet.singleton v
      | OConst _ -> VarSet.empty
      | OAdd (x,y) | OMul (x,y) | ODiv (x,y) -> VarSet.union x y
      | OFloor x -> x
    in
    T.eval f term

  let formula_free_vars phi =
    let f = function
      | OOr (x,y) | OAnd (x,y) -> VarSet.union x y
      | OLeqZ t | OEqZ t | OLtZ t -> term_free_vars t
    in
    F.eval f phi

  let of_tcons env tcons =
    let open Tcons0 in
    let t = T.of_apron env tcons.texpr0 in
    match tcons.typ with
    | EQ      -> F.eqz t
    | SUPEQ   -> F.leqz (T.neg t)
    | SUP     -> F.ltz (T.neg t)
    | DISEQ   -> negate (F.eqz t)
    | EQMOD _ -> assert false (* todo *)

  let mk_env phi = D.Env.of_enum (VarSet.enum (formula_free_vars phi))

  let of_abstract x =
    let open D in
    let man = Abstract0.manager x.prop in
    let tcons = BatArray.enum (Abstract0.to_tcons_array man x.prop) in
    big_conj (BatEnum.map (of_tcons x.env) tcons)

  let abstract man phi =
    let open D in
    let env = mk_env phi in
    let s = new Smt.solver in
    let to_apron = T.to_apron env in
    let rec go prop =
      s#push ();
      s#assrt (Smt.mk_not (F.to_smt (of_abstract prop)));
      match s#check () with
      | Smt.Unsat -> prop
      | Smt.Undef -> D.top man env
      | Smt.Sat ->
	let m = s#get_model () in
	s#pop ();
	let apron_alg = function
	  | OLeqZ t -> [Tcons0.make (to_apron (T.neg t)) Tcons0.SUPEQ]
	  | OLtZ t -> [Tcons0.make (to_apron (T.neg t)) Tcons0.SUP]
	  | OEqZ t -> [Tcons0.make (to_apron t) Tcons0.EQ]
	  | OAnd (phi, psi) -> phi @ psi
	  | OOr (_, _) -> assert false (* impossible *)
	in
	let disjunct = match select_disjunct (m#eval_qq % T.V.to_smt) phi with
	  | Some d -> F.eval apron_alg d
	  | None   -> assert false
	in
	let new_prop =
	  { prop = 
	      Abstract0.of_tcons_array
		man
		(Env.int_dim env)
		(Env.real_dim env)
		(Array.of_list disjunct);
	    env = env }
	in
	go (D.join prop new_prop)
    in
    s#assrt (F.to_smt phi);
    go (bottom man env)

  module Syntax = struct
    let ( && ) x y = conj x y
    let ( || ) x y = disj x y
    let ( == ) x y = eq x y
    let ( < ) x y = lt x y
    let ( > ) x y = gt x y
    let ( <= ) x y = leq x y
    let ( >= ) x y = geq x y
  end
end

module MakeEq (F : Formula) = struct
  open F
  module V = T.V
  module A = Linear.Affine(V)
  module AMap = BatMap.Make(A)
  module AffineTerm = Linear.Defaults(Linear.Expr.Make(A)(QQ))

  let linterm_smt = AffineTerm.to_smt A.to_smt Smt.const_qq

  (** Extract a basis for the smallest linear manifold which contains [phi]
      and is defined over the variables [vars]. *)
  let extract_equalities phi vars =
    let zero = Smt.const_int 0 in
    let const_var = A.to_smt A.AConst in
    let s = new Smt.solver in
    let space = new Smt.solver in (* solution space for implied equalities *)
    let extract_linterm m =
      let f term v =
	AffineTerm.add_term
	  (A.AVar v)
	  (m#eval_qq (V.to_smt v))
	  term
      in
      let const_term =
	AffineTerm.add_term
	  A.AConst
	  (m#eval_qq const_var)
	  AffineTerm.zero
      in
      List.fold_left f const_term vars
    in
    let rec go equalities =
      match space#check () with
      | Smt.Unsat | Smt.Undef -> equalities
      | Smt.Sat ->
	let candidate = extract_linterm (space#get_model ()) in
	let candidate_formula =
	  Smt.mk_eq (linterm_smt candidate) zero
	in
	s#push ();
	s#assrt (Smt.mk_not candidate_formula);
	match s#check () with
	| Smt.Undef -> (* give up; return the equalities we have so far *)
	  equalities
	| Smt.Unsat -> (* candidate equality is implied by phi *)
	  s#pop ();
	  let leading =
	    let e =
	      let f (x,y) = match A.get_var x with
		| Some x -> Some (x,y)
		| None -> None
	      in
	      BatEnum.filter_map f (AffineTerm.enum candidate)
	    in
	    match BatEnum.get e with
	    | Some (dim, coeff) ->
	      assert (not (QQ.equal coeff QQ.zero));
	      dim
	    | None -> assert false
	  in
	  space#assrt (Smt.mk_eq (V.to_smt leading) zero);
	  go (candidate::equalities)
	| Smt.Sat -> (* candidate equality is not implied by phi *)
	  let point = extract_linterm (s#get_model ()) in
	  s#pop ();
	  space#assrt (Smt.mk_eq (linterm_smt point) zero);
	  go equalities
    in
    let nonzero v = Smt.mk_not (Smt.mk_eq (V.to_smt v) zero) in
    s#assrt (to_smt phi);
    s#assrt (Smt.mk_eq const_var (Smt.const_int 1));
    space#assrt (Smt.big_disj (BatEnum.map nonzero (BatList.enum vars)));
    go []
end

module MakeHashconsed (T : Term) : Formula with module T = T
  = Defaults(MakeHashconsedBasis(T))
module Make (T : Term) : Formula with module T = T
  = Defaults(MakeBasis(T))

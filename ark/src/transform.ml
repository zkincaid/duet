(*pp camlp4find deriving.syntax *)

open Apak
open Numeral
open BatPervasives
open Hashcons

module Int = Putil.PInt

module type Var = sig
  include Term.Var
  val prime : t -> t
end


module Make (Var : Var) = struct
  type var = Var.t
  let max_id = ref 0

  (* Variables *)
  module V = struct
    type t =
    | PVar of Var.t
    | TVar of int * string
	deriving (Compare)
    include Putil.MakeFmt(struct
      type a = t
      let format formatter = function
	| PVar v -> Var.format formatter v
	| TVar (id,name) -> Format.fprintf formatter "%s!%d" name id
    end)
    let format = Show_t.format
    let show = Show_t.show
    let compare = Compare_t.compare
    let equal x y = compare x y = 0
    let hash = function
      | PVar v -> (Var.hash v) lsl 1
      | TVar (id,_) -> (Hashtbl.hash id) lsl 1 + 1
    let lower = function
      | PVar v -> Some v
      | TVar _ -> None
    let mk_tmp name =
      incr max_id;
      TVar (!max_id, name)
    let mk_var v = PVar v
    let to_smt = function
      | PVar x -> Var.to_smt x
      | TVar (id,name) -> Smt.int_var (name ^ "!" ^ (string_of_int id))
  end

  type 'a open_term =
  | OVar of V.t
  | OConst of ZZ.t
  | OAdd of 'a * 'a
  | OMul of 'a * 'a
  | ODiv of 'a * 'a
  type 'a term_algebra = 'a open_term -> 'a

  (* Terms *)
  module T = struct
    module rec E : sig
      type t
      include Putil.Hashed.S with type t := t
      include Putil.OrderedMix with type t := t
      val equal : t -> t -> bool
      val eval : 'a term_algebra -> t hash_consed -> 'a
      val var : V.t -> t hash_consed
      val const : ZZ.t -> t hash_consed
      val mul : t hash_consed -> t hash_consed -> t hash_consed
      val add : t hash_consed -> t hash_consed -> t hash_consed
      val sub : t hash_consed -> t hash_consed -> t hash_consed
      val div : t hash_consed -> t hash_consed -> t hash_consed
      val neg : t hash_consed -> t hash_consed
      val log_stats : unit -> unit
      val get_const : t -> ZZ.t option
    end = struct
      type t =
      | Var of V.t
      | Const of ZZ.t
      | Sum of Expr.t
      | Mul of (t hash_consed) * (t hash_consed)
      | Div of (t hash_consed) * (t hash_consed)

      let hash = function
	| Var v -> Hashtbl.hash (V.hash v, 0)
	| Const k -> Hashtbl.hash (k, 1)
	| Sum ts -> Hashtbl.hash (Expr.hash ts, 2)
	| Mul (x,y) -> Hashtbl.hash (x.tag, y.tag, 3)
	| Div (x,y) -> Hashtbl.hash (x.tag, y.tag, 4)

      let rec equal x y = match x, y with
	| (Var v0, Var v1) -> V.equal v0 v1
	| (Const k0, Const k1) -> k0 == k1
	| (Sum ts0, Sum ts1) -> Expr.equal ts0 ts1
	| (Mul (s0,s1), Mul (t0,t1)) -> s0.tag == t0.tag && s1.tag == t1.tag
	| (Div (s0,s1), Div (t0,t1)) -> s0.tag == t0.tag && s1.tag == t1.tag
	| (_, _) -> false

      let compare x y = match x, y with
	| (Var v0, Var v1) -> V.compare v0 v1
	| (Var _, _) -> 1
	| (_, Var _) -> -1

	| (Const k0, Const k1) -> ZZ.compare k0 k1
	| (Const _, _) -> 1
	| (_, Const _) -> -1

	| (Sum ts0, Sum ts1) -> Expr.compare ZZ.compare ts0 ts1
	| (Sum _, _) -> 1
	| (_, Sum _) -> -1

	| (Mul (s0,s1), Mul (t0,t1)) ->
	  Pervasives.compare (s0.tag,s1.tag) (t0.tag,t1.tag)
	| (Mul _, _) -> 1
	| (_, Mul _) -> -1
	| (Div (s0,s1), Div (t0,t1)) ->
	  Pervasives.compare (s0.tag,s1.tag) (t0.tag,t1.tag)

      module Compare_t = struct
	type a = t
	let compare = compare
      end

      module Inner = struct
	type a = t
	type t = a
	let hash = hash
	let equal = equal
      end

      include Putil.MakeFmt(struct
	type a = t
	let rec format formatter = function
	  | Var v -> V.format formatter v
	  | Const k -> ZZ.format formatter k
	  | Sum xs -> Expr.format formatter xs
	  | Mul (x,y) ->
	    Format.fprintf formatter "@[(%a)@ *@ (%a)@]"
	      format x.node
	      format y.node
	  | Div (x,y) ->
	    Format.fprintf formatter "@[(%a)@ /@ (%a)@]"
	      format x.node
	      format y.node
      end)

      module HC = Hashcons.Make(Inner)
      let term_tbl = HC.create 1000003
      let hashcons x = Log.time "term:hashcons" (HC.hashcons term_tbl) x

      let var x = hashcons (Var x)
      let const k = hashcons (Const k)
      let zero = const ZZ.zero
      let one = const ZZ.one

      let linearize = function
	| Const k -> Expr.add_term one k Expr.zero
	| Mul (s, t) as tt -> begin
	  match s.node, t.node with
	  | (Const k, _) -> Expr.add_term t k Expr.zero
	  | (_, Const k) -> Expr.add_term s k Expr.zero
	  | (_, _) -> Expr.add_term (hashcons tt) ZZ.one Expr.zero
	end
	| Sum xs -> xs
	| x -> Expr.add_term (hashcons x) ZZ.one Expr.zero

      let rec delinearize xs =
	let enum = Expr.enum xs in
	match BatEnum.get enum with
	| None -> zero
	| Some (t,coeff) -> begin match BatEnum.peek enum with
	  | None -> mul t (const coeff)
	  |    _ -> hashcons (Sum xs)
	end

      and add (x : t hash_consed) (y : t hash_consed) = 
	match x.node, y.node with
	| (Const x, Const y) -> const (ZZ.add x y)
	| (Const k, _) when ZZ.equal k ZZ.zero -> y
	| (_, Const k) when ZZ.equal k ZZ.zero -> x
	| (Div (a, b), Div (c, d)) when b.tag == d.tag ->
	  hashcons (Div (add a c, b))
	| (Mul (a, b), Mul (c, d)) when a.tag == c.tag ->
	  hashcons (Mul (a, add b d))
	| (x, y) ->
	  delinearize (Expr.add (linearize x) (linearize y))

      and mul (x : t hash_consed) (y : t hash_consed) =
	match x.node, y.node with
	| (Div (num,den), _) -> hashcons (Div (mul num y, den))
	| (Const k, _) when ZZ.equal k ZZ.one -> y
	| (_, Const k) when ZZ.equal k ZZ.one -> x
	| (Const k, _) | (_, Const k) when ZZ.equal k ZZ.zero ->
	  hashcons (Const ZZ.zero)
	| (Const x, Const y) -> hashcons (Const (ZZ.mul x y))
	| (Const x, Sum ys) | (Sum ys, Const x) ->
	  delinearize (Expr.scalar_mul x ys)
	| (_, _) -> hashcons (Mul (x, y))

      let div x y =
	match x.node, y.node with
	| (_, Const k) when ZZ.equal k ZZ.one -> x
	| (_, _) -> hashcons (Div (x, y))

      let neg x = mul (hashcons (Const (ZZ.negate ZZ.one))) x
      let sub x y = add x (neg y)

      module M = Memo.Make(struct
	type t = Inner.t hash_consed
	let hash t = t.hkey
	let equal s t = s.tag == t.tag
      end)

      let eval alg =
	M.memo_recursive ~size:991 (fun eval x ->
	  match x.node with
	  | Var v -> alg (OVar v)
	  | Const k -> alg (OConst k)
	  | Sum xs ->
	    let term (x, k) =
	      if ZZ.equal ZZ.one k then eval x
	      else alg (OMul (alg (OConst k), eval x))
	    in
	    let f acc t = alg (OAdd (acc, term t)) in
	    let enum = Expr.enum xs in
	    begin match BatEnum.get enum with
	    | None -> alg (OConst ZZ.zero)
	    | Some t -> BatEnum.fold f (term t) enum
	    end
	  | Mul (x, y) -> alg (OMul (eval x, eval y))
	  | Div (x, y) -> alg (ODiv (eval x, eval y)))

      let view = function
	| Var v -> OVar v
	| Const k -> OConst k
	| Sum xs ->
	  let enum = Expr.enum xs in
	  begin match BatEnum.get enum with
	  | Some (x, k) ->
	    OAdd (hashcons (Mul (x, const k)),
		  hashcons (Sum (Expr.of_enum enum)))
	  | None -> OConst ZZ.zero
	  end
	| Mul (x, y) -> OMul (x, y)
	| Div (x, y) -> ODiv (x, y)

      let get_const = function
	| Var _ -> None
	| Const k -> Some k
	| Sum xs -> if Expr.equal xs Expr.zero then Some ZZ.zero else None
	| Mul (_, _) -> None
	| Div (_, _) -> None

      let log_stats () =
	let (length, count, total, min, median, max) = HC.stats term_tbl in
	Log.log 0 "----------------------------\n Term stats";
	Log.logf 0 "Length:\t\t%d" length;
	Log.logf 0 "Count:\t\t%d" count;
	Log.logf 0 "Total size:\t%d" total;
	Log.logf 0 "Min bucket:\t%d" min;
	Log.logf 0 "Median bucket:\t%d" median;
	Log.logf 0 "Max bucket:\t%d" max
    end
    and Expr : Linear.Expr.Hashed.S with type dim = E.t Hashcons.hash_consed
				     and type base = Numeral.ZZ.t
	       = Linear.Expr.Hashed.HMake(E)(Numeral.ZZ)

    include E

    let to_smt =
      let alg = function
	| OVar v -> V.to_smt v
	| OConst k -> Smt.const_zz k
	| OAdd (x,y) -> Smt.add x y
	| OMul (x,y) -> Smt.mul x y
	| ODiv (x,y) -> Smt.mk_div x y
      in
      eval alg

    let subst sigma =
      let alg = function
	| OVar v -> sigma v
	| OConst k -> E.const k
	| OAdd (s,t) -> add s t
	| OMul (s,t) -> mul s t
	| ODiv (s,t) -> div s t
      in
      eval alg

    (* Don't eta-reduce - eval will memoize, and we'll get a space leak *)
    let free_tmp t =
      let alg = function
	| OVar (V.TVar (x, _)) -> Int.Set.singleton x
	| OVar (V.PVar _) | OConst _ -> Int.Set.empty
	| OAdd (xs, ys) | OMul (xs, ys) | ODiv (xs, ys) -> Int.Set.union xs ys
      in
      eval alg t

    module Syntax = struct
      let ( + ) x y = add x y
      let ( - ) x y = sub x y
      let ( * ) x y = mul x y
      let ( / ) x y = div x y
      let ( ~$ ) x = var x
      let ( ~@ ) x = const x
    end
  end

  type 'a open_formula =
  | OOr of 'a * 'a
  | OAnd of 'a * 'a
  | OLeqZ of (T.t hash_consed)
  | OEqZ of (T.t hash_consed)
  type 'a formula_algebra = 'a open_formula -> 'a

  (* Formulae *)
  module F = struct
    module Inner = struct
      type t =
      | Or of t Hset.t
      | And of t Hset.t
      | LeqZ of (T.t hash_consed)
      | EqZ of (T.t hash_consed)

      let hash = function
	| Or xs  -> Hashtbl.hash (Hset.hash xs, 0)
	| And xs -> Hashtbl.hash (Hset.hash xs, 1)
	| LeqZ t -> Hashtbl.hash (t.hkey, 2)
	| EqZ t  -> Hashtbl.hash (t.hkey, 3)

      let equal x y = match x,y with
	| Or xs, Or ys   -> Hset.equal xs ys
	| And xs, And ys -> Hset.equal xs ys
	| LeqZ s, LeqZ t -> s.tag == t.tag
	| EqZ s, EqZ t   -> s.tag == t.tag
	| _, _ -> false
    end

    include Inner
    include Putil.MakeFmt(struct
      type a = t
      let rec format formatter = function
	| Or xs -> Format.fprintf formatter "Or %a" (Hset.format format) xs
	| And xs -> Format.fprintf formatter "And %a" (Hset.format format) xs
	| LeqZ t -> Format.fprintf formatter "%a <= 0" T.format t.node
	| EqZ t -> Format.fprintf formatter "%a == 0" T.format t.node
    end)
    module Compare_t = struct
      type a = t
      let compare phi psi = match phi, psi with
	| (Or xs, Or ys) -> Hset.compare xs ys
	| (Or _, _) -> 1
	| (_, Or _) -> -1
	| (And xs, And ys) -> Hset.compare xs ys
	| (And _, _) -> 1
	| (_, And _) -> -1
	| (LeqZ s, LeqZ t) -> Pervasives.compare s.tag t.tag
	| (LeqZ _, _) -> 1
	| (_, LeqZ _) -> -1
	| (EqZ s, EqZ t) -> Pervasives.compare s.tag t.tag
    end

    module HC = Hashcons.Make(Inner)
    let formula_tbl = HC.create 200003
    let hashcons x = Log.time "formula:hashcons" (HC.hashcons formula_tbl) x

    let term_zero = T.const ZZ.zero
    let term_one = T.const ZZ.one

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
      match T.get_const term.node with
      | Some k -> if ZZ.leq k ZZ.zero then top else bottom
      | _ -> hashcons (LeqZ term)
    let eqz term =
      match T.get_const term.node with
      | Some k -> if ZZ.equal k ZZ.zero then top else bottom
      | _ -> hashcons (EqZ term)

    let eq s t = eqz (T.sub s t)
    let leq s t = leqz (T.sub s t)
    let geq s t = leqz (T.sub t s)
    let lt s t = leqz (T.add (T.sub s t) term_one)
    let gt s t = leqz (T.add (T.sub t s) term_one)

    module M = Memo.Make(struct
      type t = Inner.t hash_consed
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
	| EqZ t -> alg (OEqZ t))

    let to_smt =
      let alg = function
	| OLeqZ t -> Smt.mk_le (T.to_smt t) (Smt.const_int 0)
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
	| OAnd (x, y) -> conj x y
	| OOr (x, y) -> disj x y
      in
      eval alg

    (* Don't eta-reduce - eval will memoize, and we'll get a space leak *)
    let free_tmp phi =
      let term_free = T.free_tmp in
      let alg = function
      | OLeqZ term | OEqZ term -> term_free term
      | OAnd (x, y) | OOr (x, y) -> Int.Set.union x y
      in
      eval alg phi

    (*
      let rec to_smt phi = match phi.node with
      | LeqZ t -> Smt.mk_le (T.to_smt t) (Smt.const_int 0)
      | EqZ t -> Smt.mk_eq (T.to_smt t) (Smt.const_int 0)
      | And phi -> Smt.big_conj (BatEnum.map to_smt (Hset.enum phi))
      | Or phi -> Smt.big_disj (BatEnum.map to_smt (Hset.enum phi))

      let rec subst sigma = function
      | LeqZ term -> leqz (T.subst sigma term)
      | EqZ term -> eqz (T.subst sigma term)
      | And phi ->
      let phi = Hset.remove top (Hset.map (subst sigma) phi) in
      if Hset.mem bottom phi then bottom
      else begin match Hset.cardinal phi with
      | 0 -> top
      | 1 -> Hset.choose phi
      | _ -> BatEnum.reduce conj (Hset.enum phi)
      end
      | Or phi ->
      let phi = Hset.remove bottom (Hset.map (subst sigma) phi) in
      if Hset.mem top phi then top
      else begin match Hset.cardinal phi with
      | 0 -> bottom
      | 1 -> Hset.choose phi
      | _ -> BatEnum.reduce disj (Hset.enum phi)
      end

      let rec free_tmp = function
      | LeqZ term | EqZ term -> T.free_tmp term
      | And phi | Or phi ->
      (BatEnum.map free_tmp (Hset.enum phi)
      |> BatEnum.fold Int.Set.union Int.Set.empty)
    *)

    let log_stats () =
      let (length, count, total, min, median, max) = HC.stats formula_tbl in
      Log.log 0 "----------------------------\n Formula stats";
      Log.logf 0 "Length:\t\t%d" length;
      Log.logf 0 "Count:\t\t%d" count;
      Log.logf 0 "Total size:\t%d" total;
      Log.logf 0 "Min bucket:\t%d" min;
      Log.logf 0 "Median bucket:\t%d" median;
      Log.logf 0 "Max bucket:\t%d" max


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
  module M = Putil.MonoMap.Ordered.Make(Var)(struct
    type t = T.t hash_consed
    include Putil.MakeFmt(struct
      type a = t
      let format formatter x = T.format formatter x.node
    end)
    module Compare_t = struct
      type a = t
      let compare x y = Pervasives.compare x.tag y.tag
    end
    let compare = Compare_t.compare
  end)

  module K = struct
    open Hashcons
    type t =
      { transform: M.t;
	guard: F.t hash_consed }
	deriving (Show,Compare)

    let format = Show_t.format
    let show = Show_t.show
    let compare = Compare_t.compare
    let equal left right = compare left right = 0

    let to_smt tr =
      let guard = F.to_smt tr.guard in
      let f var term phi =
	Smt.conj (Smt.mk_eq (Var.to_smt (Var.prime var)) (T.to_smt term)) phi
      in
      M.fold f tr.transform guard

    let free_tmp tr =
      let f _ term fv = Int.Set.union (T.free_tmp term) fv in
      M.fold f tr.transform (F.free_tmp tr.guard)

    let uniq_subst left right =
      let common = Int.Set.inter (free_tmp left) (free_tmp right) in
      if Int.Set.is_empty common then right
      else
	let tbl = Int.HT.create (2 * (Int.Set.cardinal common)) in
	let f v =
	  incr max_id;
	  Int.HT.add tbl v (!max_id)
	in
	Int.Set.iter f common;
	let alpha var = match var with
	  | V.TVar (x, name) -> begin
	    try T.var (V.TVar (Int.HT.find tbl x, name))
	    with Not_found -> T.var var
	  end
	  | V.PVar _ -> T.var var
	in
	{ transform = M.map (T.subst alpha) right.transform;
	  guard = F.subst alpha right.guard }

    let rename_tmp tr =
      let sigma_tmp = Memo.memo (fun (_, name) -> T.var (V.mk_tmp name)) in
      let sigma v = match v with
	| V.PVar var -> T.var v
	| V.TVar (id, name) -> sigma_tmp (id, name)
      in
      { transform = M.map (T.subst sigma) tr.transform;
	guard = F.subst sigma tr.guard }

    let mk_subst tr v =
      match V.lower v with
      | Some var -> begin
	try M.find var tr.transform
	with Not_found -> T.var v
      end
      | None -> T.var v

    let mul left right =
      let sigma_tmp = Memo.memo (fun (_, name) -> T.var (V.mk_tmp name)) in
      let sigma v = match v with
	| V.PVar var -> begin
	  try M.find var left.transform
	  with Not_found -> T.var v
	end
	| V.TVar (id, name) -> sigma_tmp (id, name)
      in

      let transform = M.map (T.subst sigma) right.transform in

      (* Add bindings from left transform for variables that are not written
	 in right *)
      let f v term tr =
	if M.mem v tr then tr else M.add v term tr
      in
      let transform = M.fold f left.transform transform in

      let guard = F.conj left.guard (F.subst sigma right.guard) in
      { transform = transform;
	guard = guard }

    let mul_check left right =
      let right = uniq_subst left right in
      let sigma = mk_subst left in
      let transform = M.map (T.subst sigma) right.transform in

      (* Add bindings from left transform for variables that are not written
	 in right *)
      let f v term tr =
	if M.mem v tr then tr else M.add v term tr
      in
      let transform = M.fold f left.transform transform in

      let guard = F.conj left.guard (F.subst sigma right.guard) in
      { transform = transform;
	guard = guard }


    let mul x y =
      let res = mul x y in
      Log.log Log.bottom "* Mul **********";
      Log.log_pp Log.bottom format x;
      Log.log Log.bottom "    ***   ";
      Log.log_pp Log.bottom format y;
      Log.log Log.bottom "    ===   ";
      Log.log_pp Log.bottom format res;
      res

    let add left right =
      let left_guard = ref left.guard in
      let right_guard = ref right.guard in
      let left_eq s t =
	left_guard := F.conj (!left_guard) (F.eq s t)
      in
      let right_eq s t =
	right_guard := F.conj (!right_guard) (F.eq s t)
      in
      let transform =
	let merge v x y =
	  let varname = "phi_" ^ (Var.show v) in
	  match x,y with
	  | Some s, Some t ->
	    if s.tag == t.tag then Some s else begin
	      let tmp = T.var (V.mk_tmp varname) in
	      left_eq tmp s;
	      right_eq tmp t;
	      Some tmp
	    end
	  | Some s, None ->
	    let tmp = T.var (V.mk_tmp varname) in
	    left_eq tmp s;
	    right_eq tmp (T.var (V.mk_var v));
	    Some tmp
	  | None, Some t ->
	    let tmp = T.var (V.mk_tmp varname) in
	    left_eq tmp (T.var (V.mk_var v));
	    right_eq tmp t;
	    Some tmp
	  | None, None -> assert false
	in
	M.merge merge left.transform right.transform
      in
      { transform = transform;
	guard = F.disj (!left_guard) (!right_guard) }

    let add x y =
      let res = add x y in
      Log.log Log.bottom "+ Add ++++++++++";
      Log.log_pp Log.bottom format x;
      Log.log Log.bottom "    +++   ";
      Log.log_pp Log.bottom format y;
      Log.log Log.bottom "    ===   ";
      Log.log_pp Log.bottom format res;
      res

    let one =
      { transform = M.empty;
	guard = F.top }

    module Incr = struct

      open Numeral

      (* Polynomials with rational coefficients *)
      module P = Linear.Expr.MakePolynomial(QQ)
      module Gauss = Linear.GaussElim(QQ)(P)
      module Env = BatMap.Make(Var)

      let eval env =
	let alg = function
	  | OConst k -> Some (P.zero, T.const k)
	  | OAdd (Some (px, cx), Some (py, cy)) ->
	    Some (P.add px py, T.add cx cy)
	  | OAdd (_, _) -> None
	  | OMul (Some (px, cx), Some (py, cy)) ->
	    if P.equal px P.zero then begin
	      match T.get_const cx.node with
	      | Some k ->
		Some (P.scalar_mul (QQ.of_zz k) py, T.mul (T.const k) cy)
	      | None -> None
	    end else if P.equal py P.zero then begin
	      match T.get_const cy.node with
	      | Some k ->
		Some (P.scalar_mul (QQ.of_zz k) px, T.mul (T.const k) cx)
	      | None -> None
	    end else None
	  | OVar x -> begin match V.lower x with
	    | None -> None
	    | Some v ->
	      if not (Env.mem v env) then None else begin
		let (px, cx) = Env.find v env in
		let x_minus_1 = P.add_term 1 QQ.one (P.negate P.one) in
	      (* Polynomial p(X) gives closed form for the kth term in the
		 sequence of values for v.  Since recurrence is written in
		 terms of the value of v in the pre-state, we need to look at
		 the (k-1)th term, so we use p(X-1) *)
		Some (P.compose px x_minus_1, cx)
	      end
	  end
	  | _ -> None
	in
	T.eval alg

      (* Given a polynomial p, compute a polynomial q such that for any k,
	 q(k) = p(0) + p(1) + ... + p(k-1)
      *)
      let summation p =
	let open BatEnum in
	let order = (P.order p) + 1 in (* order of q is 1 + order of p *)

	(* Create a system of linear equalities:
	   c_n*0^n + ... + c_1*0 + c_0 = p(0)
	   c_n*1^n + ... + c_1*1 + c_0 = p(0) + p(1)
	   c_n*2^n + ... + c_1*2 + c_0 = p(0) + p(1) + p(2)
	   ...
	   c_n*n^n + ... + c_1*n + c_0 = p(0) + p(1) + ... + p(n)

	   We then solve for the c_i coefficients to get q
	*)
	let rec mk_sys k =
	  if k = 0 then begin
	    let rhs = P.eval p (QQ.of_int 0) in
	    let lhs = P.var 0 in
	    (rhs, [(lhs,rhs)])
	  end else begin
	    assert (k > 0);
	    let (prev, rest) = mk_sys (k - 1) in
	    let rhs = QQ.add prev (P.eval p (QQ.of_int k)) in
	    let vars = BatEnum.(---) 1 order in
	    let lhs =
	      let qq_k = QQ.of_int k in
	      let f (rx, last) ord =
		let next = QQ.mul last qq_k in
		(P.add_term ord next rx, next)
	      in
	      fst (BatEnum.fold f (P.one, QQ.one) vars)
	    in
	    (rhs, (lhs,rhs)::rest)
	  end
	in

	let sys = snd (mk_sys order) in
	let soln = Gauss.solve sys in
	let vars = BatEnum.range ~until:order 0 in
	let add_order lin k = P.add_term k (soln k) lin in
	BatEnum.fold add_order P.zero vars

      let to_term (px,cx) var =
	let open BatEnum in
	let rec go k =
	  if k = 1 then var
	  else T.mul (go (k - 1)) var
	in
	let to_term (order, cq) =
	  let coeff =
	    let (num, den) = QQ.to_zzfrac cq in
	    T.div (T.const num) (T.const den)
	  in
	  if order = 0 then coeff
	  else T.mul coeff (go order)
	in
    	(T.add cx (BatEnum.reduce T.add (P.enum px /@ to_term)))
    end

    (* Detect induction variable *)
    let induction_var s v =
      let offset = Smt.int_var "$c" in
      s#push ();
      s#assrt (Smt.mk_eq
		 (Var.to_smt (Var.prime v))
		 (Smt.add (Var.to_smt v) offset));
      let res =
	match s#check () with
	| Smt.Unsat | Smt.Undef -> None
	| Smt.Sat -> begin
	  let m = s#get_model () in
	  let incr = m#eval_int offset in
	  s#assrt (Smt.mk_not (Smt.mk_eq offset (Smt.const_int incr)));
	  match s#check () with
	  | Smt.Unsat ->
	    let px = Incr.P.add_term 0 (QQ.of_int incr) Incr.P.zero in
	    let px_closed = Incr.summation px in
	    Some (px_closed, T.var (V.mk_var v))
	  | Smt.Sat | Smt.Undef -> None
	end
      in
      s#pop ();
      res

    let higher_induction_var v rhs env loop_counter =
      match Incr.eval env (T.sub rhs (T.var (V.mk_var v))) with
      | Some (px, cx) ->
	Log.logf Log.info "Polynomial %a: %a" Var.format v Incr.P.format px;
	let px_closed = Incr.summation px in
	let cx_closed =
	  T.add (T.mul (T.var loop_counter) cx) (T.var (V.mk_var v))
	in
	Log.logf Log.info "Closed form for %a: %a"
	  Var.format v
	  Incr.P.format px_closed;
	Some (px_closed, cx_closed)
      | None -> None

    let star tr =
      let s = new Smt.solver in
      let loop_counter = V.mk_tmp "K" in
      s#push ();
      s#assrt (to_smt tr);
      
      let f v _ env =
	match induction_var s v with
	| Some incr -> Incr.Env.add v incr env
	| None -> env
      in
      let induction_vars = M.fold f tr.transform Incr.Env.empty in
      let induction_vars =
	let g v rhs env =
	  if Incr.Env.mem v env then env else begin
	    match higher_induction_var v rhs env loop_counter with
	    | Some incr -> Incr.Env.add v incr env
	    | None -> env
	  end
	in
	M.fold g tr.transform (M.fold g tr.transform induction_vars)
      in
      let g v _ =
	try
	  let incr = Incr.Env.find v induction_vars in
	  let t = Incr.to_term incr (T.var loop_counter) in
	  Log.logf Log.info "Closed term for %a: %a"
	    Var.format v
	    Show.format<T.t hash_consed> t;
	  t

	with Not_found ->
	  Log.logf Log.info "Not an induction variable: %a" Var.format v;
	  T.var (V.mk_tmp ("nondet_" ^ (Var.show v)))
      in
      let transform = M.mapi g tr.transform in
      let res = { transform = transform;
		  guard = F.top }
      in
      Log.logf Log.info "Loop summary:@\n%a" format res;
      add one (mul res tr)
  end
  include Ka.AddZero(K)
  let to_smt = function
    | Zero -> Smt.mk_false ()
    | Nonzero tr -> K.to_smt tr

  module VarMemo = Memo.Make(Var)
  let exists p tr =
    let open K in
    match tr with
    | Zero -> Zero
    | Nonzero tr -> begin
      let transform = M.filter (fun k _ -> p k) tr.transform in
      let rename = VarMemo.memo (fun v -> V.mk_tmp (Var.show v)) in
      let sigma v = match V.lower v with
	| Some var -> T.var (if p var then v else rename var)
	| None -> T.var v
      in
      Nonzero { transform = transform;
		guard = F.subst sigma tr.guard }
    end
  let exists p tr = Log.time "transform:exists" (exists p) tr
  let mul x y = Log.time "transform:mul" (mul x) y
  let star x = Log.time "transform:star" star x
  let add x y = Log.time "transform:add" (add x) y
end

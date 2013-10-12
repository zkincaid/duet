(*pp camlp4find deriving.syntax *)

open Apak
open ArkPervasives
open BatPervasives

module type Var = sig
  include Linear.Var
  val of_smt : Smt.symbol -> t
  val typ : t -> typ
  val hash : t -> int
  val equal : t -> t -> bool
end

module type TermBasis = sig
  type t
  include Putil.Hashed.S with type t := t
  include Putil.OrderedMix with type t := t

  module V : Var

  val eval : ('a,V.t) term_algebra -> t -> 'a
  val get_const : t -> QQ.t option
  val to_smt : t -> Smt.ast
  val subst : (V.t -> t) -> t -> t

  val var : V.t -> t
  val const : QQ.t -> t
  val int : ZZ.t -> t
  val mul : t -> t -> t
  val add : t -> t -> t
  val sub : t -> t -> t
  val div : t -> t -> t
  val idiv : t -> t -> t
  val neg : t -> t
  val zero : t
  val one : t
  val floor : t -> t

  val log_stats : unit -> unit
end

module type Term = sig
  include TermBasis
  module D : NumDomain.S with type var = V.t
  val evaluate : (V.t -> QQ.t) -> t -> QQ.t
  val of_smt : (int -> V.t) -> Smt.ast -> t
  val qq_linterm : (t * QQ.t) BatEnum.t -> t
  val exp : t -> int -> t
  val to_apron : D.env -> t -> NumDomain.term
  val of_apron : D.env -> NumDomain.term -> t
  module Syntax : sig
    val ( + ) : t -> t -> t
    val ( - ) : t -> t -> t
    val ( * ) : t -> t -> t
    val ( / ) : t -> t -> t
    val ( ~$ ) : V.t -> t
    val ( ~@ ) : QQ.t -> t
  end
end

module MakeHashconsedBasis (V : Var) : TermBasis with module V = V = struct
  open Hashcons
  module rec T : sig
    type t =
    | Var of V.t
    | Const of QQ.t
    | Sum of Linexpr.t
    | Mul of (t hash_consed) * (t hash_consed)
    | Div of (t hash_consed) * (t hash_consed)
    | Floor of (t hash_consed)
    include Putil.Hashed.S with type t := t
  end = struct
    type t =
    | Var of V.t
    | Const of QQ.t
    | Sum of Linexpr.t
    | Mul of (t hash_consed) * (t hash_consed)
    | Div of (t hash_consed) * (t hash_consed)
    | Floor of (t hash_consed)

    include Putil.MakeFmt(struct
      type a = t
      let rec format formatter = function
	| Var v -> V.format formatter v
	| Const k -> QQ.format formatter k
	| Sum xs -> Linexpr.format formatter xs
	| Mul (x,y) ->
	  Format.fprintf formatter "@[(%a)@ *@ (%a)@]"
	    format x.node
	    format y.node
	| Div (x,y) ->
	  Format.fprintf formatter "@[(%a)@ /@ (%a)@]"
	    format x.node
	    format y.node
	| Floor x ->
	  Format.fprintf formatter "floor(%a)"
	    format x.node
    end)

    let hash = function
      | Var v -> Hashtbl.hash (V.hash v, 0)
      | Const k -> Hashtbl.hash (QQ.hash k, 1)
      | Sum ts -> Hashtbl.hash (Linexpr.hash ts, 2)
      | Mul (x,y) -> Hashtbl.hash (x.tag, y.tag, 3)
      | Div (x,y) -> Hashtbl.hash (x.tag, y.tag, 4)
      | Floor x -> Hashtbl.hash (x.tag, 5)

    let rec equal x y = match x, y with
      | (Var v0, Var v1) -> V.equal v0 v1
      | (Const k0, Const k1) -> QQ.equal k0 k1
      | (Sum ts0, Sum ts1) -> Linexpr.equal ts0 ts1
      | (Mul (s0,s1), Mul (t0,t1)) -> s0.tag == t0.tag && s1.tag == t1.tag
      | (Div (s0,s1), Div (t0,t1)) -> s0.tag == t0.tag && s1.tag == t1.tag
      | (Floor x, Floor y) -> x.tag == y.tag
      | (_, _) -> false
  end
  and Linexpr : (Linear.Expr.Hashed.S with type dim = T.t Hashcons.hash_consed
				      and type base = QQ.t) =
    Linear.Expr.Hashed.HMake(T)(QQ)

  open T

  type t = T.t hash_consed
  module V = V
  include Putil.MakeFmt(struct
    type a = t
    let format formatter x = T.format formatter x.node
  end)
  module Compare_t = struct
    type a = t
    let compare x y = Pervasives.compare x.tag y.tag
  end
  let compare = Compare_t.compare
  let equal x y = x.tag == y.tag
  let hash x = x.hkey

  module HC = Hashcons.Make(T)
  let term_tbl = HC.create 1000003
  let hashcons x = Log.time "term:hashcons" (HC.hashcons term_tbl) x

  let var x = hashcons (Var x)
  let const k = hashcons (Const k)
  let zero = const QQ.zero
  let one = const QQ.one
  let int k = const (QQ.of_zz k)

  let linearize = function
    | Const k -> Linexpr.add_term one k Linexpr.zero
    | Mul (s, t) as tt -> begin
      match s.node, t.node with
      | (Const k, _) -> Linexpr.add_term t k Linexpr.zero
      | (_, Const k) -> Linexpr.add_term s k Linexpr.zero
      | (_, _) -> Linexpr.add_term (hashcons tt) QQ.one Linexpr.zero
    end
    | Sum xs -> xs
    | x -> Linexpr.add_term (hashcons x) QQ.one Linexpr.zero

  let rec delinearize xs =
    let enum = Linexpr.enum xs in
    match BatEnum.get enum with
    | None -> zero
    | Some (t,coeff) -> begin match BatEnum.peek enum with
      | None -> hashcons (Mul (t, (const coeff)))
      |    _ -> hashcons (Sum xs)
    end

  and add x y =
    match x.node, y.node with
    | (Const x, Const y) -> const (QQ.add x y)
    | (Const k, _) when QQ.equal k QQ.zero -> y
    | (_, Const k) when QQ.equal k QQ.zero -> x
    | (Mul (a, b), Mul (c, d)) when a.tag == c.tag ->
      hashcons (Mul (a, add b d))
    | (x, y) ->
      delinearize (Linexpr.add (linearize x) (linearize y))

  and mul x y =
    match x.node, y.node with
    | (Div (num, den), _) -> hashcons (Div (mul num y, den))
    | (Const k, _) when QQ.equal k QQ.one -> y
    | (_, Const k) when QQ.equal k QQ.one -> x
    | (Const k, _) | (_, Const k) when QQ.equal k QQ.zero ->
      hashcons (Const QQ.zero)
    | (Const x, Const y) -> hashcons (Const (QQ.mul x y))
    | (Const k, Sum ys) | (Sum ys, Const k) ->
      delinearize (Linexpr.scalar_mul k ys)

    | (Const k, Mul (a, b)) | (Mul (a, b), Const k) -> begin
      match a.node, b.node with
      | (Const k2, v) | (v, Const k2) ->
	hashcons (Mul (hashcons (Const (QQ.mul k k2)), hashcons v))
      | (_, _) -> hashcons (Mul (x, y))
    end
    | (_, _) -> hashcons (Mul (x, y))

  let div x y =
    match x.node, y.node with
    | (_, Const k) when QQ.equal k QQ.one -> x
    | (_, _) -> hashcons (Div (x, y))

  let floor x =
    match x.node with
    | Const k -> hashcons (Const (QQ.of_zz (QQ.floor k)))
    | Floor _ -> x
    | _ -> hashcons (Floor x)

  let idiv x y = floor (div x y)

  let neg x = mul (hashcons (Const (QQ.negate QQ.one))) x
  let sub x y = add x (neg y)

  module M = Memo.Make(struct
    type t = T.t hash_consed
    let hash t = t.hkey
    let equal s t = s.tag == t.tag
  end)

  let eval alg =
    M.memo_recursive ~size:991 (fun eval x ->
      match x.node with
      | Var v -> alg (OVar v)
      | Const k -> alg (OConst k)
      | Floor v -> alg (OFloor (eval v))
      | Sum xs ->
	let term (x, k) =
	  if QQ.equal QQ.one k then eval x
	  else alg (OMul (alg (OConst k), eval x))
	in
	let f acc t = alg (OAdd (acc, term t)) in
	let enum = Linexpr.enum xs in
	begin match BatEnum.get enum with
	| None -> alg (OConst QQ.zero)
	| Some t -> BatEnum.fold f (term t) enum
	end
      | Mul (x, y) -> alg (OMul (eval x, eval y))
      | Div (x, y) -> alg (ODiv (eval x, eval y)))

  let get_const x = match x.node with
    | Var _ -> None
    | Const k -> Some k
    | Sum xs -> if Linexpr.equal xs Linexpr.zero then Some QQ.zero else None
    | Mul (_, _) -> None
    | Div (_, _) -> None
    | Floor _ -> None

  let log_stats () =
    let (length, count, total, min, median, max) = HC.stats term_tbl in
    Log.log 0 "----------------------------\n Term stats";
    Log.logf 0 "Length:\t\t%d" length;
    Log.logf 0 "Count:\t\t%d" count;
    Log.logf 0 "Total size:\t%d" total;
    Log.logf 0 "Min bucket:\t%d" min;
    Log.logf 0 "Median bucket:\t%d" median;
    Log.logf 0 "Max bucket:\t%d" max

  let to_smt =
    let alg = function
      | OVar v -> (V.to_smt v, V.typ v)
      | OConst k ->
	begin match QQ.to_zz k with
	| Some z -> (Smt.const_zz z, TyInt)
	| None   -> (Smt.const_qq k, TyReal)
	end
      | OAdd ((x,x_typ),(y,y_typ)) -> (Smt.add x y, join_typ x_typ y_typ)
      | OMul ((x,x_typ),(y,y_typ)) -> (Smt.mul x y, join_typ x_typ y_typ)
      | ODiv ((x,x_typ),(y,y_typ)) ->
	let x = match x_typ with
	  | TyReal -> x
	  | TyInt  -> (Smt.mk_int2real x)
	in
	let y = match y_typ with
	  | TyReal -> y
	  | TyInt  -> (Smt.mk_int2real y)
	in
	(Smt.mk_div x y, TyReal)
      | OFloor (x, _)   -> (Smt.mk_real2int x, TyInt)
    in
    fst % eval alg

  let subst sigma =
    let alg = function
      | OVar v -> sigma v
      | OConst k -> const k
      | OAdd (s,t) -> add s t
      | OMul (s,t) -> mul s t
      | ODiv (s,t) -> div s t
      | OFloor t -> floor t
    in
    eval alg
end

module MakeBasis (V : Var) : TermBasis with module V = V = struct
  module rec T : sig
    type t =
    | Var of V.t
    | Const of QQ.t
    | Sum of Linexpr.t
    | Mul of t * t
    | Div of t * t
    | Floor of t
    include Putil.Ordered with type t := t
    val to_smt : t -> Smt.ast
  end = struct
    type t =
    | Var of V.t
    | Const of QQ.t
    | Sum of Linexpr.t
    | Mul of t * t
    | Div of t * t
    | Floor of t
	deriving (Compare)
    let compare = Compare_t.compare
    include Putil.MakeFmt(struct
      type a = t
      let rec format formatter = function
	| Var v -> V.format formatter v
	| Const k -> QQ.format formatter k
	| Sum xs -> Linexpr.format formatter xs
	| Mul (x,y) ->
	  Format.fprintf formatter "@[(%a)@ *@ (%a)@]"
	    format x
	    format y
	| Div (x,y) ->
	  Format.fprintf formatter "@[(%a)@ /@ (%a)@]"
	    format x
	    format y
	| Floor x ->
	  Format.fprintf formatter "floor(%a)" format x
    end)
    let rec to_smt = function
      | Var v -> V.to_smt v
      | Const k ->
	begin match QQ.to_zz k with
	| Some z -> Smt.const_zz z
	| None   -> Smt.const_qq k
	end
      | Sum xs ->
	let term (x,k) = Smt.mul (to_smt x) (Smt.const_qq k) in
	Smt.sum (BatEnum.map term (Linexpr.enum xs))
      | Mul (x,y) -> Smt.mul (to_smt x) (to_smt y)
      | Div (x,y) -> Smt.mk_div (to_smt x) (to_smt y)
      | Floor x -> Smt.mk_real2int (to_smt x)
  end
  and Linexpr : Linear.Expr.Ordered.S with type dim = T.t
				   and type base = QQ.t =
                Linear.Expr.Ordered.Make(T)(QQ)

  include T
  module V = V

  let equal x y = compare x y = 0

  let var x = Var x
  let const k = Const k
  let int k = const (QQ.of_zz k)

  let linearize = function
    | Const k -> Linexpr.add_term (Const QQ.one) k Linexpr.zero
    | Mul (Const k, t) | Mul (t, Const k) ->
      Linexpr.add_term t k Linexpr.zero
    | Sum xs -> xs
    | x -> Linexpr.add_term x QQ.one Linexpr.zero

  let rec delinearize xs =
    let enum = Linexpr.enum xs in
    match BatEnum.get enum with
    | None -> Const QQ.zero
    | Some (t,coeff) -> begin match BatEnum.peek enum with
      | None -> mul t (Const coeff)
      | _    -> Sum xs
    end

  and add x y = 
    match x, y with
    | (Const x, Const y) -> const (QQ.add x y)
    | (Const k, _) when QQ.equal k QQ.zero -> y
    | (_, Const k) when QQ.equal k QQ.zero -> x
    | (Div (a, b), Div (c, d)) when equal b d ->
      Div (add a c, b)
    | (Mul (a, b), Mul (c, d)) when equal a c ->
      Mul (a, add b d)
    | (x, y) ->
      delinearize (Linexpr.add (linearize x) (linearize y))

  and mul x y =
    match x,y with
    | (Div (num,den), _) -> Div (mul num y, den)
    | (Const k, _) when QQ.equal k QQ.one -> y
    | (_, Const k) when QQ.equal k QQ.one -> x
    | (Const k, _) | (_, Const k) when QQ.equal k QQ.zero ->
      Const QQ.zero
    | (Const x, Const y) -> Const (QQ.mul x y)
    | (Const x, Sum ys) | (Sum ys, Const x) ->
      delinearize (Linexpr.scalar_mul x ys)
    | (_, _) -> Mul (x, y)

  let div x y =
    match x, y with
    | (x, Const k) when QQ.equal k QQ.one -> x
    | (x, y) -> Div (x, y)
  let neg x = mul (Const (QQ.negate QQ.one)) x
  let sub x y = add x (neg y)
  let zero = Const QQ.zero
  let one = Const QQ.one

  let log_stats () = ()
  let get_const = function
    | Const k -> Some k
    | _       -> None

  let rec eval alg = function
    | Var v -> alg (OVar v)
    | Const k -> alg (OConst k)
    | Sum xs ->
      let term (x, k) =
	if QQ.equal QQ.one k then eval alg x
	else alg (OMul (alg (OConst k), eval alg x))
      in
      let f acc t = alg (OAdd (acc, term t)) in
      let enum = Linexpr.enum xs in
      begin match BatEnum.get enum with
      | None -> alg (OConst QQ.zero)
      | Some t -> BatEnum.fold f (term t) enum
      end
    | Mul (x, y) -> alg (OMul (eval alg x, eval alg y))
    | Div (x, y) -> alg (ODiv (eval alg x, eval alg y))
    | Floor x -> alg (OFloor (eval alg x))

  let hash =
    let alg = function
      | OVar v -> Hashtbl.hash (V.hash v, 0)
      | OConst k -> Hashtbl.hash (QQ.hash k, 1)
      | OAdd (x, y) -> Hashtbl.hash (x, y, 2)
      | OMul (x, y) -> Hashtbl.hash (x, y, 3)
      | ODiv (x, y) -> Hashtbl.hash (x, y, 4)
      | OFloor x -> Hashtbl.hash (x, 5)
    in
    eval alg

  let floor x =
    match x with
    | Const k -> Const (QQ.of_zz (QQ.floor k))
    | Floor _ -> x
    | _ -> Floor x

  let idiv x y = floor (div x y)

  let rec subst sigma = function
    | Var v -> sigma v
    | Const k -> Const k
    | Sum xs ->
      let f (x,k) = linearize (mul (subst sigma x) (Const k)) in
      let s = BatEnum.map f (Linexpr.enum xs) in
      delinearize (BatEnum.fold Linexpr.add Linexpr.zero s)
    | Mul (s, t) -> mul (subst sigma s) (subst sigma t)
    | Div (s, t) -> div (subst sigma s) (subst sigma t)
    | Floor t -> floor (subst sigma t)
end

module Defaults (T : TermBasis) = struct
  include T

  module D = NumDomain.Make(T.V)

  (* Don't eta-reduce - eval will memoize, and we'll get a space leak *)
(*
  let free_tmp t =
    let alg = function
      | OVar (V.TVar (x, _)) -> Int.Set.singleton x
      | OVar (V.PVar _) | OConst _ -> Int.Set.empty
      | OAdd (xs, ys) | OMul (xs, ys) | ODiv (xs, ys) -> Int.Set.union xs ys
    in
    eval alg t
*)

  let evaluate env term =
    let f = function
      | OVar v -> env v
      | OConst k -> k
      | OAdd (s, t) -> QQ.add s t
      | OMul (s, t) -> QQ.mul s t
      | ODiv (s, t) -> QQ.div s t
      | OFloor t -> QQ.of_zz (QQ.floor t)
    in
    T.eval f term

  (** Convert a linear term over rationals (expressed as an enumeration of
      (term, rational coefficient) pairs) into a term.  This is done by
      putting all coefficients over a common denominator and then taking the
      sum.  Thus, the resulting term is guaranteed to include at most one
      division operation (ignoring division operations that may appear in
      input terms).  *)
  let qq_linterm ts =
    let denominator =
      let f acc (_, qq_coeff) = ZZ.lcm acc (QQ.denominator qq_coeff) in
      BatEnum.fold f ZZ.one (BatEnum.clone ts)
    in
    let to_term (t, qq_coeff) =
      let (num, den) = QQ.to_zzfrac qq_coeff in
      let zz_coeff = T.int (ZZ.mul num (ZZ.floor_div denominator den)) in
      T.mul zz_coeff t
    in
    BatEnum.fold T.add T.zero (ts /@ to_term)

  let of_smt env ast =
    let open Z3 in
    let ctx = Smt.get_context () in
    let rec of_smt ast =
      match get_ast_kind ctx ast with
      | APP_AST -> begin
	let app = to_app ctx ast in
	let decl = get_app_decl ctx app in
	let args =
	  let f i = of_smt (get_app_arg ctx app i) in
	  BatList.of_enum (BatEnum.map f (0 -- (get_app_num_args ctx app - 1)))
	in
	match get_decl_kind ctx decl, args with
	| (OP_UNINTERPRETED, []) -> T.var (V.of_smt (get_decl_name ctx decl))
	| (OP_ADD, args) -> List.fold_left T.add T.zero args
	| (OP_SUB, [x;y]) -> T.sub x y
	| (OP_UMINUS, [x]) -> T.neg x
	| (OP_MUL, [x;y]) -> T.mul x y
	| (OP_IDIV, [x;y]) -> T.div x y
	| (OP_TO_REAL, [x]) -> x
	| (OP_TO_INT, [x]) -> T.floor x
	| (_, _) -> begin
	  Log.errorf "Couldn't translate: %s"
	    (Z3.ast_to_string ctx ast);
	  assert false
	end
      end
      | NUMERAL_AST ->
	T.const (QQ.of_string (get_numeral_string ctx ast))
      | VAR_AST -> T.var (env (Z3.get_index_value ctx ast))
      | QUANTIFIER_AST -> assert false
      | FUNC_DECL_AST
      | SORT_AST
      | UNKNOWN_AST -> assert false
    in
    of_smt ast

  let inverse x = div one x

  (** Exponentiation (with constant exponent) *)
  let exp x k =
    let rec go x k =
      if k = 0 then zero
      else if k = 1 then x
      else begin
	let y = go x (k / 2) in
	let y2 = mul y y in
	if k mod 2 = 0 then y2 else mul x y2
      end
    in
    match get_const x with
    | Some v -> const (QQ.exp v k)
    | None   -> if k < 0 then inverse (go x (-k)) else go x k

  (** Evaluate a term within a model *)
  let eval_model m = evaluate (fun v -> m#eval_qq (V.to_smt v))

  let to_apron env t =
    let open Apron in
    let open Texpr0 in
    let atyp = function
      | TyInt  -> Int
      | TyReal -> Real
    in
    let alg = function
      | OVar v -> (Dim (D.Env.dim_of_var env v), V.typ v)
      | OConst q -> begin match QQ.to_zz q with
	| Some z -> (Cst (NumDomain.coeff_of_qq q), TyInt)
	| None   -> (Cst (NumDomain.coeff_of_qq q), TyReal)
      end
      | OAdd ((s,s_typ), (t,t_typ)) ->
	let typ = join_typ s_typ t_typ in
	(Binop (Add, s, t, atyp typ, Down), typ)
      | OMul ((s,s_typ), (t,t_typ)) ->
	let typ = join_typ s_typ t_typ in
	(Binop (Mul, s, t, atyp typ, Down), typ)
      | ODiv ((s,s_typ), (t,t_typ)) ->
	(Binop (Div, s, t, Real, Down), TyReal)
      | OFloor (t,t_typ) -> (Unop (Cast, t, Int, Down), TyInt)
    in
    Texpr0.of_expr (fst (T.eval alg t))

  let of_apron env texpr =
    let open Apron in
    let open Texpr0 in
    let rec go = function
      | Cst (Coeff.Scalar s) -> T.const (NumDomain.qq_of_scalar s)
      | Cst (Coeff.Interval _) -> assert false (* todo *)
      | Dim d -> T.var (D.Env.var_of_dim env d)
      | Unop (Neg, t, _, _) -> T.neg (go t)
      | Unop (Cast, t, Int, Down) -> T.floor (go t)
      | Unop (Cast, _, _, _) | Unop (Sqrt, _, _, _) -> assert false (* todo *)
      | Binop (op, s, t, typ, round) ->
	let (s, t) = (go s, go t) in
	begin match op with
	| Add -> T.add s t
	| Sub -> T.sub s t
	| Mul -> T.mul s t
	| Mod -> assert false (* todo *)
	| Div ->
	  begin match typ, round with
	  | Int, Down -> T.idiv s t
	  | Real, _ -> T.div s t
	  | _, _ -> assert false (* todo *)
	  end
	end
    in
    go (Texpr0.to_expr texpr)

  module Syntax = struct
    let ( + ) x y = add x y
    let ( - ) x y = sub x y
    let ( * ) x y = mul x y
    let ( / ) x y = div x y
    let ( ~$ ) x = var x
    let ( ~@ ) x = const x
  end
end

module MakeHashconsed (V : Var) : Term with type V.t = V.t
  = Defaults(MakeHashconsedBasis(V))
module Make (V : Var) : Term with type V.t = V.t
  = Defaults(MakeBasis(V))

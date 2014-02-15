(*pp camlp4find deriving.syntax *)

open Apak
open ArkPervasives
open BatPervasives

module type Var = sig
  include Linear.Var
  module Map : Putil.Map.S with type key = t
  val of_smt : Smt.symbol -> t
  val typ : t -> typ
  val hash : t -> int
  val equal : t -> t -> bool
end

module type S = sig
  type t
  include Putil.Hashed.S with type t := t
  include Putil.OrderedMix with type t := t
  module V : Var
  module D : NumDomain.S with type var = V.t
  module Linterm : Linear.Affine.S with type var = V.t
				   and type base = QQ.t
  module Set : Putil.Set.S with type elt = t

  val var : V.t -> t
  val const : QQ.t -> t
  val int : ZZ.t -> t
  val mul : t -> t -> t
  val add : t -> t -> t
  val sub : t -> t -> t
  val div : t -> t -> t
  val neg : t -> t
  val floor : t -> t
  val zero : t
  val one : t

  val inverse : t -> t
  val idiv : t -> t -> t
  val qq_linterm : (t * QQ.t) BatEnum.t -> t
  val exp : t -> int -> t

  val eval : ('a,V.t) term_algebra -> t -> 'a
  val typ : t -> typ
  val to_const : t -> QQ.t option
  val to_var : t -> V.t option
  val to_smt : t -> Smt.ast
  val subst : (V.t -> t) -> t -> t
  val evaluate : (V.t -> QQ.t) -> t -> QQ.t

  val is_linear : t -> bool
  val split_linear : t -> t * ((t * QQ.t) list)

  val of_smt : (int -> V.t) -> Smt.ast -> t
  val to_apron : D.env -> t -> NumDomain.term
  val of_apron : D.env -> NumDomain.term -> t
  val to_linterm : t -> Linterm.t option
  val of_linterm : Linterm.t -> t

  val log_stats : unit -> unit

  module Syntax : sig
    val ( + ) : t -> t -> t
    val ( - ) : t -> t -> t
    val ( * ) : t -> t -> t
    val ( / ) : t -> t -> t
    val ( ~$ ) : V.t -> t
    val ( ~@ ) : QQ.t -> t
  end
end

module Make (V : Var) = struct
  open Hashcons

  module V = V

  module Linterm = struct
    include Linear.Affine.LiftMap(V)(V.Map)(QQ)
    let hash lt =
      let var_bindings =
	var_bindings_ordered lt /@ (fun (v,c) -> V.hash v, QQ.hash c)
      in
      Hashtbl.hash (QQ.hash (const_coeff lt), BatList.of_enum var_bindings)
  end

  module T = struct
    type t = term hash_consed
    and term =
    | Lin of Linterm.t
    | Add of t * t
    | Mul of t * t
    | Div of t * t
    | Floor of t

    include Putil.MakeFmt(struct
      type a = t
      let rec format formatter term = match term.node with
	| Lin linterm -> Linterm.format formatter linterm
	| Add (x,y) ->
	  Format.fprintf formatter "@[(%a)@ +@ (%a)@]" format x format y
	| Mul (x,y) ->
	  Format.fprintf formatter "@[(%a)@ *@ (%a)@]" format x format y
	| Div (x,y) ->
	  Format.fprintf formatter "@[(%a)@ /@ (%a)@]" format x format y
	| Floor x ->
	  Format.fprintf formatter "floor(%a)" format x
    end)
    let equal x y = x.tag = y.tag
    let hash x = x.hkey
  end
  include T
  module Set = Tagged.PTSet(struct
    include T
    let tag x = x.tag
  end)

  module Compare_t = struct
    type a = t
    let compare x y = Pervasives.compare x.tag y.tag
  end
  let compare = Compare_t.compare
  let equal x y = x.tag == y.tag
  let hash x = x.hkey

  module HC = Hashcons.Make(struct
    type t = term
    let equal s t = match s, t with
    | (Lin s, Lin t) -> Linterm.equal s t
    | (Floor s, Floor t) -> s.tag == t.tag
    | (Add (w,x)), (Add (y,z)) -> w.tag == y.tag && x.tag == z.tag
    | (Mul (w,x)), (Mul (y,z)) -> w.tag == y.tag && x.tag == z.tag
    | (Div (w,x)), (Div (y,z)) -> w.tag == y.tag && x.tag == z.tag
    | (_, _) -> false
    let hash t = Hashtbl.hash (match t with
    | Lin lin    -> (Linterm.hash lin, 0, 0)
    | Floor s    -> (s.hkey, 0, 1)
    | Add (x, y) -> (x.hkey, y.hkey, 2)
    | Mul (x, y) -> (x.hkey, y.hkey, 3)
    | Div (x, y) -> (x.hkey, y.hkey, 4))
  end)
  let term_tbl = HC.create 1000003
  let hashcons x = Log.time "term:hashcons" (HC.hashcons term_tbl) x

  let of_linterm linterm = hashcons (Lin linterm)
  let to_linterm x = match x.node with
    | Lin t -> Some t
    | _ -> None

  let var x = of_linterm (Linterm.var (AVar x))
  let const k = of_linterm (Linterm.add_term AConst k Linterm.zero)
  let zero = const QQ.zero
  let one = const QQ.one
  let neg_one = const (QQ.negate QQ.one)
  let int k = const (QQ.of_zz k)

  let add x y =
    if equal x zero then y
    else if equal y zero then x
    else match x.node, y.node with
    | Lin xt, Lin yt -> of_linterm (Linterm.add xt yt)
    | _, _ -> hashcons (Add (x, y))

  let to_const x = match x.node with
    | Lin lt ->
      let e = Linterm.enum lt in
      begin match BatEnum.get e with
      | Some (AConst, base) -> if BatEnum.is_empty e then Some base else None
      | Some (_, _) -> None
      | None -> Some QQ.zero
      end
    | _ -> None

  let to_var x = match x.node with
    | Lin lt ->
      let e = Linterm.enum lt in
      begin match BatEnum.get e with
      | Some (AVar v, base) when QQ.equal base QQ.one -> Some v
      | _ -> None
      end
    | _ -> None

  let mul x y =
    match to_const x, to_const y with
    | Some kx, Some ky -> const (QQ.mul kx ky)
    | Some k, t when QQ.equal k QQ.zero -> zero
    | t, Some k when QQ.equal k QQ.zero -> zero
    | Some k, _ when QQ.equal k QQ.one -> y
    | _, Some k when QQ.equal k QQ.one -> x
    | None, Some k ->
      begin match x.node with
      | Lin lt -> of_linterm (Linterm.scalar_mul k lt)
      | _ -> hashcons (Mul (x, y))
      end
    | Some k, None ->
      begin match y.node with
      | Lin lt -> of_linterm (Linterm.scalar_mul k lt)
      | _ -> hashcons (Mul (x, y))
      end
    | _, _ -> hashcons (Mul (x, y))

  let div x y =
    match to_const y with
    | Some k when not (QQ.equal k QQ.zero) ->
      begin
	if QQ.equal k QQ.one then x
	else match x.node with
	| Lin lx -> of_linterm (Linterm.scalar_mul (QQ.inverse k) lx)
	| _ -> hashcons (Div (x, y))
      end
    | _ -> hashcons (Div (x, y))

  let floor x =
    match to_const x with
    | Some k -> const (QQ.of_zz (QQ.floor k))
    | None -> hashcons (Floor x)

  let idiv x y = floor (div x y)

  let neg x = mul neg_one x
  let sub x y = add x (neg y)

  module M = Memo.Make(struct
    type t = T.t
    let hash t = t.hkey
    let equal s t = s.tag == t.tag
  end)

  let eval alg =
    M.memo_recursive ~size:991 (fun eval x ->
      match x.node with
      | Floor v -> alg (OFloor (eval v))
      | Lin lx ->
	let term = function
	  | (AConst, k) -> alg (OConst k)
	  | (AVar x, k) ->
	    if QQ.equal QQ.one k then alg (OVar x)
	    else alg (OMul (alg (OConst k), alg (OVar x)))
	in
	let f acc t = alg (OAdd (acc, term t)) in
	let enum = Linterm.enum lx in
	begin match BatEnum.get enum with
	| None -> alg (OConst QQ.zero)
	| Some t -> BatEnum.fold f (term t) enum
	end
      | Add (x, y) -> alg (OAdd (eval x, eval y))
      | Mul (x, y) -> alg (OMul (eval x, eval y))
      | Div (x, y) -> alg (ODiv (eval x, eval y)))

  let typ t =
    let f = function
      | OFloor _ -> TyInt
      | OConst k ->
	if ZZ.equal (QQ.denominator k) ZZ.one then TyInt else TyReal
      | OVar v -> V.typ v
      | OAdd (x, y) | OMul (x, y) -> join_typ x y
      | ODiv (_, _) -> TyReal
    in
    eval f t

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

  let rec is_linear t =
    match t.node with
    | Lin _ -> true
    | _ -> false


  (* Sum of products *)
  module Sop = Linear.Expr.Make(struct
    include T
    module Compare_t = Compare_t
    let compare = compare
    let to_smt = to_smt
  end)(QQ)

  let of_sop sop =
    BatEnum.fold add zero (Sop.enum sop /@ (fun (t, k) -> mul t (const k)))

  let to_sop t =
    let product x y = Putil.cartesian_product (Sop.enum x) (Sop.enum y) in
    let mul ((x,kx), (y,ky)) = (mul x y, QQ.mul kx ky) in
    let div ((x,kx), (y,ky)) =
      assert (not (QQ.equal ky QQ.zero));
      (div x y, QQ.div kx ky)
    in
    let alg = function
      | OVar v -> Sop.var (of_linterm (Linterm.var (AVar v)))
      | OConst k -> Sop.add_term (of_linterm (Linterm.var AConst)) k Sop.zero
      | OAdd (x, y) -> Sop.add x y
      | OMul (x, y) -> Sop.of_enum ((product x y) /@ mul)
      | ODiv (x, y) -> Sop.of_enum ((product x y) /@ div)
      | OFloor x -> Sop.var (floor (of_sop x))
    in
    eval alg t

  let split_linear t =
    let (lin, nonlin) =
      BatEnum.switch (is_linear % fst) (Sop.enum (to_sop t))
    in
    (of_sop (Sop.of_enum lin), BatList.of_enum nonlin)


  module D = NumDomain.Make(V)

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

  (* May raise divide-by-zero *)
  let evaluate env term =
    let f = function
      | OVar v -> env v
      | OConst k -> k
      | OAdd (s, t) -> QQ.add s t
      | OMul (s, t) -> QQ.mul s t
      | ODiv (s, t) -> QQ.div s t
      | OFloor t -> QQ.of_zz (QQ.floor t)
    in
    eval f term

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
      let zz_coeff = int (ZZ.mul num (ZZ.floor_div denominator den)) in
      mul zz_coeff t
    in
    div (BatEnum.fold add zero (ts /@ to_term)) (const (QQ.of_zz denominator))

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
	| (OP_UNINTERPRETED, []) -> var (V.of_smt (get_decl_name ctx decl))
	| (OP_ADD, args) -> List.fold_left add zero args
	| (OP_SUB, [x;y]) -> sub x y
	| (OP_UMINUS, [x]) -> neg x
	| (OP_MUL, [x;y]) -> mul x y
	| (OP_IDIV, [x;y]) -> div x y
	| (OP_TO_REAL, [x]) -> x
	| (OP_TO_INT, [x]) -> floor x
	| (_, _) -> begin
	  Log.errorf "Couldn't translate: %s"
	    (Z3.ast_to_string ctx ast);
	  assert false
	end
      end
      | NUMERAL_AST ->
	const (QQ.of_string (get_numeral_string ctx ast))
      | VAR_AST -> var (env (Z3.get_index_value ctx ast))
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
    match to_const x with
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
    Texpr0.of_expr (fst (eval alg t))

  let of_apron env texpr =
    let open Apron in
    let open Texpr0 in
    let rec go = function
      | Cst (Coeff.Scalar s) -> const (NumDomain.qq_of_scalar s)
      | Cst (Coeff.Interval _) -> assert false (* todo *)
      | Dim d -> var (D.Env.var_of_dim env d)
      | Unop (Neg, t, _, _) -> neg (go t)
      | Unop (Cast, t, Int, Down) -> floor (go t)
      | Unop (Cast, _, _, _) | Unop (Sqrt, _, _, _) -> assert false (* todo *)
      | Binop (op, s, t, typ, round) ->
	let (s, t) = (go s, go t) in
	begin match op with
	| Add -> add s t
	| Sub -> sub s t
	| Mul -> mul s t
	| Mod -> assert false (* todo *)
	| Div ->
	  begin match typ, round with
	  | Int, Down -> idiv s t
	  | Real, _ -> div s t
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

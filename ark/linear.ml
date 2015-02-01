open Apak
open Apron
open BatPervasives
open ArkPervasives

module type Var = sig
  include Putil.Ordered
end

module AffineVar (V : Var) = struct
  type t = V.t affine
  module Compare_t = struct
    type a = t
    let compare x y = match x,y with
      | AVar x, AVar y -> V.compare x y
      | AVar _, _ -> 1
      | _, AVar _ -> -1
      | AConst, AConst -> 0
  end
  include Putil.MakeFmt(struct
    type a = t
    let format formatter = function
      | AVar v -> V.format formatter v
      | AConst -> Format.pp_print_int formatter 1
  end)
  let compare = Compare_t.compare
  let to_smt f = function
    | AVar v -> f v
    | AConst -> Smt.int_var "affine$const"
end

module type HVar = sig
  include Putil.Hashed.S
end

module Impl = struct
  module type Basis = sig
    include Putil.S

    type dim
    type base
    val scalar_mul : base -> t -> t
    val add : t -> t -> t
    val negate : t -> t
    val equal : t -> t -> bool
    val zero : t
    val find : dim -> t -> base
    val enum : t -> (dim * base) BatEnum.t
    val add_term : dim -> base -> t -> t
    val min_binding : t -> (dim * base)
    val max_binding : t -> (dim * base)
    val enum_ordered : t -> (dim * base) BatEnum.t
    val var : dim -> t
  end

  module HMake (V : HVar) (R : Ring.S)
    : Basis with type dim = V.t Hashcons.hash_consed
	    and type base = R.t
	    and type t = (V.t, R.t) Hmap.t =
  struct
    type t = (V.t, R.t) Hmap.t
    type dim = V.t Hashcons.hash_consed
    type base = R.t

    let neg_one = R.negate R.one
    let is_zero x = R.equal x R.zero

    include Putil.MakeFmt(struct
      type a = t
      let format formatter lin =
	let pp formatter (var, coeff) =
	  assert (not (is_zero coeff));
	  let var = var.Hashcons.node in
	  if R.equal coeff R.one then
	    V.format formatter var
	  else if R.equal coeff neg_one then
	    Format.fprintf formatter "-%a" V.format var
	  else
	    Format.fprintf formatter "%a*%a" R.format coeff V.format var
	in
	let enum = Hmap.enum lin in
	if BatEnum.is_empty enum then
	  R.format formatter R.zero
	else
	  Putil.format_enum pp ~left:"" ~sep:" +" ~right:"" formatter enum
    end)

    let scalar_mul k lin =
      if R.equal k R.one then lin
      else if is_zero k then Hmap.empty
      else Hmap.map (fun coeff -> R.mul k coeff) lin

    let negate = scalar_mul neg_one

    let add lin0 lin1 =
      let f _ a b =
	match a, b with
	| Some a, Some b ->
	  let sum = R.add a b in
	  if is_zero sum then None else Some sum
	| Some x, None | None, Some x -> Some x
	| None, None -> assert false
      in
      Hmap.merge f lin0 lin1
    let find x m = try Hmap.find x m with Not_found -> R.zero
    let enum = Hmap.enum
    let equal = Hmap.equal R.equal

    let zero = Hmap.empty
    let var v = Hmap.add v R.one zero
    let add_term v coeff lin =
      if is_zero coeff then lin else begin
	try
	  let sum = R.add coeff (Hmap.find v lin) in
	  if not (is_zero sum) then Hmap.add v sum lin
	  else Hmap.remove v lin
	with Not_found -> Hmap.add v coeff lin
      end

    let min_binding = Hmap.min_binding
    let max_binding = Hmap.max_binding
    let enum_ordered = Hmap.enum
    let compare cmp = Hmap.compare cmp
  end

  module Make (V : Var) (R : Ring.S) = struct
    module M = BatMap.Make(V)
    type t = R.t M.t
    type base = R.t
    type dim = V.t

    let neg_one = R.negate R.one
    let is_zero x = R.equal x R.zero

    include Putil.MakeFmt(struct
      type a = t
      let format formatter lin =
	let pp formatter (var, coeff) =
	  assert (not (is_zero coeff));
	  if R.equal coeff R.one then
	    V.format formatter var
	  else if R.equal coeff neg_one then
	    Format.fprintf formatter "-%a" V.format var
	  else
	    Format.fprintf formatter "%a*%a" R.format coeff V.format var
	in
	let enum = M.enum lin in
	if BatEnum.is_empty enum then
	  R.format formatter R.zero
	else
	  Putil.format_enum pp ~left:"" ~sep:" +" ~right:"" formatter enum
    end)

    let scalar_mul k lin =
      if R.equal k R.one then lin
      else if is_zero k then M.empty
      else M.map (fun coeff -> R.mul k coeff) lin
    let negate = scalar_mul neg_one
    let add lin0 lin1 =
      let f _ a b =
	match a, b with
	| Some a, Some b ->
	  let sum = R.add a b in
	  if is_zero sum then None else Some sum
	| Some x, None | None, Some x -> Some x
	| None, None -> assert false
      in
      M.merge f lin0 lin1

    let find x m = try M.find x m with Not_found -> R.zero
    let enum = M.enum
    let equal = M.equal R.equal
    let min_binding = M.min_binding
    let max_binding = M.max_binding
    let enum_ordered lin = BatList.enum (M.bindings lin)

    let zero = M.empty
    let var v = M.add v R.one zero
    let add_term v coeff lin =
      if is_zero coeff then lin else begin
	try
	  let sum = R.add coeff (M.find v lin) in
	  if not (is_zero sum) then M.add v sum lin
	  else M.remove v lin
	with Not_found -> M.add v coeff lin
      end
    let compare = M.compare
  end

  module LiftMap
    (V : Var)
    (M : Putil.Map.S with type key = V.t)
    (R : Ring.S) =
  struct
    type t = R.t M.t
    type base = R.t
    type dim = V.t

    let neg_one = R.negate R.one
    let is_zero x = R.equal x R.zero

    include Putil.MakeFmt(struct
      type a = t
      let format formatter lin =
	let pp formatter (var, coeff) =
	  assert (not (is_zero coeff));
	  if R.equal coeff R.one then
	    V.format formatter var
	  else if R.equal coeff neg_one then
	    Format.fprintf formatter "-%a" V.format var
	  else
	    Format.fprintf formatter "%a*%a" R.format coeff V.format var
	in
	let enum = M.enum lin in
	if BatEnum.is_empty enum then
	  R.format formatter R.zero
	else
	  Putil.format_enum pp ~left:"" ~sep:" +" ~right:"" formatter enum
    end)

    let scalar_mul k lin =
      if R.equal k R.one then lin
      else if is_zero k then M.empty
      else M.map (fun coeff -> R.mul k coeff) lin
    let negate = scalar_mul neg_one
    let add lin0 lin1 =
      let f _ a b =
	match a, b with
	| Some a, Some b ->
	  let sum = R.add a b in
	  if is_zero sum then None else Some sum
	| Some x, None | None, Some x -> Some x
	| None, None -> assert false
      in
      M.merge f lin0 lin1

    let find x m = try M.find x m with Not_found -> R.zero
    let enum = M.enum
    let equal = M.equal R.equal
    let min_binding = M.min_binding
    let max_binding = M.max_binding
    let enum_ordered lin = BatList.enum (M.bindings lin)

    let zero = M.empty
    let var v = M.add v R.one zero
    let add_term v coeff lin =
      if is_zero coeff then lin else begin
	try
	  let sum = R.add coeff (M.find v lin) in
	  if not (is_zero sum) then M.add v sum lin
	  else M.remove v lin
	with Not_found -> M.add v coeff lin
      end
    let compare = M.compare
  end

end

module Defaults (E : Impl.Basis) = struct
  (** Transpose a system of linear equations.  The length of [rows] should
      match length of [equations], and the variables each equation should be
      all belong to the list [columns].  The result is a system of linear
      equations over the row variables. *)
  let transpose equations rows columns =
    let column_sum column =
      let terms =
	BatEnum.combine
	  (BatList.enum rows,
	   (BatList.enum equations) /@ (E.find column))
      in
      let f term (lambda, coeff) = E.add_term lambda coeff term in
      BatEnum.fold f E.zero terms
    in
    List.map column_sum columns

  let to_smt dim_smt coeff_smt term =
    let f t (dim, coeff) =
      Smt.add t (Smt.mul (coeff_smt coeff) (dim_smt dim))
    in
    BatEnum.fold f (Smt.const_int 0) (E.enum term)

  let of_enum = BatEnum.fold (flip (uncurry E.add_term)) E.zero

  let sub lin0 lin1 = E.add lin0 (E.negate lin1)

  let sum = BatEnum.fold E.add E.zero

  let term dim coeff = E.add_term dim coeff E.zero
end

module Expr = struct
  module type S = sig
    include Impl.Basis
    val sub : t -> t -> t
    val of_enum : (dim * base) BatEnum.t -> t
    val to_smt : (dim -> Smt.ast) -> (base -> Smt.ast) -> t -> Smt.ast
    val transpose : t list -> dim list -> dim list -> t list
    val sum : t BatEnum.t -> t
    val term : dim -> base -> t
  end
  module Make (V : Var) (R : Ring.S) = struct
    module I = Impl.Make(V)(R)
    include I
    include Defaults(I)
  end
  module LiftMap
    (V : Var)
    (M : Putil.Map.S with type key = V.t)
    (R : Ring.S) =
  struct
    module I = Impl.LiftMap(V)(M)(R)
    include I
    include Defaults(I)
  end
  module HMake (V : HVar) (R : Ring.S) = struct
    module I = Impl.HMake(V)(R)
    include I
    include Defaults(I)
  end
  (* Univariate polynomials with coefficients in R *)
  module MakePolynomial (R : Ring.S) = struct

    module IntDim = struct
      include Putil.PInt

      (* we don't know which sort the variables should be *)
      let to_smt _ = assert false
    end

    module P = Make(IntDim)(R)
    include Defaults(P)
    type base = P.base
    type dim = P.dim
    type t = P.t
    include Putil.MakeFmt(struct
      type a = P.t
      let format formatter poly =
	let pp formatter (order, coeff) =
	  Format.fprintf formatter "%a*X^%d" R.format coeff order
	in
	let enum = P.enum poly in
	match BatEnum.peek enum with
	| Some _ ->
	  Putil.format_enum pp ~left:"" ~sep:" +" ~right:"" formatter enum
	| None -> Format.pp_print_int formatter 0
    end)

    let scalar_mul = P.scalar_mul
    let negate = P.negate
    let add = P.add
    let find = P.find
    let enum = P.enum
    let of_enum = P.of_enum
    let equal = P.equal
    let min_binding = P.min_binding
    let max_binding = P.max_binding
    let order p = if P.M.is_empty p then 0 else fst (max_binding p)
    let enum_ordered = P.enum_ordered
    let zero = P.zero
    let var = P.var
    let add_term = P.add_term
    let const k = P.add_term 0 k P.zero
    let one = const R.one
    let mul_term n coeff lin =
      let f (k, cf) = (n + k, R.mul coeff cf) in
      P.M.of_enum (BatEnum.map f (P.M.enum lin))
    let mul p q =
      let f r ((pn,pc), (qn,qc)) =
	P.add_term (pn + qn) (R.mul pc qc) r
      in
      (Putil.cartesian_product (P.enum p) (P.enum q))
      |> BatEnum.fold f P.zero
    let rec exp p n =
      if n = 0 then one
      else if n = 1 then p
      else begin
	let q = exp p (n / 2) in
	let q_squared = mul q q in
	if n mod 2 = 0 then q_squared
	else mul q q_squared
      end
    let compose p q =
      let rec go n = function
      | [] -> P.zero
      | (k,coeff)::xs ->
	let multiplier = exp q (k-n) in
	mul multiplier (add_term 0 coeff (go k xs))
      in
      go 0 (BatList.of_enum (enum_ordered p))
    let eval p x =
      let q = compose p (P.add_term 0 x P.zero) in
      match P.M.cardinal q with
      | 0 -> R.zero
      | 1 ->
	let (order, coeff) = P.M.choose q in
	assert (order = 0);
	coeff
      | _ -> assert false
    let compare = P.compare
  end

  module Ordered = struct
    module type S = sig
      include S
      include Putil.OrderedMix with type t := t
    end
    module Make (V : Var) (R : Ring.Ordered.S) = struct
      include Make(V)(R)
      module Compare_t = struct
	type a = t
	let compare = M.compare R.compare
      end
      let compare = Compare_t.compare
    end
    module HMake (V : HVar) (R : Ring.Ordered.S)
      : S with type dim = V.t Hashcons.hash_consed
	  and type base = R.t =
    struct
      include HMake(V)(R)

      module Compare_t = struct
	type a = t
	let compare = Hmap.compare R.compare
      end
      let compare = Compare_t.compare
    end
  end

  module Hashed = struct
    module type S = sig
      include S
      val hash : t -> int
      val equal : t -> t -> bool
    end
    module HMake (V : HVar) (R : Ring.Hashed.S)
      : S with type dim = V.t Hashcons.hash_consed
	  and type base = R.t =
    struct
      include HMake(V)(R)
      let hash = Hmap.hash R.hash
      let equal = Hmap.equal R.equal
    end
  end
end

module Affine = struct
  module type S = sig
    type var
    include Expr.S with type dim = var affine
    val const : base -> t
    val const_coeff : t -> base
    val var_bindings : t -> (var * base) BatEnum.t
    val var_bindings_ordered : t -> (var * base) BatEnum.t
    val var_coeff : var -> t -> base
  end
  module LiftMap
    (V : Var)
    (M : Putil.Map.S with type key = V.t)
    (R : Ring.S) =
  struct
    module I = struct
      module L = Impl.LiftMap(V)(M)(R)
      type t = L.t * R.t
      type base = R.t
      type dim = V.t affine
      type var = V.t

      include Putil.MakeFmt(struct
	type a = t
	let format formatter (lt, k) =
	  if R.equal k R.zero then L.format formatter lt
	  else if L.equal lt L.zero then R.format formatter k
	  else Format.fprintf formatter "@[%a@ + %a@]" L.format lt R.format k
      end)

      (* Lift dim * base to (affine dim * base) *)
      let lift_pair (dim, base) = (AVar dim, base)

      let zero = (L.zero, R.zero)
      let equal (lt1, k1) (lt2, k2) = R.equal k1 k2 && L.equal lt1 lt2
      let scalar_mul a (lt, k) = (L.scalar_mul a lt, R.mul a k)
      let add (lt1, k1) (lt2, k2) = (L.add lt1 lt2, R.add k1 k2)
      let negate (lt, k) = (L.negate lt, R.negate k)
      let find dim (lt, k) = match dim with
	| AConst -> k
	| AVar v -> L.find v lt
      let enum (lt, k) =
	let e = L.enum lt /@ lift_pair in
	if not (R.equal k R.zero) then BatEnum.push e (AConst, k);
	e
      let add_term dim coeff (lt, k) = match dim with
	| AConst -> (lt, R.add k coeff)
	| AVar v -> (L.add_term v coeff lt, k)
      let min_binding (lt, k) =
	if R.equal k R.zero then L.min_binding lt |> lift_pair
	else (AConst, k)
      let max_binding (lt, k) =
	try L.max_binding lt |> lift_pair
	with Not_found ->
	  if R.equal k R.zero then raise Not_found else (AConst, k)
      let enum_ordered (lt, k) =
	let e = L.enum_ordered lt /@ lift_pair in
	if not (R.equal k R.zero) then BatEnum.push e (AConst, k);
	e
      let var = function
	| AConst -> (L.zero, R.one)
	| AVar v -> (L.var v, R.zero)
    end
    include I
    include Defaults(I)

    let const k = (L.zero, k)
    let const_coeff (_, k) = k
    let var_bindings (lt, _) = L.enum lt
    let var_bindings_ordered (lt, _) = L.enum_ordered lt
    let var_coeff v (lt, _) = L.find v lt
  end
end

(* Gaussian elimination *)
exception No_solution
exception Many_solutions
module GaussElim
  (F : Field.S)
  (E : Expr.S with type base = F.t) =
struct

  type eq = E.t * F.t

  module Fmt = Putil.MakeFmt(struct
    type a = eq list
    let format formatter xs =
      let pp (lhs,rhs) =
	Format.fprintf formatter "%a\t= %a@\n"
	  E.format lhs
	  F.format rhs
      in
      List.iter pp xs
  end)

  let is_zero x = F.equal x F.zero
  let is_empty x = E.equal x E.zero

  let solve sys =
    Log.logf "Solving system:@\n @[%a@]" Fmt.format sys;
    let rec reduce fin sys =
      match sys with
      | [] -> fin
      | ((lhs, rhs)::rest) ->
	if is_empty lhs
	then
	  if is_zero rhs then reduce fin rest
	  else raise No_solution
	else begin
	  let (var, coeff) = E.min_binding lhs in
	  let coeff_inv = F.inverse coeff in
	  let f (lhs', rhs') =
	    try
	      let coeff' = E.find var lhs' in
	      let k = F.negate (F.mul coeff_inv coeff') in
	      (E.add (E.scalar_mul k lhs) lhs', F.add (F.mul k rhs) rhs')
	    with Not_found -> (lhs', rhs')
	  in
	  reduce ((lhs,rhs)::fin) (List.map f rest)
	end
    in
    let rr = reduce [] sys in
    let rec backprop map = function
      | [] -> map
      | ((lhs, rhs)::rest) -> begin
	(* Ordered bindings, so first element is always going to be smallest
	   -> all other variables in lhs should already be assigned values in
	   map if the system has a single solution *)
	let enum = E.enum_ordered lhs in
	match BatEnum.get enum with
	| None -> assert false
	| Some (var,coeff) ->
	  let f acc (v, c) =
	    try F.add acc (F.mul (E.find v map) c)
	    with Not_found ->
	      (* todo: we're using 0-suppressed expressions to implement maps
		 here, so if a variable doesn't appear in the expression, it's
		 mapped to zero. *)
	      acc
	  in
	  let rhs = F.negate (BatEnum.fold f (F.negate rhs) enum) in
	  let map = E.add_term var (F.div rhs coeff) map in
	  backprop map rest
      end
    in
    let map = backprop E.zero rr in
    fun x ->
      try E.find x map
      with Not_found -> F.zero
end

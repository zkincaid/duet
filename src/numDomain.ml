(*pp camlp4find deriving.syntax *)

(** Numerical abstract domains *)
open Apron
open Apak
open BatPervasives
open ArkPervasives

type dim = int
type term = Texpr0.t
type atom = Tcons0.t

let qq_of_scalar = function
  | Scalar.Float k -> QQ.of_float k
  | Scalar.Mpqf k  -> k
  | Scalar.Mpfrf k -> Mpfrf.to_mpqf k

let qq_of_coeff = function
  | Coeff.Scalar s -> Some (qq_of_scalar s)
  | Coeff.Interval _ -> None

let coeff_of_qq = Coeff.s_of_mpqf

let scalar_zero = Coeff.s_of_int 0
let scalar_one = Coeff.s_of_int 1

module Env = struct
  module type S = sig
    type var
    include Putil.S
    val of_enum : var BatEnum.t -> t
    val of_list : var list -> t
    val empty : t
    val filter : (var -> bool) -> t -> t
    val dim_of_var : t -> var -> dim
    val var_of_dim : t -> dim -> var
    val typ_of_dim : t -> dim -> typ
    val equal : t -> t -> bool
    val int_dim : t -> int
    val real_dim : t -> int
    val dimension : t -> int
    val vars : t -> var BatEnum.t
    val dimensions : t -> dim BatEnum.t
    val mem : var -> t -> bool
  end
  module Make (V : Var) = struct
    module S = Putil.Set.Make(V)

    type t =
      { int_dim : V.t array;
	real_dim : V.t array }
	deriving (Show,Compare)

    type var = V.t

    let format = Show_t.format
    let show = Show_t.show
    let compare = Compare_t.compare

    let empty = { int_dim = [||]; real_dim = [||] }

    (* Search for an index in a sorted array *)
    let search v array =
      let rec go min max =
	if max < min then raise Not_found
	else begin
	  let mid =  min + ((max - min) / 2) in
	  let cmp = V.compare v array.(mid) in
	  if cmp < 0 then go min (mid - 1)
	  else if cmp > 0 then go (mid + 1) max
	  else mid
	end
      in
      go 0 (Array.length array - 1)

    (* Merge two (sorted) arrays *)
    let merge_array a b =
      let alen = Array.length a in
      let blen = Array.length b in
      (* count the size of the intersection of a and b *)
      let rec common i j acc = 
	if i == alen || j == blen then acc else begin
	  let cmp = V.compare a.(i) b.(j) in
	  if cmp < 0 then common (i + 1) j acc
	  else if cmp > 0 then common i (j + 1) acc
	  else common (i + 1) (j + 1) (acc + 1)
	end
      in
      let clen = alen + blen - (common 0 0 0) in
      let c = Array.create clen (Obj.magic ()) in
      let rec go i j k =
	if k < clen then begin
	  if i == alen then (c.(k) <- b.(j); go i (j + 1) (k + 1))
	  else if j == blen then (c.(k) <- a.(i); go (i + 1) j (k + 1))
	  else begin
	    let cmp = V.compare a.(i) b.(j) in
	    if cmp < 0 then (c.(k) <- a.(i); go (i + 1) j (k + 1))
	    else if cmp > 0 then (c.(k) <- b.(j); go i (j + 1) (k + 1))
	    else (c.(k) <- a.(i); go (i + 1) (j + 1) (k + 1))
	  end
	end
      in
      go 0 0 0;
      c

    (* compute the smallest environment which has env0 and env1 as
       sub-environments *)
    let merge env0 env1 =
      { int_dim = merge_array env0.int_dim env1.int_dim;
	real_dim = merge_array env0.real_dim env1.real_dim }

    let inject_array a b =
      let alen = Array.length a in
      let blen = Array.length b in
      let rec go i j acc =
	if j >= blen then acc else begin
	  if i < alen then begin
	    let cmp = V.compare a.(i) b.(j) in
	    assert (cmp >= 0);
	    if cmp == 0 then go (i + 1) (j + 1) acc
	    else go i (j + 1) (i::acc)
	  end
	  else go i (j + 1) (i::acc)
	end
      in
      List.rev (go 0 0 [])

    let inject a b =
      let int_change = inject_array a.int_dim b.int_dim in
      let idim = Array.length a.int_dim in
      let real_change =
	List.map (fun x -> x + idim) (inject_array a.real_dim b.real_dim)
      in
      let change = Array.of_list (int_change @ real_change) in 
      { Dim.dim = change;
	Dim.intdim = List.length int_change;
	Dim.realdim = List.length real_change }

    let of_set vars =
      let count v (int, real) = match V.typ v with
	| TyInt  -> (int + 1, real)
	| TyReal -> (int, real + 1)
      in
      let (int, real) = S.fold count vars (0, 0) in
      let int_dim = Array.create int (Obj.magic ()) in
      let real_dim = Array.create real (Obj.magic ()) in
      let int_max = ref 0 in
      let real_max = ref 0 in
      let f v = match V.typ v with
	| TyInt  -> (int_dim.(!int_max) <- v; incr int_max)
	| TyReal -> (real_dim.(!real_max) <- v; incr real_max)
      in
      S.iter f vars;
      { int_dim = int_dim;
	real_dim = real_dim }

    let of_enum e = of_set (S.of_enum e)
    let of_list vs = of_enum (BatList.enum vs)
    let dim_of_var env v = match V.typ v with
      | TyInt  -> search v env.int_dim
      | TyReal -> (Array.length env.int_dim) + (search v env.real_dim)
    let var_of_dim env dim =
      let intd = Array.length env.int_dim in
      if dim >= intd then env.real_dim.(dim - intd)
      else env.int_dim.(dim)
    let typ_of_dim env dim =
      if dim >= (Array.length env.int_dim) then TyReal else TyInt
    let equal e0 e1 = compare e0 e1 = 0
    let int_dim env = Array.length env.int_dim
    let real_dim env = Array.length env.real_dim
    let dimension env = int_dim env + real_dim env
    let vars env =
      BatEnum.append (BatArray.enum env.int_dim) (BatArray.enum env.real_dim)
    let dimensions env = 0 -- (dimension env)
    let filter p env =
      { int_dim = BatArray.filter p env.int_dim;
	real_dim = BatArray.filter p env.real_dim }
    let mem v env =
      try ignore (dim_of_var env v); true
      with Not_found -> false
  end
end

module type S = sig
  type 'a t =
    { prop : 'a Abstract0.t;
      env : env}
  and env
  type var
  module Env : Env.S with type t = env and type var = var
  val format : Format.formatter -> 'a t -> unit
  val show : 'a t -> string
  val is_bottom : 'a t -> bool
  val is_top : 'a t -> bool
  val top : 'a Manager.t -> env -> 'a t
  val bottom : 'a Manager.t -> env -> 'a t
  val leq : 'a t -> 'a t -> bool
  val equal : 'a t -> 'a t -> bool
  val join : 'a t -> 'a t -> 'a t
  val meet : 'a t -> 'a t -> 'a t
  val widen : 'a t -> 'a t -> 'a t
  val exists : 'a Manager.t -> (var -> bool) -> 'a t -> 'a t
  val add_vars : var BatEnum.t -> 'a t -> 'a t
  val boxify : 'a t -> 'a t
end

module Make (V : Var) = struct
  module Env = Env.Make(V)
  module VarSet = Putil.Set.Make(V)

  type 'a t =
    { prop : 'a Abstract0.t;
      env : Env.t }
  type var = V.t
  type env = Env.t

  let man prop = Abstract0.manager prop

  let format formatter x =
    Abstract0.print (V.show % (Env.var_of_dim x.env)) formatter x.prop

  let show x = Putil.pp_string format x

  let is_bottom x = Abstract0.is_bottom (man x.prop) x.prop

  let is_top x = Abstract0.is_top (man x.prop) x.prop

  let top man env =
    { prop = Abstract0.top man (Env.int_dim env) (Env.real_dim env);
      env = env }

  let bottom man env =
    { prop = Abstract0.bottom man (Env.int_dim env) (Env.real_dim env);
      env = env }

  (* Compute a common environment for the abstract values x and y, and then
     apply the function f to the numerical abstract values for x and y in the
     common environment *)
  let common_env man f x y =
    let env = Env.merge x.env y.env in
    let set_env z =
      Abstract0.add_dimensions man z.prop (Env.inject z.env env) false
    in
    f man (set_env x) (set_env y)

  let common_env_prop man f x y =
    let env = Env.merge x.env y.env in
    let set_env z =
      let open Manager in
      try
	Abstract0.add_dimensions man z.prop (Env.inject z.env env) false
      with Error log -> begin
	Log.errorf "APRON error: %s" log.msg;
	raise (Error log)
      end
    in
    { prop = f man (set_env x) (set_env y);
      env = env }

  let leq x y = common_env (man x.prop) Abstract0.is_leq x y

  let equal x y = common_env (man x.prop) Abstract0.is_eq x y

  let join x y = common_env_prop (man x.prop) Abstract0.join x y

  let meet x y = common_env_prop (man x.prop) Abstract0.meet x y

  let widen x y = common_env_prop (man x.prop) Abstract0.widening x y

  let exists man p x =
    let intdim = ref 0 in
    let realdim = ref 0 in
    let remember = ref [] in
    let forget = ref [] in
    let dimension = Env.dimension x.env in
    for i = dimension - 1 downto 0 do
      let v = Env.var_of_dim x.env i in
      if p v then begin
	remember := v::(!remember)
      end else begin
	forget := i::(!forget);
	match V.typ v with
	| TyInt  -> incr intdim
	| TyReal -> incr realdim
      end
    done;
    let prop =
      Abstract0.remove_dimensions
	man
	x.prop
	{ Dim.dim = Array.of_list (!forget);
	  Dim.intdim = !intdim;
	  Dim.realdim = !realdim }
    in
    let env = Env.of_enum (BatList.enum (!remember)) in
    { prop = prop;
      env = env}

  let add_vars vars x =
    let new_env = Env.merge x.env (Env.of_enum vars) in
    let man = man x.prop in
    let prop =
      Abstract0.add_dimensions man x.prop (Env.inject x.env new_env) false
    in
    { prop = prop;
      env = new_env }

  let boxify x =
    let man = man x.prop in
    { prop =
	Abstract0.of_box
	  man
	  (Env.int_dim x.env)
	  (Env.real_dim x.env)
	  (Abstract0.to_box man x.prop);
      env = x.env }
end

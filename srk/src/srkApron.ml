open Apron
open BatPervasives
open Syntax

type dim = int
type texpr = Texpr0.t
type lexpr = Linexpr0.t
type tcons = Tcons0.t
type lcons = Lincons0.t
type scalar = Scalar.t
type coeff = Coeff.t

let qq_of_scalar = function
  | Scalar.Float k -> QQ.of_float k
  | Scalar.Mpqf k  -> k
  | Scalar.Mpfrf k -> Mpfrf.to_mpqf k

let qq_of_coeff = function
  | Coeff.Scalar s -> Some (qq_of_scalar s)
  | Coeff.Interval _ -> None

let coeff_of_qq = Coeff.s_of_mpqf

let scalar_one = Coeff.s_of_int 1

module Env = struct
  type 'a t =
    { int_dim : symbol array;
      real_dim : symbol array;
      srk : 'a context }

  let pp formatter env =
    let pp_array formatter arr =
      SrkUtil.pp_print_enum_nobox
        (pp_symbol env.srk)
        formatter (BatArray.enum arr)
    in
    Format.fprintf formatter "@[<v 0>{int: @[%a@];@;real:@[%a@]@]"
      pp_array env.int_dim
      pp_array env.real_dim

  let empty srk = { int_dim = [||]; real_dim = [||]; srk = srk }

  (* Search for an index in a sorted array *)
  let search v array =
    let rec go min max =
      if max < min then raise Not_found
      else begin
        let mid =  min + ((max - min) / 2) in
        let cmp = Symbol.compare v array.(mid) in
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
        let cmp = Symbol.compare a.(i) b.(j) in
        if cmp < 0 then common (i + 1) j acc
        else if cmp > 0 then common i (j + 1) acc
        else common (i + 1) (j + 1) (acc + 1)
      end
    in
    let clen = alen + blen - (common 0 0 0) in
    let c = Array.make clen (Obj.magic ()) in
    let rec go i j k =
      if k < clen then begin
        if i == alen then (c.(k) <- b.(j); go i (j + 1) (k + 1))
        else if j == blen then (c.(k) <- a.(i); go (i + 1) j (k + 1))
        else begin
          let cmp = Symbol.compare a.(i) b.(j) in
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
      real_dim = merge_array env0.real_dim env1.real_dim;
      srk = env0.srk }

  let inject_array a b =
    let alen = Array.length a in
    let blen = Array.length b in
    let rec go i j acc =
      if j >= blen then acc else begin
        if i < alen then begin
          let cmp = Symbol.compare a.(i) b.(j) in
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

  let of_set srk vars =
    let count v (int, real) = match typ_symbol srk v with
      | `TyInt  -> (int + 1, real)
      | `TyReal -> (int, real + 1)
      | _ -> invalid_arg "SrkApon: environment symbols must be number-typed"
    in
    let (int, real) = Symbol.Set.fold count vars (0, 0) in
    let int_dim = Array.make int (Obj.magic ()) in
    let real_dim = Array.make real (Obj.magic ()) in
    let int_max = ref 0 in
    let real_max = ref 0 in
    let f v = match typ_symbol srk v with
      | `TyInt  -> (int_dim.(!int_max) <- v; incr int_max)
      | `TyReal -> (real_dim.(!real_max) <- v; incr real_max)
      | _ -> assert false
    in
    Symbol.Set.iter f vars;
    { int_dim = int_dim;
      real_dim = real_dim;
      srk = srk }

  let of_enum srk e = of_set srk (Symbol.Set.of_enum e)
  let of_list srk symbols = of_enum srk (BatList.enum symbols)
  let dim_of_var env sym = match typ_symbol env.srk sym with
    | `TyInt  -> search sym env.int_dim
    | `TyReal -> (Array.length env.int_dim) + (search sym env.real_dim)
    | _ -> invalid_arg "SrkApon: environment symbols must be number-typed"
  let var_of_dim env dim =
    let intd = Array.length env.int_dim in
    if dim >= intd then
      try
        env.real_dim.(dim - intd)
      with Invalid_argument _ -> invalid_arg "Env.var_of_dim: out of bounds"
    else
      env.int_dim.(dim)
  let int_dim env = Array.length env.int_dim
  let real_dim env = Array.length env.real_dim
  let dimension env = int_dim env + real_dim env
  let vars env =
    BatEnum.append (BatArray.enum env.int_dim) (BatArray.enum env.real_dim)
  let dimensions env = 0 -- ((dimension env) - 1)
  let filter p env =
    { int_dim = BatArray.filter p env.int_dim;
      real_dim = BatArray.filter p env.real_dim;
      srk = env.srk }
  let mem v env =
    try ignore (dim_of_var env v); true
    with Not_found -> false
end

type ('a,'abs) property =
  { prop : 'abs Abstract0.t;
    env : 'a Env.t }

let man prop = Abstract0.manager prop

let pp formatter x =
  Abstract0.print
    (show_symbol x.env.Env.srk % (Env.var_of_dim x.env))
    formatter
    x.prop

let show x = SrkUtil.mk_show pp x

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
      match typ_symbol x.env.Env.srk v with
      | `TyInt  -> incr intdim
      | `TyReal -> incr realdim
      | _ -> assert false
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
  let env = Env.of_enum x.env.Env.srk (BatList.enum (!remember)) in
  { prop = prop;
    env = env}

let add_vars vars x =
  let new_env = Env.merge x.env (Env.of_enum x.env.Env.srk vars) in
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

let rename f x =
  let env = Env.vars x.env /@ f |> Env.of_enum x.env.Env.srk in
  let dimensions = Env.dimensions x.env |> BatArray.of_enum in
  let replacements =
    let g var =
      Linexpr0.of_list None
        [(scalar_one, Env.dim_of_var env (f (Env.var_of_dim x.env var)))]
        None
    in
    Array.map g dimensions
  in
  let prop =
    Abstract0.substitute_linexpr_array
      (man x.prop)
      x.prop
      dimensions
      replacements
      None
  in
  { env; prop }

module V = Linear.QQVector

let lexpr_of_vec env vec =
  let mk (coeff, dim) =
    match Linear.sym_of_dim dim with
    | None -> assert false
    | Some sym -> (coeff_of_qq coeff, Env.dim_of_var env sym)
  in
  let (const_coeff, rest) = V.pivot Linear.const_dim vec in
  Linexpr0.of_list None
    (BatList.of_enum (BatEnum.map mk (V.enum rest)))
    (Some (coeff_of_qq const_coeff))

let vec_of_lexpr env linexpr =
  let vec = ref V.zero in
  Linexpr0.iter (fun coeff dim ->
      match qq_of_coeff coeff with
      | Some qq ->
        vec := V.add_term qq (Linear.dim_of_sym (Env.var_of_dim env dim)) (!vec)
      | None -> assert false)
    linexpr;
  match qq_of_coeff (Linexpr0.get_cst linexpr) with
  | Some qq -> V.add_term qq Linear.const_dim (!vec)
  | None -> assert false

let join_typ s t =
  match s,t with
  | `TyInt, `TyInt -> `TyInt
  | `TyReal, `TyReal | `TyReal, `TyInt | `TyInt, `TyReal -> `TyReal
  | _, _ -> invalid_arg "join_typ: non-numeric type"

let texpr_of_term env t =
  let open Texpr0 in
  let atyp = function
    | `TyInt  -> Int
    | `TyReal -> Real
    | _ -> assert false
  in
  let alg = function
    | `Real qq ->
      begin match QQ.to_zz qq with
        | Some _ -> (Cst (coeff_of_qq qq), `TyInt)
        | None   -> (Cst (coeff_of_qq qq), `TyReal)
      end
    | `App (sym, []) ->
      (Dim (Env.dim_of_var env sym), typ_symbol env.Env.srk sym)
    | `App (_, _) | `Ite (_, _, _) | `Var (_, _) -> assert false
    | `Binop(`Select, _, _) | `Store (_, _, _) | `Unop (`ConstArr, _) -> assert false
    | `Add terms ->
      let add (s,s_typ) (t,t_typ) =
        let typ = join_typ s_typ t_typ in
        (Binop (Add, s, t, atyp typ, Down), typ)
      in
      List.fold_left add (Cst (coeff_of_qq QQ.zero), `TyInt) terms

    | `Mul terms ->
      let mul (s,s_typ) (t,t_typ) =
        let typ = join_typ s_typ t_typ in
        (Binop (Mul, s, t, atyp typ, Down), typ)
      in
      List.fold_left mul (Cst (coeff_of_qq QQ.one), `TyInt) terms
    | `Binop (`Div, (s,_), (t,_)) ->
      (Binop (Div, s, t, Real, Zero), `TyReal)
    | `Binop (`Mod, (s,s_typ), (t,t_typ)) ->
       let typ = join_typ s_typ t_typ in
      (Binop (Mod, s, t, atyp typ, Zero), typ)
    | `Unop (`Floor, (t, _)) -> (Unop (Cast, t, Int, Down), `TyInt)
    | `Unop (`Neg, (t, typ)) ->
      (Binop (Mul, Cst (coeff_of_qq (QQ.negate QQ.one)), t, atyp typ, Down),
       typ)
  in
  Texpr0.of_expr (fst (Term.eval env.Env.srk alg t))

let term_of_texpr env texpr =
  let open Texpr0 in
  let srk = env.Env.srk in
  let rec go = function
    | Cst (Coeff.Scalar s) -> mk_real srk (qq_of_scalar s)
    | Cst (Coeff.Interval _) -> assert false (* todo *)
    | Dim d -> mk_const srk (Env.var_of_dim env d)
    | Unop (Neg, t, _, _) -> mk_neg srk (go t)
    | Unop (Cast, t, Int, Down) -> mk_floor srk (go t)
    | Unop (Cast, _, _, _) | Unop (Sqrt, _, _, _) -> assert false (* todo *)
    | Binop (op, s, t, typ, round) ->
      let (s, t) = (go s, go t) in
      begin match op with
        | Add -> mk_add srk [s; t]
        | Sub -> mk_sub srk s t
        | Mul -> mk_mul srk [s; t]
        | Mod ->
          begin match typ, round with
            | Int, Zero -> mk_mod srk s t
            | _, _ -> assert false
          end
        | Pow -> assert false (* todo *)
        | Div ->
          begin match typ, round with
            | Int, Down -> (*mk_idiv srk s t*) assert false
            | Real, _ -> mk_div srk s t
            | _, _ -> assert false (* todo *)
          end
      end
  in
  go (Texpr0.to_expr texpr)

let lcons_geqz lexpr = Lincons0.make lexpr Lincons0.SUPEQ
let lcons_gtz lexpr = Lincons0.make lexpr Lincons0.SUP
let lcons_eqz lexpr = Lincons0.make lexpr Lincons0.EQ

let tcons_geqz texpr = Tcons0.make texpr Tcons0.SUPEQ
let tcons_gtz texpr = Tcons0.make texpr Tcons0.SUP
let tcons_eqz texpr = Tcons0.make texpr Tcons0.EQ

let meet_tcons property constraints =
  { property
    with prop =
           Abstract0.meet_tcons_array
             (Abstract0.manager property.prop)
             property.prop
             (BatArray.of_list constraints) }

let meet_lcons property constraints =
  { property
    with prop =
           Abstract0.meet_lincons_array
             (Abstract0.manager property.prop)
             property.prop
             (BatArray.of_list constraints) }

let formula_of_tcons env tcons =
  let open Tcons0 in
  let t = term_of_texpr env tcons.texpr0 in
  let srk = env.Env.srk in
  let zero = mk_real srk QQ.zero in
  match tcons.typ with
  | EQ      -> mk_eq srk t zero
  | SUPEQ   -> mk_leq srk zero t
  | SUP     -> mk_lt srk zero t
  | DISEQ   -> mk_not srk (mk_eq srk t zero)
  | EQMOD _ -> assert false (* todo *)

let formula_of_property property =
  let srk = property.env.Env.srk in
  let man = man property.prop in
  BatArray.enum (Abstract0.to_tcons_array man property.prop)
  /@ (formula_of_tcons property.env)
  |> BatList.of_enum
  |> mk_and srk

let get_env property = property.env

let get_manager property = man property.prop

(* Evaluate a closed expression to an interval *)
let eval_texpr expr =
  let man = Box.manager_alloc () in
  Abstract0.bound_texpr man (Abstract0.top man 0 0) expr

let generators property =
  let man = get_manager property in
  Abstract0.to_generator_array man property.prop
  |> BatArray.to_list
  |> List.map Generator0.(fun g ->
      let vec = vec_of_lexpr property.env g.linexpr0 in
      let typ = match g.typ with
        | LINE -> `Line
        | RAY -> `Ray
        | VERTEX -> `Vertex
        | LINEMOD -> `LineMod
        | RAYMOD -> `RayMod
      in
      (vec, typ))

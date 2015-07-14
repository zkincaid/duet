open Hashcons

type const_symbol = int

type typ = TyInt | TyReal
             deriving (Compare)
module Show_typ = Deriving_Show.Defaults(struct
    type a = typ
    let format formatter = function
      | TyReal -> Format.pp_print_string formatter "real"
      | TyInt -> Format.pp_print_string formatter "int"
  end)

type label =
  | True
  | False
  | And
  | Or
  | Not
  | Exists of string * typ
  | Forall of string * typ
  | Eq
  | Leq
  | Lt
  | Const of const_symbol
  | Var of int * typ
  | Add
  | Mul
  | Div
  | Mod
  | Floor
  | Neg
  | Real of QQ.t

type expr = Node of label * ((expr hash_consed) list)
type formula = expr hash_consed
type term = expr hash_consed

module HC = Hashcons.Make(struct
    type t = expr
    let equal (Node (label, args)) (Node (label', args')) =
      (match label, label' with
       | Exists (_, typ), Exists (_, typ') -> typ = typ'
       | Forall (_, typ), Forall (_, typ') -> typ = typ'
       | _, _ -> label = label')
      && List.for_all2 (fun x y -> x.tag = y.tag) args args'
    let compare = Pervasives.compare
    let hash (Node (label, args)) =
      Hashtbl.hash (label, List.map (fun expr -> expr.tag) args)
  end)

module type Constant = sig
  type t
  val format : Format.formatter -> t -> unit
  val typ : t -> typ
  val hash : t -> int
  val equal : t -> t -> bool
end

module ConstSymbol = Apak.Putil.PInt

module Var = struct
  module I = struct
    type t = int * typ
               deriving (Show,Compare)
    let format = Show.format<t>
    let show = Show.show<t>
    let compare = Compare.compare<t>
  end
  include I
  module Set = Apak.Putil.Set.Make(I)
  module Map = Apak.Putil.Map.Make(I)
end
module Env = struct
  type 'a t = 'a list
  let push x xs = x::xs
  let find i xs =
    try List.nth i xs
    with Failure _ -> raise Not_found
  let empty = []
end

type 'a context =
  { const_of_sym : 'a BatDynArray.t;
    sym_of_const : 'a -> const_symbol;
    const_format : Format.formatter -> 'a -> unit;
    const_typ : 'a -> typ;
    expr : HC.t }

let mk_context (type t) (module C : Constant with type t = t) =
  let module HT = Hashtbl.Make(C) in
  let const_of_sym = BatDynArray.make 256 in
  let sym_of_const =
    let table = HT.create 991 in
    fun k ->
      try HT.find table k
      with Not_found ->
        let id = BatDynArray.length const_of_sym in
        BatDynArray.add const_of_sym k;
        HT.add table k id;
        id
  in
  { const_of_sym = const_of_sym;
    sym_of_const = sym_of_const;
    const_format = C.format;
    const_typ = C.typ;
    expr = HC.create 991 }

module TypedString = struct
  type t = string * typ
  let format formatter (name, _) = Format.pp_print_string formatter name
  let typ = snd
  let hash = Hashtbl.hash
  let equal = (=)
end
let mk_string_context () = mk_context (module TypedString)

let const_of_symbol ctx id = BatDynArray.get ctx.const_of_sym id
let symbol_of_const ctx = ctx.sym_of_const
let id_of_symbol id = id
let symbol_of_id id = id

let hashcons ctx = HC.hashcons ctx.expr

let const_typ ctx const = ctx.const_typ (const_of_symbol ctx const)

let const_format ctx formatter const =
  ctx.const_format formatter (const_of_symbol ctx const)

let rec eval_expr alg expr =
  let (Node (label, children)) = expr.node in
  alg label (List.map (eval_expr alg) children)

let rec flatten_expr label expr =
  let Node (label', children) = expr.node in
  if label = label' then
    List.concat (List.map (flatten_expr label) children)
  else
    [expr]

module Expr = struct
  type t = expr hash_consed

  let equal s t = s.tag = t.tag
  let compare s t = Pervasives.compare s.tag t.tag
  let hash t = t.hkey

  let substitute ctx subst expr =
    (* Avoid capture *)
    let rec decapture depth expr =
      let Node (label, children) = expr.node in
      match label with
      | Exists (_, _) | Forall (_, _) ->
        decapture_children label (depth + 1) children
      | Var (v, typ) -> hashcons ctx (Node (Var (v + depth, typ), []))
      | _ -> decapture_children label depth children      
    and decapture_children label depth children =
      hashcons ctx (Node (label, List.map (decapture depth) children))
    in
    let rec go depth expr =
      let Node (label, children) = expr.node in
      match label with
      | Exists (_, _) | Forall (_, _) ->
        go_children label (depth + 1) children
      | Var (v, _) ->
        if v < depth then (* bound var *)
          expr
        else
          decapture depth (subst (v - depth))
      | _ -> go_children label depth children
    and go_children label depth children =
        hashcons ctx (Node (label, List.map (go depth) children))
    in
    go 0 expr

  let constants expr =
    let alg label children =
      let z =
        match label with
        | Const k -> ConstSymbol.Set.singleton k
        | _ -> ConstSymbol.Set.empty
      in
      BatList.fold_left ConstSymbol.Set.union z children
    in
    eval_expr alg expr

  let vars expr =
    let rec go depth expr =
      let Node (label, children) = expr.node in
      match label with
      | Exists (_, _) | Forall (_, _) ->
        go_children (depth + 1) children
      | Var (v, typ) ->
        if v < depth then Var.Set.empty
        else Var.Set.singleton (v - depth, typ)
      | _ -> go_children depth children
    and go_children depth children =
      List.fold_left Var.Set.union Var.Set.empty (List.map (go depth) children)
    in
    go 0 expr
end

module Term = struct
  include Expr

  type 'a open_t = [
    | `Real of QQ.t
    | `Const of const_symbol
    | `Var of int * typ
    | `Binop of [`Add | `Mul | `Div | `Mod ] * 'a * 'a
    | `Unop of [`Floor | `Neg ] * 'a
  ]

  let destruct t = match t.node with
    | Node (Real qq, []) -> `Real qq
    | Node (Const k, []) -> `Const k
    | Node (Var (v, typ), []) -> `Var (v, typ)
    | Node (Add, [s; t]) -> `Binop (`Add, s, t)
    | Node (Mul, [s; t]) -> `Binop (`Mul, s, t)
    | Node (Div, [s; t]) -> `Binop (`Div, s, t)
    | Node (Mod, [s; t]) -> `Binop (`Mod, s, t)
    | Node (Floor, [t]) -> `Unop (`Floor, t)
    | Node (Neg, [t]) -> `Unop (`Neg, t)
    | _ -> invalid_arg "destruct: not a term"

  let destruct_flat t = match t.node with
    | Node (Real qq, []) -> `Real qq
    | Node (Const k, []) -> `Const k
    | Node (Var (v, typ), []) -> `Var (v, typ)
    | Node (Add, [s; t]) -> `Add ((flatten_expr Add s)@(flatten_expr Add t))
    | Node (Mul, [s; t]) -> `Mul ((flatten_expr Mul s)@(flatten_expr Mul t))
    | Node (Div, [s; t]) -> `Binop (`Div, s, t)
    | Node (Mod, [s; t]) -> `Binop (`Mod, s, t)
    | Node (Floor, [t]) -> `Unop (`Floor, t)
    | Node (Neg, [t]) -> `Unop (`Neg, t)
    | _ -> invalid_arg "destruct: not a term"

  let eval alg t =
    let f label children = match label, children with
      | Real qq, [] -> alg (`Real qq)
      | Const k, [] -> alg (`Const k)
      | Var (v, typ), [] -> alg (`Var (v, typ))
      | Add, [s; t] -> alg (`Binop (`Add, s, t))
      | Mul, [s; t] -> alg (`Binop (`Mul, s, t))
      | Div, [s; t] -> alg (`Binop (`Div, s, t))
      | Mod, [s; t] -> alg (`Binop (`Mod, s, t))
      | Floor, [t] -> alg (`Unop (`Floor, t))
      | Neg, [t] -> alg (`Unop (`Neg, t))
      | _ -> invalid_arg "eval: not a term"
    in
    eval_expr f t

  let rec format ?env:(env=Env.empty) ctx formatter t =
    let open Format in
    match destruct_flat t with
    | `Real qq -> QQ.format formatter qq
    | `Const k -> const_format ctx formatter k
    | `Var (v, typ) ->
      (try fprintf formatter "[%s:%d]" (Env.find env v) v
       with Not_found -> fprintf formatter "[free:%d]" v)
    | `Add terms ->
      fprintf formatter "(@[";
      ApakEnum.pp_print_enum
        ~pp_sep:(fun formatter () -> fprintf formatter "@ + ")
        (format ctx ~env:env)
        formatter
        (BatList.enum terms);
      fprintf formatter "@])"
    | `Mul terms ->
      fprintf formatter "(@[";
      ApakEnum.pp_print_enum
        ~pp_sep:(fun formatter () -> fprintf formatter "@ * ")
        (format ctx ~env:env)
        formatter
        (BatList.enum terms);
      fprintf formatter "@])"
    | `Binop (`Div, s, t) ->
      fprintf formatter "(@[%a@ / %a@])"
        (format ctx ~env:env) s
        (format ctx ~env:env) t
    | `Binop (`Mod, s, t) ->
      fprintf formatter "(@[%a@ mod %a@])"
        (format ctx ~env:env) s
        (format ctx ~env:env) t
    | `Unop (`Floor, t) ->
      fprintf formatter "floor(@[%a@])" (format ctx ~env:env) t
    | `Unop (`Neg, t) ->
      begin match destruct t with
        | `Real qq -> QQ.format formatter (QQ.negate qq)
        | `Const _ | `Var (_, _) ->
          fprintf formatter "-%a" (format ctx ~env:env) t          
        | _ -> fprintf formatter "-(@[%a@])" (format ctx ~env:env) t
      end

  let show ctx ?env:(env=Env.empty) t =
    Apak.Putil.pp_string (format ctx ~env:env) t

  let mk_const ctx k = hashcons ctx (Node (Const k, []))
  let mk_var ctx v typ = hashcons ctx (Node (Var (v, typ), []))
  let mk_add ctx s t = hashcons ctx (Node (Add, [s; t]))
  let mk_neg ctx t = hashcons ctx (Node (Neg, [t]))
  let mk_sub ctx s t = mk_add ctx s (mk_neg ctx t)
  let mk_mul ctx s t = hashcons ctx (Node (Mul, [s; t]))
  let mk_div ctx s t = hashcons ctx (Node (Div, [s; t]))
  let mk_mod ctx s t = hashcons ctx (Node (Mod, [s; t]))
  let mk_floor ctx t = hashcons ctx (Node (Floor, [t]))
  let mk_zero ctx = hashcons ctx (Node (Real QQ.zero, []))
  let mk_one ctx = hashcons ctx (Node (Real QQ.one, []))
  let mk_real ctx qq = hashcons ctx (Node (Real qq, []))
  let mk_idiv ctx s t = mk_floor ctx (mk_div ctx s t)

  let mk_sum ctx terms =
    if BatEnum.is_empty terms then
      mk_zero ctx
    else
      BatEnum.reduce (mk_add ctx) terms

  let mk_product ctx terms =
    if BatEnum.is_empty terms then
      mk_one ctx
    else
      BatEnum.reduce (mk_mul ctx) terms
end

module Formula = struct
  include Expr

  type 'a open_t = [
    | `Tru
    | `Fls
    | `Binop of [`And | `Or] * 'a * 'a
    | `Not of 'a
    | `Quantify of [`Exists | `Forall] * string * typ * 'a
    | `Atom of [`Eq | `Leq | `Lt] * term * term
  ]

  let destruct phi = match phi.node with
    | Node (True, []) -> `Tru
    | Node (False, []) -> `Fls
    | Node (And, [phi; psi]) -> `Binop (`And, phi, psi)
    | Node (Or, [phi; psi]) -> `Binop (`Or, phi, psi)
    | Node (Not, [phi]) -> `Not phi
    | Node (Exists (name, typ), [phi]) -> `Quantify (`Exists, name, typ, phi)
    | Node (Forall (name, typ), [phi]) -> `Quantify (`Forall, name, typ, phi)
    | Node (Eq, [s; t]) -> `Atom (`Eq, s, t)
    | Node (Leq, [s; t]) -> `Atom (`Leq, s, t)
    | Node (Lt, [s; t]) -> `Atom (`Lt, s, t)
    | _ -> invalid_arg "destruct: not a formula"

  let rec eval alg phi = match destruct phi with
    | `Tru -> alg `Tru
    | `Fls -> alg `Fls
    | `Binop (op, phi, psi) -> alg (`Binop (op, eval alg phi, eval alg psi))
    | `Or (phi, psi) -> alg (`Binop (`Or, eval alg phi, eval alg psi))
    | `Quantify (qt, name, typ, phi) ->
      alg (`Quantify (qt, name, typ, eval alg phi))
    | `Not phi -> alg (`Not (eval alg phi))
    | `Atom (op, s, t) -> alg (`Atom (op, s, t))

  let rec flatten_universal phi = match phi.node with
    | Node (Forall (name, typ), [phi]) ->
      let (varinfo, phi') = flatten_universal phi in
      ((name,typ)::varinfo, phi')
    | _ -> ([], phi)

  let rec flatten_existential phi = match phi.node with
    | Node (Exists (name, typ), [phi]) ->
      let (varinfo, phi') = flatten_existential phi in
      ((name,typ)::varinfo, phi')
    | _ -> ([], phi)

  let destruct_flat phi = match phi.node with
    | Node (True, []) -> `Tru
    | Node (False, []) -> `Fls
    | Node (And, [phi; psi]) ->
      `And ((flatten_expr And phi)@(flatten_expr And psi))
    | Node (Or, [phi; psi]) ->
      `Or ((flatten_expr Or phi)@(flatten_expr Or psi))
    | Node (Not, [phi]) -> `Not phi
    | Node (Exists (name, typ), [phi]) ->
      let varinfo, phi' = flatten_existential phi in
      `Quantify (`Exists, (name,typ)::varinfo, phi')
    | Node (Forall (name, typ), [phi]) ->
      let varinfo, phi' = flatten_universal phi in
      `Quantify (`Forall, (name, typ)::varinfo, phi')
    | Node (Eq, [s; t]) -> `Atom (`Eq, s, t)
    | Node (Leq, [s; t]) -> `Atom (`Leq, s, t)
    | Node (Lt, [s; t]) -> `Atom (`Lt, s, t)
    | _ -> invalid_arg "destruct: not a formula"

  let rec format ?env:(env=Env.empty) ctx formatter phi =
    let open Format in
    match destruct_flat phi with
    | `Tru -> pp_print_string formatter "true"
    | `Fls -> pp_print_string formatter "false"
    | `Not phi ->
      fprintf formatter "!(@[%a@])" (format ctx ~env:env) phi
    | `And conjuncts ->
      fprintf formatter "(@[";
      ApakEnum.pp_print_enum
        ~pp_sep:(fun formatter () -> fprintf formatter "@ /\\ ")
        (format ctx ~env:env)
        formatter
        (BatList.enum conjuncts);
      fprintf formatter "@])"
    | `Or conjuncts ->
      fprintf formatter "(@[";
      ApakEnum.pp_print_enum
        ~pp_sep:(fun formatter () -> fprintf formatter "@ \\/ ")
        (format ctx ~env:env)
        formatter
        (BatList.enum conjuncts);
      fprintf formatter "@])"
    | `Atom (op, x, y) ->
      let op_string = match op with
        | `Eq -> "="
        | `Leq -> "<="
        | `Lt -> "<"
      in
      fprintf formatter "@[%a %s %a@]"
        (Term.format ctx ~env:env) x
        op_string
        (Term.format ctx ~env:env) y        
    | `Quantify (qt, varinfo, psi) ->
      let env =
        List.fold_right
          (fun (name, typ) env -> Env.push name env)
          varinfo
          env
      in
      let quantifier_name =
        match qt with
        | `Exists -> "exists"
        | `Forall -> "forall"
      in
      fprintf formatter "(@[%s@ " quantifier_name;
      ApakEnum.pp_print_enum
        ~pp_sep:pp_print_space
        (fun formatter (name, typ) ->
           fprintf formatter "(%s : %s)" name (Show.show<typ> typ))
        formatter
        (BatList.enum varinfo);
      fprintf formatter ".@ %a@])" (format ~env:env ctx) psi

  let show ctx ?env:(env=Env.empty) t =
    Apak.Putil.pp_string (format ctx ~env:env) t

  let mk_and ctx phi psi = hashcons ctx (Node (And, [phi; psi]))
  let mk_or ctx phi psi = hashcons ctx (Node (Or, [phi; psi]))
  let mk_not ctx phi = hashcons ctx (Node (Not, [phi]))
  let mk_true ctx = hashcons ctx (Node (True, []))
  let mk_false ctx = hashcons ctx (Node (False, []))
  let mk_leq ctx s t = hashcons ctx (Node (Leq, [s; t]))
  let mk_lt ctx s t = hashcons ctx (Node (Lt, [s; t]))
  let mk_eq ctx s t = hashcons ctx (Node (Eq, [s; t]))
  let mk_forall ctx ?name:(name="_") typ phi =
    hashcons ctx (Node (Forall (name, typ), [phi]))
  let mk_exists ctx ?name:(name="_") typ phi =
    hashcons ctx (Node (Exists (name, typ), [phi]))

  let mk_conjunction ctx conjuncts =
    if BatEnum.is_empty conjuncts then
      mk_true ctx
    else
      BatEnum.reduce (mk_and ctx) conjuncts

  let mk_disjunction ctx disjuncts =
    if BatEnum.is_empty disjuncts then
      mk_false ctx
    else
      BatEnum.reduce (mk_or ctx) disjuncts

  let existential_closure ctx phi =
    let vars = vars phi in
    let types = Array.make (Var.Set.cardinal vars) TyInt in
    let rename =
      let n = ref (-1) in
      let map =
        Var.Set.fold (fun (v, typ) m ->
            incr n;
            types.(!n) <- typ;
            Apak.Putil.PInt.Map.add v (Term.mk_var ctx (!n) typ) m
          )
          vars
          Apak.Putil.PInt.Map.empty
      in
      fun v -> Apak.Putil.PInt.Map.find v map
    in
    Array.fold_left
      (fun psi typ -> mk_exists ctx typ psi)
      (substitute ctx rename phi)
      types
end

module ImplicitContext(C : sig
    type t
    val context : t context
  end) =
struct
  let ( ! ) = Formula.mk_not C.context
  let ( && ) = Formula.mk_and C.context
  let ( || ) = Formula.mk_or C.context
  let ( < ) = Formula.mk_lt C.context
  let ( <= ) = Formula.mk_leq C.context
  let ( = ) = Formula.mk_eq C.context
  let tru = Formula.mk_true C.context
  let fls = Formula.mk_false C.context
      
  let ( + ) = Term.mk_add C.context
  let ( - ) = Term.mk_sub C.context
  let ( * ) = Term.mk_mul C.context
  let ( / ) = Term.mk_div C.context
  let ( mod ) = Term.mk_mod C.context

  let const = Term.mk_const C.context
  let forall = Formula.mk_forall C.context
  let exists = Formula.mk_exists C.context
  let var = Term.mk_var C.context
end

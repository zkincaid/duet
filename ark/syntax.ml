open Hashcons

type const_symbol = int

type typ = TyInt | TyReal
let string_of_typ = function
  | TyInt -> "int"
  | TyReal -> "real"

type label =
  | True
  | False
  | And
  | Or
  | Not
  | Exists of string option * typ
  | Forall of string option * typ
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

module Expr = struct
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
end

module HC = Hashcons.Make(Expr)

module type Constant = sig
  type t
  val format : Format.formatter -> t -> unit
  val typ : t -> typ
  val hash : t -> int
  val equal : t -> t -> bool
end

module Env = struct
  type 'a t = 'a list
  let push x xs = x::xs
  let find = List.nth
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

let rec eval_expr alg (Node (label, children)) =
  alg label (List.map (fun child -> eval_expr alg child.node) children)

let rec flatten_expr label expr =
  let Node (label', children) = expr.node in
  if label = label' then
    List.concat (List.map (flatten_expr label) children)
  else
    [expr]

module Term = struct
  type t = term

  type 'a open_t = [
    | `Real of QQ.t
    | `Const of const_symbol
    | `Var of int * typ
    | `Binop of [`Add | `Mul | `Div | `Mod ] * 'a * 'a
    | `Unop of [`Floor | `Neg ] * 'a
  ]

  let equal s t = s.tag = t.tag
  let compare s t = Pervasives.compare s.tag t.tag
  let hash t = t.hkey

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
    eval_expr f t.node

  let rec format ctx ?env:(env=Env.empty) formatter t =
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
  type t = formula

  type 'a open_t = [
    | `Tru
    | `Fls
    | `And of 'a * 'a
    | `Or of 'a * 'a
    | `Not of 'a
    | `Exists of (string option) * typ * 'a
    | `Forall of (string option) * typ * 'a
    | `Atom of [`Eq | `Leq | `Lt] * term * term
  ]

  let equal s t = s.tag = t.tag
  let compare s t = Pervasives.compare s.tag t.tag
  let hash t = t.hkey

  let destruct phi = match phi.node with
    | Node (True, []) -> `Tru
    | Node (False, []) -> `Fls
    | Node (And, [phi; psi]) -> `And (phi, psi)
    | Node (Or, [phi; psi]) -> `Or (phi, psi)
    | Node (Not, [phi]) -> `Not phi
    | Node (Exists (hint, typ), [phi]) -> `Exists (hint, typ, phi)
    | Node (Forall (hint, typ), [phi]) -> `Forall (hint, typ, phi)
    | Node (Eq, [s; t]) -> `Atom (`Eq, s, t)
    | Node (Leq, [s; t]) -> `Atom (`Leq, s, t)
    | Node (Lt, [s; t]) -> `Atom (`Lt, s, t)
    | _ -> invalid_arg "destruct: not a formula"

  let rec eval alg phi = match destruct phi with
    | `Tru -> alg `Tru
    | `Fls -> alg `Fls
    | `And (phi, psi) -> alg (`And (eval alg phi, eval alg psi))
    | `Or (phi, psi) -> alg (`Or (eval alg phi, eval alg psi))
    | `Exists (hint, typ, phi) -> alg (`Exists (hint, typ, eval alg phi))
    | `Forall (hint, typ, phi) -> alg (`Forall (hint, typ, eval alg phi))
    | `Not phi -> alg (`Not (eval alg phi))
    | `Atom (op, s, t) -> alg (`Atom (op, s, t))

  let rec flatten_universal phi = match phi.node with
    | Node (Forall (hint, typ), [phi]) ->
      let (varinfo, phi') = flatten_universal phi in
      ((hint,typ)::varinfo, phi')
    | _ -> ([], phi)

  let rec flatten_existential phi = match phi.node with
    | Node (Exists (hint, typ), [phi]) ->
      let (varinfo, phi') = flatten_existential phi in
      ((hint,typ)::varinfo, phi')
    | _ -> ([], phi)

  let destruct_flat phi = match phi.node with
    | Node (True, []) -> `Tru
    | Node (False, []) -> `Fls
    | Node (And, [phi; psi]) ->
      `And ((flatten_expr And phi)@(flatten_expr And psi))
    | Node (Or, [phi; psi]) ->
      `Or ((flatten_expr Or phi)@(flatten_expr Or psi))
    | Node (Not, [phi]) -> `Not phi
    | Node (Exists (hint, typ), [phi]) ->
      let varinfo, phi' = flatten_existential phi in
      `Exists ((hint,typ)::varinfo, phi')
    | Node (Forall (hint, typ), [phi]) ->
      let varinfo, phi' = flatten_universal phi in
      `Forall ((hint, typ)::varinfo, phi')
    | Node (Eq, [s; t]) -> `Atom (`Eq, s, t)
    | Node (Leq, [s; t]) -> `Atom (`Leq, s, t)
    | Node (Lt, [s; t]) -> `Atom (`Lt, s, t)
    | _ -> invalid_arg "destruct: not a formula"

  let rec format ctx ?env:(env=Env.empty) formatter phi =
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
    | `Exists (varinfo, psi) | `Forall (varinfo, psi) ->
      let hint_string = function
        | Some k -> k
        | None   -> "_"
      in
      let env =
        List.fold_right
          (fun (name, typ) env -> Env.push (hint_string name) env)
          varinfo
          env
      in
      let quantifier_name =
        match destruct phi with
        | `Exists (_, _, _) -> "exists"
        | _ -> "forall"
      in
      fprintf formatter "(@[%s@ " quantifier_name;
      ApakEnum.pp_print_enum
        ~pp_sep:pp_print_space
        (fun formatter (name, typ) ->
           fprintf formatter "(%s : %s)" (hint_string name) (string_of_typ typ))
        formatter
        (BatList.enum varinfo);
      fprintf formatter ".@ %a@])" (format ctx ~env:env) psi

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
  let mk_forall ctx ?hint:(hint=None) typ phi =
    hashcons ctx (Node (Forall (hint, typ), [phi]))
  let mk_exists ctx ?hint:(hint=None) typ phi =
    hashcons ctx (Node (Exists (hint, typ), [phi]))

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

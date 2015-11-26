open BatPervasives
open BatHashcons

type typ = [
  | `TyInt
  | `TyReal
  | `TyBool
  | `TyFun of (typ list) * typ
] [@@ deriving ord]

type typ_arith = [ `TyInt | `TyReal ] [@@ deriving ord]
type typ_bool = [ `TyBool ]
type typ_fo = [ `TyInt | `TyReal | `TyBool ] [@@ deriving ord]
type 'a typ_fun = [ `TyFun of (typ list) * 'a ]

type const_sym = int

let rec pp_typ formatter = function
  | `TyReal -> Format.pp_print_string formatter "real"
  | `TyInt -> Format.pp_print_string formatter "int"
  | `TyBool -> Format.pp_print_string formatter "bool"
  | `TyFun (dom, cod) ->
    let pp_sep formatter () = Format.fprintf formatter "@ * " in
    Format.fprintf formatter "(@[%a@ -> %a@])"
      (ApakEnum.pp_print_enum ~pp_sep pp_typ) (BatList.enum dom)
      pp_typ cod

let pp_typ_arith = pp_typ
let pp_typ_fo = pp_typ

type label =
  | True
  | False
  | And
  | Or
  | Not
  | Exists of string * typ_fo
  | Forall of string * typ_fo
  | Eq
  | Leq
  | Lt
  | Const of const_sym
  | Var of int * typ_fo
  | Add
  | Mul
  | Div
  | Mod
  | Floor
  | Neg
  | Real of QQ.t

type sexpr = Node of label * ((sexpr hobj) list)
type ('a,'typ) expr = sexpr hobj
type 'a term = ('a, typ_arith) expr
type 'a formula = ('a, typ_bool) expr

module HC = BatHashcons.MakeTable(struct
    type t = sexpr
    let equal (Node (label, args)) (Node (label', args')) =
      (match label, label' with
       | Exists (_, typ), Exists (_, typ') -> typ = typ'
       | Forall (_, typ), Forall (_, typ') -> typ = typ'
       | _, _ -> label = label')
      && List.length args == List.length args'
      && List.for_all2 (fun x y -> x.tag = y.tag) args args'
    let compare = Pervasives.compare
    let hash (Node (label, args)) =
      Hashtbl.hash (label, List.map (fun sexpr -> sexpr.tag) args)
  end)

module DynArray = BatDynArray

module ConstSymbol = Apak.Putil.PInt

module Var = struct
  module I = struct
    type t = int * typ_fo [@@deriving show,ord]
  end
  include I
  module Set = Apak.Putil.Set.Make(I)
  module Map = Apak.Putil.Map.Make(I)
end

module Env = struct
  type 'a t = 'a list
  let push x xs = x::xs
  let find xs i =
    try List.nth xs i
    with Failure _ -> raise Not_found
  let empty = []
end

let rec eval_sexpr alg sexpr =
  let (Node (label, children)) = sexpr.obj in
  alg label (List.map (eval_sexpr alg) children)

let rec flatten_sexpr label sexpr =
  let Node (label', children) = sexpr.obj in
  if label = label' then
    List.concat (List.map (flatten_sexpr label) children)
  else
    [sexpr]

type 'a open_term = [
  | `Real of QQ.t
  | `Const of int
  | `Var of int * typ_arith
  | `Add of 'a list
  | `Mul of 'a list
  | `Binop of [ `Div | `Mod ] * 'a * 'a
  | `Unop of [ `Floor | `Neg ] * 'a
]

type ('a,'b) open_formula = [
  | `Tru
  | `Fls
  | `And of 'a list
  | `Or of 'a list
  | `Not of 'a
  | `Quantify of [`Exists | `Forall] * string * typ_fo * 'a
  | `Atom of [`Eq | `Leq | `Lt] * 'b * 'b
  | `Proposition of [ `Const of int | `Var of int ]
]

type 'a context =
  { hashcons : HC.t;
    symbols : (string * typ) DynArray.t }

let mk ctx label children =
  HC.hashcons ctx.hashcons (Node (label, children))
                              
let mk_symbol ctx ?(name="K") typ =
  DynArray.add ctx.symbols (name, typ);
  DynArray.length ctx.symbols - 1

let typ_symbol ctx = snd % DynArray.get ctx.symbols
let show_symbol ctx = fst % DynArray.get ctx.symbols
let pp_symbol ctx formatter sym =
  Format.pp_print_string formatter (show_symbol ctx sym)

let mk_real ctx qq = mk ctx (Real qq) []
let mk_zero ctx = mk_real ctx QQ.zero
let mk_one ctx = mk_real ctx QQ.one

let mk_const ctx k = mk ctx (Const k) []
let mk_var ctx v typ = mk ctx (Var (v, typ)) []

let mk_neg ctx t = mk ctx Neg [t]
let mk_div ctx s t = mk ctx Div [s; t]
let mk_mod ctx s t = mk ctx Mod [s; t]
let mk_floor ctx t = mk ctx Floor [t]
let mk_idiv ctx s t = mk_floor ctx (mk_div ctx s t)

let mk_add ctx = function
  | [] -> mk_zero ctx
  | [x] -> x
  | sum -> mk ctx Add sum

let mk_mul ctx = function
  | [] -> mk_one ctx
  | [x] -> x
  | product -> mk ctx Mul product

let mk_sub ctx s t = mk_add ctx [s; mk_neg ctx t]

let mk_true ctx = mk ctx True []
let mk_false ctx = mk ctx False []
let mk_leq ctx s t = mk ctx Leq [s; t]
let mk_lt ctx s t = mk ctx Lt [s; t]
let mk_eq ctx s t = mk ctx Eq [s; t]

let is_true phi = match phi.obj with
  | Node (True, []) -> true
  | _ -> false

let is_false phi = match phi.obj with
  | Node (False, []) -> true
  | _ -> false

let mk_not ctx phi =
  match phi.obj with
  | Node (True, []) -> mk_false ctx
  | Node (False, []) -> mk_true ctx
  | _ -> mk ctx Not [phi]

let mk_and ctx conjuncts =
  if List.exists is_false conjuncts then
    mk_false ctx
  else
    match List.filter (not % is_true) conjuncts with
    | [] -> mk_true ctx
    | [x] -> x
    | conjuncts -> mk ctx And conjuncts

let mk_or ctx disjuncts =
  if List.exists is_true disjuncts then
    mk_true ctx
  else
    match List.filter (not % is_false) disjuncts with
    | [] -> mk_false ctx
    | [x] -> x
    | disjuncts -> mk ctx Or disjuncts

let mk_forall ctx ?name:(name="_") typ phi = mk ctx (Forall (name, typ)) [phi]
let mk_exists ctx ?name:(name="_") typ phi = mk ctx (Exists (name, typ)) [phi]

(* Avoid capture by incrementing bound variables *)
let rec decapture ctx depth incr sexpr =
  let Node (label, children) = sexpr.obj in
  match label with
  | Exists (_, _) | Forall (_, _) ->
    decapture_children ctx label (depth + 1) incr children
  | Var (v, typ) ->
    if v < depth then
      (* v is bound *)
      sexpr
    else
      mk ctx (Var (v + incr, typ)) []
  | _ -> decapture_children ctx label depth incr children
and decapture_children ctx label depth incr children =
  mk ctx label (List.map (decapture ctx depth incr) children)

let substitute ctx subst sexpr =
  let rec go depth sexpr =
    let Node (label, children) = sexpr.obj in
    match label with
    | Exists (_, _) | Forall (_, _) ->
      go_children label (depth + 1) children
    | Var (v, _) ->
      if v < depth then (* bound var *)
        sexpr
      else
        decapture ctx 0 depth (subst (v - depth))
    | _ -> go_children label depth children
  and go_children label depth children =
    mk ctx label (List.map (go depth) children)
  in
  go 0 sexpr

let substitute_const ctx subst sexpr =
  let rec go depth sexpr =
    let Node (label, children) = sexpr.obj in
    match label with
    | Exists (_, _) | Forall (_, _) ->
      go_children label (depth + 1) children
    | Const k -> decapture ctx 0 depth (subst k)
    | _ -> go_children label depth children
  and go_children label depth children =
    mk ctx label (List.map (go depth) children)
  in
  go 0 sexpr

let fold_constants f sexpr acc =
  let rec go acc sexpr =
    let Node (label, children) = sexpr.obj in
    match label with
    | Const k -> f k acc
    | _ -> List.fold_left go acc children
  in
  go acc sexpr

let vars sexpr =
  let rec go depth sexpr =
    let Node (label, children) = sexpr.obj in
    match label with
    | Exists (_, _) | Forall (_, _) ->
      go_children (depth + 1) children
    | Var (v, typ) ->
      if v < depth then Var.Set.empty
      else Var.Set.singleton (v - depth, typ)
    | _ -> go_children depth children
  and go_children depth children =
    List.fold_left
      Var.Set.union
      Var.Set.empty
      (List.map (go depth) children)
  in
  go 0 sexpr

module Expr = struct
  let equal s t = s.tag = t.tag
  let compare s t = Pervasives.compare s.tag t.tag
  let hash t = t.hcode
end

module Term = struct
  include Expr
  type 'a t = 'a term

  let eval ctx alg t =
    let f label children = match label, children with
      | Real qq, [] -> alg (`Real qq)
      | Const k, [] ->
        begin match typ_symbol ctx k with
          | `TyInt | `TyReal -> alg (`Const k)
          | `TyBool | `TyFun _ -> invalid_arg "eval: not a term"
        end
      | Var (v, typ), [] ->
        begin match typ with
          | `TyInt -> alg (`Var (v, `TyInt))
          | `TyReal -> alg (`Var (v, `TyReal))
          | `TyBool -> invalid_arg "eval: not a term"
        end
      | Add, sum -> alg (`Add sum)
      | Mul, product -> alg (`Mul product)
      | Div, [s; t] -> alg (`Binop (`Div, s, t))
      | Mod, [s; t] -> alg (`Binop (`Mod, s, t))
      | Floor, [t] -> alg (`Unop (`Floor, t))
      | Neg, [t] -> alg (`Unop (`Neg, t))
      | _ -> invalid_arg "eval: not a term"
    in
    eval_sexpr f t

  let destruct ctx t = match t.obj with
    | Node (Real qq, []) -> `Real qq
    | Node (Const k, []) ->
      begin match typ_symbol ctx k with
        | `TyInt | `TyReal -> `Const k
        | `TyBool | `TyFun _ -> invalid_arg "destruct: not a term"
      end
    | Node (Var (v, typ), []) ->
      begin match typ with
        | `TyInt -> `Var (v, `TyInt)
        | `TyReal -> `Var (v, `TyReal)
        | `TyBool -> invalid_arg "destruct: not a term"
      end
    | Node (Add, sum) -> `Add sum
    | Node (Mul, product) -> `Mul product
    | Node (Div, [s; t]) -> `Binop (`Div, s, t)
    | Node (Mod, [s; t]) -> `Binop (`Mod, s, t)
    | Node (Floor, [t]) -> `Unop (`Floor, t)
    | Node (Neg, [t]) -> `Unop (`Neg, t)
    | _ -> invalid_arg "destruct: not a term"

  let rec pp ?(env=Env.empty) ctx formatter t =
    let open Format in
    match destruct ctx t with
    | `Real qq -> QQ.pp formatter qq
    | `Const k -> pp_symbol ctx formatter k
    | `Var (v, typ) ->
      (try fprintf formatter "[%s:%d]" (Env.find env v) v
       with Not_found -> fprintf formatter "[free:%d]" v)
    | `Add terms ->
      fprintf formatter "(@[";
      ApakEnum.pp_print_enum
        ~pp_sep:(fun formatter () -> fprintf formatter "@ + ")
        (pp ~env ctx)
        formatter
        (BatList.enum terms);
      fprintf formatter "@])"
    | `Mul terms ->
      fprintf formatter "(@[";
      ApakEnum.pp_print_enum
        ~pp_sep:(fun formatter () -> fprintf formatter "@ * ")
        (pp ~env ctx)
        formatter
        (BatList.enum terms);
      fprintf formatter "@])"
    | `Binop (`Div, s, t) ->
      fprintf formatter "(@[%a@ / %a@])"
        (pp ~env ctx) s
        (pp ~env ctx) t
    | `Binop (`Mod, s, t) ->
      fprintf formatter "(@[%a@ mod %a@])"
        (pp ~env ctx) s
        (pp ~env ctx) t
    | `Unop (`Floor, t) ->
      fprintf formatter "floor(@[%a@])" (pp ~env ctx) t
    | `Unop (`Neg, t) ->
      begin match destruct ctx t with
        | `Real qq -> QQ.pp formatter (QQ.negate qq)
        | `Const _ | `Var (_, _) ->
          fprintf formatter "-%a" (pp ~env ctx) t
        | _ -> fprintf formatter "-(@[%a@])" (pp ~env ctx) t
      end
  let show ?(env=Env.empty) ctx t = Apak.Putil.mk_show (pp ~env ctx) t
end

module Formula = struct
  include Expr
  type 'a t = 'a formula

  let destruct ctx phi = match phi.obj with
    | Node (True, []) -> `Tru
    | Node (False, []) -> `Fls
    | Node (And, conjuncts) -> `And conjuncts
    | Node (Or, disjuncts) -> `Or disjuncts
    | Node (Not, [phi]) -> `Not phi
    | Node (Exists (name, typ), [phi]) -> `Quantify (`Exists, name, typ, phi)
    | Node (Forall (name, typ), [phi]) -> `Quantify (`Forall, name, typ, phi)
    | Node (Eq, [s; t]) -> `Atom (`Eq, s, t)
    | Node (Leq, [s; t]) -> `Atom (`Leq, s, t)
    | Node (Lt, [s; t]) -> `Atom (`Lt, s, t)
    | Node (Const k, []) ->
      begin match typ_symbol ctx k with
        | `TyBool -> `Proposition (`Const k)
        | `TyInt | `TyReal | `TyFun _ -> invalid_arg "destruct: not a formula"
      end
    | Node (Var (v, `TyBool), []) -> `Proposition (`Var v)
    | _ -> invalid_arg "destruct: not a formula"

  let rec eval ctx alg phi =
    match destruct ctx phi with
      | `Tru -> alg `Tru
      | `Fls -> alg `Fls
      | `Or disjuncts -> alg (`Or (List.map (eval ctx alg) disjuncts))
      | `And conjuncts -> alg (`And (List.map (eval ctx alg) conjuncts))
      | `Quantify (qt, name, typ, phi) ->
        alg (`Quantify (qt, name, typ, eval ctx alg phi))
      | `Not phi -> alg (`Not (eval ctx alg phi))
      | `Atom (op, s, t) -> alg (`Atom (op, s, t))
      | `Proposition p -> alg (`Proposition p)

  let rec flatten_universal phi = match phi.obj with
    | Node (Forall (name, typ), [phi]) ->
      let (varinfo, phi') = flatten_universal phi in
      ((name,typ)::varinfo, phi')
    | _ -> ([], phi)

  let rec flatten_existential phi = match phi.obj with
    | Node (Exists (name, typ), [phi]) ->
      let (varinfo, phi') = flatten_existential phi in
      ((name,typ)::varinfo, phi')
    | _ -> ([], phi)

  let destruct_flat ctx phi = match phi.obj with
    | Node (True, []) -> `Tru
    | Node (False, []) -> `Fls
    | Node (And, conjuncts) ->
      `And (List.concat (List.map (flatten_sexpr And) conjuncts))
    | Node (Or, disjuncts) ->
      `Or (List.concat (List.map (flatten_sexpr Or) disjuncts))
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
    | Node (Const k, []) ->
      begin match typ_symbol ctx k with
        | `TyBool -> `Proposition (`Const k)
        | `TyInt | `TyReal | `TyFun _ -> invalid_arg "destruct: not a formula"
      end
    | Node (Var (v, `TyBool), []) -> `Proposition (`Var v)

    | _ -> invalid_arg "Formula.destruct_flat: not a formula"

  let rec pp ?(env=Env.empty) ctx formatter phi =
    let open Format in
    match destruct_flat ctx phi with
    | `Tru -> pp_print_string formatter "true"
    | `Fls -> pp_print_string formatter "false"
    | `Not phi ->
      fprintf formatter "!(@[%a@])" (pp ~env ctx) phi
    | `And conjuncts ->
      fprintf formatter "(@[";
      ApakEnum.pp_print_enum
        ~pp_sep:(fun formatter () -> fprintf formatter "@ /\\ ")
        (pp ~env ctx)
        formatter
        (BatList.enum conjuncts);
      fprintf formatter "@])"
    | `Or conjuncts ->
      fprintf formatter "(@[";
      ApakEnum.pp_print_enum
        ~pp_sep:(fun formatter () -> fprintf formatter "@ \\/ ")
        (pp ~env ctx)
        formatter
        (BatList.enum conjuncts);
      fprintf formatter "@])"
    | `Proposition (`Const k) -> pp_symbol ctx formatter k
    | `Proposition (`Var v) ->
      (try fprintf formatter "[%s:%d]" (Env.find env v) v
       with Not_found -> fprintf formatter "[free:%d]" v)
    | `Atom (op, x, y) ->
      let op_string = match op with
        | `Eq -> "="
        | `Leq -> "<="
        | `Lt -> "<"
      in
      fprintf formatter "@[%a %s %a@]"
        (Term.pp ~env ctx) x
        op_string
        (Term.pp ~env ctx) y
    | `Quantify (qt, varinfo, psi) ->
      let quantifier_name =
        match qt with
        | `Exists -> "exists"
        | `Forall -> "forall"
      in
      let env =
        List.fold_left (fun env (x,_) -> Env.push x env) env varinfo
      in
      fprintf formatter "(@[%s@ " quantifier_name;
      ApakEnum.pp_print_enum
        ~pp_sep:pp_print_space
        (fun formatter (name, typ) ->
           fprintf formatter "(%s : %a)" name pp_typ typ)
        formatter
        (BatList.enum varinfo);
      fprintf formatter ".@ %a@])" (pp ~env ctx) psi

    let show ?(env=Env.empty) ctx t = Apak.Putil.mk_show (pp ~env ctx) t

    let existential_closure ctx phi =
      let vars = vars phi in
      let types = Array.make (Var.Set.cardinal vars) `TyInt in
      let rename =
        let n = ref (-1) in
        let map =
          Var.Set.fold (fun (v, typ) m ->
              incr n;
              types.(!n) <- typ;
              Apak.Putil.PInt.Map.add v (mk_var ctx (!n) typ) m
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

    let skolemize_free ctx phi =
      let skolem =
        Apak.Memo.memo (fun (i, typ) -> mk_const ctx (mk_symbol ctx typ))
      in
      let rec go sexpr =
        let (Node (label, children)) = sexpr.obj in
        match label with
        | Var (i, typ) -> skolem (i, (typ :> typ))
        | _ -> mk ctx label (List.map go children)
      in
      go phi

    let prenex ctx phi =
      let negate_prefix =
        List.map (function
            | `Exists (name, typ) -> `Forall (name, typ)
            | `Forall (name, typ) -> `Exists (name, typ))
      in
      let combine phis =
        let f (qf_pre0, phi0) (qf_pre, phis) =
          let depth = List.length qf_pre in
          let depth0 = List.length qf_pre0 in
          let phis = List.map (decapture ctx depth depth0) phis in
          (qf_pre0@qf_pre, (decapture ctx 0 depth phi0)::phis)
        in
        List.fold_right f phis ([], [])
      in
      let alg = function
        | `Tru -> ([], mk_true ctx)
        | `Fls -> ([], mk_false ctx)
        | `Atom (`Eq, x, y) -> ([], mk_eq ctx x y)
        | `Atom (`Lt, x, y) -> ([], mk_lt ctx x y)
        | `Atom (`Leq, x, y) -> ([], mk_leq ctx x y)
        | `And conjuncts ->
          let (qf_pre, conjuncts) = combine conjuncts in
          (qf_pre, mk_and ctx conjuncts)
        | `Or disjuncts ->
          let (qf_pre, disjuncts) = combine disjuncts in
          (qf_pre, mk_or ctx disjuncts)
        | `Quantify (`Exists, name, typ, (qf_pre, phi)) ->
          (`Exists (name, typ)::qf_pre, phi)
        | `Quantify (`Forall, name, typ, (qf_pre, phi)) ->
          (`Forall (name, typ)::qf_pre, phi)
        | `Not (qf_pre, phi) -> (negate_prefix qf_pre, mk_not ctx phi)
        | `Proposition (`Const p) -> ([], mk_const ctx p)
        | `Proposition (`Var i) -> ([], mk_var ctx i `TyBool)
      in
      let (qf_pre, matrix) = eval ctx alg phi in
      List.fold_right
        (fun qf phi ->
          match qf with
          | `Exists (name, typ) -> mk_exists ctx ~name typ phi
          | `Forall (name, typ) -> mk_forall ctx ~name typ phi)
        qf_pre
        matrix
end

let quantify_const ctx qt sym phi =
  let typ = match typ_symbol ctx sym with
    | `TyInt -> `TyInt
    | `TyReal -> `TyReal
    | `TyBool -> `TyBool
    | `TyFun _ ->
      begin match qt with
        | `Forall ->
          invalid_arg "mk_forall_const: not a first-order constant"
        | `Exists ->
          invalid_arg "mk_exists_const: not a first-order constant"
      end
  in
  let replacement = mk_var ctx 0 typ in
  let subst k =
    if k = sym then replacement
    else mk_const ctx k
  in
  let psi = substitute_const ctx subst (decapture ctx 0 1 phi) in
  match qt with
  | `Forall -> mk_forall ctx ~name:(show_symbol ctx sym) typ psi
  | `Exists -> mk_exists ctx ~name:(show_symbol ctx sym) typ psi

let mk_exists_const ctx = quantify_const ctx `Exists
let mk_forall_const ctx = quantify_const ctx `Forall

let term_typ ctx =
  let join s t =
    match s, t with
    | `TyInt, `TyInt -> `TyInt
    | `TyInt, `TyReal | `TyReal, `TyInt | `TyReal, `TyReal -> `TyReal
    | _, _ -> assert false
  in
  let alg = function
    | `Real qq ->
      begin match QQ.to_zz qq with
        | Some _ -> `TyInt
        | None -> `TyReal
      end
    | `Var (_, typ) -> typ
    | `Const k ->
      begin match typ_symbol ctx k with
        | `TyInt -> `TyInt
        | `TyReal -> `TyReal
        | _ -> invalid_arg "typ: not an arithmetic term"
      end
    | `Add xs | `Mul xs -> List.fold_left join `TyInt xs
    | `Binop (`Div, s, t) -> `TyReal
    | `Binop (`Mod, s, t) -> join s t
    | `Unop (`Floor, _) -> `TyInt
    | `Unop (`Neg, t) -> t
  in
  Term.eval ctx alg

module Infix (C : sig
    type t
    val context : t context
  end) =
struct
  let ( ! ) = mk_not C.context
  let ( && ) x y = mk_and C.context [x; y]
  let ( || ) x y = mk_or C.context [x; y]
  let ( < ) = mk_lt C.context
  let ( <= ) = mk_leq C.context
  let ( = ) = mk_eq C.context
  let tru = mk_true C.context
  let fls = mk_false C.context
      
  let ( + ) x y = mk_add C.context [x; y]
  let ( - ) x y = mk_add C.context [x; mk_neg C.context y]
  let ( * ) x y = mk_mul C.context [x; y]
  let ( / ) = mk_div C.context
  let ( mod ) = mk_mod C.context

  let const = mk_const C.context
  let forall = mk_forall C.context
  let exists = mk_exists C.context
  let var = mk_var C.context
end

module MakeContext () = struct
  type t = unit
  type term = (t, typ_arith) expr
  type formula = (t, typ_bool) expr

  let context =
    { hashcons = HC.create 991;
      symbols = DynArray.make 512 }

  let mk_symbol = mk_symbol context
  let mk_const = mk_const context
  let mk_var = mk_var context
  let mk_add = mk_add context
  let mk_mul = mk_mul context
  let mk_div = mk_div context
  let mk_mod = mk_mod context
  let mk_real = mk_real context
  let mk_floor = mk_floor context
  let mk_neg = mk_neg context
  let mk_sub = mk_sub context
  let mk_forall = mk_forall context
  let mk_exists = mk_exists context
  let mk_forall_const = mk_forall_const context
  let mk_exists_const = mk_exists_const context
  let mk_and = mk_and context
  let mk_or = mk_or context
  let mk_not = mk_not context
  let mk_eq = mk_eq context
  let mk_lt = mk_lt context
  let mk_leq = mk_leq context
  let mk_true = mk_true context
  let mk_false = mk_false context
end

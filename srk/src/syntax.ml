open BatPervasives
open BatHashcons

type typ_fo = [ `TyInt | `TyReal | `TyBool ] [@@ deriving ord]

type typ = [
  | `TyInt
  | `TyReal
  | `TyBool
  | `TyFun of (typ_fo list * typ_fo)
]

type typ_arith = [ `TyInt | `TyReal ]
type typ_bool = [ `TyBool ]
type 'a typ_fun = [ `TyFun of (typ_fo list) * 'a ]

type symbol = int
  [@@deriving ord]

let pp_typ_fo formatter = function
  | `TyReal -> Format.pp_print_string formatter "real"
  | `TyInt -> Format.pp_print_string formatter "int"
  | `TyBool -> Format.pp_print_string formatter "bool"

let pp_typ formatter = function
  | `TyInt -> pp_typ_fo formatter `TyInt
  | `TyReal -> pp_typ_fo formatter `TyReal
  | `TyBool -> pp_typ_fo formatter `TyBool
  | `TyFun (dom, cod) ->
    let pp_sep formatter () = Format.fprintf formatter "@ * " in
    Format.fprintf formatter "(@[%a@ -> %a@])"
      (SrkUtil.pp_print_enum ~pp_sep pp_typ_fo) (BatList.enum dom)
      pp_typ_fo cod

let subtype s t = s = t || (s = `TyInt && t = `TyReal)

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
  | App of symbol
  | Var of int * typ_fo
  | Add
  | Mul
  | Div
  | Mod
  | Floor
  | Neg
  | Real of QQ.t
  | Ite

type sexpr = Node of label * ((sexpr hobj) list) * typ_fo
type ('a,'typ) expr = sexpr hobj
type 'a term = ('a, typ_arith) expr
type 'a formula = ('a, typ_bool) expr

let compare_expr s t = Stdlib.compare s.tag t.tag
let compare_formula = compare_expr
let compare_term = compare_expr

module HC = BatHashcons.MakeTable(struct
    type t = sexpr
    let equal (Node (label, args, typ)) (Node (label', args', typ')) =
      (match label, label' with
       | Exists (_, typ), Exists (_, typ') -> typ = typ'
       | Forall (_, typ), Forall (_, typ') -> typ = typ'
       | _, _ -> label = label')
      && typ == typ'
      && List.length args == List.length args'
      && List.for_all2 (fun x y -> x.tag = y.tag) args args'
    let hash (Node (label, args, _)) =
      Hashtbl.hash (label, List.map (fun sexpr -> sexpr.tag) args)
  end)

module DynArray = BatDynArray

module Symbol = struct
  type t = symbol
  let compare = Stdlib.compare
  module Set = SrkUtil.Int.Set
  module Map = SrkUtil.Int.Map
end

module Var = struct
  module I = struct
    type t = int * typ_fo [@@deriving ord]
  end
  include I
  module Set = BatSet.Make(I)
  module Map = BatMap.Make(I)
end

module Env = struct
  type 'a node =
    | Node of ('a * 'a node * 'a node)
    | Leaf of 'a

  type 'a elt =
    { size : int;
      tree : 'a node }

  type 'a t = 'a elt list

  let push (x : 'a) (env : 'a t) : 'a t = match env with
    | (y::z::env) when y.size = z.size ->
       let head =
         { size = 2 * y.size + 1;
           tree = Node (x, y.tree, z.tree) }
       in
       head::env
    | _ -> { size = 1; tree = Leaf x } :: env

  let rec find_tree tree i size =
    match tree with
    | Leaf x when i = 0 -> x
    | Leaf _ -> assert false
    | Node (x, left, right) ->
       let halfsize = size / 2 in
       if i = 0 then
         x
       else if i <= halfsize then
         find_tree left (i - 1) halfsize
       else
         find_tree right (i - halfsize - 1) halfsize

  let rec find (env : 'a t) (i : int) : 'a =
    match env with
    | [] -> raise Not_found
    | x::_ when i < x.size ->
       find_tree x.tree i x.size
    | x::env -> find env (i - x.size)

  let empty = []

  let rec make_enum rest size =
    let remaining = ref rest in
    let nb_remaining = ref size in
    let next () = match !remaining with
      | [] -> raise BatEnum.No_more_elements
      | Leaf x::xs ->
         remaining := xs;
         decr nb_remaining;
         x
      | Node (x, left, right)::xs ->
         remaining := left::right::xs;
         decr nb_remaining;
         x
    in
    let count () = !nb_remaining in
    let clone () = make_enum (!remaining) (!nb_remaining) in
    BatEnum.make ~next ~count ~clone

  let enum xs =
    BatEnum.concat_map (fun elt -> make_enum [elt.tree] elt.size) (BatList.enum xs)
end

let rec flatten_sexpr label sexpr =
  let Node (label', children, _) = sexpr.obj in
  if label = label' then
    List.concat (List.map (flatten_sexpr label) children)
  else
    [sexpr]

type ('a, 'b) open_term = [
  | `Real of QQ.t
  | `App of symbol * (('b, typ_fo) expr list)
  | `Var of int * typ_arith
  | `Add of 'a list
  | `Mul of 'a list
  | `Binop of [ `Div | `Mod ] * 'a * 'a
  | `Unop of [ `Floor | `Neg ] * 'a
  | `Ite of ('b formula) * 'a * 'a
]

type ('a,'b) open_formula = [
  | `Tru
  | `Fls
  | `And of 'a list
  | `Or of 'a list
  | `Not of 'a
  | `Quantify of [`Exists | `Forall] * string * typ_fo * 'a
  | `Atom of [`Eq | `Leq | `Lt] * 'b term * 'b term
  | `Ite of 'a * 'a * 'a
  | `Proposition of [ `Var of int
                    | `App of symbol * ('b, typ_fo) expr list ]
]

exception Quit

type 'a context =
  { hashcons : HC.t;
    symbols : (string * typ) DynArray.t;
    named_symbols : (string,int) Hashtbl.t;
    mk : label -> (sexpr hobj) list -> sexpr hobj;
    id : int }

let context_stats srk = (HC.count srk.hashcons, DynArray.length srk.symbols, Hashtbl.length srk.named_symbols)

let fresh_id =
  let max_id = ref (-1) in
  fun () ->
    incr max_id;
    !max_id

let size expr =
  let open SrkUtil.Int in
  let counted = ref Set.empty in
  let rec go sexpr =
    let (Node (_, children, _)) = sexpr.obj in
    if Set.mem sexpr.tag (!counted) then
      1
    else begin
      counted := Set.add sexpr.tag (!counted);
      List.fold_left (fun sz child -> sz + (go child)) 1 children
    end
  in
  go expr

let mk_symbol srk ?(name="K") typ =
  DynArray.add srk.symbols (name, typ);
  DynArray.length srk.symbols - 1

let register_named_symbol srk name typ =
  if Hashtbl.mem srk.named_symbols name then
    invalid_arg ("register_named_symbol: The name `"
                 ^ name
                 ^ "' has already been registered")
  else
    Hashtbl.add srk.named_symbols name (mk_symbol srk ~name typ)

let get_named_symbol srk name = Hashtbl.find srk.named_symbols name

let is_registered_name srk name = Hashtbl.mem srk.named_symbols name

let symbol_name srk sym =
  let name = fst (DynArray.get srk.symbols sym) in
  if is_registered_name srk name then Some name
  else None

let typ_symbol srk = snd % DynArray.get srk.symbols
let pp_symbol srk formatter symbol =
  Format.fprintf formatter "%s:%d"
    (fst (DynArray.get srk.symbols symbol))
    symbol

let show_symbol srk symbol = fst (DynArray.get srk.symbols symbol)
let symbol_of_int x = x
let int_of_symbol x = x

let mk_real srk qq = srk.mk (Real qq) []
let mk_zz srk z = mk_real srk (QQ.of_zz z)
let mk_int srk n = mk_real srk (QQ.of_int n)
let mk_zero srk = mk_real srk QQ.zero
let mk_one srk = mk_real srk QQ.one

let mk_const srk k = srk.mk (App k) []
let mk_app srk symbol actuals = srk.mk (App symbol) actuals
let mk_var srk v typ = srk.mk (Var (v, typ)) []

let mk_neg srk t = srk.mk Neg [t]
let mk_div srk s t = srk.mk Div [s; t]
let mk_mod srk s t = srk.mk Mod [s; t]
let mk_floor srk t = srk.mk Floor [t]
let mk_ceiling srk t = mk_neg srk (mk_floor srk (mk_neg srk t))

let mk_add srk = function
  | [] -> mk_zero srk
  | [x] -> x
  | sum -> srk.mk Add sum

let mk_mul srk = function
  | [] -> mk_one srk
  | [x] -> x
  | product -> srk.mk Mul product

let mk_sub srk s t = mk_add srk [s; mk_neg srk t]

let rec mk_pow srk t n =
  if n = 0 then mk_one srk
  else if n = 1 then t
  else if n < 0 then mk_div srk (mk_one srk) (mk_pow srk t (-n))
  else
    let q = mk_pow srk t (n / 2) in
    let q_squared = mk_mul srk [q; q] in
    if n mod 2 = 0 then q_squared
    else mk_mul srk [t; q_squared]

let mk_true srk = srk.mk True []
let mk_false srk = srk.mk False []
let mk_leq srk s t = srk.mk Leq [s; t]
let mk_lt srk s t = srk.mk Lt [s; t]
let mk_eq srk s t = srk.mk Eq [s; t]

let is_true phi = match phi.obj with
  | Node (True, [], _) -> true
  | _ -> false

let is_false phi = match phi.obj with
  | Node (False, [], _) -> true
  | _ -> false

let is_zero phi = match phi.obj with
  | Node (Real k, [], _) -> QQ.equal k QQ.zero
  | _ -> false


let mk_not srk phi = srk.mk Not [phi]
let mk_and srk conjuncts = srk.mk And conjuncts
let mk_or srk disjuncts = srk.mk Or disjuncts
let mk_forall srk ?name:(name="_") typ phi = srk.mk (Forall (name, typ)) [phi]
let mk_exists srk ?name:(name="_") typ phi = srk.mk (Exists (name, typ)) [phi]

let mk_ite srk cond bthen belse = srk.mk Ite [cond; bthen; belse]
let mk_iff srk phi psi =
  mk_or srk [mk_and srk [phi; psi]; mk_and srk [mk_not srk phi; mk_not srk psi]]
let mk_if srk phi psi = mk_or srk [mk_not srk phi; psi]

let mk_truncate srk t =
  mk_ite srk
    (mk_leq srk (mk_zero srk) t)
    (mk_floor srk t)
    (mk_ceiling srk t)

let mk_idiv srk s t =
  let zero = mk_zero srk in
  let div = mk_div srk s t in
  let s_pos = mk_leq srk zero s in
  let t_pos = mk_leq srk zero t in
  mk_ite srk
    (mk_iff srk s_pos t_pos)
    (mk_floor srk div)
    (mk_ceiling srk div)

(* Avoid capture by incrementing bound variables *)
let rec decapture srk depth incr sexpr =
  let Node (label, children, _) = sexpr.obj in
  match label with
  | Exists (_, _) | Forall (_, _) ->
    decapture_children srk label (depth + 1) incr children
  | Var (v, typ) ->
    if v < depth then
      (* v is bound *)
      sexpr
    else
      srk.mk (Var (v + incr, typ)) []
  | _ -> decapture_children srk label depth incr children
and decapture_children srk label depth incr children =
  srk.mk label (List.map (decapture srk depth incr) children)

let substitute srk subst sexpr =
  let rec go depth sexpr =
    let Node (label, children, _) = sexpr.obj in
    match label with
    | Exists (_, _) | Forall (_, _) ->
      go_children label (depth + 1) children
    | Var (v, _) ->
      if v < depth then (* bound var *)
        sexpr
      else
        decapture srk 0 depth (subst (v - depth))
    | _ -> go_children label depth children
  and go_children label depth children =
    srk.mk label (List.map (go depth) children)
  in
  go 0 sexpr

let substitute_const srk subst sexpr =
  let rec go depth sexpr =
    let Node (label, children, _) = sexpr.obj in
    match label with
    | Exists (_, _) | Forall (_, _) ->
      go_children label (depth + 1) children
    | App k when children = [] -> decapture srk 0 depth (subst k)
    | _ -> go_children label depth children
  and go_children label depth children =
    srk.mk label (List.map (go depth) children)
  in
  go 0 sexpr

let substitute_map srk map sexpr =
  let subst sym =
    if Symbol.Map.mem sym map then
      Symbol.Map.find sym map
    else
      mk_const srk sym
  in
  substitute_const srk subst sexpr

let substitute_sym srk subst sexpr =
  let rec go depth sexpr =
    let Node (label, children, _) = sexpr.obj in
    match label with
    | Exists (_, _) | Forall (_, _) ->
      go_children label (depth + 1) children
    | App k ->
      let env =
        List.fold_right
          (fun c env -> Env.push (go depth c) env)
          children
          Env.empty
      in
      substitute srk (Env.find env) (subst k)
      |> decapture srk 0 (depth - (List.length children))
    | _ -> go_children label depth children
  and go_children label depth children =
    srk.mk label (List.map (go depth) children)
  in
  go 0 sexpr


let fold_constants f sexpr acc =
  let rec go acc sexpr =
    let Node (label, children, _) = sexpr.obj in
    match label with
    | App k -> List.fold_left go (f k acc) children
    | _ -> List.fold_left go acc children
  in
  go acc sexpr

let symbols sexpr = fold_constants Symbol.Set.add sexpr Symbol.Set.empty

let vars sexpr =
  let rec go depth sexpr =
    let Node (label, children, _) = sexpr.obj in
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

let free_vars sexpr =
  let table = BatHashtbl.create 991 in
  let add_var v typ =
    if BatHashtbl.mem table v then
      (if not (BatHashtbl.find table v = typ) then
         invalid_arg "free_vars: ill-formed expression")
    else
      BatHashtbl.add table v typ
  in
  let rec go depth sexpr =
    let Node (label, children, _) = sexpr.obj in
    match label with
    | Exists (_, _) | Forall (_, _) ->
      List.iter (go (depth + 1)) children
    | Var (v, typ) when v >= depth ->
      add_var (v - depth) typ
    | _ -> List.iter (go depth) children
  in
  go 0 sexpr;
  table

let destruct _srk sexpr =
  match sexpr.obj with
  | Node (Real qq, [], _) -> `Real qq
  | Node (App func, args, _) -> `App (func, args)
  | Node (Var (v, `TyReal), [], _) -> `Var (v, `TyReal)
  | Node (Var (v, `TyInt), [], _) -> `Var (v, `TyInt)
  | Node (Var (v, `TyBool), [], _) -> `Proposition (`Var v)
  | Node (Add, sum, _) -> `Add sum
  | Node (Mul, product, _) -> `Mul product
  | Node (Div, [s; t], _) -> `Binop (`Div, s, t)
  | Node (Mod, [s; t], _) -> `Binop (`Mod, s, t)
  | Node (Floor, [t], _) -> `Unop (`Floor, t)
  | Node (Neg, [t], _) -> `Unop (`Neg, t)
  | Node (Ite, [cond; bthen; belse], _) -> `Ite (cond, bthen, belse)
  | Node (True, [], _) -> `Tru
  | Node (False, [], _) -> `Fls
  | Node (And, conjuncts, _) -> `And conjuncts
  | Node (Or, disjuncts, _) -> `Or disjuncts
  | Node (Not, [phi], _) -> `Not phi
  | Node (Exists (name, typ), [phi], _) -> `Quantify (`Exists, name, typ, phi)
  | Node (Forall (name, typ), [phi], _) -> `Quantify (`Forall, name, typ, phi)
  | Node (Eq, [s; t], _) -> `Atom (`Eq, s, t)
  | Node (Leq, [s; t], _) -> `Atom (`Leq, s, t)
  | Node (Lt, [s; t], _) -> `Atom (`Lt, s, t)
  | Node (_, _, _) -> assert false

let rec flatten_universal phi = match phi.obj with
  | Node (Forall (name, typ), [phi], _) ->
    let (varinfo, phi') = flatten_universal phi in
    ((name,typ)::varinfo, phi')
  | _ -> ([], phi)

let rec flatten_existential phi = match phi.obj with
  | Node (Exists (name, typ), [phi], _) ->
    let (varinfo, phi') = flatten_existential phi in
    ((name,typ)::varinfo, phi')
  | _ -> ([], phi)

let rec pp_expr ?(env=Env.empty) srk formatter expr =
  let Node (label, children, _) = expr.obj in
  let open Format in
  match label, children with
  | Real qq, [] -> QQ.pp formatter qq
  | App k, [] -> pp_symbol srk formatter k
  | App func, args ->
    fprintf formatter "%a(@[%a@])"
      (pp_symbol srk) func
      (SrkUtil.pp_print_enum_nobox (pp_expr ~env srk)) (BatList.enum args)
  | Var (v, _), [] ->
    (try fprintf formatter "[%s:%d]" (Env.find env v) v
     with Not_found -> fprintf formatter "[free:%d]" v)
  | Add, terms ->
    fprintf formatter "(@[";
    SrkUtil.pp_print_enum
      ~pp_sep:(fun formatter () -> fprintf formatter "@ + ")
      (pp_expr ~env srk)
      formatter
      (BatList.enum terms);
    fprintf formatter "@])"
  | Mul, terms ->
    fprintf formatter "(@[";
    SrkUtil.pp_print_enum
      ~pp_sep:(fun formatter () -> fprintf formatter "@ * ")
      (pp_expr ~env srk)
      formatter
      (BatList.enum terms);
    fprintf formatter "@])"
  | Div, [s; t] ->
    fprintf formatter "(@[%a@ / %a@])"
      (pp_expr ~env srk) s
      (pp_expr ~env srk) t
  | Mod, [s; t] ->
    fprintf formatter "(@[%a@ mod %a@])"
      (pp_expr ~env srk) s
      (pp_expr ~env srk) t
  | Floor, [t] ->
    fprintf formatter "floor(@[%a@])" (pp_expr ~env srk) t
  | Neg, [{obj = Node (Real qq, [], _); _}] ->
    QQ.pp formatter (QQ.negate qq)
  | Neg, [{obj = Node (App _, _, _); _} as t]
  | Neg, [{obj = Node (Var (_, _), [], _); _} as t] ->
    fprintf formatter "-%a" (pp_expr ~env srk) t
  | Neg, [t] -> fprintf formatter "-(@[%a@])" (pp_expr ~env srk) t
  | True, [] -> pp_print_string formatter "true"
  | False, [] -> pp_print_string formatter "false"
  | Not, [phi] ->
    fprintf formatter "!(@[%a@])" (pp_expr ~env srk) phi
  | And, conjuncts ->
    fprintf formatter "(@[";
    SrkUtil.pp_print_enum
      ~pp_sep:(fun formatter () -> fprintf formatter "@ /\\ ")
      (pp_expr ~env srk)
      formatter
      (BatList.enum (List.concat (List.map (flatten_sexpr And) conjuncts)));
    fprintf formatter "@])"
  | Or, disjuncts ->
    fprintf formatter "(@[";
    SrkUtil.pp_print_enum
      ~pp_sep:(fun formatter () -> fprintf formatter "@ \\/ ")
      (pp_expr ~env srk)
      formatter
      (BatList.enum (List.concat (List.map (flatten_sexpr Or) disjuncts)));
    fprintf formatter "@])"
  | Eq, [x; y] ->
    fprintf formatter "@[%a = %a@]"
      (pp_expr ~env srk) x
      (pp_expr ~env srk) y
  | Leq, [x; y] ->
    fprintf formatter "@[%a <= %a@]"
      (pp_expr ~env srk) x
      (pp_expr ~env srk) y
  | Lt, [x; y] ->
    fprintf formatter "@[%a < %a@]"
      (pp_expr ~env srk) x
      (pp_expr ~env srk) y
  | Exists (name, typ), [psi] | Forall (name, typ), [psi] ->
      let (quantifier_name, varinfo, psi) =
        match label with
        | Exists (_, _) ->
          let (varinfo, psi) = flatten_existential psi in
          ("exists", (name, typ)::varinfo, psi)
        | Forall (_, _) ->
          let (varinfo, psi) = flatten_universal psi in
          ("forall", (name, typ)::varinfo, psi)
        | _ -> assert false
      in
      let env =
        List.fold_left (fun env (x,_) -> Env.push x env) env varinfo
      in
      fprintf formatter "(@[%s@ " quantifier_name;
      SrkUtil.pp_print_enum
        ~pp_sep:pp_print_space
        (fun formatter (name, typ) ->
           fprintf formatter "(%s : %a)" name pp_typ typ)
        formatter
        (BatList.enum varinfo);
      fprintf formatter ".@ %a@])" (pp_expr ~env srk) psi
  | Ite, [cond; bthen; belse] ->
    fprintf formatter "ite(@[%a,@ %a,@ %a@])"
      (pp_expr ~env srk) cond
      (pp_expr ~env srk) bthen
      (pp_expr ~env srk) belse
  | _ -> failwith "pp_expr: ill-formed expression"




(* This variant of pp_expr avoids printing a symbol number (e.g., "x:5") for a
   symbol S (i.e., a program variable or function name) if there does not exist
   any other symbol in the expression that has the same name as S. *)
let pp_expr_unnumbered ?(env=Env.empty) srk formatter expr =

  (* find a unique string that can be used to identify each symbol *)
  let strings = Hashtbl.create 991 in
  let symbol_name = Hashtbl.create 991 in
  Symbol.Set.iter (fun symbol ->
      let name = fst (DynArray.get srk.symbols symbol) in
      if Hashtbl.mem strings name then
        let rec go n =
          let name' = name ^ ":" ^ (string_of_int n) in
          if Hashtbl.mem strings name' then
            go (n + 1)
          else begin
            Hashtbl.add strings name' ();
            Hashtbl.add symbol_name symbol name'
          end
        in
        go 0
      else begin
        Hashtbl.add strings name ();
        Hashtbl.add symbol_name symbol name
      end)
    (symbols expr);

  let rec go ?(env=Env.empty) srk formatter expr =
    let Node (label, children, _) = expr.obj in
    let open Format in
    match label, children with
    | Real qq, [] -> QQ.pp formatter qq
    | App k, [] -> 
      pp_print_string formatter (Hashtbl.find symbol_name k)
    | App func, args ->
      fprintf formatter "%s(@[%a@])"
      (Hashtbl.find symbol_name func)
      (SrkUtil.pp_print_enum_nobox (go ~env srk)) (BatList.enum args)
    | Var (v, _), [] ->
      (try fprintf formatter "[%s:%d]" (Env.find env v) v
       with Not_found -> fprintf formatter "[free:%d]" v)
    | Add, terms ->
      fprintf formatter "(@[";
      SrkUtil.pp_print_enum
        ~pp_sep:(fun formatter () -> fprintf formatter "@ + ")
        (go ~env srk)
        formatter
        (BatList.enum terms);
      fprintf formatter "@])"
    | Mul, terms ->
      fprintf formatter "(@[";
      SrkUtil.pp_print_enum
        ~pp_sep:(fun formatter () -> fprintf formatter "@ * ")
        (go ~env srk)
        formatter
        (BatList.enum terms);
      fprintf formatter "@])"
    | Div, [s; t] ->
      fprintf formatter "(@[%a@ / %a@])"
        (go ~env srk) s
        (go ~env srk) t
    | Mod, [s; t] ->
      fprintf formatter "(@[%a@ mod %a@])"
        (go ~env srk) s
        (go ~env srk) t
    | Floor, [t] ->
      fprintf formatter "floor(@[%a@])" (go ~env srk) t
    | Neg, [{obj = Node (Real qq, [], _); _}] ->
      QQ.pp formatter (QQ.negate qq)
    | Neg, [{obj = Node (App _, _, _); _} as t]
    | Neg, [{obj = Node (Var (_, _), [], _); _} as t] ->
      fprintf formatter "-%a" (go ~env srk) t
    | Neg, [t] -> fprintf formatter "-(@[%a@])" (go ~env srk) t
    | True, [] -> pp_print_string formatter "true"
    | False, [] -> pp_print_string formatter "false"
    | Not, [phi] ->
      fprintf formatter "!(@[%a@])" (go ~env srk) phi
    | And, conjuncts ->
      fprintf formatter "(@[";
      SrkUtil.pp_print_enum
        ~pp_sep:(fun formatter () -> fprintf formatter "@ /\\ ")
        (go ~env srk)
        formatter
        (BatList.enum (List.concat (List.map (flatten_sexpr And) conjuncts)));
      fprintf formatter "@])"
    | Or, disjuncts ->
      fprintf formatter "(@[";
      SrkUtil.pp_print_enum
        ~pp_sep:(fun formatter () -> fprintf formatter "@ \\/ ")
        (go ~env srk)
        formatter
        (BatList.enum (List.concat (List.map (flatten_sexpr Or) disjuncts)));
      fprintf formatter "@])"
    | Eq, [x; y] ->
      fprintf formatter "@[%a = %a@]"
        (go ~env srk) x
        (go ~env srk) y
    | Leq, [x; y] ->
      fprintf formatter "@[%a <= %a@]"
        (go ~env srk) x
        (go ~env srk) y
    | Lt, [x; y] ->
      fprintf formatter "@[%a < %a@]"
        (go ~env srk) x
        (go ~env srk) y
    | Exists (name, typ), [psi] | Forall (name, typ), [psi] ->
        let (quantifier_name, varinfo, psi) =
          match label with
          | Exists (_, _) ->
            let (varinfo, psi) = flatten_existential psi in
            ("exists", (name, typ)::varinfo, psi)
          | Forall (_, _) ->
            let (varinfo, psi) = flatten_universal psi in
            ("forall", (name, typ)::varinfo, psi)
          | _ -> assert false
        in
        let env =
          List.fold_left (fun env (x,_) -> Env.push x env) env varinfo
        in
        fprintf formatter "(@[%s@ " quantifier_name;
        SrkUtil.pp_print_enum
          ~pp_sep:pp_print_space
          (fun formatter (name, typ) ->
             fprintf formatter "(%s : %a)" name pp_typ typ)
          formatter
          (BatList.enum varinfo);
        fprintf formatter ".@ %a@])" (go ~env srk) psi
    | Ite, [cond; bthen; belse] ->
      fprintf formatter "ite(@[%a,@ %a,@ %a@])"
        (go ~env srk) cond
        (go ~env srk) bthen
        (go ~env srk) belse
    | _ -> failwith "pp_expr_unnumbered: ill-formed expression"

  in go ~env srk formatter expr



module Expr = struct
  module Inner = struct
    type t = sexpr hobj
    let equal s t = s.tag = t.tag
    let compare s t = Stdlib.compare s.tag t.tag
    let hash t = t.hcode
  end
  include Inner

  let refine _srk sexpr =
    match sexpr.obj with
    | Node (_, _, `TyInt) -> `Term sexpr
    | Node (_, _, `TyReal) -> `Term sexpr
    | Node (_, _, `TyBool) -> `Formula sexpr

  let term_of _srk sexpr =
    match sexpr.obj with
    | Node (_, _, `TyInt)
    | Node (_, _, `TyReal) -> sexpr
    | Node (_, _, `TyBool) -> invalid_arg "Syntax.term_of: not a term"

  let formula_of _srk sexpr =
    match sexpr.obj with
    | Node (_, _, `TyInt)
    | Node (_, _, `TyReal) -> invalid_arg "Syntax.formula_of: not a formula"
    | Node (_, _, `TyBool) -> sexpr

  let pp = pp_expr

  module HT = struct
    module HT = BatHashtbl.Make(Inner)
    type ('a, 'typ, 'b) t = 'b HT.t
    let create = HT.create
    let add = HT.add
    let replace = HT.replace
    let remove = HT.remove
    let find = HT.find
    let mem = HT.mem
    let keys = HT.keys
    let values = HT.values
    let enum = HT.enum
  end

  module Set = struct
    module S = BatSet.Make(Inner)
    type ('a, 'typ) t = S.t
    let empty = S.empty
    let add = S.add
    let union = S.union
    let inter = S.inter
    let enum = S.enum
    let mem = S.mem
    let equal = S.equal
    let of_list = S.of_list
    let elements = S.elements
    let filter = S.filter
  end

  module Map = struct
    module M = BatMap.Make(Inner)
    type ('a, 'typ, 'b) t = 'b M.t
    let empty = M.empty
    let is_empty = M.is_empty
    let add = M.add
    let map = M.map
    let filter = M.filter
    let filter_map = M.filter_map
    let remove = M.remove
    let find = M.find
    let keys = M.keys
    let values = M.values
    let enum = M.enum
    let merge = M.merge
    let fold = M.fold
    let equal = M.equal
  end
end

module Term = struct
  type 'a t = 'a term
  let equal s t = s.tag = t.tag
  let compare s t = Stdlib.compare s.tag t.tag
  let hash t = t.hcode

  let eval _srk alg t =
    let rec go t =
      match t.obj with
      | Node (Real qq, [], _) -> alg (`Real qq)
      | Node (App _, _, `TyBool) -> invalid_arg "eval: not a term"
      | Node (App func, args, `TyInt) | Node (App func, args, `TyReal) ->
        alg (`App (func, args))
      | Node (Var (v, typ), [], _) ->
        begin match typ with
          | `TyInt -> alg (`Var (v, `TyInt))
          | `TyReal -> alg (`Var (v, `TyReal))
          | `TyBool -> invalid_arg "eval: not a term"
        end
      | Node (Add, sum, _) -> alg (`Add (List.map go sum))
      | Node (Mul, product, _) -> alg (`Mul (List.map go product))
      | Node (Div, [s; t], _) -> alg (`Binop (`Div, go s, go t))
      | Node (Mod, [s; t], _) -> alg (`Binop (`Mod, go s, go t))
      | Node (Floor, [t], _) -> alg (`Unop (`Floor, go t))
      | Node (Neg, [t], _) -> alg (`Unop (`Neg, go t))
      | Node (Ite, [cond; bthen; belse], `TyReal)
      | Node (Ite, [cond; bthen; belse], `TyInt) ->
        alg (`Ite (cond, go bthen, go belse))
      | _ -> invalid_arg "eval: not a term"
    in
    go t

  let eval_partial srk alg t =
    let alg' term =
      match alg term with
      | Some t -> t
      | None -> raise Quit
    in
    try Some (eval srk alg' t)
    with Quit -> None

  let destruct _srk t = match t.obj with
    | Node (Real qq, [], _) -> `Real qq
    | Node (App _, _, `TyBool) -> invalid_arg "destruct: not a term"
    | Node (App func, args, `TyInt) | Node (App func, args, `TyReal) ->
      `App (func, args)
    | Node (Var (v, typ), [], _) ->
      begin match typ with
        | `TyInt -> `Var (v, `TyInt)
        | `TyReal -> `Var (v, `TyReal)
        | `TyBool -> invalid_arg "destruct: not a term"
      end
    | Node (Add, sum, _) -> `Add sum
    | Node (Mul, product, _) -> `Mul product
    | Node (Div, [s; t], _) -> `Binop (`Div, s, t)
    | Node (Mod, [s; t], _) -> `Binop (`Mod, s, t)
    | Node (Floor, [t], _) -> `Unop (`Floor, t)
    | Node (Neg, [t], _) -> `Unop (`Neg, t)
    | Node (Ite, [cond; bthen; belse], `TyReal)
    | Node (Ite, [cond; bthen; belse], `TyInt) ->
      `Ite (cond, bthen, belse)
    | _ -> invalid_arg "destruct: not a term"

  let pp = pp_expr
  let show ?(env=Env.empty) srk t = SrkUtil.mk_show (pp ~env srk) t
end

module Formula = struct
  type 'a t = 'a formula
  let equal s t = s.tag = t.tag
  let compare s t = Stdlib.compare s.tag t.tag
  let hash t = t.hcode

  let destruct _srk phi = match phi.obj with
    | Node (True, [], _) -> `Tru
    | Node (False, [], _) -> `Fls
    | Node (And, conjuncts, _) -> `And conjuncts
    | Node (Or, disjuncts, _) -> `Or disjuncts
    | Node (Not, [phi], _) -> `Not phi
    | Node (Exists (name, typ), [phi], _) ->
      `Quantify (`Exists, name, typ, phi)
    | Node (Forall (name, typ), [phi], _) ->
      `Quantify (`Forall, name, typ, phi)
    | Node (Eq, [s; t], _) -> `Atom (`Eq, s, t)
    | Node (Leq, [s; t], _) -> `Atom (`Leq, s, t)
    | Node (Lt, [s; t], _) -> `Atom (`Lt, s, t)
    | Node (Var (v, `TyBool), [], _) -> `Proposition (`Var v)
    | Node (App f, args, `TyBool) -> `Proposition (`App (f, args))
    | Node (Ite, [cond; bthen; belse], `TyBool) -> `Ite (cond, bthen, belse)
    | _ -> invalid_arg "destruct: not a formula"

  let rec eval srk alg phi = match destruct srk phi with
    | `Tru -> alg `Tru
    | `Fls -> alg `Fls
    | `Or disjuncts -> alg (`Or (List.map (eval srk alg) disjuncts))
    | `And conjuncts -> alg (`And (List.map (eval srk alg) conjuncts))
    | `Quantify (qt, name, typ, phi) ->
      alg (`Quantify (qt, name, typ, eval srk alg phi))
    | `Not phi -> alg (`Not (eval srk alg phi))
    | `Atom (op, s, t) -> alg (`Atom (op, s, t))
    | `Proposition p -> alg (`Proposition p)
    | `Ite (cond, bthen, belse) ->
      alg (`Ite (eval srk alg cond, eval srk alg bthen, eval srk alg belse))

  let eval_memo srk alg =
    let table = BatInnerWeaktbl.create 991 in
    let rec go phi =
      try BatInnerWeaktbl.find table phi.tag
      with Not_found ->
        let result = match destruct srk phi with
          | `Tru -> alg `Tru
          | `Fls -> alg `Fls
          | `Or disjuncts -> alg (`Or (List.map go disjuncts))
          | `And conjuncts -> alg (`And (List.map go conjuncts))
          | `Quantify (qt, name, typ, phi) ->
            alg (`Quantify (qt, name, typ, go phi))
          | `Not phi -> alg (`Not (go phi))
          | `Atom (op, s, t) -> alg (`Atom (op, s, t))
          | `Proposition p -> alg (`Proposition p)
          | `Ite (cond, bthen, belse) ->
            alg (`Ite (go cond, go bthen, go belse))
        in
        BatInnerWeaktbl.add table phi.tag result;
        result
    in
    go

  let pp = pp_expr
  let show ?(env=Env.empty) srk t = SrkUtil.mk_show (pp ~env srk) t

  let quantify_closure quantify srk phi =
    let vars = vars phi in
    let types = Array.make (Var.Set.cardinal vars) `TyInt in
    let rename =
      let n = ref (-1) in
      let map =
        Var.Set.fold (fun (v, typ) m ->
            incr n;
            types.(!n) <- typ;
            SrkUtil.Int.Map.add v (mk_var srk (!n) typ) m
          )
          vars
          SrkUtil.Int.Map.empty
      in
      fun v -> SrkUtil.Int.Map.find v map
    in
    Array.fold_left
      (fun psi typ -> quantify typ psi)
      (substitute srk rename phi)
      types

  let existential_closure srk = quantify_closure (mk_exists srk) srk
  let universal_closure srk = quantify_closure (mk_forall srk) srk

  let skolemize_free srk phi =
    let skolem =
      Memo.memo (fun (_, typ) -> mk_const srk (mk_symbol srk typ))
    in
    let rec go sexpr =
      let (Node (label, children, _)) = sexpr.obj in
      match label with
      | Var (i, typ) -> skolem (i, (typ :> typ))
      | _ -> srk.mk label (List.map go children)
    in
    go phi

  let prenex srk phi =
    let negate_prefix =
      List.map (function
          | `Exists (name, typ) -> `Forall (name, typ)
          | `Forall (name, typ) -> `Exists (name, typ))
    in
    let combine phis =
      let f (qf_pre0, phi0) (qf_pre, phis) =
        let depth = List.length qf_pre in
        let depth0 = List.length qf_pre0 in
        let phis = List.map (decapture srk depth depth0) phis in
        (qf_pre0@qf_pre, (decapture srk 0 depth phi0)::phis)
      in
      List.fold_right f phis ([], [])
    in
    let alg = function
      | `Tru -> ([], mk_true srk)
      | `Fls -> ([], mk_false srk)
      | `Atom (`Eq, x, y) -> ([], mk_eq srk x y)
      | `Atom (`Lt, x, y) -> ([], mk_lt srk x y)
      | `Atom (`Leq, x, y) -> ([], mk_leq srk x y)
      | `And conjuncts ->
        let (qf_pre, conjuncts) = combine conjuncts in
        (qf_pre, mk_and srk conjuncts)
      | `Or disjuncts ->
        let (qf_pre, disjuncts) = combine disjuncts in
        (qf_pre, mk_or srk disjuncts)
      | `Quantify (`Exists, name, typ, (qf_pre, phi)) ->
        (`Exists (name, typ)::qf_pre, phi)
      | `Quantify (`Forall, name, typ, (qf_pre, phi)) ->
        (`Forall (name, typ)::qf_pre, phi)
      | `Not (qf_pre, phi) -> (negate_prefix qf_pre, mk_not srk phi)
      | `Proposition (`Var i) -> ([], mk_var srk i `TyBool)
      | `Proposition (`App (p, args)) -> ([], mk_app srk p args)
      | `Ite (cond, bthen, belse) ->
        begin match combine [cond; bthen; belse] with
          | (qf_pre, [cond; bthen; belse]) ->
            (qf_pre, mk_ite srk cond bthen belse)
          | _ -> assert false
        end
    in
    let (qf_pre, matrix) = eval srk alg phi in
    List.fold_right
      (fun qf phi ->
         match qf with
         | `Exists (name, typ) -> mk_exists srk ~name typ phi
         | `Forall (name, typ) -> mk_forall srk ~name typ phi)
      qf_pre
      matrix
end

let quantify_const srk qt sym phi =
  let typ = match typ_symbol srk sym with
    | #typ_fo as x -> x
    | `TyFun _ ->
      begin match qt with
        | `Forall ->
          invalid_arg "mk_forall_const: not a first-order constant"
        | `Exists ->
          invalid_arg "mk_exists_const: not a first-order constant"
      end
  in
  let replacement = mk_var srk 0 typ in
  let subst k =
    if k = sym then replacement
    else mk_const srk k
  in
  let psi = substitute_const srk subst (decapture srk 0 1 phi) in
  match qt with
  | `Forall -> mk_forall srk ~name:(show_symbol srk sym) typ psi
  | `Exists -> mk_exists srk ~name:(show_symbol srk sym) typ psi

let mk_exists_const srk = quantify_const srk `Exists
let mk_forall_const srk = quantify_const srk `Forall

let quantify_consts srk qt p phi =
  let nb_vars = ref 0 in
  let varinfo = ref [] in
  let subst =
    Memo.memo (fun sym ->
        if p sym then
          mk_const srk sym
        else
          let i = !nb_vars in
          let typ =
            match typ_symbol srk sym with
            | #typ_fo as x -> x
            | `TyFun _ ->
               begin match qt with
               | `Forall ->
                  invalid_arg "mk_forall_consts: not a first-order constant"
               | `Exists ->
                  invalid_arg "mk_exists_consts: not a first-order constant"
               end
          in
          incr nb_vars;
          varinfo := (show_symbol srk sym, typ)::(!varinfo);
          mk_var srk i typ)
  in
  let quantify =
    match qt with
    | `Forall -> mk_forall srk
    | `Exists -> mk_exists srk
  in
  let matrix = substitute_const srk subst phi in
  List.fold_right
    (fun (name, typ) phi -> quantify ~name typ phi)
    (!varinfo)
    matrix

let mk_exists_consts srk = quantify_consts srk `Exists
let mk_forall_consts srk = quantify_consts srk `Forall

let node_typ symbols label children =
  match label with
  | Real qq ->
    begin match QQ.to_zz qq with
      | Some _ -> `TyInt
      | None -> `TyReal
    end
  | Var (_, typ) -> typ
  | App func ->
    begin match snd (DynArray.get symbols func) with
      | `TyFun (args, ret) ->
        if List.length args != List.length children then
          invalid_arg "Arity mis-match in function application";
        if (BatList.for_all2
              (fun typ { obj = Node (_, _, typ'); _ } -> subtype typ' typ)
              args
              children)
        then
          ret
        else
          invalid_arg "Mis-matched types in function application"
      | `TyInt when children = [] -> `TyInt
      | `TyReal when children = [] -> `TyReal
      | `TyBool when children = [] -> `TyBool
      | _ -> invalid_arg "Application of a non-function symbol"
    end
  | Forall (_, _) | Exists (_, _) | And | Or | Not
  | True | False | Eq | Leq | Lt  -> `TyBool
  | Floor -> `TyInt
  | Div -> `TyReal
  | Add | Mul | Mod | Neg ->
    List.fold_left (fun typ { obj = Node (_, _, typ'); _ } ->
        match typ, typ' with
        | `TyInt, `TyInt -> `TyInt
        | `TyInt, `TyReal | `TyReal, `TyInt | `TyReal, `TyReal -> `TyReal
        | _, _ -> assert false)
      `TyInt
      children
  | Ite ->
    begin match children with
      | [cond; bthen; belse] ->
        begin match cond.obj, bthen.obj, belse.obj with
          | Node (_, _, `TyBool), Node (_, _, `TyBool), Node (_, _, `TyBool) ->
            `TyBool
          | Node (_, _, `TyBool), Node (_, _, `TyInt), Node (_, _, `TyInt) ->
            `TyInt
          | Node (_, _, `TyBool), Node (_, _, `TyInt), Node (_, _, `TyReal)
          | Node (_, _, `TyBool), Node (_, _, `TyReal), Node (_, _, `TyInt)
          | Node (_, _, `TyBool), Node (_, _, `TyReal), Node (_, _, `TyReal) ->
            `TyReal
          | _, _, _ -> invalid_arg "ill-typed if-then-else"
        end
      | _ -> assert false
    end

let term_typ _ node =
  match node.obj with
  | Node (_, _, `TyInt) -> `TyInt
  | Node (_, _, `TyReal) -> `TyReal
  | Node (_, _, `TyBool) -> invalid_arg "term_typ: not an arithmetic term"

let expr_typ _ node =
  match node.obj with
  | Node (_, _, `TyInt) -> `TyInt
  | Node (_, _, `TyReal) -> `TyReal
  | Node (_, _, `TyBool) -> `TyBool

type 'a rewriter = ('a, typ_fo) expr -> ('a, typ_fo) expr

let rec nnf_rewriter srk sexpr =
  match sexpr.obj with
  | Node (Not, [phi], _) ->
    begin match phi.obj with
      | Node (Not, [psi], _) -> nnf_rewriter srk psi
      | Node (And, conjuncts, _) -> mk_or srk (List.map (mk_not srk) conjuncts)
      | Node (Or, conjuncts, _) -> mk_and srk (List.map (mk_not srk) conjuncts)
      | Node (Leq, [s; t], _) -> mk_lt srk t s
      | Node (Eq, [s; t], _) -> mk_or srk [mk_lt srk s t; mk_lt srk t s]
      | Node (Lt, [s; t], _) -> mk_leq srk t s
      | Node (Exists (name, typ), [psi], _) ->
        mk_forall srk ~name typ (mk_not srk psi)
      | Node (Forall (name, typ), [psi], _) ->
        mk_exists srk ~name typ (mk_not srk psi)
      | Node (Ite, [cond; bthen; belse], `TyBool) ->
        mk_ite srk cond (mk_not srk bthen) (mk_not srk belse)
      | _ -> sexpr
    end
  | _ -> sexpr

let rec rewrite srk ?down:(down=fun x -> x) ?up:(up=fun x -> x) sexpr =
  let (Node (label, children, _)) = (down sexpr).obj in
  up (srk.mk label (List.map (rewrite srk ~down ~up) children))

let eliminate_ite srk phi =
  let rec map_ite f ite =
    match ite with
    | `Term t -> f t
    | `Ite (cond, bthen, belse) ->
      `Ite (cond, map_ite f bthen, map_ite f belse)
  in
  let mk_ite cond bthen belse =
    mk_or srk [mk_and srk [cond; bthen];
               mk_and srk [mk_not srk cond; belse]]
  in
  let rec ite_formula ite =
    match ite with
    | `Term phi -> phi
    | `Ite (cond, bthen, belse) ->
      mk_ite cond (ite_formula bthen) (ite_formula belse)
  in
  let mk_atom op =
    match op with
    | `Eq -> mk_eq srk
    | `Leq -> mk_leq srk
    | `Lt -> mk_lt srk
  in
  let rec promote_ite term =
    match Term.destruct srk term with
    | `Ite (cond, bthen, belse) ->
      `Ite (elim_ite cond, promote_ite bthen, promote_ite belse)
    | `Real _ | `Var (_, _) -> `Term term
    | `Add xs -> map_ite (fun xs -> `Term (mk_add srk xs)) (ite_list xs)
    | `Mul xs -> map_ite (fun xs -> `Term (mk_mul srk xs)) (ite_list xs)
    | `Binop (`Div, x, y) ->
      let promote_y = promote_ite y in
      map_ite
        (fun t -> map_ite (fun s -> `Term (mk_div srk t s)) promote_y)
        (promote_ite x)
    | `Binop (`Mod, x, y) ->
      let promote_y = promote_ite y in
      map_ite
        (fun t -> map_ite (fun s -> `Term (mk_mod srk t s)) promote_y)
        (promote_ite x)
    | `Unop (`Neg, x) ->
      map_ite (fun t -> `Term (mk_neg srk t)) (promote_ite x)
    | `Unop (`Floor, x) ->
      map_ite (fun t -> `Term (mk_floor srk t)) (promote_ite x)
    | `App (func, args) ->
      List.fold_right (fun x rest ->
          match Expr.refine srk x with
          | `Formula phi ->
            let phi = elim_ite phi in
            map_ite (fun xs -> `Term (phi::xs)) rest
          | `Term t ->
            map_ite
              (fun t -> map_ite (fun xs -> `Term (t::xs)) rest)
              (promote_ite t))
        args
        (`Term [])
      |> map_ite (fun args -> `Term (mk_app srk func args))
  and ite_list xs =
    List.fold_right (fun x ite ->
        map_ite
          (fun x_term -> map_ite (fun xs -> `Term (x_term::xs)) ite)
          (promote_ite x))
      xs
      (`Term [])
  and elim_ite phi =
    let alg = function
      | `Tru -> mk_true srk
      | `Fls -> mk_false srk
      | `And xs -> mk_and srk xs
      | `Or xs -> mk_or srk xs
      | `Not phi  -> mk_not srk phi
      | `Quantify (`Exists, name, typ, phi) -> mk_exists srk ~name typ phi
      | `Quantify (`Forall, name, typ, phi) -> mk_forall srk ~name typ phi
      | `Ite (cond, bthen, belse) -> mk_ite cond bthen belse
      | `Atom (op, s, t) ->
        let promote_t = promote_ite t in
        map_ite
          (fun s -> map_ite (fun t -> `Term (mk_atom op s t)) promote_t)
          (promote_ite s)
        |> ite_formula
      | `Proposition (`Var i) -> mk_var srk i `TyBool
      | `Proposition (`App (func, args)) ->
        List.fold_right (fun x rest ->
            match Expr.refine srk x with
            | `Formula phi ->
              let phi = elim_ite phi in
              map_ite (fun xs -> `Term (phi::xs)) rest
            | `Term t ->
              map_ite
                (fun t -> map_ite (fun xs -> `Term (t::xs)) rest)
                (promote_ite t))
          args
          (`Term [])
        |> map_ite (fun args -> `Term (mk_app srk func args))
        |> ite_formula
    in
    Formula.eval srk alg phi
  in
  elim_ite phi

let pp_smtlib2_gen ?(named=false) ?(env=Env.empty) ?(strings=Hashtbl.create 991) srk formatter assertions =
  let open Format in
  let pp_sep = pp_print_space in

  (* Legal characters in an SMTLIB2 symbol *)
  let legal_char x =
    BatChar.is_letter x || BatChar.is_digit x
    || BatString.contains "~!@$%^&*_-+=<>.?/" x
  in
  (* Convert a string to a valid SMTLIB2 symbol *)
  let symbol_of_string name =
    if BatEnum.for_all legal_char (BatString.enum name) then
      name
    else
      let replaced =
        BatString.map (fun c ->
            if legal_char c || BatString.contains " \"#'(),;:`{}" c then
              c
            else
              '?')
          name
      in
      "|" ^ replaced ^ "|"
  in
  let fresh_var_name =
    let nb_vars = ref 0 in
    fun name -> begin
        incr nb_vars;
        symbol_of_string (Format.sprintf "%s?%d" name (!nb_vars))
      end
  in

  let all_symbols =
    List.fold_left (fun syms phi ->
      Symbol.Set.union syms (symbols phi)
    ) Symbol.Set.empty assertions
  in

  (* find a unique string that can be used to identify each symbol *)
  let symbol_name = Hashtbl.create 991 in
  Symbol.Set.iter (fun symbol ->
      let base_name = fst (DynArray.get srk.symbols symbol) in
      let name = symbol_of_string base_name in
      if Hashtbl.mem strings name then
        let rec go n =
          let name' = symbol_of_string (base_name ^ (string_of_int n)) in
          if Hashtbl.mem strings name' then
            go (n + 1)
          else begin
            Hashtbl.add strings name' symbol;
            Hashtbl.add symbol_name symbol name'
          end
        in
        go 0
      else begin
        let name = symbol_of_string (fst (DynArray.get srk.symbols symbol)) in
        Hashtbl.add strings name symbol;
        Hashtbl.add symbol_name symbol name
      end)
    all_symbols;

  fprintf formatter "@[<v 0>";

  let pp_typ_fo formatter = function
    | `TyReal -> pp_print_string formatter "Real"
    | `TyInt -> pp_print_string formatter "Int"
    | `TyBool -> pp_print_string formatter "Bool"
  in
  (* print declarations *)
  symbol_name |> Hashtbl.iter (fun symbol name ->
      match typ_symbol srk symbol with
      | `TyReal -> fprintf formatter "(declare-const %s Real)@;" name
      | `TyInt -> fprintf formatter "(declare-const %s Int)@;" name
      | `TyBool -> fprintf formatter "(declare-const %s Bool)@;" name
      | `TyFun (args, ret) ->
        fprintf formatter "(declare-fun %s (%a) %a)@;"
          name
          (SrkUtil.pp_print_enum ~pp_sep pp_typ_fo) (BatList.enum args)
          pp_typ_fo ret
    );

  let rec go env formatter expr =
    let Node (label, children, _) = expr.obj in
    match label, children with
    | Real qq, [] ->
      let (num, den) = QQ.to_zzfrac qq in
      if ZZ.equal den ZZ.one then
        ZZ.pp formatter num
      else
        fprintf formatter "(/ %a %a)"
          ZZ.pp num
          ZZ.pp den
    | App k, [] ->
      pp_print_string formatter (Hashtbl.find symbol_name k)
    | App func, args ->
      fprintf formatter "(%s %a)"
        (Hashtbl.find symbol_name func)
        (SrkUtil.pp_print_enum ~pp_sep (go env)) (BatList.enum args)
    | Var (v, _), [] ->
       (try pp_print_string formatter (Env.find env v)
       with Not_found -> invalid_arg "pp_smtlib2: free variable")
    | Add, terms ->
      fprintf formatter "(+ @[";
      SrkUtil.pp_print_enum
        ~pp_sep
        (go env)
        formatter
        (BatList.enum terms);
      fprintf formatter "@])"
    | Mul, terms ->
      fprintf formatter "(* @[";
      SrkUtil.pp_print_enum
        ~pp_sep
        (go env)
        formatter
        (BatList.enum terms);
      fprintf formatter "@])"
    | Div, [s; t] ->
      fprintf formatter "(/ @[%a@ %a@])"
        (go env) s
        (go env) t
    | Mod, [s; t] ->
      fprintf formatter "(mod @[%a@ %a@])"
        (go env) s
        (go env) t
    | Floor, [t] ->
      fprintf formatter "(to_int @[%a@])" (go env) t
    | Neg, [{obj = Node (Real qq, [], _); _}] ->
      QQ.pp formatter (QQ.negate qq)
    | Neg, [{obj = Node (App _, _, _); _} as t]
    | Neg, [t] -> fprintf formatter "(- @[%a@])" (go env) t
    | True, [] -> pp_print_string formatter "true"
    | False, [] -> pp_print_string formatter "false"
    | Not, [phi] ->
      fprintf formatter "(not @[%a@])" (go env) phi
    | And, conjuncts ->
      fprintf formatter "(and @[";
      SrkUtil.pp_print_enum
        ~pp_sep
        (go env)
        formatter
        (BatList.enum (List.concat (List.map (flatten_sexpr And) conjuncts)));
      fprintf formatter "@])"
    | Or, disjuncts ->
      fprintf formatter "(or @[";
      SrkUtil.pp_print_enum
        ~pp_sep
        (go env)
        formatter
        (BatList.enum (List.concat (List.map (flatten_sexpr Or) disjuncts)));
      fprintf formatter "@])"
    | Eq, [x; y] ->
      fprintf formatter "(= @[%a %a@])"
        (go env) x
        (go env) y
    | Leq, [x; y] ->
      fprintf formatter "(<= @[%a %a@])"
        (go env) x
        (go env) y
    | Lt, [x; y] ->
      fprintf formatter "(< @[%a %a@])"
        (go env) x
        (go env) y
    | Exists (name, typ), [psi] | Forall (name, typ), [psi] ->
      let (quantifier_name, varinfo, psi) =
        match label with
        | Exists (_, _) ->
          let (varinfo, psi) = flatten_existential psi in
          ("exists", (name, typ)::varinfo, psi)
        | Forall (_, _) ->
          let (varinfo, psi) = flatten_universal psi in
          ("forall", (name, typ)::varinfo, psi)
        | _ -> assert false
      in
      let varinfo =
        List.map (fun (name, typ) -> (fresh_var_name name, typ)) varinfo
      in
      let env =
        List.fold_left (fun env (x,_) -> Env.push x env) env varinfo
      in
      fprintf formatter "(@[%s@ (" quantifier_name;
      SrkUtil.pp_print_enum
        ~pp_sep
        (fun formatter (name, typ) ->
           fprintf formatter "(%s %a)" name pp_typ_fo typ)
        formatter
        (BatList.enum varinfo);
      fprintf formatter ")@ %a@])" (go env) psi
    | Ite, [cond; bthen; belse] ->
      fprintf formatter "(ite @[%a@ %a@ %a@])"
        (go env) cond
        (go env) bthen
        (go env) belse
    | _ -> failwith "pp_smtlib2: ill-formed expression"
  in
  List.iteri (fun i phi ->
    if named then
      fprintf formatter "(assert (! %a :named f%d))@;" (go env) phi i
    else
      fprintf formatter "(assert %a)@;" (go env) phi
  ) assertions;
  fprintf formatter "(check-sat)@]"

let pp_smtlib2 ?(env=Env.empty) srk formatter expr =
  pp_smtlib2_gen ~env srk formatter [expr]

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

module type Context = sig
  type t (* magic type parameter unique to this context *)
  val context : t context
  type term = (t, typ_arith) expr
  type formula = (t, typ_bool) expr

  val mk_symbol : ?name:string -> typ -> symbol
  val mk_const : symbol -> ('a, 'typ) expr
  val mk_app : symbol -> ('a, 'b) expr list -> ('a, 'typ) expr
  val mk_var : int -> typ_fo -> ('a, 'typ) expr
  val mk_add : term list -> term
  val mk_mul : term list -> term
  val mk_div : term -> term -> term
  val mk_idiv : term -> term -> term
  val mk_mod : term -> term -> term
  val mk_real : QQ.t -> term
  val mk_zz : ZZ.t -> term
  val mk_int : int -> term
  val mk_floor : term -> term
  val mk_neg : term -> term
  val mk_sub : term -> term -> term
  val mk_forall : ?name:string -> typ_fo -> formula -> formula
  val mk_exists : ?name:string -> typ_fo -> formula -> formula
  val mk_forall_const : symbol -> formula -> formula
  val mk_exists_const : symbol -> formula -> formula
  val mk_and : formula list -> formula
  val mk_or : formula list -> formula
  val mk_not : formula -> formula
  val mk_eq : term -> term -> formula
  val mk_lt : term -> term -> formula
  val mk_leq : term -> term -> formula
  val mk_true : formula
  val mk_false : formula
  val mk_ite : formula -> (t, 'a) expr -> (t, 'a) expr -> (t, 'a) expr
  val stats : unit -> (int * int * int)
end

module ImplicitContext(C : sig
    type t
    val context : t context
  end) = struct
  open C
  let mk_symbol = mk_symbol context
  let mk_const = mk_const context
  let mk_app = mk_app context
  let mk_var = mk_var context
  let mk_add = mk_add context
  let mk_mul = mk_mul context
  let mk_div = mk_div context
  let mk_idiv = mk_idiv context
  let mk_mod = mk_mod context
  let mk_real = mk_real context
  let mk_zz = mk_zz context
  let mk_int = mk_int context
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
  let mk_ite = mk_ite context
  let stats _ = context_stats context
end

module MakeContext () =
struct
  type t = unit
  type term = (t, typ_arith) expr
  type formula = (t, typ_bool) expr

  let context =
    let hashcons = HC.create 991 in
    let symbols = DynArray.make 512 in
    let mk label children =
      let typ = node_typ symbols label children in
      HC.hashcons hashcons (Node (label, children, typ))
    in
    let named_symbols = Hashtbl.create 991 in
    let id = fresh_id () in
    { hashcons; symbols; named_symbols; mk; id }

  include ImplicitContext(struct
      type t = unit
      let context = context
    end)
end

module MakeSimplifyingContext () =
struct
  type t = unit
  type term = (t, typ_arith) expr
  type formula = (t, typ_bool) expr

  let context =
    let hashcons = HC.create 991 in
    let symbols = DynArray.make 512 in
    let named_symbols = Hashtbl.create 991 in
    let true_ = HC.hashcons hashcons (Node (True, [], `TyBool)) in
    let false_ = HC.hashcons hashcons (Node (False, [], `TyBool)) in
    let rec mk label children =
      let hc label children =
        let typ = node_typ symbols label children in
        HC.hashcons hashcons (Node (label, children, typ))
      in
      match label, children with
      | Lt, [x; y] ->
        begin match x.obj, y.obj with
          | Node (Real xv, [], _), Node (Real yv, [], _) ->
            if QQ.lt xv yv then true_ else false_
          | _ -> hc label [x; y]
        end

      | Leq, [x; y] ->
        begin match x.obj, y.obj with
          | Node (Real xv, [], _), Node (Real yv, [], _) ->
            if QQ.leq xv yv then true_ else false_
          | _ -> hc label [x; y]
        end

      | Eq, [x; y] ->
        begin match x.obj, y.obj with
          | Node (Real xv, [], _), Node (Real yv, [], _) ->
            if QQ.equal xv yv then true_ else false_
          | _ -> hc label [x; y]
        end

      | And, conjuncts ->
        if List.exists is_false conjuncts then
          false_
        else
          begin
            match List.filter (not % is_true) conjuncts with
            | [] -> true_
            | [x] -> x
            | conjuncts -> hc And conjuncts
          end

      | Or, disjuncts ->
          if List.exists is_true disjuncts then
            true_
          else
            begin
              match List.filter (not % is_false) disjuncts with
              | [] -> false_
              | [x] -> x
              | disjuncts -> hc Or disjuncts
            end

      | Not, [phi] when is_true phi -> false_
      | Not, [phi] when is_false phi -> true_
      | Not, [phi] ->
        begin match phi.obj with
          | Node (Not, [psi], _) -> psi
          | _ -> hc Not [phi]
        end

      | Add, xs ->
        begin match List.filter (not % is_zero) xs with
          | [] -> mk (Real QQ.zero) []
          | [x] -> x
          | xs -> hc Add xs
        end

      | Mul, xs ->
        let (const, non_const) =
          List.fold_right (fun x (const, non_const) ->
              match x.obj with
              | Node (Real xv, [], _) -> (QQ.mul xv const, non_const)
              | _ -> (const, x::non_const))
            xs
            (QQ.one, [])
        in
        if QQ.equal const QQ.zero then
          mk (Real QQ.zero) []
        else if non_const = [] then
          mk (Real const) []
        else if QQ.equal const QQ.one then
          match non_const with
          | [x] -> x
          | _ -> hc Mul non_const
        else if QQ.equal const (QQ.of_int (-1)) then
          match non_const with
          | [x] -> mk Neg [x]
          | _ -> mk Neg [hc Mul (non_const)]
        else
          hc Mul ((mk (Real const) [])::non_const)

      | Neg, [x] ->
        begin match x.obj with
          | Node (Real xv, [], _) -> mk (Real (QQ.negate xv)) []
          | _ -> hc Neg [x]
        end

      | Floor, [x] ->
        begin match x.obj with
          | Node (Real xv, [], _) -> mk (Real (QQ.of_zz (QQ.floor xv))) []
          | _ -> hc Floor [x]
        end

      | Div, [num; den] ->
        begin match num.obj, den.obj with
          | _, Node (Real d, [], _) when QQ.equal d QQ.zero ->
            hc Div [num; den]
          | (Node (Real num, [], _), Node (Real den, [], _)) ->
            mk (Real (QQ.div num den)) []
          | _, Node (Real den, [], _) when QQ.equal den QQ.one -> num
          | _, _ -> hc Div [num; den]
        end

      | Mod, [num; den] ->
        begin match num.obj, den.obj with
          | _, Node (Real d, [], _) when QQ.equal d QQ.zero ->
            hc Mod [num; den]
          | (Node (Real num, [], _), Node (Real den, [], _)) ->
            mk (Real (QQ.modulo num den)) []
          | Node (_, _, `TyInt), Node (Real den, [], _) when QQ.equal den QQ.one -> mk (Real QQ.zero) []
          | _, _ -> hc Mod [num; den]
        end

      | Ite, [cond; bthen; _] when is_true cond -> bthen
      | Ite, [cond; _; belse] when is_false cond -> belse
      | Ite, [_; x; y] when x.tag = y.tag -> x

      | _, _ -> hc label children
    in
    let id = fresh_id () in
    { hashcons; symbols; named_symbols; mk; id }

  include ImplicitContext(struct
      type t = unit
      let context = context
    end)
end

module ContextTable = struct
  module H = Hashtbl.Make(SrkUtil.Int)
  type 'a t = 'a H.t
  let create = H.create
  let clear = H.clear
  let remove table k = H.remove table k.id (* Do not expose *)
  let add table k v =
    H.add table k.id v;
    Gc.finalise (remove table) k
  let replace table k v = H.replace table k.id v
  let find table k = H.find table k.id
  let mem table k = H.mem table k.id
end

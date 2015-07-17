open Hashcons

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
  | Const of int
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


module TypedString = struct
  type t = string * typ
  let format formatter (name, _) = Format.pp_print_string formatter name
  let typ = snd
  let hash = Hashtbl.hash
  let equal = (=)
end

let rec eval_expr alg expr =
  let (Node (label, children)) = expr.node in
  alg label (List.map (eval_expr alg) children)

let rec flatten_expr label expr =
  let Node (label', children) = expr.node in
  if label = label' then
    List.concat (List.map (flatten_expr label) children)
  else
    [expr]

type 'a open_term = [
  | `Real of QQ.t
  | `Const of int
  | `Var of int * typ
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
  | `Quantify of [`Exists | `Forall] * string * typ * 'a
  | `Atom of [`Eq | `Leq | `Lt] * 'b * 'b
]

module Make (C : Constant) = struct
  type term = expr hash_consed
  type formula = expr hash_consed

  module E = Apak.Enumeration.Make(C)

  let hashcons =
    let hc = HC.create 991 in
    HC.hashcons hc

  let constants = E.empty ()
  
  let const_of_symbol = E.from_int constants
  let symbol_of_const = E.to_int constants

  let mk_real qq = hashcons (Node (Real qq, []))
  let mk_zero = mk_real QQ.zero
  let mk_one = mk_real QQ.one
  let mk_const k = hashcons (Node (Const k, []))
  let mk_var v typ = hashcons (Node (Var (v, typ), []))
  let mk_neg t = hashcons (Node (Neg, [t]))
  let mk_div s t = hashcons (Node (Div, [s; t]))
  let mk_mod s t = hashcons (Node (Mod, [s; t]))
  let mk_floor t = hashcons (Node (Floor, [t]))
  let mk_idiv s t = mk_floor (mk_div s t)

  let mk_add = function
    | [] -> mk_zero
    | [x] -> x
    | sum -> hashcons (Node (Add, sum))

  let mk_mul = function
    | [] -> mk_one
    | [x] -> x
    | product -> hashcons (Node (Mul, product))

  let mk_sub s t = mk_add [s; (mk_neg t)]

  let mk_true = hashcons (Node (True, []))
  let mk_false = hashcons (Node (False, []))
  let mk_not phi = hashcons (Node (Not, [phi]))
  let mk_leq s t = hashcons (Node (Leq, [s; t]))
  let mk_lt s t = hashcons (Node (Lt, [s; t]))
  let mk_eq s t = hashcons (Node (Eq, [s; t]))

  let mk_forall ?name:(name="_") typ phi =
    hashcons (Node (Forall (name, typ), [phi]))

  let mk_exists ?name:(name="_") typ phi =
    hashcons (Node (Exists (name, typ), [phi]))

  let mk_and = function
    | [] -> mk_true
    | [x] -> x
    | conjuncts -> hashcons (Node (And, conjuncts))

  let mk_or = function
    | [] -> mk_false
    | [x] -> x
    | disjuncts -> hashcons (Node (Or, disjuncts))

  let mk_iff phi psi =
    mk_or [mk_and [phi; psi];
           mk_not (mk_or [phi; psi])]

  module Expr = struct
    type t = expr hash_consed

    let equal s t = s.tag = t.tag
    let compare s t = Pervasives.compare s.tag t.tag
    let hash t = t.hkey

    (* Avoid capture by incrementing bound variables *)
    let rec decapture depth expr =
      let Node (label, children) = expr.node in
      match label with
      | Exists (_, _) | Forall (_, _) ->
        decapture_children label (depth + 1) children
      | Var (v, typ) -> hashcons (Node (Var (v + depth, typ), []))
      | _ -> decapture_children label depth children
    and decapture_children label depth children =
      hashcons (Node (label, List.map (decapture depth) children))

    let substitute subst expr =
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
        hashcons (Node (label, List.map (go depth) children))
      in
      go 0 expr

    let substitute_const subst expr =
      let rec go depth expr =
        let Node (label, children) = expr.node in
        match label with
        | Exists (_, _) | Forall (_, _) ->
          go_children label (depth + 1) children
        | Const k -> decapture depth (subst k)
        | _ -> go_children label depth children
      and go_children label depth children =
        hashcons (Node (label, List.map (go depth) children))
      in
      go 0 expr

    let fold_constants f expr acc =
      let rec go acc expr =
        let Node (label, children) = expr.node in
        match label with
        | Const k -> f k acc
        | _ -> List.fold_left go acc children
      in
      go acc expr

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

    let eval alg t =
      let f label children = match label, children with
        | Real qq, [] -> alg (`Real qq)
        | Const k, [] -> alg (`Const k)
        | Var (v, typ), [] -> alg (`Var (v, typ))
        | Add, sum -> alg (`Add sum)
        | Mul, product -> alg (`Mul product)
        | Div, [s; t] -> alg (`Binop (`Div, s, t))
        | Mod, [s; t] -> alg (`Binop (`Mod, s, t))
        | Floor, [t] -> alg (`Unop (`Floor, t))
        | Neg, [t] -> alg (`Unop (`Neg, t))
        | _ -> invalid_arg "eval: not a term"
      in
      eval_expr f t

    let destruct t = match t.node with
      | Node (Real qq, []) -> `Real qq
      | Node (Const k, []) -> `Const k
      | Node (Var (v, typ), []) -> `Var (v, typ)
      | Node (Add, sum) -> `Add sum
      | Node (Mul, product) -> `Mul product
      | Node (Div, [s; t]) -> `Binop (`Div, s, t)
      | Node (Mod, [s; t]) -> `Binop (`Mod, s, t)
      | Node (Floor, [t]) -> `Unop (`Floor, t)
      | Node (Neg, [t]) -> `Unop (`Neg, t)
      | _ -> invalid_arg "destruct: not a term"

    let rec format formatter t =
      let open Format in
      match destruct t with
      | `Real qq -> QQ.format formatter qq
      | `Const k -> C.format formatter (const_of_symbol k)
      | `Var (v, typ) -> fprintf formatter "[free:%d]" v
      | `Add terms ->
        fprintf formatter "(@[";
        ApakEnum.pp_print_enum
          ~pp_sep:(fun formatter () -> fprintf formatter "@ + ")
          format
          formatter
          (BatList.enum terms);
        fprintf formatter "@])"
      | `Mul terms ->
        fprintf formatter "(@[";
        ApakEnum.pp_print_enum
          ~pp_sep:(fun formatter () -> fprintf formatter "@ * ")
          format
          formatter
          (BatList.enum terms);
        fprintf formatter "@])"
      | `Binop (`Div, s, t) ->
        fprintf formatter "(@[%a@ / %a@])"
          format s
          format t
      | `Binop (`Mod, s, t) ->
        fprintf formatter "(@[%a@ mod %a@])"
          format s
          format t
      | `Unop (`Floor, t) ->
        fprintf formatter "floor(@[%a@])" format t
      | `Unop (`Neg, t) ->
        begin match destruct t with
          | `Real qq -> QQ.format formatter (QQ.negate qq)
          | `Const _ | `Var (_, _) ->
            fprintf formatter "-%a" format t
          | _ -> fprintf formatter "-(@[%a@])" format t
        end
    let show t = Apak.Putil.pp_string format t
  end
  module Formula = struct
    include Expr
    let destruct phi = match phi.node with
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
      | _ -> invalid_arg "destruct: not a formula"

    let rec eval : (('a, term) open_formula -> 'a) -> t -> 'a =
        fun alg phi -> match destruct phi with
      | `Tru -> alg `Tru
      | `Fls -> alg `Fls
      | `Or disjuncts -> alg (`Or (List.map (eval alg) disjuncts))
      | `And conjuncts -> alg (`And (List.map (eval alg) conjuncts))
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
      | Node (And, conjuncts) ->
        `And (List.concat (List.map (flatten_expr And) conjuncts))
      | Node (Or, disjuncts) ->
        `Or (List.concat (List.map (flatten_expr Or) disjuncts))
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
      | _ -> invalid_arg "Formula.destruct_flat: not a formula"

    let rec format formatter phi =
      let open Format in
      match destruct_flat phi with
      | `Tru -> pp_print_string formatter "true"
      | `Fls -> pp_print_string formatter "false"
      | `Not phi ->
        fprintf formatter "!(@[%a@])" format phi
      | `And conjuncts ->
        fprintf formatter "(@[";
        ApakEnum.pp_print_enum
          ~pp_sep:(fun formatter () -> fprintf formatter "@ /\\ ")
          format
          formatter
          (BatList.enum conjuncts);
        fprintf formatter "@])"
      | `Or conjuncts ->
        fprintf formatter "(@[";
        ApakEnum.pp_print_enum
          ~pp_sep:(fun formatter () -> fprintf formatter "@ \\/ ")
          format
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
          Term.format x
          op_string
          Term.format y
      | `Quantify (qt, varinfo, psi) ->
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
        fprintf formatter ".@ %a@])" format psi

    let show t = Apak.Putil.pp_string format t

    let existential_closure phi =
      let vars = vars phi in
      let types = Array.make (Var.Set.cardinal vars) TyInt in
      let rename =
        let n = ref (-1) in
        let map =
          Var.Set.fold (fun (v, typ) m ->
              incr n;
              types.(!n) <- typ;
              Apak.Putil.PInt.Map.add v (mk_var (!n) typ) m
            )
            vars
            Apak.Putil.PInt.Map.empty
        in
        fun v -> Apak.Putil.PInt.Map.find v map
      in
      Array.fold_left
        (fun psi typ -> mk_exists typ psi)
        (substitute rename phi)
        types
  end
end

module type BuilderContext = sig
  type term
  type formula

  val mk_add : term list -> term
  val mk_mul : term list -> term
  val mk_div : term -> term -> term
  val mk_mod : term -> term -> term
  val mk_var : int -> typ -> term
  val mk_real : QQ.t -> term
  val mk_const : int -> term
  val mk_floor : term -> term
  val mk_neg : term -> term

  val mk_forall : ?name:string -> typ -> formula -> formula
  val mk_exists : ?name:string -> typ -> formula -> formula
  val mk_and : formula list -> formula
  val mk_or : formula list -> formula
  val mk_not : formula -> formula
  val mk_eq : term -> term -> formula
  val mk_lt : term -> term -> formula
  val mk_leq : term -> term -> formula
end

module type EvalContext = sig
  type term
  type formula
  module Formula : sig
    type t = formula
    val eval : (('a, term) open_formula -> 'a) -> t -> 'a    
  end
  module Term : sig
    type t = term
    val eval : ('a open_term -> 'a) -> t -> 'a
  end
end

module MakeTranslator (Source : EvalContext) (Target : BuilderContext) = struct
  let term term =
    let alg = function
      | `Real qq -> Target.mk_real qq
      | `Const sym -> Target.mk_const sym
      | `Var (i, typ) -> Target.mk_var i typ
      | `Add sum -> Target.mk_add sum
      | `Mul product -> Target.mk_mul product
      | `Binop (`Div, s, t) -> Target.mk_div s t
      | `Binop (`Mod, s, t) -> Target.mk_mod s t
      | `Unop (`Floor, t) -> Target.mk_floor t
      | `Unop (`Neg, t) -> Target.mk_neg t
    in
    Source.Term.eval alg term
  let formula phi =
    let alg = function
      | `Tru -> Target.mk_and []
      | `Fls -> Target.mk_or []
      | `And conjuncts -> Target.mk_and conjuncts
      | `Or disjuncts -> Target.mk_or disjuncts
      | `Not phi -> Target.mk_not phi
      | `Quantify (`Exists, name, typ, phi) ->
        Target.mk_exists ~name:name typ phi
      | `Quantify (`Forall, name, typ, phi) ->
        Target.mk_forall ~name:name typ phi
      | `Atom (`Eq, s, t) -> Target.mk_eq (term s) (term t)
      | `Atom (`Leq, s, t) -> Target.mk_leq (term s) (term t)
      | `Atom (`Lt, s, t) -> Target.mk_lt (term s) (term t)
    in
    Source.Formula.eval alg phi
end

module Infix (C : BuilderContext) =
struct
  let ( ! ) = C.mk_not
  let ( && ) x y = C.mk_and [x; y]
  let ( || ) x y = C.mk_or [x; y]
  let ( < ) = C.mk_lt
  let ( <= ) = C.mk_leq
  let ( = ) = C.mk_eq
  let tru = C.mk_and []
  let fls = C.mk_or []
      
  let ( + ) x y = C.mk_add [x; y]
  let ( - ) x y = C.mk_add [x; C.mk_neg y]
  let ( * ) x y = C.mk_mul [x; y]
  let ( / ) = C.mk_div
  let ( mod ) = C.mk_mod

  let const = C.mk_const
  let forall = C.mk_forall
  let exists = C.mk_exists
  let var = C.mk_var
end

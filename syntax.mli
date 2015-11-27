module Env : sig
  type 'a t
  val empty : 'a t
  val push : 'a -> 'a t -> 'a t
  val find : 'a t -> int -> 'a
end

type typ = [ `TyInt | `TyReal | `TyBool | `TyFun of (typ list) * typ]
type typ_arith = [ `TyInt | `TyReal ]
type typ_fo = [ `TyInt | `TyReal | `TyBool ]
type typ_bool = [ `TyBool ]
type 'a typ_fun = [ `TyFun of (typ list) * 'a ]

type const_sym

(* context is a phantom type: the 'a type parameter ensures that expressions
   don't cross contexts. *)
type 'a context

type ('a,+'typ) expr
type 'a term = ('a, typ_arith) expr
type 'a formula = ('a, typ_bool) expr

type 'a open_term = [
  | `Real of QQ.t
  | `Const of const_sym
  | `Var of int * typ_arith
  | `Add of 'a list
  | `Mul of 'a list
  | `Binop of [ `Div | `Mod ] * 'a * 'a
  | `Unop of [ `Floor | `Neg ] * 'a
]

type ('a,'term) open_formula = [
  | `Tru
  | `Fls
  | `And of 'a list
  | `Or of 'a list
  | `Not of 'a
  | `Quantify of [`Exists | `Forall] * string * typ_fo * 'a
  | `Atom of [`Eq | `Leq | `Lt] * 'term * 'term
  | `Proposition of [ `Const of const_sym | `Var of int ]
]

module type Context = sig
  type t (* magic type parameter unique to this context *)
  val context : t context
  type term = (t, typ_arith) expr
  type formula = (t, typ_bool) expr

  val mk_symbol : ?name:string -> typ -> const_sym
  val mk_const : const_sym -> ('a, 'typ) expr
  val mk_var : int -> typ_fo -> ('a, 'typ) expr
  val mk_add : term list -> term
  val mk_mul : term list -> term
  val mk_div : term -> term -> term
  val mk_mod : term -> term -> term
  val mk_real : QQ.t -> term
  val mk_floor : term -> term
  val mk_neg : term -> term
  val mk_sub : term -> term -> term
  val mk_forall : ?name:string -> typ_fo -> formula -> formula
  val mk_exists : ?name:string -> typ_fo -> formula -> formula
  val mk_forall_const : const_sym -> formula -> formula
  val mk_exists_const : const_sym -> formula -> formula
  val mk_and : formula list -> formula
  val mk_or : formula list -> formula
  val mk_not : formula -> formula
  val mk_eq : term -> term -> formula
  val mk_lt : term -> term -> formula
  val mk_leq : term -> term -> formula
  val mk_true : formula
  val mk_false : formula
end

module MakeContext () : Context

(** Create a context which simplifies expressions on the fly *)
module MakeSimplifyingContext () : Context

val mk_symbol : 'a context -> ?name:string -> typ -> const_sym

val mk_const : 'a context -> const_sym -> ('a, 'typ) expr

val mk_var : 'a context -> int -> typ_fo -> ('a, 'typ) expr

val mk_add : 'a context -> 'a term list -> 'a term
val mk_mul : 'a context -> 'a term list -> 'a term
val mk_div : 'a context -> 'a term -> 'a term -> 'a term
val mk_mod : 'a context -> 'a term -> 'a term -> 'a term
val mk_real : 'a context -> QQ.t -> 'a term
val mk_floor : 'a context -> 'a term -> 'a term
val mk_neg : 'a context -> 'a term -> 'a term
val mk_sub : 'a context -> 'a term -> 'a term -> 'a term

val mk_forall : 'a context -> ?name:string -> typ_fo -> 'a formula -> 'a formula
val mk_exists : 'a context -> ?name:string -> typ_fo -> 'a formula -> 'a formula
val mk_forall_const : 'a context -> const_sym -> 'a formula -> 'a formula
val mk_exists_const : 'a context -> const_sym -> 'a formula -> 'a formula

val mk_and : 'a context -> 'a formula list -> 'a formula
val mk_or : 'a context -> 'a formula list -> 'a formula
val mk_not : 'a context -> 'a formula -> 'a formula
val mk_eq : 'a context -> 'a term -> 'a term -> 'a formula
val mk_lt : 'a context -> 'a term -> 'a term -> 'a formula
val mk_leq : 'a context -> 'a term -> 'a term -> 'a formula
val mk_true : 'a context -> 'a formula
val mk_false : 'a context -> 'a formula

val typ_symbol : 'a context -> const_sym -> typ

val pp_symbol : 'a context -> Format.formatter -> const_sym -> unit
val show_symbol : 'a context -> const_sym -> string

val substitute : 'a context ->
  (int -> ('a,'b) expr) -> ('a,'typ) expr -> ('a,'typ) expr

val substitute_const : 'a context ->
  (const_sym -> ('a,'b) expr) -> ('a,'typ) expr -> ('a,'typ) expr

val fold_constants : (const_sym -> 'a -> 'a) -> ('b, 'c) expr -> 'a -> 'a

val pp_typ : Format.formatter -> typ -> unit
val term_typ : 'a context -> 'a term -> typ_arith

module Term : sig
  type 'a t = 'a term
  val equal : 'a term -> 'a term -> bool
  val compare : 'a term -> 'a term -> int
  val hash : 'a term -> int
  val pp : ?env:(string Env.t) -> 'a context ->
    Format.formatter -> 'a term -> unit
  val show : ?env:(string Env.t) -> 'a context -> 'a term -> string
  val destruct : 'a context -> 'a term -> ('a term) open_term
  val eval : 'a context ->
    ('b open_term -> 'b) -> 'a term -> 'b
end

module Formula : sig
  type 'a t = 'a formula
  val equal : 'a formula -> 'a formula -> bool
  val compare : 'a formula -> 'a formula -> int
  val hash : 'a formula -> int
  val pp : ?env:(string Env.t) -> 'a context ->
    Format.formatter -> 'a formula -> unit
  val show : ?env:(string Env.t) -> 'a context -> 'a formula -> string
  val destruct : 'a context -> 'a formula -> ('a formula, 'a term) open_formula
  val eval : 'a context ->
    (('b, 'c term) open_formula -> 'b) -> 'a formula -> 'b
  val existential_closure : 'a context -> 'a formula -> 'a formula
  val skolemize_free : 'a context -> 'a formula -> 'a formula
  val prenex : 'a context -> 'a formula -> 'a formula
end

module Infix (C : sig
    type t
    val context : t context
  end) : sig
  val exists : ?name:string -> typ_fo -> C.t formula -> C.t formula
  val forall : ?name:string -> typ_fo -> C.t formula -> C.t formula
  val ( ! ) : C.t formula -> C.t formula
  val ( && ) : C.t formula -> C.t formula -> C.t formula
  val ( || ) : C.t formula -> C.t formula -> C.t formula
  val ( < ) : C.t term -> C.t term -> C.t formula
  val ( <= ) : C.t term -> C.t term -> C.t formula
  val ( = ) : C.t term -> C.t term -> C.t formula
  val tru : C.t formula
  val fls : C.t formula

  val ( + ) : C.t term -> C.t term -> C.t term
  val ( - ) : C.t term -> C.t term -> C.t term
  val ( * ) : C.t term -> C.t term -> C.t term
  val ( / ) : C.t term -> C.t term -> C.t term
  val ( mod ) : C.t term -> C.t term -> C.t term
  val const : const_sym -> (C.t, 'typ) expr
  val var : int -> typ_fo -> (C.t, 'typ) expr
end

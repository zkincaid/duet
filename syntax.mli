type typ = [ `TyInt | `TyReal | `TyBool | `TyFun of (typ list) * typ]
type typ_arith = [ `TyInt | `TyReal ]
type typ_fo = [ `TyInt | `TyReal | `TyBool ]
type typ_bool = [ `TyBool ]
type 'a typ_fun = [ `TyFun of (typ list) * 'a ]

type const_sym

module type Constant = sig
  type t
  val pp : Format.formatter -> t -> unit
  val typ : t -> typ
  val hash : t -> int
  val equal : t -> t -> bool
end

module TypedString : Constant with type t = string * typ

module Env : sig
  type 'a t
  val empty : 'a t
  val push : 'a -> 'a t -> 'a t
  val find : 'a t -> int -> 'a
end

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

val pp_typ : Format.formatter -> typ -> unit

module Make (C : Constant) () : sig
  type 'a expr
  type term = typ_arith expr
  type formula = typ_bool expr

  val symbol_of_const : C.t -> const_sym
  val const_of_symbol : const_sym -> C.t option
  val const_of_symbol_exn : const_sym -> C.t

  val mk_skolem : ?name:string -> typ -> const_sym
  val is_skolem : const_sym -> bool
  val const_typ : const_sym -> typ
  val pp_const : Format.formatter -> const_sym -> unit

  val mk_add : term list -> term
  val mk_mul : term list -> term
  val mk_div : term -> term -> term
  val mk_mod : term -> term -> term
  val mk_var : int -> typ_arith -> term
  val mk_real : QQ.t -> term
  val mk_const : const_sym -> term
  val mk_floor : term -> term
  val mk_neg : term -> term
  val mk_sub : term -> term -> term

  val mk_forall : ?name:string -> typ_fo -> formula -> formula
  val mk_exists : ?name:string -> typ_fo -> formula -> formula
  val mk_and : formula list -> formula
  val mk_or : formula list -> formula
  val mk_not : formula -> formula
  val mk_eq : term -> term -> formula
  val mk_lt : term -> term -> formula
  val mk_leq : term -> term -> formula
  val mk_true : formula
  val mk_false : formula
  val mk_prop_const : const_sym -> formula
  val mk_prop_var : int -> formula
  
  val mk_exists_const : const_sym -> formula -> formula
  val mk_forall_const : const_sym -> formula -> formula

  module Term : sig
    type t = term
    val hash : t -> int
    val equal : t -> t -> bool
    val compare : t -> t -> int
    val open_pp : ?env:(string Env.t) -> Format.formatter -> t -> unit
    val open_show : ?env:(string Env.t) -> t -> string
    val pp : Format.formatter -> t -> unit
    val show : t -> string

    val destruct : t -> t open_term
    val eval : ('a open_term -> 'a) -> t -> 'a
    val fold_constants : (const_sym -> 'a -> 'a) -> t -> 'a -> 'a
    val substitute : (int -> t) -> t -> t
    val substitute_const : (const_sym -> t) -> t -> t
  end

  module Formula : sig
    type t = formula
    val hash : t -> int
    val equal : t -> t -> bool
    val compare : t -> t -> int
    val open_pp : ?env:(string Env.t) -> Format.formatter -> t -> unit
    val open_show : ?env:(string Env.t) -> t -> string
    val pp : Format.formatter -> t -> unit
    val show : t -> string

    val destruct : t -> (t, term) open_formula
    val eval : (('a, term) open_formula -> 'a) -> t -> 'a
    val fold_constants : (const_sym -> 'a -> 'a) -> t -> 'a -> 'a
    val substitute : (int -> term) -> t -> t
    val substitute_const : (const_sym -> term) -> t -> t
    val existential_closure : t -> t
    val skolemize_free : t -> t
    val prenex : t -> t
  end
end

module type BuilderContext = sig
  type term
  type formula

  val mk_add : term list -> term
  val mk_mul : term list -> term
  val mk_div : term -> term -> term
  val mk_mod : term -> term -> term
  val mk_var : int -> typ_arith -> term
  val mk_real : QQ.t -> term
  val mk_const : const_sym -> term
  val mk_floor : term -> term
  val mk_neg : term -> term

  val mk_forall : ?name:string -> typ_fo -> formula -> formula
  val mk_exists : ?name:string -> typ_fo -> formula -> formula
  val mk_and : formula list -> formula
  val mk_or : formula list -> formula
  val mk_true : formula
  val mk_false : formula
  val mk_prop_const : const_sym -> formula
  val mk_prop_var : int -> formula
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

module Infix (C : BuilderContext) : sig
  val exists : ?name:string -> typ_fo -> C.formula -> C.formula
  val forall : ?name:string -> typ_fo -> C.formula -> C.formula
  val ( ! ) : C.formula -> C.formula
  val ( && ) : C.formula -> C.formula -> C.formula
  val ( || ) : C.formula -> C.formula -> C.formula
  val ( < ) : C.term -> C.term -> C.formula
  val ( <= ) : C.term -> C.term -> C.formula
  val ( = ) : C.term -> C.term -> C.formula
  val tru : C.formula
  val fls : C.formula

  val ( + ) : C.term -> C.term -> C.term
  val ( - ) : C.term -> C.term -> C.term
  val ( * ) : C.term -> C.term -> C.term
  val ( / ) : C.term -> C.term -> C.term
  val ( mod ) : C.term -> C.term -> C.term
  val const : int -> C.term
  val var : int -> typ_arith -> C.term
end

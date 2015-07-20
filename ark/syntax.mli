type typ = TyInt | TyReal

type const_sym

module type Constant = sig
  type t
  val pp : Format.formatter -> t -> unit
  val typ : t -> typ
  val hash : t -> int
  val equal : t -> t -> bool
end

module MakeSymbolManager (C : Constant)() : sig
  val symbol_of_const : C.t -> const_sym
  val const_of_symbol : const_sym -> C.t option
  val const_of_symbol_exn : const_sym -> C.t

  val mk_skolem : ?name:string -> typ -> const_sym
  val is_skolem : const_sym -> bool
  val const_typ : const_sym -> typ
  val pp_const : Format.formatter -> const_sym -> unit
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
  | `Var of int * typ
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
  | `Quantify of [`Exists | `Forall] * string * typ * 'a
  | `Atom of [`Eq | `Leq | `Lt] * 'term * 'term
]

module Make (C : Constant) () : sig
  type term
  type formula

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
  val mk_var : int -> typ -> term
  val mk_real : QQ.t -> term
  val mk_const : const_sym -> term
  val mk_floor : term -> term
  val mk_neg : term -> term
  val mk_sub : term -> term -> term

  val mk_forall : ?name:string -> typ -> formula -> formula
  val mk_exists : ?name:string -> typ -> formula -> formula
  val mk_and : formula list -> formula
  val mk_or : formula list -> formula
  val mk_not : formula -> formula
  val mk_eq : term -> term -> formula
  val mk_lt : term -> term -> formula
  val mk_leq : term -> term -> formula
  val mk_true : formula
  val mk_false : formula
  
  module Term : sig
    type t = term
    val hash : t -> int
    val equal : t -> t -> bool
    val compare : t -> t -> int
    val pp : Format.formatter -> t -> unit
    val show : t -> string

    val destruct : t -> t open_term
    val eval : ('a open_term -> 'a) -> t -> 'a
    val fold_constants : (int -> 'a -> 'a) -> t -> 'a -> 'a
    val substitute : (int -> t) -> t -> t
    val substitute_const : (const_sym -> t) -> t -> t
  end

  module Formula : sig
    type t = formula
    val hash : t -> int
    val equal : t -> t -> bool
    val compare : t -> t -> int
    val pp : Format.formatter -> t -> unit
    val show : t -> string

    val destruct : t -> (t, term) open_formula
    val eval : (('a, term) open_formula -> 'a) -> t -> 'a
    val fold_constants : (const_sym -> 'a -> 'a) -> t -> 'a -> 'a
    val substitute : (int -> term) -> t -> t
    val substitute_const : (const_sym -> term) -> t -> t
    val existential_closure : t -> t
    val skolemize_free : t -> t
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
  val mk_const : const_sym -> term
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

module MakeTranslator (Source : EvalContext) (Target : BuilderContext) : sig
  val term : Source.term -> Target.term
  val formula : Source.formula -> Target.formula
end

module Infix (C : BuilderContext) : sig
  val exists : ?name:string -> typ -> C.formula -> C.formula
  val forall : ?name:string -> typ -> C.formula -> C.formula
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
  val var : int -> typ -> C.term
end

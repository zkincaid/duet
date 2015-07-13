type 'a context
type typ = TyInt | TyReal
type formula
type term

module type Constant = sig
  type t
  val format : Format.formatter -> t -> unit
  val typ : t -> typ
  val hash : t -> int
  val equal : t -> t -> bool
end

module Env : sig
  type 'a t
  val empty : 'a t
  val push : 'a -> 'a t -> 'a t
  val find : 'a t -> int -> 'a
end

type const_symbol

val mk_context : (module Constant with type t = 'a) -> 'a context
val mk_string_context : unit -> (string * typ) context

val symbol_of_const : 'a context -> 'a -> const_symbol
val const_of_symbol : 'a context -> const_symbol -> 'a
val id_of_symbol : const_symbol -> int
val symbol_of_id : int -> const_symbol

module Term : sig
  type t = term
  type 'a open_t = [
    | `Real of QQ.t
    | `Const of const_symbol
    | `Var of int * typ
    | `Binop of [`Add | `Mul | `Div | `Mod ] * 'a * 'a
    | `Unop of [`Floor | `Neg] * 'a
  ]
  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val format : 'a context ->
    ?env:(string Env.t) ->
    Format.formatter ->
    t ->
    unit
  val show : 'a context -> ?env:(string Env.t) -> t -> string

  val destruct : t -> t open_t
  val eval : ('a open_t -> 'a) -> t -> 'a

  val mk_zero : 'a context -> t
  val mk_one : 'a context -> t
  val mk_real : 'a context -> QQ.t -> t
  val mk_const : 'a context -> const_symbol -> t
  val mk_var : 'a context -> int -> typ -> t
  val mk_add : 'a context -> t -> t -> t
  val mk_sub : 'a context -> t -> t -> t
  val mk_neg : 'a context -> t -> t
  val mk_mul : 'a context -> t -> t -> t
  val mk_div : 'a context -> t -> t -> t
  val mk_idiv : 'a context -> t -> t -> t
  val mk_mod : 'a context -> t -> t -> t
  val mk_floor : 'a context -> t -> t
  val mk_sum : 'a context -> t BatEnum.t -> t
  val mk_product : 'a context -> t BatEnum.t -> t
end

module Formula : sig
  type t = formula
  type 'a open_t = [
    | `Tru
    | `Fls
    | `Binop of [`And | `Or] * 'a * 'a
    | `Not of 'a
    | `Quantify of [`Exists | `Forall] * string * typ * 'a
    | `Atom of [`Eq | `Leq | `Lt] * term * term
  ]
  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val format : 'a context ->
    ?env:(string Env.t) ->
    Format.formatter ->
    t ->
    unit
  val show : 'a context -> ?env:(string Env.t) -> t -> string

  val destruct : t -> t open_t
  val eval : ('a open_t -> 'a) -> t -> 'a

  val mk_true : 'a context -> t
  val mk_false : 'a context -> t

  val mk_leq : 'a context -> term -> term -> t
  val mk_lt : 'a context -> term -> term -> t
  val mk_eq : 'a context -> term -> term -> t

  val mk_and : 'a context -> t -> t -> t
  val mk_or : 'a context -> t -> t -> t
  val mk_not : 'a context -> t -> t

  val mk_exists : 'a context -> ?name:string -> typ -> t -> t
  val mk_forall : 'a context -> ?name:string -> typ -> t -> t

  val mk_conjunction : 'a context -> t BatEnum.t -> t
  val mk_disjunction : 'a context -> t BatEnum.t -> t
end

module ImplicitContext(C : sig
    type t
    val context : t context
  end) : sig
  val exists : ?name:string -> typ -> formula -> formula
  val forall : ?name:string -> typ -> formula -> formula
  val ( ! ) : formula -> formula
  val ( && ) : formula -> formula -> formula
  val ( || ) : formula -> formula -> formula
  val ( < ) : term -> term -> formula
  val ( <= ) : term -> term -> formula
  val ( = ) : term -> term -> formula
  val tru : formula
  val fls : formula

  val ( + ) : term -> term -> term
  val ( - ) : term -> term -> term
  val ( * ) : term -> term -> term
  val ( / ) : term -> term -> term
  val ( mod ) : term -> term -> term
  val const : const_symbol -> term    
  val var : int -> typ -> term
end

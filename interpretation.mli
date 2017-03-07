open Syntax
open Smt

exception Divide_by_zero

type 'a interpretation

val pp : Format.formatter -> 'a interpretation -> unit

val empty : 'a context -> 'a interpretation
val add_real : symbol -> QQ.t -> 'a interpretation -> 'a interpretation
val add_bool : symbol -> bool -> 'a interpretation -> 'a interpretation
val real : 'a interpretation -> symbol -> QQ.t
val bool : 'a interpretation -> symbol -> bool
val value : 'a interpretation -> symbol -> [`Real of QQ.t | `Bool of bool]
val of_model : 'a context -> 'a smt_model -> symbol list -> 'a interpretation
val enum : 'a interpretation ->
  (symbol * [`Real of QQ.t | `Bool of bool]) BatEnum.t

(** Replace constant symbols by their interpretations within an expression.  A
    constant symbol that is not defined within the interpretation is not
    replaced. *)
val substitute : 'a interpretation -> ('a,'typ) expr -> ('a,'typ) expr

val evaluate_term : 'a interpretation ->
  ?env:[`Real of QQ.t | `Bool of bool] Env.t ->
  'a term ->
  QQ.t
    
val evaluate_formula : 'a interpretation ->
  ?env:[`Real of QQ.t | `Bool of bool] Env.t ->
  'a formula ->
  bool

val get_context : 'a interpretation -> 'a context

(** [select_implicant ark m ?env phi] selects an implicant [I] of [phi] such
    that [m,?env |= I |= phi].  The implicant [I] is a list of atomic
    formulas, which can be destructed using [destruct_atom]. *)
val select_implicant : 'a interpretation ->
  ?env:[`Real of QQ.t | `Bool of bool] Env.t ->
  'a formula ->
  ('a formula list) option

val destruct_atom : 'a context ->
  'a formula ->
  [ `Comparison of ([`Lt | `Leq | `Eq] * 'a term * 'a term)
  | `Literal of ([ `Pos | `Neg ] * [ `Const of symbol | `Var of int ])
  | `Tru ]

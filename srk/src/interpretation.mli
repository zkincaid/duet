open Syntax

exception Divide_by_zero

type 'a value = [`Real of QQ.t | `Bool of bool | `Fun of ('a, typ_fo) expr ]

(** An interpretation is a mapping from symbols to values.  Interpretations
    are a collection of concrete bindings (explicit (symbol, value) pairs)
    combined with an optional abstract binding (a symbol -> value function
    that can only be inspected by calling). *)
type 'a interpretation

val pp : Format.formatter -> 'a interpretation -> unit

val empty : 'a context -> 'a interpretation

(** Wrap a function mapping symbols to values in an interpretation.  Calls to
    this function are cached.  Symbols belonging to the optional symbol list
    argument are pre-cached.  *)
val wrap : ?symbols:symbol list ->
  'a context ->
  (symbol -> 'a value) ->
  'a interpretation

val add_real : symbol -> QQ.t -> 'a interpretation -> 'a interpretation
val add_bool : symbol -> bool -> 'a interpretation -> 'a interpretation
val add_fun : symbol -> ('a,typ_fo) expr -> 'a interpretation -> 'a interpretation
val add : symbol -> 'a value -> 'a interpretation -> 'a interpretation

val real : 'a interpretation -> symbol -> QQ.t
val bool : 'a interpretation -> symbol -> bool
val value : 'a interpretation -> symbol -> 'a value

(** Enumerate the concrete bindings in an interpretation. *)
val enum : 'a interpretation ->
  (symbol * [ `Real of QQ.t
            | `Bool of bool
            | `Fun of ('a, typ_fo) expr ]) BatEnum.t

(** Replace constant symbols by their interpretations within an expression.  A
    constant symbol that is not defined within the interpretation is not
    replaced. *)
val substitute : 'a interpretation -> ('a,'typ) expr -> ('a,'typ) expr

val evaluate_term : 'a interpretation ->
  ?env:[`Real of QQ.t | `Bool of bool] Env.t ->
  'a arith_term ->
  QQ.t
    
val evaluate_formula : 'a interpretation ->
  ?env:[`Real of QQ.t | `Bool of bool] Env.t ->
  'a formula ->
  bool

val get_context : 'a interpretation -> 'a context

(** [select_implicant srk m ?env phi] selects an implicant [I] of [phi] such
    that [m,?env |= I |= phi].  The implicant [I] is a list of atomic
    formulas, which can be destructed using [destruct_atom]. *)
val select_implicant : 'a interpretation ->
  ?env:[`Real of QQ.t | `Bool of bool] Env.t ->
  'a formula ->
  ('a formula list) option

val select_ite : 'a interpretation ->
  ?env:[`Real of QQ.t | `Bool of bool] Env.t ->
  ('a,'b) expr ->
  (('a,'b) expr) * ('a formula list)

val destruct_atom : 'a context ->
  'a formula ->
  [ `ArithComparison of ([`Lt | `Leq | `Eq] * 'a arith_term * 'a arith_term)
  | `Literal of ([ `Pos | `Neg ] * [ `Const of symbol | `Var of int ])
  | `ArrEq of ('a arr_term * 'a arr_term) ]

val destruct_atom_for_weak_theory : 'a context ->
  'a formula ->
  [ `ArithComparisonWeak of ([`Neq | `Lt | `Leq | `Eq] * 'a arith_term * 'a arith_term)
  | `IsInt of ([`Pos | `Neg]) * 'a arith_term
  | `Literal of ([ `Pos | `Neg ] * [ `Const of symbol | `Var of int ])
  ]

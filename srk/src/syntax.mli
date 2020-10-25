(** Defines Formulas, Terms, Symbols, Types, and Contexts.  Syntactic
    manipulation of terms and formulas. *)

(** A context manages symbols and sharing between expressions. [context] is a
    phantom type: the ['a] type parameter ensures that expressions don't cross
    contexts. *)
type 'a context

(** takes a context and outputs a tuple containing the (# of sexprs, # of symbols, # of named symbols) *)
val context_stats : 'a context -> (int * int * int)

(** Environments are maps whose domain is a set of free variable symbols.
    Typically used to travese quantified formulas. *)
module Env : sig
  type 'a t
  val empty : 'a t
  val push : 'a -> 'a t -> 'a t
  val find : 'a t -> int -> 'a
  val enum : 'a t -> 'a BatEnum.t
end

(** {2 Types} *)
type typ_arith = [ `TyInt | `TyReal ]
type typ_fo = [ `TyInt | `TyReal | `TyBool ]
type typ = [ `TyInt | `TyReal | `TyBool | `TyFun of (typ_fo list) * typ_fo]
type typ_bool = [ `TyBool ]
type 'a typ_fun = [ `TyFun of (typ_fo list) * 'a ]

val pp_typ : Format.formatter -> [< typ] -> unit

(** {2 Symbols} *)

(** Symbols are represented as non-negative integers, but the type definition
    is hidden.  The isomorphism is witnessed by [int_of_symbol] and
    [symbol_of_int]. *)
type symbol

(** Create a fresh symbol.  Multiple calls to [mk_symbol] with the same
    context, name, and type will always result in different symbols. *)
val mk_symbol : 'a context -> ?name:string -> typ -> symbol

(** Register a named symbol.  The strings identifying named symbols must be
    unique.  The symbol associated with a name can be retrieved with
    [get_named_symbol]. *)
val register_named_symbol : 'a context -> string -> typ -> unit

(** Test if a name is already associated with a symbol *)
val is_registered_name : 'a context -> string -> bool

(** Retrieve the symbol associated with a given name.  Raises [Not_found] if
    there is no such symbol. *)
val get_named_symbol : 'a context -> string -> symbol

(** Retrieve the name of a named symbol.  Evaluates to [None] for ordinary
    (non-named) symbols. *)
val symbol_name : 'a context -> symbol -> string option

val pp_symbol : 'a context -> Format.formatter -> symbol -> unit

val typ_symbol : 'a context -> symbol -> typ

val show_symbol : 'a context -> symbol -> string

val int_of_symbol : symbol -> int

val symbol_of_int : int -> symbol

val compare_symbol : symbol -> symbol -> int

module Symbol : sig
  type t = symbol
  val compare : t -> t -> int
  module Set : BatSet.S with type elt = symbol
  module Map : BatMap.S with type key = symbol
end

(** {2 Expressions} *)

type ('a, +'typ) expr
type 'a term = ('a, typ_arith) expr
type 'a formula = ('a, typ_bool) expr

val compare_expr : ('a,'typ) expr -> ('a,'typ) expr -> int
val compare_formula : 'a formula -> 'a formula -> int
val compare_term : 'a term -> 'a term -> int

val destruct : 'a context -> ('a, 'b) expr -> [
    | `Real of QQ.t
    | `App of symbol * (('a, typ_fo) expr list)
    | `Var of int * typ_arith
    | `Add of ('a term) list
    | `Mul of ('a term) list
    | `Binop of [ `Div | `Mod ] * ('a term) * ('a term)
    | `Unop of [ `Floor | `Neg ] * ('a term)
    | `Ite of ('a formula) * ('a,'b) expr * ('a,'b) expr
    | `Tru
    | `Fls
    | `And of ('a formula) list
    | `Or of ('a formula) list
    | `Not of ('a formula)
    | `Quantify of [`Exists | `Forall] * string * typ_fo * ('a formula)
    | `Atom of [`Eq | `Leq | `Lt] * ('a term) * ('a term)
    | `Proposition of [ `Var of int
                      | `App of symbol * (('b, typ_fo) expr) list ]
  ]

val expr_typ : 'a context -> ('a, 'b) expr -> typ

val free_vars : ('a, 'b) expr -> (int, typ_fo) BatHashtbl.t

val size : ('a, 'b) expr -> int

val mk_const : 'a context -> symbol -> ('a, 'typ) expr

val mk_app : 'a context -> symbol -> ('a, 'b) expr list -> ('a, 'typ) expr

val mk_var : 'a context -> int -> typ_fo -> ('a, 'typ) expr

(** Create an if-then-else expression. *)
val mk_ite : 'a context -> 'a formula -> ('a, 'typ) expr -> ('a, 'typ) expr ->
  ('a, 'typ) expr

(** Create an implication formula. *)
val mk_if : 'a context -> 'a formula -> 'a formula -> 'a formula

(** Create an if-and-only-if formula *)
val mk_iff : 'a context -> 'a formula -> 'a formula -> 'a formula

(** [substitute srk subst exp] replaces each occurrence of a variable
   symbol with De Bruijn [i] with the expression [subst i].  If [subst
   i] contains free variables, capture is avoided. *)
val substitute : 'a context ->
  (int -> ('a,'b) expr) -> ('a,'typ) expr -> ('a,'typ) expr

(** [substitute_const srk subst exp] replaces each occurrence of a
   constant symbol [s] with the expression [subst s].  If [subst s]
   contains free variables, capture is avoided.  Function symbols are
   not affected. *)
val substitute_const : 'a context ->
  (symbol -> ('a,'b) expr) -> ('a,'typ) expr -> ('a,'typ) expr

(** [substitute_map srk subst exp] replaces each occurrence of a
   constant symbol [s] in the domain of the map subst with the
   expression [subst s].  If [subst s] contains free variables,
   capture is avoided.  Function symbols are not affected. *)
val substitute_map : 'a context ->
  (('a,'b) expr Symbol.Map.t) -> ('a,'typ) expr -> ('a,'typ) expr

(** [substitute_sym srk subst exp] replaces each occurrence of a an
   application [f(e_0,...,e_n)] with the result of replacing the De
   Bruijn indices [0, ..., n] with [e_0, ..., e_n] in the expression
   [subst f].  If [subst f] contains free variables (beyond
   [0,...,n]), capture is avoided.  Constant symbols are treated as
   nullary function applications, and so are also replaced according
   to [subst]. *)
val substitute_sym : 'a context ->
  (symbol -> ('a,'b) expr) -> ('a,'typ) expr -> ('a,'typ) expr

val fold_constants : (symbol -> 'a -> 'a) -> ('b, 'c) expr -> 'a -> 'a

val symbols : ('a, 'b) expr -> Symbol.Set.t

(** {3 Expression rewriting} *)

(** A rewriter is a function that transforms an expression into another.  {b
    The transformation should preserve types}; if not, [rewrite] will fail. *)
type 'a rewriter = ('a, typ_fo) expr -> ('a, typ_fo) expr

(** Rewrite an expression.  The {i down} rewriter is applied to each
    expression going down the expression tree, and the {i up} rewriter is
    applied to each expression going up the tree. *)
val rewrite : 'a context -> ?down:('a rewriter) -> ?up:('a rewriter) ->
  ('a, 'typ) expr -> ('a, 'typ) expr

(** Convert to negation normal form ({i down} pass). *)
val nnf_rewriter : 'a context -> 'a rewriter

module Expr : sig
  val equal : ('a,'b) expr -> ('a,'b) expr -> bool
  val compare : ('a,'b) expr -> ('a,'b) expr -> int
  val hash : ('a,'b) expr -> int
  val pp : ?env:(string Env.t) ->
    'a context ->
    Format.formatter ->
    ('a, 'b) expr ->
    unit
  val refine : 'a context -> ('a, typ_fo) expr -> [ `Term of 'a term
                                                  | `Formula of 'a formula ]

  (** Convert an expression to a term.  Raise [Invalid_arg] if the
     expression is not a term. *)
  val term_of : 'a context -> ('a, typ_fo) expr -> 'a term

  (** Convert an expression to a formula.  Raise [Invalid_arg] if the
     expression is not a formula. *)
  val formula_of : 'a context -> ('a, typ_fo) expr -> 'a formula

  module HT : sig
    type ('a, 'typ, 'b) t
    val create : int -> ('a, 'typ, 'b) t
    val add : ('a, 'typ, 'b) t -> ('a, 'typ) expr -> 'b -> unit
    val replace : ('a, 'typ, 'b) t -> ('a, 'typ) expr -> 'b -> unit
    val remove : ('a, 'typ, 'b) t -> ('a, 'typ) expr -> unit
    val find : ('a, 'typ, 'b) t -> ('a, 'typ) expr -> 'b
    val mem : ('a, 'typ, 'b) t -> ('a, 'typ) expr -> bool
    val keys : ('a, 'typ, 'b) t -> (('a, 'typ) expr) BatEnum.t
    val values : ('a, 'typ, 'b) t -> 'b BatEnum.t
    val enum : ('a, 'typ, 'b) t -> (('a, 'typ) expr * 'b) BatEnum.t
  end

  module Set : sig
    type ('a, 'typ) t
    val empty : ('a, 'typ) t
    val add : ('a, 'typ) expr -> ('a, 'typ) t -> ('a, 'typ) t
    val union : ('a, 'typ) t -> ('a, 'typ) t -> ('a, 'typ) t
    val inter : ('a, 'typ) t -> ('a, 'typ) t -> ('a, 'typ) t
    val enum : ('a, 'typ) t -> (('a, 'typ) expr) BatEnum.t
    val mem : ('a, 'typ) expr -> ('a, 'typ) t -> bool
    val equal : ('a, 'typ) t -> ('a, 'typ) t -> bool
    val of_list : ('a, 'typ) expr list -> ('a, 'typ) t
    val elements : ('a, 'typ) t -> ('a, 'typ) expr list
    val filter : (('a, 'typ) expr -> bool) -> ('a, 'typ) t -> ('a, 'typ) t
  end

  module Map : sig
    type ('a, 'typ, 'b) t
    val empty : ('a, 'typ, 'b) t
    val is_empty : ('a, 'typ, 'b) t -> bool
    val add : ('a, 'typ) expr -> 'b -> ('a, 'typ, 'b) t -> ('a, 'typ, 'b) t
    val remove : ('a, 'typ) expr -> ('a, 'typ, 'b) t -> ('a, 'typ, 'b) t
    val filter : (('a, 'typ) expr -> 'b -> bool) ->
      ('a, 'typ, 'b) t ->
      ('a, 'typ, 'b) t
    val filter_map : (('a, 'typ) expr -> 'b -> 'c option) ->
      ('a, 'typ, 'b) t ->
      ('a, 'typ, 'c) t
    val map : ('b -> 'c) -> ('a, 'typ, 'b) t -> ('a, 'typ, 'c) t
    val find : ('a, 'typ) expr -> ('a, 'typ, 'b) t -> 'b
    val keys : ('a, 'typ, 'b) t -> (('a, 'typ) expr) BatEnum.t
    val values : ('a, 'typ, 'b) t -> 'b BatEnum.t
    val enum : ('a, 'typ, 'b) t -> (('a, 'typ) expr * 'b) BatEnum.t
    val merge : ((('a, 'typ) expr) -> 'b option -> 'c option -> 'd option) ->
      ('a, 'typ, 'b) t -> ('a, 'typ, 'c) t -> ('a, 'typ, 'd) t
    val fold : (('a, 'typ) expr -> 'b -> 'c -> 'c) -> ('a, 'typ, 'b) t -> 'c -> 'c
    val equal : ('b -> 'b -> bool) -> ('a, 'typ, 'b) t -> ('a, 'typ, 'b) t -> bool
  end
end

(** {2 Terms} *)

type ('a,'b) open_term = [
  | `Real of QQ.t
  | `App of symbol * (('b, typ_fo) expr list)
  | `Var of int * typ_arith
  | `Add of 'a list
  | `Mul of 'a list
  | `Binop of [ `Div | `Mod ] * 'a * 'a
  | `Unop of [ `Floor | `Neg ] * 'a
  | `Ite of ('b formula) * 'a * 'a
]

val mk_add : 'a context -> 'a term list -> 'a term
val mk_mul : 'a context -> 'a term list -> 'a term
val mk_div : 'a context -> 'a term -> 'a term -> 'a term
val mk_pow : 'a context -> 'a term -> int -> 'a term

(** C99 integer division.  Equivalent to truncate(x/y). *)
val mk_idiv : 'a context -> 'a term -> 'a term -> 'a term
val mk_mod : 'a context -> 'a term -> 'a term -> 'a term
val mk_real : 'a context -> QQ.t -> 'a term

val mk_zz : 'a context -> ZZ.t -> 'a term
val mk_int : 'a context -> int -> 'a term

val mk_zero : 'a context -> 'a term
val mk_one : 'a context -> 'a term
val mk_floor : 'a context -> 'a term -> 'a term
val mk_ceiling : 'a context -> 'a term -> 'a term

(** [truncate(t)] removes the fractional part of [t] (rounding it towards
    0).  *)
val mk_truncate : 'a context -> 'a term -> 'a term

(** Unary negation *)
val mk_neg : 'a context -> 'a term -> 'a term

(** Subtraction *)
val mk_sub : 'a context -> 'a term -> 'a term -> 'a term

val term_typ : 'a context -> 'a term -> typ_arith

module Term : sig
  type 'a t = 'a term
  val equal : 'a term -> 'a term -> bool
  val compare : 'a term -> 'a term -> int
  val hash : 'a term -> int
  val pp : ?env:(string Env.t) -> 'a context ->
    Format.formatter -> 'a term -> unit
  val show : ?env:(string Env.t) -> 'a context -> 'a term -> string
  val destruct : 'a context -> 'a term -> ('a term, 'a) open_term
  val eval : 'a context -> (('b, 'a) open_term -> 'b) -> 'a term -> 'b
  val eval_partial : 'a context -> (('b, 'a) open_term -> 'b option) -> 'a term -> 'b option
end

(** {2 Formulas} *)

type ('a,'b) open_formula = [
  | `Tru
  | `Fls
  | `And of 'a list
  | `Or of 'a list
  | `Not of 'a
  | `Quantify of [`Exists | `Forall] * string * typ_fo * 'a
  | `Atom of [`Eq | `Leq | `Lt] * ('b term) * ('b term)
  | `Proposition of [ `Var of int
                    | `App of symbol * (('b, typ_fo) expr) list ]
  | `Ite of 'a * 'a * 'a
]

val mk_forall : 'a context -> ?name:string -> typ_fo -> 'a formula -> 'a formula
val mk_exists : 'a context -> ?name:string -> typ_fo -> 'a formula -> 'a formula

(** Replace a constant symbol by a universally quantified variable. *)
val mk_forall_const : 'a context -> symbol -> 'a formula -> 'a formula

(** Replace a constant symbol by an existentially quantified variable. *)
val mk_exists_const : 'a context -> symbol -> 'a formula -> 'a formula

(** Replace all constant symbols that do not satisfy the given
   predicate by universally quantified variables. *)
val mk_forall_consts : 'a context -> (symbol -> bool) -> 'a formula -> 'a formula

(** Replace all constant symbols that do not satisfy the given
   predicate by existentially quantified variables. *)
val mk_exists_consts : 'a context -> (symbol -> bool) -> 'a formula -> 'a formula


val mk_and : 'a context -> 'a formula list -> 'a formula
val mk_or : 'a context -> 'a formula list -> 'a formula
val mk_not : 'a context -> 'a formula -> 'a formula
val mk_eq : 'a context -> 'a term -> 'a term -> 'a formula
val mk_lt : 'a context -> 'a term -> 'a term -> 'a formula
val mk_leq : 'a context -> 'a term -> 'a term -> 'a formula
val mk_true : 'a context -> 'a formula
val mk_false : 'a context -> 'a formula

(** Given a formula [phi], compute an equivalent formula without
   if-then-else terms.  [eliminate-ite] does not introduce new
   symbols or quantifiers. *)
val eliminate_ite : 'a context -> 'a formula -> 'a formula

(** Print a formula as a satisfiability query in SMTLIB2 format.
    The query includes function declarations and (check-sat).

    if named is true then ":named" attribute will be set to "fi"
    for each formula where i is the formulas index in the list of
    formulas to output. When using a text interface to an SMT solver
    this allows determining which formula belongs to the unsat core
    of the SMT query. The output will be a list formula names
    fi_0, ..., fi_k that correspond to the unsat core.

    If provided strings will store the mapping from Smtlib2 names to Srk symbols.
    This allows converting any Smtlib2 terms provided as a response (e.g. from get-model)
    back into Srk expressions with the proper symbols.
*)
val pp_smtlib2_gen : ?named:bool -> ?env:(string Env.t) -> ?strings:((string, symbol) Hashtbl.t) ->
    'a context -> Format.formatter -> ('a formula) list -> unit

(** Same as pp_smtlib2_gen but only has one unnamed assertions *)
val pp_smtlib2 : ?env:(string Env.t) -> 'a context ->
    Format.formatter -> 'a formula -> unit

(** Print an expression.  This variant of pp_expr avoids printing a symbol
    number (e.g., "x:5") for a symbol S (i.e., a program variable or function 
    name) if there does not exist any other symbol in the expression that has 
    the same name as S.  *)
val pp_expr_unnumbered : ?env:(string Env.t) -> 'a context -> 
    Format.formatter -> ('a, 'b) expr -> unit

module Formula : sig
  type 'a t = 'a formula
  val equal : 'a formula -> 'a formula -> bool
  val compare : 'a formula -> 'a formula -> int
  val hash : 'a formula -> int
  val pp : ?env:(string Env.t) -> 'a context ->
    Format.formatter -> 'a formula -> unit
  val show : ?env:(string Env.t) -> 'a context -> 'a formula -> string
  val destruct : 'a context -> 'a formula -> ('a formula, 'a) open_formula
  val eval : 'a context -> (('b, 'a) open_formula -> 'b) -> 'a formula -> 'b
  val eval_memo : 'a context -> (('b, 'a) open_formula -> 'b) -> 'a formula -> 'b
  val existential_closure : 'a context -> 'a formula -> 'a formula
  val universal_closure : 'a context -> 'a formula -> 'a formula
  val skolemize_free : 'a context -> 'a formula -> 'a formula
  val prenex : 'a context -> 'a formula -> 'a formula
end

(** {2 Contexts} *)

module type Context = sig
  type t (* magic type parameter unique to this context *)
  val context : t context
  type term = (t, typ_arith) expr
  type formula = (t, typ_bool) expr

  val mk_symbol : ?name:string -> typ -> symbol
  val mk_const : symbol -> (t, 'typ) expr
  val mk_app : symbol -> (t, 'b) expr list -> (t, 'typ) expr
  val mk_var : int -> typ_fo -> (t, 'typ) expr
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

module MakeContext () : Context

(** Create a context which simplifies expressions on the fly *)
module MakeSimplifyingContext () : Context

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
  val const : symbol -> (C.t, 'typ) expr
  val var : int -> typ_fo -> (C.t, 'typ) expr
end

(** A context table is a hash table mapping contents to values.  If a context
    is garbage collected, the corresponding entry in the table will be
    removed.  The values stored in a context table should have pointers back
    to their associated context.  *)
module ContextTable : sig
  type 'a t
  val create : int -> 'a t
  val add : 'a t -> 'b context -> 'a -> unit
  val replace : 'a t -> 'b context -> 'a -> unit
  val find : 'a t -> 'b context -> 'a
  val mem : 'a t -> 'b context -> bool
  val clear : 'a t -> unit
end

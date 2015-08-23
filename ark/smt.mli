open Syntax

exception Unknown_result

module type TranslationContext = sig
  include Syntax.BuilderContext
  include Syntax.EvalContext with type term := term and type formula := formula
  val const_typ : const_sym -> typ
end

module Make
    (Opt : sig val opts : (string * string) list end)
    () : sig

  type expr
  type func_decl

  type 'a open_expr = [
    | `Real of QQ.t
    | `App of func_decl * 'a list
    | `Var of int * typ_arith
    | `Add of 'a list
    | `Mul of 'a list
    | `Binop of [ `Div | `Mod ] * 'a * 'a
    | `Unop of [ `Floor | `Neg ] * 'a
    | `Tru
    | `Fls
    | `And of 'a list
    | `Or of 'a list
    | `Not of 'a
    | `Quantify of [`Exists | `Forall] * string * typ_arith * 'a
    | `Atom of [`Eq | `Leq | `Lt] * 'a * 'a
  ]

  val eval : ('a open_expr -> 'a) -> expr -> 'a
  val mk : expr open_expr -> expr

  val mk_add : expr list -> expr
  val mk_mul : expr list -> expr
  val mk_div : expr -> expr -> expr
  val mk_mod : expr -> expr -> expr
  val mk_var : int -> typ_arith -> expr
  val mk_real : QQ.t -> expr
  val mk_app : func_decl -> expr list -> expr
  val mk_const : func_decl -> expr
  val mk_floor : expr -> expr
  val mk_neg : expr -> expr
  val mk_sub : expr -> expr -> expr

  val mk_forall : ?name:string -> typ_arith -> expr -> expr
  val mk_exists : ?name:string -> typ_arith -> expr -> expr
  val mk_and : expr list -> expr
  val mk_or : expr list -> expr
  val mk_not : expr -> expr
  val mk_eq : expr -> expr -> expr
  val mk_lt : expr -> expr -> expr
  val mk_leq : expr -> expr -> expr
  val mk_true : expr
  val mk_false : expr
end

module MakeSolver
    (C : TranslationContext)
    (Opt : sig val opts : (string * string) list end)
    () : sig
  
  type solver
  type model

  (** May raise [Unknown_result]. *)
  val implies : C.formula -> C.formula -> bool

  (** May raise [Unknown_result]. *)
  val equiv : C.formula -> C.formula -> bool

  val is_sat : C.formula -> [ `Sat | `Unsat | `Unknown ]
  val get_model : C.formula -> [ `Sat of model | `Unsat | `Unknown ]
  val interpolate_seq : C.formula list ->
    [ `Sat of model | `Unsat of C.formula list | `Unknown ]

  module Solver : sig
    val mk_solver : unit -> solver
    val add : solver -> C.formula list -> unit
    val push : solver -> unit
    val pop : solver -> int -> unit
    val check : solver -> C.formula list -> [ `Sat | `Unsat | `Unknown ]
    val get_model : solver -> [ `Sat of model | `Unsat | `Unknown ]
  end

  module Model : sig
    val eval_int : model -> C.term -> ZZ.t
    val eval_real : model -> C.term -> QQ.t
    val sat : model -> C.formula -> bool
    val to_string : model -> string
  end

  val term_of : Z3.Expr.expr -> C.term
  val of_term : C.term -> Z3.Expr.expr
  val formula_of : Z3.Expr.expr -> C.formula
  val of_formula : C.formula -> Z3.Expr.expr
end

open Syntax

exception Unknown_result

type 'a open_expr = [
  | `Real of QQ.t
  | `App of Z3.FuncDecl.func_decl * 'a list
  | `Var of int * typ_fo
  | `Add of 'a list
  | `Mul of 'a list
  | `Binop of [ `Div | `Mod ] * 'a * 'a
  | `Unop of [ `Floor | `Neg ] * 'a
  | `Tru
  | `Fls
  | `And of 'a list
  | `Or of 'a list
  | `Not of 'a
  | `Ite of 'a * 'a * 'a
  | `Quantify of [`Exists | `Forall] * string * typ_fo * 'a
  | `Atom of [`Eq | `Leq | `Lt] * 'a * 'a
]

val typ_of_sort : Z3.Sort.sort -> typ_fo
val eval : ('a open_expr -> 'a) -> Z3.Expr.expr -> 'a

val z3_of_term : 'a context -> Z3.context -> 'a term -> Z3.Expr.expr
val z3_of_formula : 'a context -> Z3.context -> 'a formula -> Z3.Expr.expr

val formula_of_z3 : 'a context -> Z3.Expr.expr -> 'a formula
val term_of_z3 : 'a context -> Z3.Expr.expr -> 'a term

class type ['a] smt_model = object
  method eval_int : 'a term -> ZZ.t
  method eval_real : 'a term -> QQ.t
  method sat :  'a formula -> bool
  method to_string : unit -> string
end

class type ['a] smt_solver = object
  method add : ('a formula) list -> unit
  method push : unit -> unit
  method pop : int -> unit
  method reset : unit -> unit
  method check : ('a formula) list -> [ `Sat | `Unsat | `Unknown ]  
  method to_string : unit -> string
  method get_model : unit -> [ `Sat of 'a smt_model | `Unsat | `Unknown ]
  method get_unsat_core : ('a formula) list ->
    [ `Sat | `Unsat of ('a formula) list | `Unknown ]
end

class type ['a] smt_context = object
  method ark : 'a context
  method z3 : Z3.context
  method mk_solver : unit -> 'a smt_solver

  method of_term : 'a term -> Z3.Expr.expr
  method of_formula : 'a formula -> Z3.Expr.expr
  method term_of : Z3.Expr.expr -> 'a term
  method formula_of : Z3.Expr.expr -> 'a formula

  (** May raise [Unknown_result]. *)
  method implies : 'a formula -> 'a formula -> bool

  (** May raise [Unknown_result]. *)
  method equiv : 'a formula -> 'a formula -> bool

  method is_sat : 'a formula -> [ `Sat | `Unsat | `Unknown ]

  method get_model : 'a formula -> [ `Sat of 'a smt_model | `Unsat | `Unknown ]

  method qe_sat : 'a formula -> [ `Sat | `Unsat | `Unknown ]

  method qe : 'a formula -> 'a formula

  method interpolate_seq : 'a formula list ->
    [ `Sat of 'a smt_model | `Unsat of 'a formula list | `Unknown ]

  method optimize_box : 'a formula -> 'a term list -> [ `Sat of Interval.t list
						      | `Unsat
						      | `Unknown ]

  method load_smtlib2 : string -> 'a formula
end

val mk_context : 'a context -> (string * string) list -> 'a smt_context

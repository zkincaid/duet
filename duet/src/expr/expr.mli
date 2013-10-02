open Core

val format_expr : Format.formatter -> expr -> unit
val format_bexpr : Format.formatter -> bexpr -> unit
val show_expr : expr -> string
val show_bexpr : bexpr -> string
val expr_compare : expr -> expr -> int
val bexpr_compare : bexpr -> bexpr -> int
val expr_equal : expr -> expr -> bool
val bexpr_equal : bexpr -> bexpr -> bool

val add : expr -> expr -> expr
val sub : expr -> expr -> expr
val mul : expr -> expr -> expr
val div : expr -> expr -> expr
val modulo : expr -> expr -> expr
val neg : expr -> expr

val eval_binop : binop -> int -> int -> int

val iter_expr : (expr -> unit) -> (bexpr -> unit) -> expr -> unit
val iter_bexpr : (expr -> unit) -> (bexpr -> unit) -> bexpr -> unit
val get_type_expr : expr -> typ
val negate : bexpr -> bexpr
val implies : bexpr -> bexpr -> bexpr
val ge : expr -> expr -> bexpr
val gt : expr -> expr -> bexpr

val normalize : bexpr -> bexpr
val expr_as_bexpr : expr -> bexpr
val expr_of_int : int -> expr
val expr_zero : expr
val expr_one : expr
val expr_null : typ -> expr
val bexpr_true : bexpr
val bexpr_false : bexpr

val constant_bexpr : bexpr -> bool option
val is_constant_bexpr : bexpr -> bool
val simplify_bexpr : bexpr -> bexpr
val simplify_expr : expr -> expr
val bexpr_dnf : bexpr -> bexpr

val get_uses_expr : expr -> AP.Set.t
val get_uses_bexpr : bexpr -> AP.Set.t

val free_vars_expr : expr -> Var.Set.t
val free_vars_bexpr : bexpr -> Var.Set.t
val free_vars_ap : ap -> Var.Set.t

val accessed_expr : expr -> AP.Set.t
val accessed_bexpr : bexpr -> AP.Set.t
val accessed_ap : ap -> AP.Set.t

val subst_ap_expr : (AP.t -> AP.t) -> expr -> expr
val subst_ap_bexpr : (AP.t -> AP.t) -> bexpr -> bexpr
val subst_ap_ap : (AP.t -> AP.t) -> AP.t -> AP.t

val subst_expr_expr : (expr -> expr) -> expr -> expr
val subst_expr_bexpr : (expr -> expr) -> bexpr -> bexpr
val subst_expr_ap : (expr -> expr) -> AP.t -> AP.t

val subst_var_expr : (var -> var) -> expr -> expr
val subst_var_bexpr : (var -> var) -> bexpr -> bexpr
val subst_var_ap : (var -> var) -> ap -> ap

val psubst_var_expr : (var -> var option) -> expr -> expr option
val psubst_var_bexpr : (var -> var option) -> bexpr -> bexpr option
val psubst_var_ap : (var -> var option) -> ap -> ap option


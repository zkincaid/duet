

type var
type pvar
type bvar
type all_var = Variable of var | Pointer of pvar | Block of bvar

type boogie_var
type boogie_avar

val boogie_var_of_var : var -> boogie_var
val boogie_var_of_pvar : pvar -> boogie_var
val boogie_avar_of_bvar : bvar -> boogie_avar
val boogie_length_of_boogie_avar : boogie_avar -> boogie_var 


val var_name : var -> string
val pvar_name : pvar -> string
val bvar_name : bvar -> string

val boogie_var_name : boogie_var -> string
val boogie_avar_name : boogie_avar -> string
val boogie_avar_input_name : boogie_avar -> string
val boogie_avar_local_name : boogie_avar -> string

val var_to_svar : var -> Global.Ctx.t Srk.Syntax.arith_term
val pvarblock_to_svar : pvar -> Global.Ctx.t Srk.Syntax.arith_term
val pvaroffset_to_svar : pvar -> Global.Ctx.t Srk.Syntax.arith_term
val bvar_to_svar : bvar -> Global.Ctx.t Srk.Syntax.arith_term

val new_var : string -> var
val new_pvar : string -> pvar
val new_bvar : int -> bvar
val new_avar : string -> boogie_avar

val prime_var : var -> var
val prime_pvar : pvar -> pvar

val generate_new_bvar : boogie_avar list -> bvar

module Var : sig
  type t = BVar of boogie_var | BAVar of boogie_avar
    val compare : t -> t -> int
    val pp : Format.formatter -> t -> unit
    val show : t -> string
    val typ : t -> Srk.Syntax.typ_term
    val symbol_of : t -> Srk.Syntax.symbol
    val of_symbol : Srk.Syntax.symbol -> t option
    val is_global : t -> bool
    val hash : t -> int
    val equal : t -> t -> bool
end
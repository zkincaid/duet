open SrkSmtlib2Defs

val pp_constant : Format.formatter -> constant -> unit
val pp_symbol : Format.formatter -> symbol -> unit
val pp_index : Format.formatter -> index -> unit
val pp_identifier : Format.formatter -> identifier -> unit
val pp_sort : Format.formatter -> sort -> unit
val pp_qual_id : Format.formatter -> qual_id -> unit
val pp_term : Format.formatter -> term -> unit
val pp_model : Format.formatter -> model -> unit

val file_parse_term : string -> term
val string_parse_term : string -> term

val file_parse_model : string -> model
val string_parse_model : string -> model

val typ_of_sort : sort -> Syntax.typ

module MakeSMT2Srk(C : sig type t val context : t Syntax.context end) : sig
  val arith_term_of_smt : (symbol -> Syntax.symbol) -> term -> C.t Syntax.arith_term
  val arr_term_of_smt : (symbol -> Syntax.symbol) -> term -> C.t Syntax.arr_term
  val formula_of_smt : (symbol -> Syntax.symbol) -> term -> C.t Syntax.formula
  val expr_of_smt : (symbol -> Syntax.symbol) -> term -> (C.t, Syntax.typ_fo) Syntax.expr

  val model_of_smt : (symbol -> Syntax.symbol) -> model -> (Syntax.symbol * C.t Interpretation.value) list
end

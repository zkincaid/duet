type subscript = SAdd of string * int | SSVar of string

type expr =
    Product of expr list
  | Sum of expr list
  | Max of expr list
  | Min of expr list
  | Base_case of string * int
  | Output_variable of string * subscript
  | Input_variable of string
  | Rational of Mpq.t

type inequation =
    Equals of expr * expr
  | LessEq of expr * expr
  | GreaterEq of expr * expr

type fweight = Mpq.t
type weight = Inf | Fin of fweight

val maxPlusTests : unit -> unit
val minPlusTests : unit -> unit

val maxPlusSolveForBoundingMatricesFromMatrix :
  weight array array -> weight array array * weight array array

val minPlusSolveForBoundingMatricesFromMatrix :
  weight array array -> weight array array * weight array array

val maxPlusSolveForInequationsFromMatrix :
  weight array array -> string array -> string -> inequation list

val minPlusSolveForInequationsFromMatrix :
  weight array array -> string array -> string -> inequation list


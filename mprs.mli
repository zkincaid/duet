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

(* An infinite weight is negative infinity in the max-plus semiring, and
   positive infinity in the min-plus semiring. *)
type weight = Inf | Fin of fweight

val maxPlusTests : unit -> unit
val minPlusTests : unit -> unit

(* The following four functions assume that we're given a max-plus or min-plus 
   matrix equation; they take the matrix of the equation as their only input. *) 

(* The following two functions return a pair of matrices representing
   the slopes and intercepts of a bound expression. *)

val maxPlusSolveForBoundingMatricesFromMatrix :
  weight array array -> weight array array * weight array array

val minPlusSolveForBoundingMatricesFromMatrix :
  weight array array -> weight array array * weight array array

(* As a convenience, the following two functions return a list of 
   inequations instead of a pair of slope and intercept matrices.  *)

val maxPlusSolveForInequationsFromMatrix :
  weight array array -> string array -> string -> inequation list

val minPlusSolveForInequationsFromMatrix :
  weight array array -> string array -> string -> inequation list



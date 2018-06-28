(* In MPRS, the numeric type used by max-plus/min-plus matrix recurrences
   is called "weight". *)

(* A finite weight is a GMP multi-precision rational *)
type fweight = Mpq.t

(* A weight is either a finite weight or an infinite weight. *)
(* An infinite weight is negative infinity in the max-plus semiring, and
   positive infinity in the min-plus semiring. *)
type weight = Inf | Fin of fweight

(* The following types describe max-plus/min-plus expressions and
   inequations; they are used to specify bounds on recurrence relations,
   i.e., the output of MPRS; in the future, they may also be used to specify 
   the recurrences themselves, i.e., the input to MPRS. *)
(* -------------------------------------------------------------------- *)
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
(* -------------------------------------------------------------------- *)
(* The folowing functions are used only for testing and debugging *)
val maxPlusMatrixTest : weight array array -> weight array array * weight array array
val minPlusMatrixTest : weight array array -> weight array array * weight array array
val maxPlusMatrixVectorTest : weight array array -> weight array -> (weight array array * weight array) * (weight array array * weight array)
val minPlusMatrixVectorTest : weight array array -> weight array -> (weight array array * weight array) * (weight array array * weight array)

val verbose : bool ref
(* -------------------------------------------------------------------- *)

(* The remainder of this file gives the main interface functions of MPRS: *)

(* The following four functions assume that we're given a max-plus or min-plus 
   matrix equation of the form x' = A x; they take the matrix A as their only
   input. *) 

(* The following two functions return a pair of matrices representing
   the slopes and intercepts of a bound expression. *)

val maxPlusSolveForBoundingMatricesFromMatrix :
  weight array array -> weight array array * weight array array

val minPlusSolveForBoundingMatricesFromMatrix :
  weight array array -> weight array array * weight array array

(* The following two functions return a list of inequations (using the 
   algebraic data types defined above) instead of a pair of slope and 
   intercept matrices.  In order to build the inequations, we need to
   have an array of variable names and a name for the loop counter variable. *)

val maxPlusSolveForInequationsFromMatrix :
  weight array array -> string array -> string -> inequation list

val minPlusSolveForInequationsFromMatrix :
  weight array array -> string array -> string -> inequation list

(* The following four are like the above four, except that they take both a
   matrix A and vector b, representing the equation x' = A x + b.  *)

(* The following two return a pair of pairs; the first pair is a slope
   matrix and slope vector, and the second pair is an intercept matrix
   and an intercept vector. *)

val maxPlusSolveForBoundingMatricesFromMatrixAndVector :
  weight array array -> weight array -> (weight array array * weight array) * (weight array array * weight array)

val minPlusSolveForBoundingMatricesFromMatrixAndVector :
  weight array array -> weight array -> (weight array array * weight array) * (weight array array * weight array)

(* These final two functions build inequations; so, you must supply a matrix,
   a vector, an array of variable names, and a loop counter name. *)

val maxPlusSolveForInequationsFromMatrixAndVector :
  weight array array -> weight array -> string array -> string -> inequation list

val minPlusSolveForInequationsFromMatrixAndVector :
  weight array array -> weight array -> string array -> string -> inequation list



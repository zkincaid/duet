open Syntax

(** Various operations for the vector space [int -> QQ] *)

(** Raised for unsolvable systems of linear equations *)
exception No_solution

exception Nonlinear

module type Vector = sig
  type t
  type dim
  type scalar

  val equal : t -> t -> bool
  val add : t -> t -> t
  val scalar_mul : scalar -> t -> t
  val negate : t -> t
  val dot : t -> t -> scalar

  val zero : t
  val is_zero : t -> bool
  val add_term : scalar -> dim -> t -> t
  val of_term : scalar -> dim -> t

  val enum : t -> (scalar * dim) BatEnum.t
  val of_enum : (scalar * dim) BatEnum.t -> t
  val coeff : dim -> t -> scalar

  val pivot : dim -> t -> scalar * t
end

module ZZVector : sig
  include Vector with type dim = int and type scalar = ZZ.t
  val compare : t -> t -> int
  val pp : Format.formatter -> t -> unit
  val show : t -> string
end

module QQVector : sig
  include Vector with type dim = int and type scalar = QQ.t
  val compare : t -> t -> int
  val pp : Format.formatter -> t -> unit
  val show : t -> string
end

module QQMatrix : sig
  type t
  type dim = int
  type scalar = QQ.t

  val equal : t -> t -> bool
  val add : t -> t -> t
  val scalar_mul : scalar -> t -> t
  val mul : t -> t -> t

  val zero : t

  val row : dim -> t -> QQVector.t

  val rowsi : t -> (dim * QQVector.t) BatEnum.t

  val add_row : dim -> QQVector.t -> t -> t

  val add_column : dim -> QQVector.t -> t -> t

  val add_entry : dim -> dim -> QQ.t -> t -> t

  val pivot : dim -> t -> QQVector.t * t

  val transpose : t -> t

  val entry : dim -> dim -> t -> scalar

  val entries : t -> (dim * dim * scalar) BatEnum.t

  val nb_rows : t -> int
  val nb_columns : t -> int

  val pp : Format.formatter -> t -> unit
  val show : t -> string
end

module type AbelianGroup = sig
  type t
  val equal : t -> t -> bool
  val add : t -> t -> t
  val negate : t -> t
  val zero : t
end

module type Ring = sig
  type t
  val equal : t -> t -> bool
  val add : t -> t -> t
  val negate : t -> t
  val zero : t
  val mul : t -> t -> t
  val one : t
end

(** Lift a map type over a ring to a left-module *)
module RingMap
    (M : sig
       type 'a t
       type key

       val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
       val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
       val enum : 'a t -> (key * 'a) BatEnum.t
       val map : ('a -> 'b) -> 'a t -> 'b t
       val find : key -> 'a t -> 'a
       val add : key -> 'a -> 'a t -> 'a t
       val remove : key -> 'a t -> 'a t
       val empty : 'a t
       val merge : (key -> 'a option -> 'b option -> 'c option) ->
         'a t ->
         'b t ->
         'c t
     end)
    (R : Ring) : Vector with type t = R.t M.t
                         and type dim = M.key
                         and type scalar = R.t


(** As RingMap, except with ExprMap as the map type *)
module type ExprRingMap = sig
  type scalar
  type 'a t = ('a, typ_arith, scalar) Expr.Map.t

  val zero : 'a t
  val one : 'a context -> 'a t
  val add : 'a t -> 'a t -> 'a t
  val mul : 'a context -> 'a t -> 'a t -> 'a t
  val scalar_mul : scalar -> 'a t -> 'a t
  val negate : 'a t -> 'a t
  val const : 'a context -> scalar -> 'a t
  val term : scalar -> 'a term -> 'a t
  val add_term : scalar -> 'a term -> 'a t -> 'a t
  val enum : 'a t -> ('a term * scalar) BatEnum.t
  val of_enum : ('a term * scalar) BatEnum.t -> 'a t
  val coeff : 'a term -> 'a t -> scalar
  val pivot : 'a term -> 'a t -> scalar * 'a t
end

module MakeExprRingMap (R : Ring) : ExprRingMap with type scalar = R.t

(** Vector of terms with rational coefficients. *)
module ExprQQVector : sig
  include ExprRingMap with type scalar = QQ.t
  val of_term : 'a context -> 'a term -> 'a t
  val term_of : 'a context -> 'a t -> 'a term
end


(** [solve_exn mat b] computes a rational vector [x] such that [mat*x =
    b]. Raises [No_solution] if there is no solution. *)
val solve_exn : QQMatrix.t -> QQVector.t -> QQVector.t

(** Given a predicate on dimensions and a list of terms (all implicitly equal
    to zero), orient the equations as rewrite rules that eliminate dimensions
    that don't satisfy the predicate. *)
val orient : (int -> bool) -> QQVector.t list -> (int * QQVector.t) list

val vector_right_mul : QQMatrix.t -> QQVector.t -> QQVector.t

val solve : QQMatrix.t -> QQVector.t -> QQVector.t option

(** Given two matrices A and B, compute matrices C and D such that CA = DB is a
    basis for the intersection of the rowspaces of A and B *)
val intersect_rowspace : QQMatrix.t -> QQMatrix.t -> (QQMatrix.t * QQMatrix.t)

(** Given two matrices A and B, compute a matrix C such that CB = A (if one
    exists).  C exists when the rowspace of B is contained in the rowspace of
    A.  If A and B are invertible, then C is exactly AB^{-1}. *)
val divide_right : QQMatrix.t -> QQMatrix.t -> QQMatrix.t option

(** {2 Affine terms} *)

(** Various operations for manipulating affine terms over symbols, represented
    as rational vectors *)

(** Map a symbol to a dimension.  The following equations hold:
    - [sym_of_dim (dim_of_sym sym) = Some sym]
    - [sym_of_dim const_dim = None] *)
val sym_of_dim : int -> symbol option

(** Map a dimension to symbol.  The following equations hold:
    - [sym_of_dim (dim_of_sym sym) = Some sym]
    - [sym_of_dim const_dim = None] *)
val dim_of_sym : symbol -> int

(** Dimension for representing the coefficient of the constant 1. *)
val const_dim : int

(** Representation of a rational number as an affine term.  The equation
    [const_of_linterm (const_linterm qq) = Some qq] must hold. *)
val const_linterm : QQ.t -> QQVector.t

(** Convert an affine term to a rational number, if possible.  The equation
    [const_of_linterm (const_linterm qq) = Some qq] must hold. *)
val const_of_linterm : QQVector.t -> QQ.t option

(** Convert a rational vector representing an affine term.  Raises [Nonlinear]
    if the input term is non-linear. *)
val linterm_of : 'a context -> 'a term -> QQVector.t

(** Convert a rational vector to an affine term.  The equation [of_linterm ark
    (linterm_of ark t) = t] must hold. *)
val of_linterm : 'a context -> QQVector.t -> 'a term

(** Pretty-print an affine term *)
val pp_linterm : 'a context -> Format.formatter -> QQVector.t -> unit

(** [evaluate_linterm env t] evaluates the affine term t in the environment
    [env] *)
val evaluate_linterm : (symbol -> QQ.t) -> QQVector.t -> QQ.t

(** Count the number of dimensions with non-zero coefficients *)
val linterm_size : QQVector.t -> int

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
  val compare : t -> t -> int
  val add : t -> t -> t
  val scalar_mul : scalar -> t -> t
  val negate : t -> t
  val dot : t -> t -> scalar

  val zero : t
  val add_term : scalar -> dim -> t -> t
  val of_term : scalar -> dim -> t

  val enum : t -> (scalar * dim) BatEnum.t
  val of_enum : (scalar * dim) BatEnum.t -> t
  val coeff : dim -> t -> scalar

  val pivot : dim -> t -> scalar * t

  val pp : Format.formatter -> t -> unit
  val show : t -> string
end

module ZZVector : Vector with type dim = int and type scalar = ZZ.t
module QQVector : Vector with type dim = int and type scalar = QQ.t

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

  val add_row : dim -> QQVector.t -> t -> t

  val add_column : dim -> QQVector.t -> t -> t

  val pivot : dim -> t -> QQVector.t * t

  val transpose : t -> t

  val entry : dim -> dim -> t -> scalar

  val entries : t -> (dim * dim * scalar) BatEnum.t

  val pp : Format.formatter -> t -> unit
  val show : t -> string
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

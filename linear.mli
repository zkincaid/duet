open Syntax

(** Various operations for the vector space [int -> QQ] *)

(** Raised for unsolvable systems of linear equations *)
exception No_solution
  
module type Context = sig
  val const_typ : const_sym -> typ
  val pp_const : Format.formatter -> const_sym -> unit
  include Smt.TranslationContext
end

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
  val add_term : scalar -> dim -> t -> t
  val of_term : scalar -> dim -> t

  val enum : t -> (scalar * dim) BatEnum.t
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

val vector_right_mul : QQMatrix.t -> QQVector.t -> QQVector.t

val solve : QQMatrix.t -> QQVector.t -> QQVector.t option

(** Operations on rings. *)

(** Signature of rings *)
module type S = sig
  type t
  val equal : t -> t -> bool
  val add : t -> t -> t
  val negate : t -> t
  val zero : t
  val mul : t -> t -> t
  val one : t
end

module type Vector = sig
  type t
  type dim
  type scalar
  val equal : t -> t -> bool
  val add : t -> t -> t
  val scalar_mul : scalar -> t -> t
  val negate : t -> t
  val sub : t -> t -> t
  val dot : t -> t -> scalar
  val zero : t
  val is_zero : t -> bool
  val add_term : scalar -> dim -> t -> t
  val of_term : scalar -> dim -> t
  val enum : t -> (scalar * dim) BatEnum.t
  val of_enum : (scalar * dim) BatEnum.t -> t
  val of_list : (scalar * dim) list -> t
  val coeff : dim -> t -> scalar
  val pivot : dim -> t -> scalar * t
end

module type Matrix = sig
  type t
  type dim = int
  type scalar
  type vector

  val equal : t -> t -> bool
  val add : t -> t -> t
  val scalar_mul : scalar -> t -> t
  val mul : t -> t -> t

  val zero : t

  val identity : dim list -> t

  val row : dim -> t -> vector

  val rowsi : t -> (dim * vector) BatEnum.t

  val min_row : t -> dim * vector

  val add_row : dim -> vector -> t -> t

  val add_column : dim -> vector -> t -> t

  val add_entry : dim -> dim -> scalar -> t -> t

  val pivot : dim -> t -> vector * t

  val transpose : t -> t

  val entry : dim -> dim -> t -> scalar

  val entries : t -> (dim * dim * scalar) BatEnum.t

  val row_set : t -> SrkUtil.Int.Set.t
  val column_set : t -> SrkUtil.Int.Set.t

  val nb_rows : t -> int
  val nb_columns : t -> int

  val map_rows : (vector -> vector) -> t -> t

  (** [vector_right_mul m v] computes [m*v] *)
  val vector_right_mul : t -> vector -> vector

  (** [vector_left_mul v m] computes [(v^t)*m] *)
  val vector_left_mul : vector -> t -> vector

  val of_dense : scalar array array -> t
end

module type Map = sig
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
end

(** Lift a map type over a ring to a left-module *)
module RingMap
    (M : Map)
    (R : S) : Vector with type t = R.t M.t
                      and type dim = M.key
                      and type scalar = R.t

module MakeVector (R : S) : Vector with type scalar = R.t
                                    and type dim = int
                                    and type t = RingMap(SrkUtil.Int.Map)(R).t

module MakeMatrix (R : S) : sig
  include Matrix with type scalar = R.t
                  and type vector = MakeVector(R).t
  val pp : (Format.formatter -> scalar -> unit) -> Format.formatter -> t -> unit
end


(** Ultimately periodic sequences.  An ultimately periodic sequence is an
    infinite sequence consisting of a finite transient phase and an infinite
    periodic phase (with finite period).  Ring operations are pointwise:
    {ul
    {- [(f+g)(i) = f(i) + g(i)] }
    {- [(f*g)(i) = f(i) * g(i)] (Hadamard product) }
    {- [(-f)(i) = -f(i)] }
    {- [(0)(i) = 0] }
    {- [(1)(i) = 1] } } *)
module MakeUltPeriodicSeq (R : S) : sig
  include S
  val pp : (Format.formatter -> R.t -> unit) -> Format.formatter -> t -> unit

  (** [make t p] constructs an ultimately periodic sequence *)
  val make : R.t list -> R.t list -> t

  (** Retrieve the transient part of a sequence *)
  val transient : t -> R.t list

  (** Retrieve the periodic part of a sequence *)
  val periodic : t -> R.t list

  (** Enumerate the sequence. *)
  val enum : t -> R.t BatEnum.t

  val period_len : t -> int
  val transient_len : t -> int
end

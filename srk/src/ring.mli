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

(** Sparse vectors of infinite dimension. *)
module type Vector = sig
  type t
  type dim
  type scalar

  (** Vector equality. *)
  val equal : t -> t -> bool

  (** Vector addition. *)
  val add : t -> t -> t

  (** Multiply a vector by a scalar. *)
  val scalar_mul : scalar -> t -> t

  (** Additive inverse of a vector. *)
  val negate : t -> t

  (** Vector subtraction. *)
  val sub : t -> t -> t

  (** Inner product: [dot u v = sum_i (u_i * v_i)]. *)
  val dot : t -> t -> scalar

  (** The vector with all zero entries. *)
  val zero : t

  (** Is the given vector the zero vector? *)
  val is_zero : t -> bool

  (** [add_term a i v] adds [a] to the [i]th position of [v]. *)
  val add_term : scalar -> dim -> t -> t

  (** [of_term a i] is the all-zero vector except has [a] at position [i]. *)
  val of_term : scalar -> dim -> t

  (** Enumerate over all (non-zero) entries of a vector and their position. *)
  val enum : t -> (scalar * dim) BatEnum.t

  (** Convert an enumeration into a vector.  Satisfies [of_enum (enum
     v) = v], but not necessarily [enum (of_enum e) = e]; equivalent
     to [add_term a i] over all [(a,i)] in the given enumeration so
     (1) zero entries are suppressed and (2) if the enumeration
     contains multiple entries for the samae position, those entries
     are added. *)
  val of_enum : (scalar * dim) BatEnum.t -> t

  (** See [of_enum]. *)
  val of_list : (scalar * dim) list -> t

  (** [coeff i v] finds the entry at the [i]th position of [v]. *)
  val coeff : dim -> t -> scalar

  (** [pivot i v] find the entry at the [i]th position of [v], and the
     result of removing the [i]th position (replacing it with 0).  If
     [(a,v') = pivot i v], then [add_term a i v' = v].  *)
  val pivot : dim -> t -> scalar * t

  val pop : t -> (dim * scalar) * t

  val map : (dim -> scalar -> scalar) -> t -> t
  val merge : (dim -> scalar -> scalar -> scalar) -> t -> t -> t

  val hash : (dim * scalar -> int) -> t -> int
  val compare : (scalar -> scalar -> int) -> t -> t -> int
  val fold : (dim -> scalar -> 'a -> 'a) -> t -> 'a -> 'a
end

(** Sparse matrices of infinite dimension. *)
module type Matrix = sig
  type t
  type dim = int
  type scalar
  type vector

  (** Matrix equality. *)
  val equal : t -> t -> bool

  (** Matrix addition. *)
  val add : t -> t -> t

  (** Multiply a matrix by a scalar. *)
  val scalar_mul : scalar -> t -> t

  (** Matrix multiplication. *)
  val mul : t -> t -> t

  (** Matrix with all zero entries. *)
  val zero : t

  (** [identity dims] is the identity matrix restricted to the
     dimensions in dims; that is, the matrix with M with M{_ij} = 1 if
     i in dims and i = j, and M{_ij} = 0 otherwise. *)
  val identity : dim list -> t

  (** [row i mat] finds the [i]th row vector in [mat]. *)
  val row : dim -> t -> vector

  (** [column j mat] finds the [j]th row vector in [mat]. *)
  val column : dim -> t -> vector
  
  (** Enumerate over the (non-zero) rows of a matrix and their
     positions. *)
  val rowsi : t -> (dim * vector) BatEnum.t

  (** Find the (non-zero) row at the least position. *)
  val min_row : t -> dim * vector

  (** [add_row i vec mat] adds [vec] (considered as a row vector) to
     the [i]th row of [mat].  Equivalent to adding [mat + n],
     where [n] is a matrix that is zero everywhere except the [i]th
     row, which is [vec]. *)
  val add_row : dim -> vector -> t -> t

  (** [add_column i vec mat] adds [vec] (considered as a column
     vector) to the [j]th column of [mat].  Equivalent to [mat + n],
     where [n] is a matrix that is zero everywhere except the [j]th
     column, which is [vec]. *)
  val add_column : dim -> vector -> t -> t

  (** [add_entry i j a mat] adds [a] to the [(i,j)]th position of [mat]. *)
  val add_entry : dim -> dim -> scalar -> t -> t

  (** [pivot i mat] finds the [i]th row of [mat] as well as the matrix
     obtained by removing the [i]th row (i.e., replacing it with a
     zero row).  If [(v,mat') = pivot i mat], then [add_row i v mat' =
     mat]. *)
  val pivot : dim -> t -> vector * t

  (** [pivot_column i mat] finds the [i]th column of [mat] as well as the matrix
     obtained by removing the [i]th column (i.e., replacing it with a
     zero column).  If [(v,mat') = pivot i mat], then [add_column i v mat' =
     mat]. *)
  val pivot_column : dim -> t -> vector * t

  (** [transpose mat] is a matrix [mat*] with [mat*]{_ij} [= mat]{_ji}. *)
  val transpose : t -> t

  (** [entry i j mat] is the (i,j)th position of [mat]. *)
  val entry : dim -> dim -> t -> scalar

  (** Enumerate over all (non-zero) entries of a matrix and their positions *)
  val entries : t -> (dim * dim * scalar) BatEnum.t

  (** Set of positions corresponding to (non-zero) rows of a matrix *)
  val row_set : t -> SrkUtil.Int.Set.t

  (** Set of positions corresponding to (non-zero) columns of a matrix *)
  val column_set : t -> SrkUtil.Int.Set.t

  (** Number of (non-zero) rows *)
  val nb_rows : t -> int

  (** Number of (non-zero) columns *)
  val nb_columns : t -> int

  (** [map_rows f mat] computes a matrix [mat'] whose [i]th row is [f
     mat_i], where [mat_i] denotes the [i]th row of [mat].  Assumes
     that the function [f] is zero-strict ([f zero] = zero). *)
  val map_rows : (vector -> vector) -> t -> t

  (** [vector_right_mul m v] computes [m*v] *)
  val vector_right_mul : t -> vector -> vector

  (** [vector_left_mul v m] computes [(v^t)*m] *)
  val vector_left_mul : vector -> t -> vector

  (** Compute an equivalent sparse matrix from a dense representation *)
  val of_dense : scalar array array -> t

  (** [dense_of mat m n] computes the dense m-by-n matrix [d] where
     [d]{_ij} [= mat]{_ij}. *)
  val dense_of : t -> int -> int -> scalar array array

  (** Given vectors v{_0},v{_1},v{_2},...,v{_n} create a matrix where row [i] is v{_i} *)
  val of_rows : vector list -> t

  (** Given two matrices M and N, M and N into a single matrix, using
      the even columns for M and the odd columns for N *)
  val interlace_columns : t -> t -> t
end

(** Lift a map type over a ring to a left-module *)
module RingMap
    (K : BatInterfaces.OrderedType)
    (R : S) : Vector with type dim = K.t
                      and type scalar = R.t

(** Sparse vectors of infinite dimension, with entries drawn from a
   given ring. *)
module MakeVector (R : S) : sig
  include Vector with type scalar = R.t
                  and type dim = int
                  and type t = SparseMap.Make(SrkUtil.Int)(R).t

  (** Combine two vectors u and v into a single vector, using the even
     coordinates for u and the odd coordinates for v *)
  val interlace : t -> t -> t

  (** Reverse the operation of [interlace] *)
  val deinterlace : t -> (t * t)
end

(** Sparse matrices of infinite dimension, with entries drawn from a
   given ring. *)
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

  (** Length of the period of a sequence *)
  val period_len : t -> int

  (** Length of the transient part of a sequence *)
  val transient_len : t -> int
end

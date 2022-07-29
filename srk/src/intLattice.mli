
(** A lattice is the ZZ-span of a finite set of QQ-vectors.
    When the set of generators is empty, the lattice is the zero lattice.
*)
type t

(** [hermitize ordering generators] computes a basis B that is the 
    row-Hermite normal form of [generators] considered as rows of a matrix.
    A vector is considered as a row in the matrix by ordering its dimensions
    according to [ordering], with the smallest dimension appearing on the right.
    By default, [ordering] is the usual ordering on integers, so the constant
    dimension is last.
*)
val hermitize : ?ordering: (Linear.QQVector.dim -> Linear.QQVector.dim -> int)
                -> Linear.QQVector.t list -> t

(** Obtain the basis of the lattice. The zero lattice has an empty basis. *)
val basis : t -> Linear.QQVector.t list

(** Recompute a basis for the lattice according to a new order on dimensions *)
val reorder : (Linear.QQVector.dim -> Linear.QQVector.dim -> int) -> t -> t

(** [member v L] = true iff v is a member of the lattice L. *)
val member : Linear.QQVector.t -> t -> bool

(** [project p t] computes the projection of the lattice onto the dimensions
    marked true by [p].
 *)
val project : t -> (int -> bool) -> t

val pp : Format.formatter -> t -> unit

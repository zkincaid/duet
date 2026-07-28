
type unreduced
type hnf

(** A lattice is the ZZ-span of a finite set of QQ-vectors.
    When the set of generators is empty, the lattice is the zero lattice.
    The constant dimension is treated the same as any other dimension
    and has no special interpretation, so this can be used to compute
    the HNF of a constraint matrix.

    A lattice can be an unreduced lattice (unreduced t) or in HNF (hnf t).
 *)
type 'a t

(** [generators t] returns the generators of [t].
    An empty list denotes {0}, i.e., the zero lattice.
*)
val generators: 'a t -> Linear.QQVector.t list

val of_generators: Linear.QQVector.t list -> unreduced t

(** [hermitize compare t] is the row-HNF of the generators of [t]
    considered as rows of a matrix, with the smallest dimension according to
    [compare] in the rightmost column. The default is [Int.compare], so
    the constant dimension is rightmost.
*)
val hermitize: ?compare:(int -> int -> int) -> 'a t -> hnf t

val forget: hnf t -> unreduced t

(** [member v t] = true iff v is a member of the lattice L. *)
val member : Linear.QQVector.t -> hnf t -> bool

(** The highest dimension that appears in some generator. *)
val max_dim : 'a t -> Linear.QQVector.dim option

(** [project_as_dual keep t] interprets the generators of [t] as constraints
    of a mixed-integer lattice, and computes the constraints for the projection
    of this lattice onto the dimensions marked true by [keep].
*)
val project_as_dual : keep:(Linear.QQVector.dim -> bool) -> 'a t -> hnf t

(** [project keep t] projects the generators of [t] onto dimensions marked true
    by [keep].
 *)
val project: keep:(Linear.QQVector.dim -> bool) -> 'a t -> unreduced t

(** The zero lattice *)
val bottom : unreduced t

val sum : 'a t -> 'a t -> unreduced t

val intersect : 'a t -> 'a t -> hnf t

val subset : 'a t -> hnf t -> bool

val equal : hnf t -> hnf t -> bool

val pp : (Format.formatter -> int -> unit) -> Format.formatter -> 'a t -> unit

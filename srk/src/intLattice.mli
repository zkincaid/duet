
(** A lattice is a set ZZ B, where B is a finite set of vectors in QQ^n *)
type t

(** [ordering] is the ordering on dimensions that Hermite Normal Form is 
    computed with respect to.
    By default, the constant dimension is last.
*)
val lattice_of : ?ordering: (Linear.QQVector.dim -> Linear.QQVector.dim -> int)
                 -> Linear.QQVector.t list -> t

(** basis L = (d, B), where L = ZZ (1/d B) = { \sum_i (1/d b_i) : b_i in B }
    and B is a basis in Hermite normal form.
*)
val basis : t -> ZZ.t * Linear.ZZVector.t list

val pp : Format.formatter -> t -> unit

val pp_term : (Format.formatter -> int -> unit) -> Format.formatter -> t -> unit

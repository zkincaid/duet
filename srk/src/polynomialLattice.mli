open Polynomial

(** A polynomial lattice L is of the form QQ[X] Z + ZZ B,
    where Z is an ideal and B is a basis (i.e., linearly independent set).
    When B is the empty set, ZZ B = {0}, and similarly for QQ[X] Z.
*)
type t

val make : Ideal.t -> QQXs.t list -> t

val member : QQXs.t -> t -> bool

val sum : t -> t -> t

val intersect : t -> t -> t

(* TODO: val project : (Linear.QQVector.dim -> bool) -> t -> t *)

val pp : (Format.formatter -> int -> unit)
         -> Format.formatter -> t -> unit

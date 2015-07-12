open Apak
include Putil.Ordered with type t = Mpqf.t

val equal : t -> t -> bool
val leq : t -> t -> bool
val lt : t -> t -> bool

val hash : t -> int

val add : t -> t -> t
val mul : t -> t -> t
val zero : t
val one : t
val negate : t -> t
val inverse : t -> t

val sub : t -> t -> t
val exp : t -> int -> t

val numerator : t -> ZZ.t
val denominator : t -> ZZ.t
val to_zz : t -> ZZ.t option
val to_zzfrac : t -> ZZ.t * ZZ.t

val of_string : string -> t
val of_int : int -> t
val of_zz : ZZ.t -> t
val of_frac : int -> int -> t
val of_zzfrac : ZZ.t -> ZZ.t -> t
val of_float : float -> t

val min : t -> t -> t
val max : t -> t -> t
val abs : t -> t

val nudge_up : ?accuracy:int -> t -> t
val nudge_down : ?accuracy:int -> t -> t
val nudge : ?accuracy:int -> t -> t * t

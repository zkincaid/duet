type t

val compare : t -> t -> int
val equal : t -> t -> bool
val pp : Format.formatter -> t -> unit
val show : t -> string

val make : QQ.t option -> QQ.t option -> t
val make_bounded : QQ.t -> QQ.t -> t
val top : t
val bottom : t
val const : QQ.t -> t
val zero : t
val const_of : t -> QQ.t option

val negate : t -> t

val mul : t -> t -> t
val div : t -> t -> t
val modulo : t -> t -> t
val add : t -> t -> t
val floor : t -> t

val join : t -> t -> t
val meet : t -> t -> t
val leq : t -> t -> bool

val is_nonnegative : t -> bool
val is_nonpositive : t -> bool
val is_negative : t -> bool
val is_positive : t -> bool
val elem : QQ.t -> t -> bool

val lower : t -> QQ.t option
val upper : t -> QQ.t option

(*
val of_apron : Apron.Interval.t -> t
val apron_of : t -> Apron.Interval.t
 *)

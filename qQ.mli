(** Unbounded rationals *)

type t = Mpqf.t

val pp : Format.formatter -> t -> unit
val show : t -> string

val compare : t -> t -> int
val equal : t -> t -> bool
val leq : t -> t -> bool
val lt : t -> t -> bool

val hash : t -> int

val add : t -> t -> t
val mul : t -> t -> t
val div : t -> t -> t
val idiv : t -> t -> ZZ.t
val modulo : t -> t -> t
val gcd : t -> t -> t
val lcm : t -> t -> t
val zero : t
val one : t
val negate : t -> t
val inverse : t -> t
val floor : t -> ZZ.t
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

(** {3 Approximation of rationals} *)

(** Compute an upper and lower bound for a rational number (with small
    representations) via truncated continued fractions.  The optional
    [accuracy] parameter determines the number of terms in the continued
    fraction (larger => more accurate, smaller => smaller representation) *)
val nudge : ?accuracy:int -> t -> t * t

(** Compute an upper bound for a rational number (with a small
    representation). *)
val nudge_up : ?accuracy:int -> t -> t

(** Compute an lower bound for a rational number (with a small
    representation). *)
val nudge_down : ?accuracy:int -> t -> t

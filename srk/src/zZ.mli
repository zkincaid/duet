(** Unbounded integers *)

type t = Z.t

val pp : Format.formatter -> t -> unit
val show : t -> string

val compare : t -> t -> int
val equal : t -> t -> bool
val leq : t -> t -> bool
val lt : t -> t -> bool

val hash : t -> int

val add : t -> t -> t
val mul : t -> t -> t
val zero : t
val one : t
val negate : t -> t
  
val sub : t -> t -> t

(** Integer division conforming to SMTLIB2:
    [a == (a/b)*b + a%b] and [0 <= a%b < |b|] *)
val div : t -> t -> t

(** Modulo conforming to SMTLIB2:
    [a == (a/b)*b + a%b] and [0 <= a%b < |b|] *)
val modulo : t -> t -> t

(** Division with remainder, conforming to SMTLIB2.
    [div_rem a b == (div a b, rem a b)] *)
val div_rem : t -> t -> (t * t)

(** Divide, rounding towards +oo ([ceil(a/b)]) *)
val cdiv : t -> t -> t

(** Remainder after division, rounding towards +oo:
    [crem a b == a - ceil(a/b) * b)] *)
val crem : t -> t -> t

(** Divide, rounding towards -oo ([floor(a,b)]) *)
val fdiv : t -> t -> t

(** Remainder after division, rounding towards -oo:
    [frem a b == a - floor(a/b) * b)] *)
val frem : t -> t -> t

val gcd : t -> t -> t
val lcm : t -> t -> t

val max : t -> t -> t
val min : t -> t -> t
val abs : t -> t

val of_int : int -> t
val of_string : string -> t

val to_int : t -> int option

val mpz_of : t -> Mpzf.t
val of_mpz : Mpzf.t -> t

(** Unbounded integers *)

type t = Mpzf.t

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

(** Integer division conforming to C99:
    [a == (a/b)*b + a%b],
    division truncates towards zero *)
val div : t -> t -> t

(** Modulo conforming to C99:
    [a == (a/b)*b + a%b],
    division truncates towards zero *)
val modulo : t -> t -> t

val gcd : t -> t -> t
val lcm : t -> t -> t

val max : t -> t -> t
val min : t -> t -> t
val abs : t -> t

val of_int : int -> t
val of_string : string -> t

val to_int : t -> int option

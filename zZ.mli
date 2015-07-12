open Apak
include Putil.Ordered with type t = Mpzf.t

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
val floor_div : t -> t -> t
val gcd : t -> t -> t
val lcm : t -> t -> t

val of_int : int -> t
val of_string : string -> t

val to_int : t -> int option

type 'a t

val make : int -> 'a t

val create : unit -> 'a t

val of_list : 'a list -> 'a t

val length : 'a t -> int

val add : 'a t -> 'a -> unit

val set : 'a t -> int -> 'a option -> unit

val get : 'a t -> int -> 'a option

val get_copy : 'a t -> int -> 'a option

val check : 'a t -> int -> bool

val blit : 'a t -> int -> 'a t -> int -> int -> unit

val iter : ('a -> unit) -> 'a t -> unit

val iteri : (int -> 'a -> unit) -> 'a t -> unit

val pp : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit

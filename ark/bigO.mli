open Syntax
type t
val pp : Format.formatter -> t -> unit
val of_term : 'a context -> 'a term -> t

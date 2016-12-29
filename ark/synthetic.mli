open Syntax


type 'a t

val pp : Format.formatter -> 'a t -> unit

val show : 'a t -> string

val join : ?integrity:('a formula -> unit) -> 'a t -> 'a t -> 'a t

val equal : 'a t -> 'a t -> bool

(*
val widen : 'a t -> 'a t -> 'a t
*)

val of_atoms : 'a context ->
  ?integrity:('a formula -> unit) ->
  ('a formula) list ->
  'a t

val to_atoms : 'a t -> ('a formula) list

val to_formula : 'a t -> 'a formula

val exists : ?integrity:('a formula -> unit) -> (symbol -> bool) -> 'a t -> 'a t

(*
val upper_bounds : 'a t -> 'a term -> ('a term) list
*)

val top : 'a context -> 'a t

val bottom : 'a context -> 'a t

val is_bottom : 'a t -> bool

val is_top : 'a t -> bool


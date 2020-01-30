open Syntax

type 'a t

val exp : 'a context -> (symbol * symbol) list -> 'a term -> 'a t -> 'a formula

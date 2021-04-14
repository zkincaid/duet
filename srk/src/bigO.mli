(** Simplification for Big-O expressions. *)

open Syntax
type t
val pp : Format.formatter -> t -> unit
val of_arith_term : 'a context -> 'a arith_term -> t

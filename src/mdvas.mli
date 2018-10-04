(** Wedge abstract domain.  A wedge corresponds to a conjunction of equations
    and inequations over a vocabulary that includes addition, multiplication,
    exponentiation, logarithm, division, and modulo. *)
open Syntax

type 'a t

val gamma : 'a context ->  'a t -> (symbol * symbol) list -> 'a formula

val abstract : ?exists:(symbol -> bool) -> 
  'a context ->
  (symbol * symbol) list -> 
  'a formula ->
  'a t

val pp : 'a context -> (symbol * symbol) list -> Format.formatter -> 'a t -> unit

val exp : 'a context -> (symbol * symbol) list -> 'a term -> 'a t -> 'a formula

 val join : 'a context -> (symbol * symbol) list -> 'a t -> 'a t -> 'a t
  val widen : 'a context -> (symbol * symbol) list -> 'a t -> 'a t -> 'a t
  val equal : 'a context -> (symbol * symbol) list -> 'a t -> 'a t -> bool
val remove_row: 'a t -> int -> int -> 'a t

module Mdvass : sig
    type 'a t
  val pp : 'a context -> (symbol * symbol) list -> Format.formatter -> 'a t -> unit
  val exp : 'a context -> (symbol * symbol) list -> 'a term -> 'a t -> 'a formula
  val join : 'a context -> (symbol * symbol) list -> 'a t -> 'a t -> 'a t
  val widen : 'a context -> (symbol * symbol) list -> 'a t -> 'a t -> 'a t
  val equal : 'a context -> (symbol * symbol) list -> 'a t -> 'a t -> bool
  val abstract : ?exists:(symbol -> bool) ->
    'a context ->
    (symbol * symbol) list ->
    'a formula ->
    'a t
end

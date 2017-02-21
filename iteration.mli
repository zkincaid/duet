open Syntax

type 'a iter

val pp_iter : Format.formatter -> 'a iter -> unit

val abstract_iter : ?exists:(symbol -> bool) ->
  'a context ->
  'a formula ->
  (symbol * symbol) list ->
  'a iter

val closure : 'a iter -> 'a formula

val star : ?exists:(symbol -> bool) ->
  'a context ->
  'a formula ->
  (symbol * symbol) list ->
  'a formula

val join : 'a iter -> 'a iter -> 'a iter
val widen : 'a iter -> 'a iter -> 'a iter
val equal : 'a iter -> 'a iter -> bool


module Split : sig
  type 'a split_iter
  val pp : Format.formatter -> 'a split_iter -> unit
  val abstract_iter : ?exists:(symbol -> bool) ->
    'a context ->
    'a formula ->
    (symbol * symbol) list ->
    'a split_iter
  val closure : 'a split_iter -> 'a formula
  val join : 'a split_iter -> 'a split_iter -> 'a split_iter
  val widen : 'a split_iter -> 'a split_iter -> 'a split_iter
  val equal : 'a split_iter -> 'a split_iter -> bool
end

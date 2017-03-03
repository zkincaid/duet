open Syntax

type 'a iter


val pp_iter : Format.formatter -> 'a iter -> unit
val show_iter : 'a iter -> string

val abstract_iter : ?exists:(symbol -> bool) ->
  'a context ->
  'a formula ->
  (symbol * symbol) list ->
  'a iter

val closure : ?guard:('a formula option) -> 'a iter -> 'a formula

val closure_ocrs : ?guard:('a formula option) -> 'a iter -> 'a formula

val star : ?exists:(symbol -> bool) ->
  'a context ->
  'a formula ->
  (symbol * symbol) list ->
  'a formula

val join : 'a iter -> 'a iter -> 'a iter
val widen : 'a iter -> 'a iter -> 'a iter
val equal : 'a iter -> 'a iter -> bool
val tr_symbols : 'a iter -> (symbol * symbol) list

module Split : sig
  type 'a split_iter
  val pp_split_iter : Format.formatter -> 'a split_iter -> unit
  val show_split_iter : 'a split_iter -> string
  val abstract_iter : ?exists:(symbol -> bool) ->
    'a context ->
    'a formula ->
    (symbol * symbol) list ->
    'a split_iter
  val closure : ?use_ocrs:bool -> 'a split_iter -> 'a formula
  val join : 'a split_iter -> 'a split_iter -> 'a split_iter
  val widen : 'a split_iter -> 'a split_iter -> 'a split_iter
  val equal : 'a split_iter -> 'a split_iter -> bool
  val tr_symbols : 'a split_iter -> (symbol * symbol) list
  val lift_split : 'a iter -> 'a split_iter
end

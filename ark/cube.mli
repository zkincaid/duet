open Syntax

type 'a t

val pp : Format.formatter -> 'a t -> unit

val show : 'a t -> string

val join : ?integrity:('a formula -> unit) -> 'a t -> 'a t -> 'a t

val equal : 'a t -> 'a t -> bool

val widen : 'a t -> 'a t -> 'a t

val of_atoms : 'a context ->
  ?integrity:('a formula -> unit) ->
  ('a formula) list ->
  'a t

val to_atoms : 'a t -> ('a formula) list

val to_formula : 'a t -> 'a formula

(** Project symbols out of a cube that do not satisfy the given predicate.
    Additionally project out terms that contain a symbol that does not satisfy
    the subterm predicate. *)
val exists : ?integrity:('a formula -> unit) ->
  ?subterm:(symbol -> bool) ->
  (symbol -> bool) ->
  'a t ->
  'a t

val top : 'a context -> 'a t

val bottom : 'a context -> 'a t

val is_bottom : 'a t -> bool

val is_top : 'a t -> bool

(** Compute a representation of the set of equalities that are entailed by a
    given cube as a list [(term0, vector0),...,(termn,vectorn)].  The interpretation of this
    representation is that for any vector v,
    [cube |= (vector0 . v) term0 + ... + (vectorn . v) termn = 0]
    where [.] represents the dot product. *)
val farkas_equalities : 'a t -> ('a term * Linear.QQVector.t) list

(** Given a cube [cube] and a symbol [symbol], compute a list of lower bounds
    and upper bounds for [symbol] that are implied by [cube]. *)
val symbolic_bounds : 'a t -> symbol -> ('a term) list * ('a term) list
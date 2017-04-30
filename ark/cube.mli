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
    given cube as a list [(term0, vector0),...,(termn,vectorn)].  The
    interpretation of this representation is that for any vector v,
    [cube |= (vector0 . v) term0 + ... + (vectorn . v) termn = 0]
    where [.] represents the dot product. *)
val farkas_equalities : 'a t -> ('a term * Linear.QQVector.t) list

(** Given a cube [cube] and a symbol [symbol], compute a list of lower bounds
    and upper bounds for [symbol] that are implied by [cube]. *)
val symbolic_bounds : 'a t -> symbol -> ('a term) list * ('a term) list

(** Ensure that the named symbols [pow : Real x Real -> Real] and [log : Real
    x Real -> Real] belong to a given context. *)
val ensure_nonlinear_symbols : 'a context -> unit

(** Compute a cube that over-approximates a given formula *)
val abstract : ?exists:(symbol -> bool) -> 'a context -> 'a formula -> 'a t

(** Check if a formula is satisfiable by computing an over-approximating cube
    and checking whether it is feasible.  This procedure improves on the naive
    implementation by returning [`Unknown] as soon as it finds a disjunct that
    it can't prove to be infeasible.  *)
val is_sat : 'a context -> 'a formula -> [ `Sat | `Unsat | `Unknown ]

(** Compute lower and upper bounds for a symbol that are implied by the given
    formula (if they exist).  The upper and lower bounds may involve only
    symbols that satisfy the exist predicate, and may involve the functions
    [max] and [min] (binary named symbols).  (For example, if [x] is bounded
    above by [0] and [y], then the upper bound computed by [symbolic_bounds]
    is [min(0,y)]). *)
val symbolic_bounds_formula : ?exists:(symbol -> bool) ->
  'a context ->
  'a formula ->
  symbol ->
  ('a term) option * ('a term) option

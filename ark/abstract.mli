open Syntax
open Smt

(** [affine_hull ark phi symbols] computes a basis for the affine hull of phi,
    projected onto the given set of symbols.  The basis is represented as a
    list of terms, with the interpretation that a point [p] belongs to the
    affine hull if every term in the list evaluates to 0 at [p]. *)
val affine_hull : 'a context -> 'a formula -> symbol list -> 'a term list

(** [boxify ark phi terms] computes the strongest formula of the form
    [/\ { lo <= t <= hi : t in terms }]
    that is implied by [phi]. *)
val boxify : 'a context -> 'a formula -> 'a term list -> 'a formula

(** [abstract ?exists ark man phi] computes the strongest property that is
    implied by [phi] which is expressible within a given abstract domain.  The
    property is restricted to use only the symbols that satisfy the [?exists]
    predicate (which defaults to the constant [true] predicate). *)
val abstract : ?exists:(symbol -> bool) ->
  'a context ->
  'abs Apron.Manager.t ->
  'a formula ->
  ('a,'abs) ArkApron.property

(** Replace non-linear arithmetic with uninterpreted functions.  The
    uninterpreted function symbols are named symbols: mul, div, and mod.  This
    rewriter is safe to apply top-down or bottom-up. *)
val nonlinear_uninterpreted_rewriter : 'a context ->
  ('a,typ_fo) expr ->
  ('a,typ_fo) expr

(** Compute a linear approximation of a non-linear formula. *)
val linearize : 'a context -> 'a formula -> 'a formula

val is_sat : 'a context -> 'a formula -> [ `Sat | `Unsat | `Unknown ]

val abstract_nonlinear : ?exists:(symbol -> bool) ->
  'a context ->
  'a formula ->
  'a Cube.t

(** Compute lower and upper bounds for a symbol that are implied by the given
    formula (if they exist).  The upper and lower bounds may involve only
    symbols that satisfy the exist predicate, and may involve the functions
    [max] and [min] (binary named symbols).  (For example, if [x] is bounded
    above by [0] and [y], then the upper bound computed by [symbolic_bounds]
    is [min(0,y)]). *)
val symbolic_bounds : ?exists:(symbol -> bool) ->
  'a context ->
  'a formula ->
  symbol ->
  ('a term) option * ('a term) option

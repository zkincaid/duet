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

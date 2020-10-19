(** Approximate transitive closure computation. *)
open Syntax

module type PreDomain = sig
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

module type PreDomainWedge = sig
  include PreDomain
  val abstract_wedge : 'a context -> (symbol * symbol) list -> 'a Wedge.t -> 'a t
end

module type Domain = sig
  type 'a t
  val pp : Format.formatter -> 'a t -> unit
  val closure : 'a t -> 'a formula
  val join : 'a t -> 'a t -> 'a t
  val widen : 'a t -> 'a t -> 'a t
  val equal : 'a t -> 'a t -> bool
  val abstract : ?exists:(symbol -> bool) ->
    'a context ->
    (symbol * symbol) list ->
    'a formula ->
    'a t
  val tr_symbols : 'a t -> (symbol * symbol) list
end


module WedgeGuard : PreDomainWedge

module PolyhedronGuard : sig
  include PreDomain
  val precondition : 'a t -> ('a, Polka.strict Polka.t) SrkApron.property
  val postcondition : 'a t -> ('a, Polka.strict Polka.t) SrkApron.property
end
module LinearGuard : PreDomain

(** Abstract a transition formula F(x,x') by a system of recurrences of the form
    a(x') >= a(x) + c
    where a is a linear map and c is a scalar. *)
module LinearRecurrenceInequation : PreDomain

(** Abstract a transition formula F(x,x',y) (where y denotes a set of
   symbolic constants) by a system of recurrences of the form
    [ax' >= ax + t(y)]
   where a is a linear map and t(y) is a (possibly non-linear)
   term over y. *)
module NonlinearRecurrenceInequation : PreDomainWedge

(** Improve iteration operator using split invariants *)
module Split(Iter : PreDomain) : PreDomain

(** Improve iteration operator using variable directions (increasing,
   decreasing, stable) to find phase splits. *)
module InvariantDirection(Iter : PreDomain) : PreDomain


module Product (A : PreDomain) (B : PreDomain) : PreDomain
  with type 'a t = 'a A.t * 'a B.t

(** Same as product, but faster for iteration domains that abstract
   through the wedge domain. *)
module ProductWedge (A : PreDomainWedge) (B : PreDomainWedge) : PreDomainWedge
  with type 'a t = 'a A.t * 'a B.t

module MakeDomain(Iter : PreDomain) : Domain

val identity : 'a context -> (symbol * symbol) list -> 'a formula

(** Given a transition formula T and a transition predicate p, we say
   that p is an invariant of T if T(x,x') /\ T(x',x'') is consistent and
     T(x,x') /\ T(x',x'') /\ p(x,x') => p(x',x'')
   A set of transition predicates defines a partition of T, which is acyclic
   in the sense that when a computation leaves a cell it may never return.
   This function takes a set of candidate transition predicates as input,
   determines which are invariant, and returns the non-empty cells of the
   partition. *)
val invariant_partition : ?exists:(symbol -> bool) ->
                          'a context ->
                          (symbol * symbol) list ->
                          ('a formula) list ->
                          'a formula ->
                          ('a formula) list

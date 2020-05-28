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

module Split(Iter : PreDomain) : PreDomain

module Sum (A : PreDomain) (B : PreDomain) () : sig
  include PreDomain
  val left : 'a A.t -> 'a t
  val right : 'a B.t -> 'a t
  val abstract_left : bool ref
end
module SumWedge (A : PreDomainWedge) (B : PreDomainWedge) () : sig
  include PreDomainWedge
  val left : 'a A.t -> 'a t
  val right : 'a B.t -> 'a t
  val abstract_left : bool ref
end

module Product (A : PreDomain) (B : PreDomain) : PreDomain
  with type 'a t = 'a A.t * 'a B.t

(** Same as product, but faster for iteration domains that abstract
   through the wedge domain. *)
module ProductWedge (A : PreDomainWedge) (B : PreDomainWedge) : PreDomainWedge
  with type 'a t = 'a A.t * 'a B.t

module MakeDomain(Iter : PreDomain) : Domain

val identity : 'a context -> (symbol * symbol) list -> 'a formula

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

module SolvablePolynomialOne : PreDomainWedge
module SolvablePolynomial : PreDomainWedge
module SolvablePolynomialPeriodicRational : PreDomainWedge

module WedgeGuard : PreDomainWedge

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
module ProductWedge (A : PreDomainWedge) (B : PreDomainWedge) : PreDomainWedge

module MakeDomain(Iter : PreDomain) : Domain

(** Approximate transitive closure computation. *)
open Syntax

module type PreDomain = sig
  type 'a t
  val pp : Format.formatter -> 'a t -> unit
  val show : 'a t -> string
  val closure : 'a t -> 'a formula
  val join : 'a t -> 'a t -> 'a t
  val widen : 'a t -> 'a t -> 'a t
  val equal : 'a t -> 'a t -> bool
  val tr_symbols : 'a t -> (symbol * symbol) list
end

module type Domain = sig
  include PreDomain
  val abstract_iter : ?exists:(symbol -> bool) ->
    'a context ->
    'a formula ->
    (symbol * symbol) list ->
    'a t
end

module type DomainPlus = sig
  include Domain
  val closure_plus : 'a t -> 'a formula
end

module WedgeVector : DomainPlus
module WedgeVectorOCRS : DomainPlus
module WedgeMatrix : DomainPlus

module Split(Iter : DomainPlus) : Domain

module Sum (A : PreDomain) (B : PreDomain) : sig
  include PreDomain
  val left : 'a A.t -> 'a t
  val right : 'a B.t -> 'a t
end

(* Finite structures *)
open PaFormula

val embed : int ref

module type Symbol = sig
  type t
  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val pp : Format.formatter -> t -> unit
end

module type S = sig
  type t
  type predicate
  module Predicate : Symbol with type t = predicate
  val pp : Format.formatter -> t -> unit
  val show : t -> string
  val equal : t -> t -> bool
  val hash : t -> int
  val compare : t -> t -> int

  (** Enumerate the propositions which hold in a structure *)
  val props : t -> (predicate * int list) BatEnum.t
  val preds : t -> predicate BatEnum.t

  val universe_size : t -> int
  val universe : t -> int BatEnum.t

  val make : ?size:int -> (predicate * int list) BatEnum.t -> t

  val models : ?env:(int list) -> t -> (predicate,int) formula -> bool

  (** Find all minimal models of a given formula, with a given universe *)
  val min_models :
    ?env:(int list) ->
    int ->
    (predicate,int) formula ->
    t BatEnum.t

  (** Is the first structure a substructure of the second? *)
  val substructure : t -> t -> bool
  
  (** Is there an embedding (injective homomorphism) from the first structure
      into the second? *)
  val embeds : t -> t -> bool
  val embeds_novel : t -> t -> bool
  val embeds_novel2 : t -> t -> bool
  val uembeds : t -> t -> bool
  val cembeds : t -> t -> bool
  val bembeds : t -> t -> bool
  val str2mzn : t -> t -> bool
  val str2dimacs : t -> t -> bool
  val haifacsp : t -> t -> bool
  val ortools : t -> t -> bool

  (** [union s s'] is a structure whose universe is the union of the universes
      of [s] and [s'] and whose interpretation of each predicate [p] is the
      union of its interpretation in [s] and [s']. *)
  val union : t -> t -> t

  val empty : int -> t

  (** [full vocabulary] is the largest structure over the given vocabulary *)
  val full : (predicate * int) BatEnum.t -> int -> t

  val add : predicate -> int list -> t -> t
  val remove : predicate -> int list -> t -> t

  (** Given a structure m and positive formula phi such that m |= phi, find a
      minimal substructure m' of m such that m' |= phi *)
  val minimize : ?env:(int list) -> t -> (predicate,int) formula -> t

  (** Given a structure m and positive formula phi, if m |= phi then
      strengthen phi by removing disjuncts and instantiating existential
      quantifiers so that the resulting formula is satisfied by m; if m |/=
      phi, then return [None]. *)
  val instantiate :
    ?env:(int list) ->
    t ->
    (predicate,int) formula ->
    (predicate,int) formula option
end

module Make (P : Symbol) : S with type predicate = P.t


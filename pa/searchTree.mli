module type Element = sig
  type t
  val compare : t -> t -> int
  val hash : t -> int
  val equal : t -> t -> bool
  val pp : Format.formatter -> t -> unit
end

module type S = sig
  type t
  type baseSet
  type elt

  val empty : baseSet -> (elt -> baseSet) -> t
  val make  : baseSet -> (elt -> baseSet) -> elt BatSet.t -> t

  exception Item_not_known
  val insert : t -> elt -> unit
  val covered : (elt -> elt -> bool) -> t -> elt -> elt option
end

module Make (Base : Element) (Elt : Element) : S with type baseSet = BatSet.Make(Base).t with type elt = Elt.t


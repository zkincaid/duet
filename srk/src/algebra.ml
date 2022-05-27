(** Signatures for algebraic structures. *)

module type Semigroup = sig
  type t
  val mul : t -> t -> t
end

module type Ring = sig
  type t
  val equal : t -> t -> bool
  val add : t -> t -> t
  val negate : t -> t
  val zero : t
  val mul : t -> t -> t
  val one : t
end

module type Semilattice = sig
  type t
  val join : t -> t -> t
  val equal : t -> t -> bool
end

module type Lattice = sig
  type t
  val join : t -> t -> t
  val equal : t -> t -> bool
  val meet : t -> t -> t
end

module type Field = sig
  type t
  val equal : t -> t -> bool
  val add : t -> t -> t
  val negate : t -> t
  val inverse : t -> t
  val zero : t
  val mul : t -> t -> t
  val one : t
  val pp : Format.formatter -> t -> unit
end

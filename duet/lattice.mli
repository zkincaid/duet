(** Operations on lattices.  A lattice is a set equipped with a partial order
    which has binary least upper bounds and greatest lower bounds. *)

module type S = sig
  include Srk.Algebra.Lattice
  val pp : Format.formatter -> t -> unit
end

(** Powerset lattice under the subset ordering. *)
module LiftSubset (S : Putil.Set.S) : sig
  include S with type t = S.t
  val compare : t -> t -> int
  val bottom : S.t
end

(** Flip the order in a lattice *)
module Dual (L : S) : S with type t = L.t

module FunctionSpace : sig
  (** Total function spaces where all but finitely many elements map to the
      same "default" value. *)
  module type S = sig
    include Srk.Algebra.Lattice
    type dom
    type cod

    val pp : Format.formatter -> t -> unit
    val eval : t -> dom -> cod
    val update : dom -> cod -> t -> t
    val enum : t -> (dom * cod) BatEnum.t
    val merge : (cod -> cod -> cod) -> t -> t -> t
    val default : t -> cod
    val const : cod -> t
  end
  module Make (Domain : Putil.Ordered) (Codomain : sig
               include Srk.Algebra.Lattice
               val pp : Format.formatter -> t -> unit
             end) :
  S with type dom = Domain.t
         and type cod = Codomain.t
end


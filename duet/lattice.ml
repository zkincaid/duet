open Srk
module type S = sig
  include Algebra.Lattice
  val pp : Format.formatter -> t -> unit
end

module LiftSubset (S : Putil.Set.S) = struct
  include S
  let join = S.union
  let meet = S.inter
  let equal = S.equal
  let bottom = S.empty
end

module Dual (L : S) = struct
  include L
  let join = L.meet
  let meet = L.join
end

module FunctionSpace = struct
  module type S = sig
    include Algebra.Lattice
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
             end) = struct
    include Putil.TotalFunction.LiftMap(Putil.Map.Make(Domain))(Codomain)
    let join = merge Codomain.join
    let meet = merge Codomain.meet
  end
end

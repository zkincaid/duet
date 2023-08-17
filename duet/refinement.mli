(** Module for computing refined stars *)

module type PreKleeneAlgebra = sig
  type t
  val mul : t -> t -> t
  val add : t -> t -> t
  val zero : t
  val one : t
  val star : t -> t
  val is_zero : t -> bool
  val compare : t -> t -> int
end


module DomainRefinement : functor (A : PreKleeneAlgebra) -> sig

  (** {!val:refine_full} determines whether refinement should compute a refinement 
  that uses a traditional path expression or the algorithm from POPL19. Default is false *)
  val refine_full : bool ref

  (** {!val:refinement} gives an alternative star operation that theoretically gives
  more accurate if {!module:A} is truly a PKA and {!val:refine_full} is false. {!val:refinement} in 
  practice provides better answers otherwise, but with no guarentee.*)
  val refinement :  A.t list -> A.t
end

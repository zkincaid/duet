(** Linear transition systems.  A transition system is linear if its
   state space is a finite dimensional vector space and its transition
   relation is a linear space. *)

open Syntax

module QQMatrix = Linear.QQMatrix
module QQVector = Linear.QQVector
module QQVectorSpace = Linear.QQVectorSpace

(** Linear transition systems *)
type lts = QQMatrix.t * QQMatrix.t

val pp : (Format.formatter -> int -> unit) -> Format.formatter -> lts -> unit

(** Find the best LTS abstraction of a transition formula w.r.t. affine simulations *)
val abstract_lts : ?exists:(symbol -> bool) -> 'a context -> (symbol * symbol) list -> 'a formula -> lts

(** Determine if the transition relation of one LTS is contained within another *)
val contains : lts -> lts -> bool

(** Given LTS [Ax' = Bx] and [Cx' = Dx], if [Ax' = Bx] entails [Cx' =
   Dx], find a matrix [M] such that [MA = C] and [MB = D]; otherwise
   return [None]. *)
val containment_witness : lts -> lts -> Linear.QQMatrix.t option

(** {2 Partial linear maps} *)
module PartialLinearMap : sig

  (** A partial linear map is a partial function that is linear and
     whose domain is a vector space *)
  type t

  val equal : t -> t -> bool

  (** [identity n] is the (total) identity map on the coordinates [0
     .. n-1]; all other coordinates are sent to 0. *)
  val identity : int -> t

  (** [make A G] creates the partial map whose action is given by the
     matrix A, and whose domain of definition is the set of all [v]
     such that [g.v = 0] for all [g in G].  (I.e., [G] is a set of
     equality constraints that must on the input for [make A G] to be
     defined; the domain is the orthogonal complement of G). *)
  val make : QQMatrix.t -> QQVector.t list -> t

  val pp : Format.formatter -> t -> unit

  (** (Partial) map composition *)
  val compose : t -> t -> t

  (** Repeatly compose a partial map with itself until the domain
     stabilizes; return both iteration sequence and the invariant guard
     of the function.

     We have guard(f) <= guard(f o f) <= guard(f o f o f) <= ...
     and there is some (least) n such that guard(f^n) = guard(f^m)
     for all m >= n.  The pair returned by [iteration_sequence f] is
     [([f; f o f; ...; f^n], dom(f^n))].
  *)
  val iteration_sequence : t -> (t list) * (QQVector.t list)

  (** Access the underlying (total) map of a partial map. *)
  val map : t -> QQMatrix.t

  (** Access the guard of a partial map.  The domain of the map is its
     orthogonal complement *)
  val guard : t -> QQVectorSpace.t
end

(** Deterministic linear transition systems. *)
type dlts = PartialLinearMap.t

(** Find the best deterministic abstraction of a linear transition system. *)
val determinize : lts -> dlts * QQMatrix.t

(** Given a dlts [T], and a linear map [s] into the state space of
   [T], compute the inverse image of the transition relation of [T]
   under [s]. *)
val dlts_inverse_image : QQMatrix.t -> dlts -> lts

(** Find the best abstraction of a DLTS as a DLTS with rational
   spectrum. *)
val rational_spectrum_reflection : dlts -> int -> (dlts * QQMatrix.t)

(** Find the best abstraction of a DLTS as a DLTS with periodic
   rational spectrum. *)
val periodic_rational_spectrum_reflection : dlts -> int -> (dlts * QQMatrix.t)

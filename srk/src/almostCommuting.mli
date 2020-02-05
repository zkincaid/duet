open Linear

val commuting_space : QQMatrix.t -> QQMatrix.t -> QQVectorSpace.t
val commuting_segment : QQMatrix.t array -> int list -> (QQMatrix.t * QQMatrix.t array)

type kind = Commute | Reset | Ignore

type phased_segment = {
   sim1 : QQMatrix.t;                 (* Simulation for phase 1 (all matrices commute) *)
   sim2 : QQMatrix.t;                 (* Simulation for phase 2 (all non-reset matrices commute) *)
   phase1 : QQMatrix.t array;         (* Image of each transition under the phase 1 simulation *)
   phase2 : (kind * QQMatrix.t) array (* Each transition i is either of kind Commute, in which case
                                         phase2.(i) is the image of transition i under the phase 2
                                         simulation, or of kind Reset, in which case phase2.(i) gives
                                         a representation of transition i as a transformation from the 
                                         phase 1 space to the phase 2 space *)
}

module PhasedSegment : sig
   type t = phased_segment

   val show : t -> string
   val equal : t -> t -> bool

   (** Computes the best phased segment for the given partition of matrices *)
   val make : (kind * QQMatrix.t) array -> t
end

module PhasedSegmentation : sig
   type t = phased_segment list

   (** Computes a phased segmentation for the given matrices by exhaustively exploring all partitions *)
   val make_naive : QQMatrix.t array -> t

   (** Returns the vector space where the given segmentation almost commutes *)
   val almost_commuting_space : t -> QQVectorSpace.t

   (** Returns whether the given phased segmentation almost commutes or not *)
   val almost_commutes : t -> bool

   (** Computes the best almost commuting abstraction for the given LTS *)
   val best_almost_commuting : QQMatrix.t array -> (QQMatrix.t * QQMatrix.t array)
end
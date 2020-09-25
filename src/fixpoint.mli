(** Iterative fixpoint computation. *)

module Make
         (G : sig
            type t
            module V : sig
              type t
              val compare : t -> t -> int
              val hash : t -> int
              val equal : t -> t -> bool
            end
            module E : sig
              type t
              val src : t -> V.t
            end
            val iter_vertex : (V.t -> unit) -> t -> unit
            val iter_succ : (V.t -> unit) -> t -> V.t -> unit
            val fold_pred_e : (E.t -> 'a -> 'a) -> t -> V.t -> 'a -> 'a
          end)
         (Domain : sig
            type t
            type edge = G.E.t
            val join : t -> t -> t
            val widening : t -> t -> t
            val equal : t -> t -> bool
            val transform : edge -> t -> t
          end) : sig
  (** [analyze delay graph init] computes a function [annotation] such that
      - for all vertices [v], [init v <= annotation v]
      - for all edge [e : u -> v],
        [Domain.transform e (annotation u) <= annotation v].
      The optional delay parameter specifies a widening delay. *)
  val analyze : ?delay:int -> G.t -> (G.V.t -> Domain.t) -> (G.V.t -> Domain.t)
end

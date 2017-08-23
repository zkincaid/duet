(** A feature tree organizes a collection by vectors of integer features.
    Each element of the universe from which the collection is drawn is
    associated with a feature vector; multiple elements may be associated with
    the same feature vector.  The feature tree can be queried for *)

type 'a t
val empty : ('a -> int array) -> 'a t
val of_list : ('a -> int array) -> 'a list -> 'a t
val insert : 'a -> 'a t -> 'a t
val features : 'a t -> 'a -> int array

(** Find an element with features <= the given feature vector, and which
    satisfies the given predicate.  Raises [Not_found] if there is no such
    element. *)
val find_leq : int array -> ('a -> bool) -> 'a t -> 'a

(** Find an element [elt] with features <= the given feature vector, and on
    which the given partial function [f] is defined; return [f elt].  Raises
    [Not_found] if there is no such element. *)
val find_leq_map : int array -> ('a -> 'b option) -> 'a t -> 'b

val remove : ('a -> 'a -> bool) -> 'a -> 'a t -> 'a t
val rebalance : 'a t -> 'a t

val enum : 'a t -> 'a BatEnum.t

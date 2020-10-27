(** Weighted forests with path compression.  Based on Tarjan's
   EVAL-LINK-UPDATE data structure from "Applications of Path
   Compression on Balanced Trees". *)

(** Forest with edges weighted by elements of a monoid. *)
type 'a t

type node

(** Create a fresh weighted compressed forest. *)
val create : mul:('a -> 'a -> 'a) -> one:'a -> 'a t

(** Allocate a fresh root in the forest. *)
val root : 'a t -> node

(** Find the root that is connected to a node. *)
val find : 'a t -> node -> node

(** Find w1 * w2 * ... * wn, where w1,...,wn is the sequence of
    weights on the links from node to root. *)
val eval : 'a t -> node -> 'a

(** Add a weighted link from [child] to [parent].  Raises
   [Invalid_arg] if [child] is not a root. *)
val link : 'a t -> child:node -> 'a -> parent:node -> unit

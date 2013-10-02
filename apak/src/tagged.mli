(** Data structures for tagged types.  Tagged types are equipped with
    injections into the integers, which allows for an efficient implementation
    of Patricia trees. *)

module type Tagged = sig
  include Putil.S
  val tag : t -> int
end

(** Sets implemented with Patricia trees.  This module is taken from
    Jean-Christophe Filliatre's implementation of Patricia trees. *)
module PTSet (T : Tagged) : Putil.Hashed.Set.S with type elt = T.t

(** Maps implemented with Patricia trees.  This module is taken from
    Jean-Christophe Filliatre's implementation of Patricia trees. *)
module PTMap (T : Tagged) : Putil.Map.S with type key = T.t

module MakeCoreType (T : Tagged) : sig
  include Putil.CoreType with type t = T.t
  val tag : t -> int
end

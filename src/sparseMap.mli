(** Sparse maps.

   A sparse map is a total function with finite support (i.e., only
   finitely many elements of the domain are mapped to a non-zero value
   in the codomain). *)

module type S = sig
  type t
  type key
  type value

  val equal : t -> t -> bool

  (** Evaluate a sparse map at a key.  *)
  val get : key -> t -> value

  (** Functional update. *)
  val set : key -> value -> t -> t

  (** Constant-zero map *)
  val zero : t

  (** [singleton key value] maps [key] to [value], and everythine else
     to zero. *)
  val singleton : key -> value -> t

  (** Is the map constant-zero ? *)
  val is_zero : t -> bool

  (** Apply a binary operation pointwise to two maps. *)
  val merge : (key -> value -> value -> value) -> t -> t -> t

  (** [modify k f m] replaces the binding of [k] in [m] with [f (m k)]. *)
  val modify : key -> (value -> value) -> t -> t

  (** Apply a unary operation pointwise to a map. *)
  val map : (key -> value -> value) -> t -> t

  (** [extract key map] return the pair ([get key map], [set key zero
     map]) *)
  val extract : key -> t -> (value * t)

  (** Enumerate the bindings in the support of a map. *)
  val enum : t-> (key * value) BatEnum.t

  (** Construct a sparse map from an enumeration of the bindings in
     its support.  If a key appears multiple times, the latest
     binding in the enumeration has priority. *)
  val of_enum : (key * value) BatEnum.t -> t

  (** Fold overthe support of a map. *)
  val fold : (key -> value -> 'a -> 'a) -> t -> 'a -> 'a

  (** Find the binding in the support of the map with minimal key.
     Raise [Not_found] if the support is empty. *)
  val min_support : t -> (key * value)

  (** Remove a binding from the support of a map.  Raise [Not_found]
     if the support is empty. *)
  val pop : t -> (key * value) * t

  val hash : (key * value -> int) -> t -> int
  val compare : (value -> value -> int) -> t -> t -> int
end

module Make
         (K : BatInterfaces.OrderedType)
         (V : sig
            type t
            val equal : t -> t -> bool
            val zero : t
          end) : sig
  include S with type key = K.t
             and type value = V.t
end

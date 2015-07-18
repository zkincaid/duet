(** Operations on semilattices.  A semilattice is a set equipped with an
    associative, commutative, idempotent binary operation *)

module type S = Sig.Semilattice.S
module Ordered : sig
  module type S = Sig.Semilattice.Ordered.S
end

module FunctionSpace : sig
  (** Common signature for partial & total function spaces *)
  module type S = sig
    include Sig.Semilattice.S
    include Sig.FunctionSpace.S with type t := t
    (** [weak_update k v f] constructs a function which maps [k] to [join v (f
        k)] and all other elements [y] to [f y]. *)
    val weak_update : dom -> cod -> t -> t
  end

  (** Total function spaces where all but finitely many elements map to the
      same "default" value. *)
  module Total : sig
    module type S = sig
      include Sig.Semilattice.S
      include Sig.FunctionSpace.Total with type t := t
      val weak_update : dom -> cod -> t -> t
    end

    (** [LiftMap(M)(Codomain)] constructs a total function space semilattice
        where [M] is used as the underlying map representation.  This
        is useful (for example) with tagged types, since Patricia
        trees support fast merging. *)
    module LiftMap (M : Putil.Map.S) (Codomain : Sig.Semilattice.S) :
      S with type dom = M.key
         and type cod = Codomain.t

    module Make (Domain : Putil.Ordered) (Codomain : Sig.Semilattice.S) :
      S with type dom = Domain.t
         and type cod = Codomain.t

    module Ordered : sig
      module type S = sig
        include S
        include Putil.OrderedMix with type t := t
      end
      module LiftMap (M : Putil.Map.S) (Codomain : Sig.Semilattice.Ordered.S) :
        S with type dom = M.key
           and type cod = Codomain.t
      module Make
          (Domain : Putil.Ordered)
          (Codomain : Sig.Semilattice.Ordered.S) :
        S with type dom = Domain.t
           and type cod = Codomain.t
    end
  end

  (** Partial function spaces. *)
  module Partial : sig
    module type S = sig
      include Sig.Semilattice.Bounded.S
      include Sig.FunctionSpace.Partial with type t := t
      val weak_update : dom -> cod -> t -> t
    end

    (** [LiftMap(M)(Codomain)] constructs a partial function space semilattice
        where [M] is used as the underlying map representation.  This
        is useful (for example) with tagged types, since Patricia
        trees support fast merging. *)
    module LiftMap (M : Putil.Map.S) (Codomain : Sig.Semilattice.S) :
      S with type dom = M.key
         and type cod = Codomain.t

    module Make (Domain : Putil.Ordered) (Codomain : Sig.Semilattice.S) :
      S with type dom = Domain.t
         and type cod = Codomain.t

    module Ordered : sig
      module type S = sig
        include S
        include Putil.OrderedMix with type t := t
      end
      module LiftMap (M : Putil.Map.S) (Codomain : Sig.Semilattice.Ordered.S) :
        S with type dom = M.key
           and type cod = Codomain.t
      module Make
          (Domain : Putil.Ordered)
          (Codomain : Sig.Semilattice.Ordered.S) :
        S with type dom = Domain.t
           and type cod = Codomain.t
    end
  end
end

(** Hash table where values stored in the table belong to a semilattice.  For
    each key [k] in the table [ht], [find ht k] is the least upper bound of
    all values that have been added with key [k]. *)
module Table (D : Hashtbl.HashedType) (C : Sig.Semilattice.S) : sig
  type t
  val create : int -> t
  val mem : t -> D.t -> bool
  val clear : t -> unit
  val find : t -> D.t -> C.t
  val add : t -> D.t -> C.t -> unit
end

(** Bounded semilattices are semilattices with a least element, bottom *)
module Bounded : sig
  type 'a bounded =
    | Bottom
    | Value of 'a
  val pp_bounded : (Format.formatter -> 'a -> unit) ->
    Format.formatter ->
    'a bounded ->
    unit

  (** Augment a semilattice with a least element *)
  module Lift (S : Sig.Semilattice.S) :
    Sig.Semilattice.Bounded.S with type t = S.t bounded

  (** A bounded semilattice forms a monoid, taking multiplication to be join
      and the unit to be bottom. *)
  module Monoid (S : Sig.Semilattice.Bounded.S) :
    Sig.Monoid.S with type t = S.t
  module Ordered : sig
    module Monoid (S : Sig.Semilattice.Bounded.Ordered.S) :
      Sig.Monoid.Ordered.S with type t = S.t
  end
end

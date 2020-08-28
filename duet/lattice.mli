(** Operations on lattices.  A lattice is a set equipped with a partial order
    which has binary least upper bounds and greatest lower bounds. *)

module type S = Sig.Lattice.S
module Ordered : sig
  module type S = Sig.Lattice.Ordered.S
end

(** Powerset lattice under the subset ordering. *)
module LiftSubset (S : Putil.Set.S) : sig
  include Sig.Lattice.Ordered.S with type t = S.t
  val bottom : S.t
end

(** Flip the order in a lattice *)
module Dual (L : Sig.Lattice.S) : Sig.Lattice.S with type t = L.t

module FunctionSpace : sig
  (** Common signature for partial & total function spaces *)
  module type S = sig
    include Sig.Lattice.S
    include Sig.FunctionSpace.S with type t := t
    (** [weak_update k v f] constructs a function which maps [k] to
        	[join v (f k)] and all other elements [y] to [f y]. *)
    val weak_update : dom -> cod -> t -> t
  end

  (** Total function spaces where all but finitely many elements map to the
      same "default" value. *)
  module Total : sig
    module type S = sig
      include Sig.Lattice.S
      include Sig.FunctionSpace.Total with type t := t
      val weak_update : dom -> cod -> t -> t
    end

    (** [LiftMap(M)(Codomain)] constructs a total function space lattice where
        [M] is used as the underlying map representation.  This is
        useful (for example) with tagged types, since Patricia trees
        support fast merging. *)
    module LiftMap (M : Putil.Map.S) (Codomain : Sig.Lattice.S) :
      S with type dom = M.key
         and type cod = Codomain.t

    module Make (Domain : Putil.Ordered) (Codomain : Sig.Lattice.S) :
      S with type dom = Domain.t
         and type cod = Codomain.t

    module Ordered : sig
      module type S = sig
        include S
        include Putil.OrderedMix with type t := t
      end
      module LiftMap (M : Putil.Map.S) (Codomain : Sig.Lattice.Ordered.S) :
        S with type dom = M.key
           and type cod = Codomain.t
      module Make
          (Domain : Putil.Ordered)
          (Codomain : Sig.Lattice.Ordered.S) :
        S with type dom = Domain.t
           and type cod = Codomain.t
    end
  end

  (** Partial function spaces. *)
  module Partial : sig
    module type S = sig
      include Sig.Lattice.S
      include Sig.FunctionSpace.Partial with type t := t
      val weak_update : dom -> cod -> t -> t
      val bottom : t
    end

    (** [LiftMap(M)(Codomain)] constructs a partial function space lattice
        where [M] is used as the underlying map representation.  This
        is useful (for example) with tagged types, since Patricia
        trees support fast merging. *)
    module LiftMap (M : Putil.Map.S) (Codomain : Sig.Lattice.S) :
      S with type dom = M.key
         and type cod = Codomain.t

    module Make (Domain : Putil.Ordered) (Codomain : Sig.Lattice.S) :
      S with type dom = Domain.t
         and type cod = Codomain.t

    module Ordered : sig
      module type S = sig
        include S
        include Putil.OrderedMix with type t := t
      end
      module LiftMap (M : Putil.Map.S) (Codomain : Sig.Lattice.Ordered.S) :
        S with type dom = M.key
           and type cod = Codomain.t
      module Make
          (Domain : Putil.Ordered)
          (Codomain : Sig.Lattice.Ordered.S) :
        S with type dom = Domain.t
           and type cod = Codomain.t
    end
  end
end

(** A bounded lattice has a least and greatest element *)
module Bounded : sig
  type 'a bounded =
    | Top
    | Bottom
    | Value of 'a

  (** Augment a lattice with least and greatest elements *)
  module Lift (L : Sig.Lattice.S) :
    Sig.Lattice.Bounded.S with type t = L.t bounded
  module Ordered : sig
    module Lift (L : Sig.Lattice.Ordered.S) :
      Sig.Lattice.Bounded.Ordered.S with type t = L.t bounded
  end

  (** Boolean algebra of finite + cofinite sets.  The type [S.elt] is assumed
      to have infinitely many inhabitants (so finite sets and cofinite sets
      are disjoint). *)
  module LiftSubset (S : Putil.Set.S) : sig
    type t = Set of S.t | Neg of S.t
    include Sig.Lattice.Bounded.Ordered.S with type t := t
    type elt = S.elt
    val complement : t -> t
    val is_empty : t -> bool
    val mem : elt -> t -> bool
    val add : elt -> t -> t
    val remove : elt -> t -> t
    val singleton : elt -> t
    val empty : t
    val universe : t
    val union : t -> t -> t
    val inter : t -> t -> t
    val diff : t -> t -> t
    val equal : t -> t -> bool
    val subset : t -> t -> bool
  end

  module FunctionSpace : sig
    (** Total function spaces where all but finitely many elements map to the
        same "default" value. *)
    module Total : sig
      module type S = sig
        include Sig.Lattice.Bounded.S
        include Sig.FunctionSpace.Total with type t := t
        (** [weak_update k v f] constructs a function which maps [k] to [join
            v (f k)] and all other elements [y] to [f y]. *)
        val weak_update : dom -> cod -> t -> t
      end

      (** [LiftMap(M)(Codomain)] constructs a total function space lattice
          where [M] is used as the underlying map representation.
          This is useful (for example) with tagged types, since
          Patricia trees support fast merging. *)
      module LiftMap (M : Putil.Map.S) (Codomain : Sig.Lattice.Bounded.S) :
        S with type dom = M.key
           and type cod = Codomain.t

      module Make (Domain : Putil.Ordered) (Codomain : Sig.Lattice.Bounded.S) :
        S with type dom = Domain.t
           and type cod = Codomain.t

      (** Total function space where every function that maps at least one
          point to bottom is identified with bottom *)
      module Smash (Domain : Putil.Ordered) (Codomain : Sig.Lattice.Bounded.S) :
        S with type dom = Domain.t
           and type cod = Codomain.t

      module Ordered : sig
        module type S = sig
          include S
          include Putil.OrderedMix with type t := t
        end
        module LiftMap
            (M : Putil.Map.S)
            (Codomain : Sig.Lattice.Bounded.Ordered.S) :
          S with type dom = M.key
             and type cod = Codomain.t
        module Make
            (Domain : Putil.Ordered)
            (Codomain : Sig.Lattice.Bounded.Ordered.S) :
          S with type dom = Domain.t
             and type cod = Codomain.t
      end
    end
  end
end

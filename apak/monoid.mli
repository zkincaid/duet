(** Operations on monoids.  A monoid is a set equipped with an associative
    binary operation and a unit for that operation. *)

module type S = Sig.Monoid.S
module Ordered : sig
  module type S = Sig.Monoid.Ordered.S
end

(** The monoid [(int,+,0)] *)
module ZPlus : Ordered.S with type t = int

(** Augment a semigroup with a unit to form a monoid *)
module AddUnit
  (M : sig
    include Putil.S
    val mul : t -> t -> t
    val equal : t -> t -> bool
  end) : sig
    include S

    (** Lift an element of the underlying semigroup into the monoid *)
    val lift : M.t -> t

    (** Drop an element of the monoid into the underyling semigroup; evaluates
	to [None] on the unit. *)
    val drop : t -> M.t option
  end

module FunctionSpace : sig
  (** Common signature for partial & total function spaces *)
  module type S = sig
    include Sig.Monoid.S
    type dom
    type cod
    val eval : t -> dom -> cod
    val map : (cod -> cod) -> t -> t
    val update : dom -> cod -> t -> t
    val enum : t -> (dom * cod) BatEnum.t
    val support : t -> dom BatEnum.t
  end

  (** Total function spaces where all but finitely many elements map to the
      same "default" value. *)
  module Total : sig
    module type S = sig
      include S
      (** [merge m f g] constructs the function which maps each [x] to
	  [m (f x) (g x)] *)
      val merge : (cod -> cod -> cod) -> t -> t -> t

      (** [default f] is the value to which [f] maps all elements of the
	  domain which are not in the support of [f]. *)
      val default : t -> cod

      (** [const k] constructs a function where every element of the domain is
	  mapped to [k] *)
      val const : cod -> t
    end

    (** [LiftMap(M)(Codomain)] constructs a total function space monoid where
	[M] is used as the underlying map representation.  This is useful (for
	example) with tagged types, since Patricia trees support fast
	merging. *)
    module LiftMap (M : Putil.Map.S) (Codomain : Sig.Monoid.S) :
      S with type dom = M.key
	and type cod = Codomain.t

    module Make (Domain : Putil.Ordered) (Codomain : Sig.Monoid.S) :
      S with type dom = Domain.t
	and type cod = Codomain.t

    module Ordered : sig
      module type S = sig
	include S
	include Putil.OrderedMix with type t := t
      end
      module LiftMap (M : Putil.Map.S) (Codomain : Sig.Monoid.Ordered.S) :
	S with type dom = M.key
	  and type cod = Codomain.t
      module Make (Domain : Putil.Ordered) (Codomain : Sig.Monoid.Ordered.S) :
	S with type dom = Domain.t
	  and type cod = Codomain.t
    end
  end

  (** Partial function spaces.  Multiplication is defined as
      - [(f*g) x = (f x)*(g x)] if [f x] and [g x] are defined
      - [(f*g) x = f x] if [f x] is defined and [g x] is not
      - [(f*g) x = g x] if [g x] is defined and [f x] is not
      - [(f*g) x] if [f x] and [g x] are undefined.
  *)
  module Partial : sig
    module type S = sig
      include S
      val partition : (dom -> cod -> bool) -> t -> (t * t)
      val filter : (dom -> cod -> bool) -> t -> t
      val fold : (dom -> cod -> 'a -> 'a) -> t -> 'a -> 'a
      val mapi : (dom -> cod -> cod) -> t -> t
      val merge : (dom -> cod option -> cod option -> cod option) -> t -> t -> t
    end

    (** [LiftMap(M)(Codomain)] constructs a partial function space monoid
	where [M] is used as the underlying map representation.  This is
	useful (for example) with tagged types, since Patricia trees support
	fast merging. *)
    module LiftMap (M : Putil.Map.S) (Codomain : Sig.Monoid.S) :
      S with type dom = M.key
	and type cod = Codomain.t

    module Make (Domain : Putil.Ordered) (Codomain : Sig.Monoid.S) :
      S with type dom = Domain.t
	and type cod = Codomain.t

    module Ordered : sig
      module type S = sig
	include S
	include Putil.OrderedMix with type t := t
      end
      module LiftMap (M : Putil.Map.S) (Codomain : Sig.Monoid.Ordered.S) :
	S with type dom = M.key
	  and type cod = Codomain.t
      module Make (Domain : Putil.Ordered) (Codomain : Sig.Monoid.Ordered.S) :
	S with type dom = Domain.t
	  and type cod = Codomain.t
    end
  end
end

module Semigroup = struct
  module type S = sig
    type t
    val mul : t -> t -> t
  end
end

module Monoid = struct
  module type S = sig
    include Putil.S
    val mul : t -> t -> t
    val equal : t -> t -> bool
    val unit : t
  end
  module Ordered = struct
    module type S = sig
      include S
      include Putil.OrderedMix with type t := t
    end
  end
end

module Semiring = struct
  module type S = sig
    include Putil.S
    val equal : t -> t -> bool
    val mul : t -> t -> t
    val add : t -> t -> t
    val zero : t
    val one : t
  end
end

module KA = struct
  module type S = sig
    include Putil.S
    val equal : t -> t -> bool
    val mul : t -> t -> t
    val add : t -> t -> t
    val zero : t
    val one : t
    val star : t -> t
  end
  module Quantified = struct
    module type S = sig
      include S
      type var
      val exists : (var -> bool) -> t -> t
    end
    module Ordered = struct
      module type S = sig
	include S
	include Putil.OrderedMix with type t := t
      end
    end
  end
  module Ordered = struct
    module type S = sig
      include S
      include Putil.OrderedMix with type t := t
    end
  end
end

module Semilattice = struct
  module type S = sig
    include Putil.S
    val join : t -> t -> t
    val equal : t -> t -> bool
  end
  module Bounded = struct
    module type S = sig
      include S
      val bottom : t
    end
    module Ordered = struct
      module type S = sig
	include S
	include Putil.OrderedMix with type t := t
      end
    end
  end
  module Ordered = struct
    module type S = sig
      include S
      include Putil.OrderedMix with type t := t
    end
  end
end

module Lattice = struct
  module type S = sig
    include Putil.S
    val join : t -> t -> t
    val meet : t -> t -> t
    val equal : t -> t -> bool
  end
  module Bounded = struct
    module type S = sig
      include S
      val top : t
      val bottom : t
    end
    module Ordered = struct
      module type S = sig
	include S
	include Putil.OrderedMix with type t := t
      end
    end
  end
  module Ordered = struct
    module type S = sig
      include S
      include Putil.OrderedMix with type t := t
    end
  end
end

module AbstractDomain = struct
  module type S = sig
    include Semilattice.Bounded.S
    val widen : t -> t -> t
  end
end

module FunctionSpace = struct
  module type S = sig
    type t
    type dom
    type cod
    val eval : t -> dom -> cod
    val map : (cod -> cod) -> t -> t
    val update : dom -> cod -> t -> t
    val enum : t -> (dom * cod) BatEnum.t
    val support : t -> dom BatEnum.t
  end
  module type Total = sig
    include S
    val merge : (cod -> cod -> cod) -> t -> t -> t
    val default : t -> cod
    val const : cod -> t
  end
  module type Partial = sig
    include S
    val partition : (dom -> cod -> bool) -> t -> (t * t)
    val filter : (dom -> cod -> bool) -> t -> t
    val fold : (dom -> cod -> 'a -> 'a) -> t -> 'a -> 'a
    val mapi : (dom -> cod -> cod) -> t -> t
    val merge : (dom -> cod option -> cod option -> cod option) -> t -> t -> t
  end
end

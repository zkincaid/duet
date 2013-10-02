(*pp camlp4find deriving.syntax *)

module type S = Sig.Semilattice.S
module Ordered = struct
  module type S = Sig.Semilattice.Ordered.S
end

module FunctionSpace = struct
  module type S = sig
    include Sig.Semilattice.S
    include Sig.FunctionSpace.S with type t := t
    val weak_update : dom -> cod -> t -> t
  end
  module Partial = struct
    module type S = sig
      include Sig.Semilattice.Bounded.S
      include Sig.FunctionSpace.Partial with type t := t
      val weak_update : dom -> cod -> t -> t
    end
    module LiftMap (M : Putil.Map.S) (Codomain : Sig.Semilattice.S) =
    struct
      type dom = M.key
      type cod = Codomain.t
      type t = cod M.t
      include Putil.MakeFmt(struct
	type a = t
	let format formatter map = M.format Codomain.format formatter map
      end)

      let equal = M.equal Codomain.equal
      let bottom = M.empty

      let join x y =
	let f _ a b =
	  match a, b with
	  | Some a, Some b -> Some (Codomain.join a b)
	  | Some x, _ | _, Some x -> Some x
	  | None, None -> assert false
	in
	M.merge f x y

      let update = M.add
      let weak_update k v f =
	try M.add k (Codomain.join v (M.find k f)) f
	with Not_found -> M.add k v f
      let partition = M.partition
      let filter = M.filter
      let map = M.map
      let mapi = M.mapi
      let fold = M.fold
      let enum = M.enum
      let support = M.keys
      let merge = M.merge
      let eval f x = M.find x f
    end
    module Make (Domain : Putil.Ordered) (Codomain : Sig.Semilattice.S) =
      LiftMap(Putil.Map.Make(Domain))(Codomain)
    module Ordered = struct
      module type S = sig
	include S
	include Putil.OrderedMix with type t := t
      end
      module LiftMap (M : Putil.Map.S) (Codomain : Sig.Semilattice.Ordered.S) =
      struct
	include LiftMap(M)(Codomain)
	module Compare_t = struct
	  type a = t
	  let compare = M.compare Codomain.compare
	end
	let compare = Compare_t.compare
      end
      module Make
	(Domain : Putil.Ordered)
	(Codomain : Sig.Semilattice.Ordered.S) =
	LiftMap(Putil.Map.Make(Domain))(Codomain)
    end
  end
  module Total = struct
    module type S = sig
      include Sig.Semilattice.S
      include Sig.FunctionSpace.Total with type t := t
      val weak_update : dom -> cod -> t -> t
    end
    module LiftMap (M : Putil.Map.S) (Codomain : Sig.Semilattice.S) = struct
      include Putil.TotalFunction.LiftMap(M)(Codomain)
      let join = merge Codomain.join
      let weak_update k v f = update k (Codomain.join v (eval f k)) f
    end
    module Make (Domain : Putil.Ordered) (Codomain : Sig.Semilattice.S) =
      LiftMap(Putil.Map.Make(Domain))(Codomain)
    module Ordered = struct
      module type S = sig
	include S
	include Putil.OrderedMix with type t := t
      end
      module LiftMap (M : Putil.Map.S) (Codomain : Sig.Semilattice.Ordered.S) =
      struct
	include Putil.TotalFunction.Ordered.LiftMap(M)(Codomain)
	let join = merge Codomain.join
	let weak_update k v f = update k (Codomain.join v (eval f k)) f
      end
      module Make
	(Domain : Putil.Ordered)
	(Codomain : Sig.Semilattice.Ordered.S) =
	LiftMap(Putil.Map.Make(Domain))(Codomain)
    end
  end
end

module Table (D : Hashtbl.HashedType) (C : S) = struct
  module HT = Hashtbl.Make(D)
  type t = C.t HT.t
  let create = HT.create
  let mem = HT.mem
  let clear = HT.clear
  let find = HT.find
  let add ht x y =
    try HT.replace ht x (C.join y (HT.find ht x))
    with Not_found -> HT.add ht x y
end

module Bounded = struct
  type 'a bounded =
    | Bottom
    | Value of 'a

  let format_bounded pp formatter = function
    | Bottom -> Format.pp_print_string formatter "_|_"
    | Value x -> pp formatter x

  module Lift(S : Sig.Semilattice.S) = struct
    type t = S.t bounded

    include Putil.MakeFmt(struct
      type a = t
      let format = format_bounded S.format
    end)

    let join d e = match (d, e) with
      | (Bottom, x) | (x, Bottom) -> x
      | (Value d, Value e) -> Value (S.join d e)
    let equal d e = match (d, e) with
      | (Bottom, Bottom) -> true
      | (Value d, Value e) -> S.equal d e
      | _ -> false
    let bottom = Bottom
  end
  module Monoid (S : Sig.Semilattice.Bounded.S) = struct
    type t = S.t deriving (Show)
    let format = Show_t.format
    let show = Show_t.show
    let equal = S.equal
    let mul = S.join
    let unit = S.bottom
  end
  module Ordered = struct
    module Monoid(S : Sig.Semilattice.Bounded.Ordered.S) = struct
      type t = S.t deriving (Show,Compare)
      let format = Show_t.format
      let show = Show_t.show
      let compare = Compare_t.compare
      let equal = S.equal
      let mul = S.join
      let unit = S.bottom
    end
  end
end

open Sig.Lattice

module type S = Sig.Lattice.S
module Ordered = struct
  module type S = Sig.Lattice.Ordered.S
end

module LiftSubset (S : Putil.Set.S) = struct
  include S
  let join = S.union
  let meet = S.inter
  let equal = S.equal
  let bottom = S.empty
end

module Dual (L : Sig.Lattice.S) = struct
  include L
  let join = L.meet
  let meet = L.join
end

module FunctionSpace = struct
  module type S = sig
    include Sig.Lattice.S
    include Sig.FunctionSpace.S with type t := t
    val weak_update : dom -> cod -> t -> t
  end
  module Partial = struct
    module type S = sig
      include Sig.Lattice.S
      include Sig.FunctionSpace.Partial with type t := t
      val weak_update : dom -> cod -> t -> t
      val bottom : t
    end
    module LiftMap (M : Putil.Map.S) (Codomain : Sig.Lattice.S) =
    struct
      include Semilattice.FunctionSpace.Partial.LiftMap(M)(Codomain)
      let meet x y =
        let f _ a b =
          match a, b with
          | Some a, Some b -> Some (Codomain.meet a b)
          | _, _ -> None
        in
        merge f x y
    end
    module Make (Domain : Putil.Ordered) (Codomain : Sig.Lattice.S) =
      LiftMap(Putil.Map.Make(Domain))(Codomain)
    module Ordered = struct
      module type S = sig
        include S
        include Putil.OrderedMix with type t := t
      end
      module LiftMap (M : Putil.Map.S) (Codomain : Sig.Lattice.Ordered.S) =
      struct
        include Semilattice.FunctionSpace.Partial.Ordered.LiftMap(M)(Codomain)
        let meet x y =
          let f _ a b =
            match a, b with
            | Some a, Some b -> Some (Codomain.meet a b)
            | _, _ -> None
          in
          merge f x y
      end
      module Make
          (Domain : Putil.Ordered)
          (Codomain : Sig.Lattice.Ordered.S) =
        LiftMap(Putil.Map.Make(Domain))(Codomain)
    end
  end
  module Total = struct
    module type S = sig
      include Sig.Lattice.S
      include Sig.FunctionSpace.Total with type t := t
      val weak_update : dom -> cod -> t -> t
    end
    module LiftMap (M : Putil.Map.S) (Codomain : Sig.Lattice.S) = struct
      include Putil.TotalFunction.LiftMap(M)(Codomain)
      let join = merge Codomain.join
      let meet = merge Codomain.meet
      let weak_update k v f = update k (Codomain.join v (eval f k)) f
    end
    module Make (Domain : Putil.Ordered) (Codomain : Sig.Lattice.S) =
      LiftMap(Putil.Map.Make(Domain))(Codomain)
    module Ordered = struct
      module type S = sig
        include S
        include Putil.OrderedMix with type t := t
      end
      module LiftMap (M : Putil.Map.S) (Codomain : Sig.Lattice.Ordered.S) =
      struct
        include Putil.TotalFunction.Ordered.LiftMap(M)(Codomain)
        let join = merge Codomain.join
        let meet = merge Codomain.meet
        let weak_update k v f = update k (Codomain.join v (eval f k)) f
      end
      module Make
          (Domain : Putil.Ordered)
          (Codomain : Sig.Lattice.Ordered.S) =
        LiftMap(Putil.Map.Make(Domain))(Codomain)
    end
  end
end

module Bounded = struct
  open Sig.Lattice.Bounded

  type 'a bounded =
    | Top
    | Bottom
    | Value of 'a

  let format_bounded pp formatter = function
    | Bottom -> Format.pp_print_string formatter "_|_"
    | Top -> Format.pp_print_string formatter "T"
    | Value x -> pp formatter x

  module Lift (L : Sig.Lattice.S) = struct
    type t = L.t bounded

    include Putil.MakeFmt(struct
        type a = t
        let format = format_bounded L.format
      end)

    let join d e = match (d, e) with
      | (Top, x) | (x, Top) -> Top
      | (Bottom, x) | (x, Bottom) -> x
      | (Value d, Value e) -> Value (L.join d e)
    let meet x y = match x, y with
      | (Top, x) | (x, Top) -> x
      | (Bottom, _) | (_, Bottom) -> Bottom
      | (Value x, Value y) -> Value (L.meet x y)
    let equal d e = match (d, e) with
      | (Bottom, Bottom) -> true
      | (Top, Top) -> true
      | (Value d, Value e) -> L.equal d e
      | _ -> false
    let top = Top
    let bottom = Bottom
  end

  module LiftSubset (S : Putil.Set.S) = struct
    type t =
      | Set of S.t
      | Neg of S.t
            deriving (Compare)
    type elt = S.elt

    include Putil.MakeFmt(struct
        type a = t
        let format formatter = function
          | Set x -> S.format formatter x
          | Neg x -> Format.fprintf formatter "@[complement(%a)@]" S.format x
      end)
    let compare = Compare_t.compare

    let join x y = match x, y with
      | (Set a, Set b) -> Set (S.union a b)
      | (Neg a, Neg b) -> Neg (S.inter a b)
      | (Set a, Neg b) | (Neg b, Set a) -> Neg (S.diff b a)

    let meet x y = match x, y with
      | (Set a, Set b) -> Set (S.inter a b)
      | (Neg a, Neg b) -> Neg (S.union a b)
      | (Set a, Neg b) | (Neg b, Set a) -> Set (S.diff a b)

    let bottom = Set S.empty
    let top = Neg S.empty

    let complement = function
      | Set x -> Neg x
      | Neg x -> Set x

    let empty = bottom
    let universe = top

    (** Assumes an infinite universe, so {!Neg a} is never empty *)
    let is_empty = function
      | Set x -> S.is_empty x
      | Neg _ -> false

    let mem elt = function
      | Set x -> S.mem elt x
      | Neg x -> not (S.mem elt x)

    let add elt = function
      | Set x -> Set (S.add elt x)
      | Neg x -> Neg (S.remove elt x)

    let singleton elt = Set (S.singleton elt)

    let remove elt = function
      | Set x -> Set (S.remove elt x)
      | Neg x -> Neg (S.add elt x)

    let union = join
    let inter = meet

    let diff x y = inter x (complement y)

    (** Assumes an infinite universe (so {!Set a} and {!Neg b} can never be
        equal). *)
    let equal x y = match x, y with
      | (Set a, Set b) | (Neg a, Neg b) -> S.equal a b
      | _ -> false

    (** Assumes an infinite universe (so {!Neg a} can never be a subset of
        {!Set a}) *)
    let subset x y = match x, y with
      | (Set x, Set y) -> S.subset x y
      | (Set x, Neg y) -> S.is_empty (S.inter x y)
      | (Neg x, Set y) -> false
      | (Neg x, Neg y) -> S.subset y x
  end

  module FunctionSpace = struct
    module Total = struct
      module type S = sig
        include Sig.Lattice.Bounded.S
        include Sig.FunctionSpace.Total with type t := t
        val weak_update : dom -> cod -> t -> t
      end
      module LiftMap (M : Putil.Map.S) (Codomain : Sig.Lattice.Bounded.S) =
      struct
        include FunctionSpace.Total.LiftMap(M)(Codomain)
        let top = const Codomain.top
        let bottom = const Codomain.bottom
      end
      module Make (Domain : Putil.Ordered) (Codomain : Sig.Lattice.Bounded.S) =
        LiftMap(Putil.Map.Make(Domain))(Codomain)

      module Smash (Domain : Putil.Ordered) (Codomain : Sig.Lattice.Bounded.S) =
      struct
        module M = Putil.TotalFunction.LiftMap(Putil.Map.Make(Domain))(Codomain)
        (* Todo: we can get rid of bottom, and just represent it with const
           bottom *)
        type t =
          | Bottom
          | Map of M.t
        type dom = Domain.t
        type cod = Codomain.t

        include Putil.MakeFmt(struct
            type a = t
            let format formatter = function
              | Bottom -> Format.pp_print_string formatter "_|_"
              | Map f -> M.format formatter f
          end)

        let equal f g = match f,g with
          | Bottom, Bottom -> true
          | Bottom, _ | _, Bottom -> false
          | Map f, Map g -> M.equal f g

        let top = Map (M.const Codomain.top)
        let bottom = Bottom

        let update k v = function
          | Bottom -> Bottom
          | Map f ->
            if Codomain.equal v Codomain.bottom then Bottom
            else Map (M.update k v f)

        let eval f x = match f with
          | Bottom -> Codomain.bottom
          | Map f -> M.eval f x

        let weak_update k v f = update k (Codomain.join v (eval f k)) f

        let join x y = match x, y with
          | x, Bottom | Bottom, x -> x
          | Map f, Map g -> Map (M.merge Codomain.join f g)

        exception Bot
        let meet x y =
          let meet x y =
            let z = Codomain.meet x y in
            if Codomain.equal z Codomain.bottom then raise Bot
            else z
          in
          match x, y with
          | x, Bottom | Bottom, x -> Bottom
          | Map f, Map g ->
            try Map (M.merge meet f g)
            with Bot -> Bottom

        let const k =
          if Codomain.equal k Codomain.bottom then Bottom else Map (M.const k)
        let default = function
          | Map f -> M.default f
          | Bottom -> Codomain.bottom

        let merge m f g =
          let op x y =
            let z = m x y in
            if Codomain.equal z Codomain.bottom then raise Bot
            else z
          in
          let f = match f with
            | Bottom -> M.const Codomain.bottom
            | Map f -> f
          in
          let g = match g with
            | Bottom -> M.const Codomain.bottom
            | Map g -> g
          in
          try Map (M.merge op f g)
          with Bot -> Bottom
        let support = function
          | Map m -> M.support m
          | Bottom -> BatEnum.empty ()
        let enum = function
          | Map m -> M.enum m
          | Bottom -> BatEnum.empty ()
        let map f = function
          | Bottom -> const (f Codomain.bottom)
          | Map x ->
            let g x =
              let y = f x in
              if Codomain.equal y Codomain.bottom then raise Bot else y
            in
            try Map (M.map g x)
            with Bot -> Bottom
      end

      module Ordered = struct
        module type S = sig
          include S
          include Putil.OrderedMix with type t := t
        end
        module LiftMap
            (M : Putil.Map.S)
            (Codomain : Sig.Lattice.Bounded.Ordered.S) =
        struct
          include FunctionSpace.Total.Ordered.LiftMap(M)(Codomain)
          let top = const Codomain.top
          let bottom = const Codomain.bottom
        end
        module Make
            (Domain : Putil.Ordered)
            (Codomain : Sig.Lattice.Bounded.Ordered.S) =
          LiftMap(Putil.Map.Make(Domain))(Codomain)
      end
    end
  end
  module Ordered = struct
    open Ordered (* Sig.Lattice.Bounded.Ordered *)
    module Lift (L : Sig.Lattice.Ordered.S) = struct
      include Lift(L)
      let compare x y = match x,y with
        | (Top, Top) -> 0
        | (Top, _) -> 1
        | (_, Top) -> -1
        | (Bottom, Bottom) -> 0
        | (Bottom, _) -> 1
        | (_, Bottom) -> -1
        | (Value x, Value y) -> L.compare x y
      module Compare_t = struct
        type a = t
        let compare = compare
      end
    end
  end
end

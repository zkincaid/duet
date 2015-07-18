module type S = Sig.Monoid.S
module Ordered = struct
  module type S = Sig.Monoid.Ordered.S
end

module ZPlus : Ordered.S with type t = int =
struct
  type t = int [@@deriving show,ord]

  let mul x y = x + y
  let equal x y = (x = y)
  let unit = 0
end

module AddUnit (M : sig
    include Putil.S
    val mul : t -> t -> t
    val equal : t -> t -> bool
  end) = struct
  type t = M.t option

  let pp formatter = function
    | None -> Format.pp_print_string formatter "Unit"
    | Some x -> M.pp formatter x

  let mul x y = match x, y with
    | (Some x, Some y) -> Some (M.mul x y)
    | (x, None) | (None, x) -> x

  let equal x y = match x, y with
    | (Some x, Some y) -> M.equal x y
    | (None, None) -> true
    | (_, _) -> false

  let unit = None
  let lift x = Some x
  let drop x = x
end

module FunctionSpace = struct
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
  module Partial = struct

    module type S = sig
      include S
      val partition : (dom -> cod -> bool) -> t -> (t * t)
      val filter : (dom -> cod -> bool) -> t -> t
      val fold : (dom -> cod -> 'a -> 'a) -> t -> 'a -> 'a
      val mapi : (dom -> cod -> cod) -> t -> t
      val merge : (dom -> cod option -> cod option -> cod option) -> t -> t -> t
    end

    module LiftMap (M : Putil.Map.S) (Codomain : Sig.Monoid.S) =
    struct
      type dom = M.key
      type cod = Codomain.t
      type t = Codomain.t M.t [@@deriving show]

      let equal = M.equal Codomain.equal
      let unit = M.empty

      let mul x y =
        let f _ a b =
          match a, b with
          | Some a, Some b -> Some (Codomain.mul a b)
          | Some x, _ | _, Some x -> Some x
          | None, None -> assert false
        in
        M.merge f x y

      let update = M.add
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

    module Make (Domain : Putil.Ordered) (Codomain : Sig.Monoid.S) =
      LiftMap(Putil.Map.Make(Domain))(Codomain)

    module Ordered = struct
      module type S = sig
        include S
        include Putil.OrderedMix with type t := t
      end
      module LiftMap (M : Putil.Map.S) (Codomain : Sig.Monoid.Ordered.S) =
      struct
        include LiftMap(M)(Codomain)
        module Compare_t = struct
          type a = t
          let compare = M.compare Codomain.compare
        end
        let compare = Compare_t.compare
      end
      module Make (Domain : Putil.Ordered) (Codomain : Sig.Monoid.Ordered.S) =
        LiftMap(Putil.Map.Make(Domain))(Codomain)
    end
  end
  module Total = struct
    module type S = sig
      include S
      val merge : (cod -> cod -> cod) -> t -> t -> t
      val default : t -> cod
      val const : cod -> t
    end

    module LiftMap (M : Putil.Map.S) (Codomain : Sig.Monoid.S) =
    struct
      type dom = M.key
      type cod = Codomain.t
      type t =
        { map : Codomain.t M.t;
          default : Codomain.t }
          [@@deriving show]

      let equal f g =
        Codomain.equal f.default g.default
        && M.equal Codomain.equal f.map g.map

      let const v = { map = M.empty; default = v }
      let unit = const Codomain.unit

      let update k v f =
        if Codomain.equal f.default v
        then if M.mem k f.map then { f with map = M.remove k f.map } else f
        else { f with map = M.add k v f.map }

      let eval f x =
        try M.find x f.map
        with Not_found -> f.default

      let merge m f g =
        let default = m f.default g.default in
        let return x = if Codomain.equal x default then None else Some x in
        let merge _ a b = match a,b with
          | Some a, Some b -> return (m a b)
          | Some a, _ -> return (m a g.default)
          | _, Some b -> return (m f.default b)
          | None, None -> assert false
        in
        { map = M.merge merge f.map g.map;
          default = default }

      let mul = merge Codomain.mul

      let unit = { map = M.empty; default = Codomain.unit }

      let map f x =
        { map = M.map f x.map;
          default = f x.default }
      let enum f = M.enum f.map
      let support f = M.keys f.map
      let default f = f.default
    end

    module Make (Domain : Putil.Ordered) (Codomain : Sig.Monoid.S) =
      LiftMap(Putil.Map.Make(Domain))(Codomain)

    module Ordered = struct
      module type S = sig
        include S
        include Putil.OrderedMix with type t := t
      end
      module LiftMap (M : Putil.Map.S) (Codomain : Sig.Monoid.Ordered.S) =
      struct
        include LiftMap(M)(Codomain)
        module Compare_t = struct
          type a = t
          let compare f g =
            match Codomain.compare f.default g.default with
            | 0 -> M.compare Codomain.compare f.map g.map
            | x -> x
        end
        let compare = Compare_t.compare
      end
      module Make (Domain : Putil.Ordered) (Codomain : Sig.Monoid.Ordered.S) =
        LiftMap(Putil.Map.Make(Domain))(Codomain)
    end
  end
end

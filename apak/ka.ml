open Ark

open Sig.KA

(** Compute x* as 1 + x + xx + xxx + ... Diverges if the sequence does.*)
let generic_star equal mul add one x =
  let rec fix s =
    let next = mul s s in
    if equal s next then s else fix next
  in
  fix (add one x)

(** Augment a structure with an additive unit *)
module AddZero(M : sig
    include Putil.Ordered
    val equal : t -> t -> bool
    val mul : t -> t -> t
    val add : t -> t -> t
    val star : t -> t
    val one : t
  end) = struct
  type t = Zero | Nonzero of M.t
               [@@deriving ord]

  let pp formatter = function
    | Zero -> Format.pp_print_int formatter 0
    | Nonzero x -> M.pp formatter x
  let show = ArkUtil.mk_show pp

  let equal x y = match x,y with
    | (Nonzero x, Nonzero y) -> M.equal x y
    | (Zero, Zero) -> true
    | (_, _) -> false

  let strict f = function
    | Nonzero x -> Nonzero (f x)
    | Zero -> Zero
  let strict_binary f x y = match x,y with
    | (Nonzero x, Nonzero y) -> Nonzero (f x y)
    | (_, _) -> Zero

  let mul = strict_binary M.mul
  let add x y = match x, y with
    | (Zero, x) | (x, Zero) -> x
    | (Nonzero x, Nonzero y) -> Nonzero (M.add x y)
  let star = function
    | Zero -> Nonzero M.one
    | Nonzero x -> Nonzero (M.star x)
  let zero = Zero
  let one = Nonzero M.one
end

(** Lift a monoid to a Kleene algebra by taking its disjunctive completion.
    This is safe if the monoid is finite; otherwise, care needs to be taken to
    ensure that star does not diverge.  *)
module ReducedDisjCompletion (M : sig
    include Sig.Monoid.Ordered.S
    val implies : t -> t -> bool
  end) = struct
  module S = Putil.Set.Make(M)
  type t = S.t [@@deriving show,ord]

  let equal x y = compare x y = 0
  let zero = S.empty
  let one = S.singleton M.unit

  let strict_implies x y = not (M.equal x y) && (M.implies x y)

  let add x y =
    let add_x a s =
      if S.exists (M.implies a) s then s
      else S.add a s
    in
    let add_y a s =
      if S.exists (strict_implies a) x then s
      else S.add a s
    in
    S.fold add_x x (S.fold add_y y S.empty)

  let reduce set =
    let add x s =
      if S.exists (strict_implies x) set then s else S.add x s
    in
    Log.time "Reduce [disjunctive completion]" (S.fold add set) S.empty

  (** {!mul} is O(m*n), where m is the number of minterms in x, and n is the
      number of minterms in y *)
  let mul x y =
    let g a b = S.add (M.mul a b) in
    let f a = S.fold (g a) y in
    let result =
      Log.time "mul [disjunctive completion] " (S.fold f x) S.empty
    in
    reduce result

  let star x =
    let rec fix s =
      let next = mul s s in
      if equal s next then s else fix next
    in
    fix (add one x)

  (*  let star = generic_star equal mul add one*)
end

(** Lift a monoid to a Kleene algebra by taking its disjunctive completion.
    This is safe if the monoid is finite; otherwise, care needs to be taken to
    ensure that star does not diverge.  *)
module DisjCompletion (M : Sig.Monoid.Ordered.S) = struct
  module S = Putil.Set.Make(M)
  type t = S.t [@@deriving show,ord]

  let equal x y = compare x y = 0
  let zero = S.empty
  let one = S.singleton M.unit
  let add = S.union

  (** {!mul} is O(m*n), where m is the number of minterms in x, and n is the
      number of minterms in y *)
  let mul x y =
    (*    print_endline ("MUL " ^ (string_of_int (S.cardinal x)) ^ " * " ^ (string_of_int (S.cardinal y)));*)
    let g a b = S.add (M.mul a b) in
    let f a = S.fold (g a) y in
    let res = S.fold f x S.empty in
    (*      print_endline ("res " ^ (string_of_int (S.cardinal res)));*)
    res

  let star x =
    let rec fix s =
      let next = mul s s in
      if equal s next then s else fix next
    in
    fix (add one x)

  (*  let star = generic_star equal mul add one*)
end

module AdditiveMonoid (K : S) : Sig.Monoid.S with type t = K.t =
struct
  type t = K.t [@@deriving show]

  let mul = K.add
  let equal = K.equal
  let unit = K.zero
end

module MultiplicativeMonoid (K : S) : Sig.Monoid.S with type t = K.t =
struct
  type t = K.t [@@deriving show]

  let mul = K.mul
  let equal = K.equal
  let unit = K.one
end


(** Function space Kleene algebra.  All but finitely many elements of the
    domain are mapped to the same element of the Kleene algebra. *)
module FunctionSpace = struct
  module Make (Domain : Putil.Ordered) (Codomain : S) = struct
    module M = Putil.MonoMap.Make(Domain)(Codomain)
    type t = { map : M.t;
               default : Codomain.t }
        [@@deriving show]

    let equal f g =
      Codomain.equal f.default g.default
      && M.equal Codomain.equal f.map g.map

    let singleton k v default =
      { map = M.add k v M.empty;
        default = default }

    let empty default =
      { map = M.empty;
        default = default }

    let set_default f default = { f with default = default }

    let map_codomain func f =
      { map = M.map func f.map;
        default = func f.default }

    let eval f x =
      try M.find x f.map
      with Not_found -> f.default

    let pointwise combine f g =
      let add_f k v map =
        M.add k (combine v (eval g k)) map
      in
      let add_g k v map =
        if M.mem k f.map then map
        else M.add k (combine f.default v) map
      in
      { map = M.fold add_g g.map (M.fold add_f f.map M.empty);
        default = combine f.default g.default }

    let mul = pointwise Codomain.mul
    let add = pointwise Codomain.add

    let zero =
      { map = M.empty;
        default = Codomain.zero }
    let one =
      { map = M.empty;
        default = Codomain.one }
    let star f =
      { map = M.map Codomain.star f.map;
        default = Codomain.star f.default }
  end
end

module MakePath (Domain : Putil.Ordered) (Codomain : Ordered.S) =
struct
  module M = Putil.MonoMap.Ordered.Make(Domain)(Codomain)
  type t = { map : M.t;
             default : Codomain.t }
      [@@deriving show,ord]

  let equal f g =
    Codomain.equal f.default g.default
    && M.equal Codomain.equal f.map g.map

  let singleton k v default =
    { map = M.add k v M.empty;
      default = default }

  let empty default =
    { map = M.empty;
      default = default }

  let map_codomain func f =
    { map = M.map func f.map;
      default = func f.default }

  let eval f x =
    try M.find x f.map
    with Not_found -> Codomain.zero

  let pointwise combine f g =
    let add_f k v map =
      M.add k (combine v (eval g k)) map
    in
    let add_g k v map =
      if M.mem k f.map then map
      else M.add k (combine f.default v) map
    in
    { map = M.fold add_g g.map (M.fold add_f f.map M.empty);
      default = combine f.default g.default }

  let add_map fmap gmap =
    let add_f k v map =
      if M.mem k gmap then M.add k (Codomain.add v (M.find k gmap)) map
      else M.add k v map
    in
    let add_g k v map =
      if M.mem k fmap then map
      else M.add k v map
    in
    M.fold add_g gmap (M.fold add_f fmap M.empty)

  let add f g =
    { map = add_map f.map g.map;
      default = Codomain.add f.default g.default }

  let mul f g =
    let extend_g = M.map (Codomain.mul f.default) g.map in
    { map = add_map f.map extend_g;
      default = Codomain.mul f.default g.default }

  let zero =
    { map = M.empty;
      default = Codomain.zero }
  let one =
    { map = M.empty;
      default = Codomain.one }
  let star f =
    let default = Codomain.star f.default in
    { map = M.map (Codomain.mul default) f.map;
      default = default }
end

module MakeRevPath (Domain : Putil.Ordered) (Codomain : Ordered.S) =
struct
  include MakePath(Domain)(Codomain)

  let mul f g =
    let extend_f = M.map (fun x -> Codomain.mul x g.default) f.map in
    { map = add_map extend_f g.map;
      default = Codomain.mul f.default g.default }

  let star f =
    let default = Codomain.star f.default in
    { map = M.map (fun x -> Codomain.mul x default) f.map;
      default = default }
end

module MakePointedFS
    (Domain : Putil.Ordered)
    (Codomain : Ordered.S) =
struct
  type path = { left : Codomain.t;
                right : Codomain.t }
      [@@deriving show,ord]
  module Path = struct
    type t = path [@@deriving show,ord]
  end
  module M = Putil.MonoMap.Ordered.Make(Domain)(Path)
  type t = { map : M.t;
             default : Codomain.t }
      [@@deriving show,ord]

  let path_equal x y = Path.compare x y = 0

  let path_add x y =
    { left = Codomain.add x.left y.left;
      right = Codomain.add x.right y.right }

  let equal f g = compare f g = 0

  let singleton k left right default =
    let v = { left = left;
              right = right }
    in
    { map = M.add k v M.empty;
      default = default }

  let empty default =
    { map = M.empty;
      default = default }

  let map_codomain func f =
    let path_func x =
      { left = func x.left;
        right = func x.right }
    in
    { map = M.map path_func f.map;
      default = func f.default }

  let eval_left f x =
    try (M.find x f.map).left
    with Not_found -> f.default

  let eval_right f x =
    try (M.find x f.map).right
    with Not_found -> f.default

  let add_map m n =
    let add k v map =
      let value = 
        try path_add v (M.find k map)
        with Not_found -> v
      in
      M.add k value map
    in
    M.fold add m n

  let add f g =
    { map = add_map f.map g.map;
      default = Codomain.mul f.default g.default }

  let mul f g =
    let f_extend_right =
      M.map (fun x -> { x with right = Codomain.mul x.right g.default}) f.map
    in
    let g_extend_left =
      M.map (fun x -> { x with left = Codomain.mul f.default x.left}) g.map
    in
    { map = add_map f_extend_right g_extend_left;
      default = Codomain.mul f.default g.default }

  let zero =
    { map = M.empty;
      default = Codomain.zero }
  let one =
    { map = M.empty;
      default = Codomain.one }
  let star f = 
    let default = Codomain.star f.default in
    let extend x =
      { left = Codomain.mul default x.left;
        right = Codomain.mul x.right default }
    in
    { map = M.map extend f.map;
      default = default }

  let compare f g =
    let cmp = Codomain.compare f.default g.default in
    if cmp != 0 then cmp
    else M.compare f.map g.map
end

module Ordered = struct
  module FunctionSpace = struct
    module Make (Domain : Putil.Ordered) (Codomain : Ordered.S) = struct
      include FunctionSpace.Make(Domain)(Codomain)
      let compare f g =
        let cmp = Codomain.compare f.default g.default in
        if cmp != 0 then cmp
        else M.compare Codomain.compare f.map g.map
    end
  end

  module AdditiveMonoid (K : Ordered.S) = struct
    include AdditiveMonoid(K)
    let compare = K.compare
  end

  module MultiplicativeMonoid (K : Ordered.S) = struct
    include MultiplicativeMonoid(K)
    let compare = K.compare
  end
end

(** ZMin is a Kleene algebra of integers, extended with positive and negative
    infinity, where
    - multiplication is integer addition
    - addition is minimum
    - star x is negative infinity if x is negative, and 0 otherwise.

    ZMin can be used to compute shortest path lengths using Kleene's
    algorithm. *)
module ZMin =
struct
  type t = 
    | PosInfinity
    | NegInfinity
    | Z of int
          [@@deriving ord]
  let pp formatter = function
    | PosInfinity -> Format.pp_print_string formatter "+infinity"
    | NegInfinity -> Format.pp_print_string formatter "-infinity"
    | Z x -> Format.pp_print_int formatter x
  let show = ArkUtil.mk_show pp

  let equal = (=)

  let star = function
    | Z x -> if x < 0 then NegInfinity else Z 0
    | PosInfinity -> Z 0
    | NegInfinity -> NegInfinity
  let mul x y = match x,y with
    | (PosInfinity, _) -> PosInfinity
    | (_, PosInfinity) -> PosInfinity
    | (NegInfinity, _) -> NegInfinity
    | (_, NegInfinity) -> NegInfinity
    | (Z x, Z y)       -> Z (x + y)
  let add x y = match x,y with
    | (PosInfinity, x) -> x
    | (x, PosInfinity) -> x
    | (NegInfinity, _) -> NegInfinity
    | (_, NegInfinity) -> NegInfinity
    | (Z x, Z y)       -> Z (min x y)
  let zero = PosInfinity
  let one = Z 0
end

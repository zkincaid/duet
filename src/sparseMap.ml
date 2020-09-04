module type S = sig
  type t
  type key
  type value
  val equal : t -> t -> bool
  val get : key -> t -> value
  val set : key -> value -> t -> t
  val zero : t
  val singleton : key -> value -> t
  val is_zero : t -> bool
  val merge : (key -> value -> value -> value) -> t -> t -> t
  val map : (key -> value -> value) -> t -> t
  val extract : key -> t -> (value * t)
  val enum : t-> (key * value) BatEnum.t
  val of_enum : (key * value) BatEnum.t -> t
  val fold : (key -> value -> 'a -> 'a) -> t -> 'a -> 'a
  val min_support : t -> (key * value)
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
          end) = struct

  module M = BatMap.Make(K)

  type t = V.t M.t
  type key = M.key
  type value = V.t

  let equal = M.equal V.equal

  let enum = M.enum

  let get k m = M.find_default V.zero k m

  let set k v m =
    if V.equal v V.zero then
      M.remove k m
    else
      M.add k v m

  let zero = M.empty

  let merge f m n =
    let g k v1 v2 =
      let v1 = BatOption.default V.zero v1 in
      let v2 = BatOption.default V.zero v2 in
      let result = f k v1 v2 in
      if V.equal result V.zero then
        None
      else
        Some result
    in
    M.merge g m n

  let map f m =
    M.filter_map
      (fun k v ->
        let result = f k v in
        if V.equal result V.zero then
          None
        else
          Some result)
      m

  let extract dim map =
    try M.extract dim map
    with Not_found -> (V.zero, map)

  let singleton key value =
    if V.equal value V.zero then
      zero
    else
      M.add key value M.empty

  let of_enum e = BatEnum.fold (fun m (k, v) -> set k v m) zero e

  let fold = M.fold
  let hash f m = Hashtbl.hash (List.map f (BatList.of_enum (enum m)))
  let compare = M.compare
  let min_support = M.min_binding
  let pop = M.pop
  let is_zero = M.is_empty
end

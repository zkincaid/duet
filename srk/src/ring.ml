open BatPervasives

module IntMap = SrkUtil.Int.Map
module IntSet = SrkUtil.Int.Set

include Log.Make(struct let name = "srk.ring" end)

module type AbelianGroup = sig
  type t
  val equal : t -> t -> bool
  val add : t -> t -> t
  val negate : t -> t
  val zero : t
end

module type S = sig
  include AbelianGroup
  val mul : t -> t -> t
  val one : t
end

module type Map = sig
  type 'a t
  type key

  val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
  val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
  val enum : 'a t -> (key * 'a) BatEnum.t
  val map : ('a -> 'b) -> 'a t -> 'b t
  val find : key -> 'a t -> 'a
  val add : key -> 'a -> 'a t -> 'a t
  val remove : key -> 'a t -> 'a t
  val empty : 'a t
  val merge : (key -> 'a option -> 'b option -> 'c option) ->
    'a t ->
    'b t ->
    'c t
end

module type Vector = sig
  type t
  type dim
  type scalar
  val equal : t -> t -> bool
  val add : t -> t -> t
  val scalar_mul : scalar -> t -> t
  val negate : t -> t
  val sub : t -> t -> t
  val dot : t -> t -> scalar
  val zero : t
  val is_zero : t -> bool
  val add_term : scalar -> dim -> t -> t
  val of_term : scalar -> dim -> t
  val enum : t -> (scalar * dim) BatEnum.t
  val of_enum : (scalar * dim) BatEnum.t -> t
  val of_list : (scalar * dim) list -> t
  val coeff : dim -> t -> scalar
  val pivot : dim -> t -> scalar * t
end

module type Matrix = sig
  type t
  type dim = int
  type scalar
  type vector

  val equal : t -> t -> bool
  val add : t -> t -> t
  val scalar_mul : scalar -> t -> t
  val mul : t -> t -> t

  val zero : t

  val identity : dim list -> t

  val row : dim -> t -> vector

  val rowsi : t -> (dim * vector) BatEnum.t

  val min_row : t -> dim * vector

  val add_row : dim -> vector -> t -> t

  val add_column : dim -> vector -> t -> t

  val add_entry : dim -> dim -> scalar -> t -> t

  val pivot : dim -> t -> vector * t

  val transpose : t -> t

  val entry : dim -> dim -> t -> scalar

  val entries : t -> (dim * dim * scalar) BatEnum.t

  val row_set : t -> SrkUtil.Int.Set.t
  val column_set : t -> SrkUtil.Int.Set.t

  val nb_rows : t -> int
  val nb_columns : t -> int

  val map_rows : (vector -> vector) -> t -> t

  val vector_right_mul : t -> vector -> vector
  val vector_left_mul : vector -> t -> vector
  val of_dense : scalar array array -> t
  val dense_of : t -> int -> int -> scalar array array
end

module AbelianGroupMap (M : Map) (G : AbelianGroup) = struct
  type t = G.t M.t
  type dim = M.key
  type scalar = G.t

  let is_scalar_zero x = G.equal x G.zero

  let zero = M.empty

  let is_zero = M.equal G.equal zero

  let add u v =
    let f _ a b =
      match a, b with
      | Some a, Some b ->
        let sum = G.add a b in
        if is_scalar_zero sum then None else Some sum
      | Some x, None | None, Some x -> Some x
      | None, None -> assert false
    in
    M.merge f u v

  let add_term coeff dim vec =
    if is_scalar_zero coeff then vec else begin
      try
        let sum = G.add coeff (M.find dim vec) in
        if not (is_scalar_zero sum) then M.add dim sum vec
        else M.remove dim vec
      with Not_found -> M.add dim coeff vec
    end

  let coeff dim vec = try M.find dim vec with Not_found -> G.zero

  let enum vec = M.enum vec /@ (fun (x,y) -> (y,x))

  let of_enum = BatEnum.fold (fun vec (x,y) -> add_term x y vec) zero

  let of_list = List.fold_left (fun vec (x,y) -> add_term x y vec) zero

  let equal = M.equal G.equal

  let compare = M.compare

  let of_term coeff dim = add_term coeff dim zero

  let negate = M.map G.negate

  let sub u v = add u (negate v)

  let pivot dim vec =
    (coeff dim vec, M.remove dim vec)
end

module RingMap (M : Map) (R : S) = struct
  include AbelianGroupMap(M)(R)

  let scalar_mul k vec =
    if R.equal k R.one then vec
    else if R.equal k R.zero then M.empty
    else M.map (fun coeff -> R.mul k coeff) vec

  let dot u v =
    BatEnum.fold
      (fun sum (co, i) -> R.add sum (R.mul co (coeff i v)))
      R.zero
      (enum u)
end

module MakeVector (R : S) = RingMap(IntMap)(R)

module MakeMatrix (R : S) = struct
  module V = MakeVector(R)
  module M = AbelianGroupMap(IntMap)(V)
  type t = M.t
  type dim = int
  type scalar = R.t
  type vector = V.t

  let scalar_mul k mat =
    if R.equal k R.one then mat
    else if R.equal k R.zero then IntMap.empty
    else IntMap.map (fun vec -> V.scalar_mul k vec) mat

  let row = M.coeff
  let add = M.add
  let zero = M.zero

  let equal = M.equal
  let pivot = M.pivot
  let compare = IntMap.compare
  let add_row i vec = M.add_term vec i
  let rows = IntMap.values
  let rowsi = IntMap.enum
  let entry i j mat = V.coeff j (row i mat)

  let add_entry i j k mat =
    add_row i (V.of_term k j) mat

  let identity = List.fold_left (fun m d -> add_entry d d R.one m) zero

  let add_column i col mat =
    BatEnum.fold
      (fun mat (co,j) -> add_entry j i co mat)
      mat
      (V.enum col)

  let entries mat =
    rowsi mat
    /@ (fun (i, row) -> IntMap.enum row /@ (fun (j, coeff) -> (i, j, coeff)))
    |> BatEnum.concat

  let row_set mat =
    BatEnum.fold
      (fun set (i, _) -> IntSet.add i set)
      IntSet.empty
      (rowsi mat)

  let column_set mat =
    rowsi mat
    |> BatEnum.fold (fun set (_, row) ->
        IntMap.enum row
        |> BatEnum.fold (fun set (j, _) -> IntSet.add j set) set)
      IntSet.empty

  let nb_rows mat =
    BatEnum.fold (fun nb _ -> nb + 1) 0 (rowsi mat)

  let nb_columns mat = IntSet.cardinal (column_set mat)

  let pp pp_scalar formatter mat =
    let cols = column_set mat in
    let pp_entry row formatter j =
      pp_scalar formatter (V.coeff j row)
    in
    let pp_row formatter row =
      Format.fprintf formatter "[%a]"
        (SrkUtil.pp_print_enum (pp_entry row)) (IntSet.enum cols)
    in
    let pp_sep formatter () =
      Format.fprintf formatter "@\n"
    in
    if equal mat zero then
      Format.pp_print_int formatter 0
    else
      Format.fprintf formatter "@[<v 0>%a x %a@;%a@]"
        IntSet.pp (row_set mat)
        IntSet.pp cols
        (SrkUtil.pp_print_enum_nobox ~pp_sep pp_row) (rows mat)

  let transpose mat =
    entries mat
    |> BatEnum.fold (fun mat (i, j, k) -> add_entry j i k mat) zero

  let mul mat mat' =
    let tr = transpose mat' in
    BatEnum.fold 
      (fun res (i, row) ->
         add_row
           i
           (BatEnum.fold
              (fun res_row (j, col) ->
                 V.add_term (V.dot row col) j res_row)
              V.zero
              (rowsi tr))
           res)
      zero
      (rowsi mat)

  let min_row = IntMap.min_binding

  let map_rows f m =
    let g _ row =
      let row' = f row in
      if V.is_zero row' then
        None
      else
        Some row'
    in
    IntMap.filter_map g m

  let vector_right_mul m v =
    m |> IntMap.filter_map (fun _ row ->
        let cell = V.dot row v in
        if R.equal cell R.zero then None
        else Some cell)

  let vector_left_mul v m =
    IntMap.fold (fun k coeff result ->
        V.add result (V.scalar_mul coeff (row k m)))
      v
      V.zero

  let of_dense dense_matrix =
    BatArray.fold_lefti (fun matrix i dense_row  ->
        let row =
          BatArray.fold_lefti (fun row j entry ->
              V.add_term entry j row)
            V.zero
            dense_row
        in
        add_row i row matrix)
      zero
      dense_matrix

  let dense_of matrix rows cols =
    Array.init rows (fun row ->
        Array.init cols (fun col ->
            entry row col matrix))
end

module MakeUltPeriodicSeq(R : S) = struct
  type t = R.t list * R.t list

  let lcm x y =
    match ZZ.to_int (ZZ.lcm (ZZ.of_int x) (ZZ.of_int y)) with
    | Some lcm -> lcm
    | None -> invalid_arg "Period length too long"

  let enum =
    let count () = raise BatEnum.Infinite_enum in
    let rec next ct cp p () =
      match !ct with
      | (x::xs) ->
        ct := xs; x
      | [] -> match !cp with
        | x::xs ->
          cp := xs; x
        | [] ->
          cp := List.tl p;
          List.hd p
    and clone ct cp p () =
      let ct = ref !ct in
      let cp = ref !cp in
      BatEnum.make ~next:(next ct cp p) ~count ~clone:(clone ct cp p)
    in
    fun (t, p) ->
      let ct = ref t in
      let cp = ref p in
      BatEnum.make
        ~next:(next ct cp p)
        ~count
        ~clone:(clone ct cp p)

  let rec take_skip e n =
    if n = 0 then
      []
    else
      let hd = BatEnum.get_exn e in
      let tl = take_skip e (n-1) in
      hd::tl

  let transient_len (t, _) = List.length t
  let period_len (_, p) = List.length p

  let transient (t, _) = t
  let periodic (_, p) = p

  let pointwise f seq seq' =
    let transient = max (transient_len seq) (transient_len seq') in
    let period = lcm (period_len seq) (period_len seq') in
    let e =
      BatEnum.combine (enum seq, enum seq')
      /@ (fun (x, y) -> f x y)
    in
    let t = take_skip e transient in
    let p = take_skip e period in
    (t, p)

  let add = pointwise R.add

  let mul = pointwise R.mul

  let zero = ([], [R.zero])

  let one = ([], [R.one])

  let equal seq seq' =
    let transient = max (transient_len seq) (transient_len seq') in
    let period = lcm (period_len seq) (period_len seq') in
    (BatEnum.combine (enum seq, enum seq'))
    |> BatEnum.take (transient+period)
    |> BatEnum.for_all (fun (x,y) -> R.equal x y)

  let negate (t, p) =
    (List.map R.negate t, List.map R.negate p)

  let make t p = match p with
    | [] -> invalid_arg "Cannot make ultimate periodic sequence with empty period"
    | _ -> (t, p)

  let pp pp_elt formatter (t, p) =
    Format.fprintf formatter "%a(@[%a@])^omega"
      (SrkUtil.pp_print_enum_nobox pp_elt) (BatList.enum t)
      (SrkUtil.pp_print_enum_nobox pp_elt) (BatList.enum p)
end

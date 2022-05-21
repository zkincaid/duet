open BatPervasives

module IntSet = SrkUtil.Int.Set

include Log.Make(struct let name = "srk.ring" end)

module type AbelianGroup = sig
  type t
  val equal : t -> t -> bool
  val add : t -> t -> t
  val negate : t -> t
  val zero : t
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
  val pop : t -> (dim * scalar) * t
  val map : (dim -> scalar -> scalar) -> t -> t
  val merge : (dim -> scalar -> scalar -> scalar) -> t -> t -> t
  val min_support : t -> (dim * scalar)
  val set : dim -> scalar -> t -> t
  val hash : (dim * scalar -> int) -> t -> int
  val compare : (scalar -> scalar -> int) -> t -> t -> int
  val fold : (dim -> scalar -> 'a -> 'a) -> t -> 'a -> 'a
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
  val column : dim -> t -> vector
  val rowsi : t -> (dim * vector) BatEnum.t
  val min_row : t -> dim * vector
  val add_row : dim -> vector -> t -> t
  val add_column : dim -> vector -> t -> t
  val add_entry : dim -> dim -> scalar -> t -> t
  val pivot : dim -> t -> vector * t
  val pivot_column : dim -> t -> vector * t
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
  val of_rows : vector list -> t
  val interlace_columns : t -> t -> t
end

module AbelianGroupMap (K : BatInterfaces.OrderedType) (G : AbelianGroup) = struct
  include SparseMap.Make(K)(G)
  type dim = K.t
  type scalar = G.t

  let is_scalar_zero = G.equal G.zero

  let add = merge (fun _ -> G.add)

  let add_term coeff dim vec =
    if is_scalar_zero coeff then
      vec
    else
      modify dim (G.add coeff) vec

  let coeff = get

  let enum m = BatEnum.map (fun (x,y) -> (y,x)) (enum m)

  let of_enum = BatEnum.fold (fun vec (x,y) -> add_term x y vec) zero

  let of_list = List.fold_left (fun vec (x,y) -> add_term x y vec) zero

  let of_term coeff dim = singleton dim coeff

  let negate = map (fun _ -> G.negate)

  let sub = merge (fun _ x y -> G.add x (G.negate y))

  let pivot dim vec = extract dim vec
end

module RingMap (K : BatInterfaces.OrderedType) (R : Algebra.Ring) = struct
  include AbelianGroupMap(K)(R)

  let scalar_mul k vec =
    if R.equal k R.one then vec
    else if R.equal k R.zero then zero
    else map (fun _ coeff -> R.mul k coeff) vec

  let dot u v =
    BatEnum.fold
      (fun sum (co, i) -> R.add sum (R.mul co (coeff i v)))
      R.zero
      (enum u)
end

module MakeVector (R : Algebra.Ring) = struct
  include RingMap(SrkUtil.Int)(R)

  let interlace u v =
    let u_shift =
      BatEnum.fold
        (fun s (coeff, i) -> add_term coeff (2 * i) s)
        zero
        (enum u)
    in
    BatEnum.fold
      (fun s (coeff, i) -> add_term coeff (2 * i + 1) s)
      u_shift
      (enum v)

  let deinterlace u =
    BatEnum.fold
      (fun (v, w) (coeff, i) ->
         if i mod 2 == 0 then
           (add_term coeff (i / 2) v, w)
         else
           (v, add_term coeff (i / 2) w))
      (zero, zero)
      (enum u)
end

module MakeMatrix (R : Algebra.Ring) = struct
  module V = MakeVector(R)
  module M = AbelianGroupMap(SrkUtil.Int)(V)
  type t = M.t
  type dim = int
  type scalar = R.t
  type vector = V.t

  let scalar_mul k mat =
    if R.equal k R.one then mat
    else if R.equal k R.zero then M.zero
    else M.map (fun _ vec -> V.scalar_mul k vec) mat

  let row = M.coeff
  let add = M.add
  let zero = M.zero

  let equal = M.equal
  let pivot = M.pivot
  let add_row i vec = M.add_term vec i
  let rowsi m = BatEnum.map (fun (x,y) -> (y,x)) (M.enum m)
  let entry i j mat = V.coeff j (row i mat)

  let column j mat =
    BatEnum.fold (fun column (i, row) ->
        V.add_term (V.coeff j row) i column)
      V.zero
      (rowsi mat)

  let pivot_column j mat =
    BatEnum.fold (fun (column, mat') (i, row) ->
        let (entry, row') = V.pivot j row in
        (V.add_term entry i column, add_row i row' mat'))
      (V.zero, zero)
      (rowsi mat)

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
    /@ (fun (i, row) -> V.enum row /@ (fun (coeff, j) -> (i, j, coeff)))
    |> BatEnum.concat

  let row_set mat =
    BatEnum.fold
      (fun set (i, _) -> IntSet.add i set)
      IntSet.empty
      (rowsi mat)

  let column_set mat =
    rowsi mat
    |> BatEnum.fold (fun set (_, row) ->
        V.enum row
        |> BatEnum.fold (fun set (_, j) -> IntSet.add j set) set)
      IntSet.empty

  let nb_rows mat =
    BatEnum.fold (fun nb _ -> nb + 1) 0 (rowsi mat)

  let nb_columns mat = IntSet.cardinal (column_set mat)

  let pp pp_scalar formatter mat =
    let cols = column_set mat in
    let pp_entry row formatter j =
      pp_scalar formatter (V.coeff j row)
    in
    let pp_row formatter (_, row) =
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
        (SrkUtil.pp_print_enum_nobox ~pp_sep pp_row) (rowsi mat)

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

  let min_row m =
    let (x,y) = BatEnum.get_exn (M.enum m) in
    (y, x)

  let map_rows f m = M.map (fun _ -> f) m

  let vector_right_mul m v =
    M.fold (fun i row result ->
        V.add_term (V.dot row v) i result)
      m
      V.zero

  let vector_left_mul v m =
    V.fold (fun i scalar result ->
        V.add result (V.scalar_mul scalar (row i m)))
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

  let of_rows =
    BatList.fold_lefti (fun m i v ->
        add_row i v m)
      zero

  let interlace_columns m n =
    IntSet.fold (fun i s ->
        add_row i (V.interlace (row i m) (row i n)) s)
      (IntSet.union (row_set m) (row_set n))
      zero
end

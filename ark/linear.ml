open Apak
open Syntax
open BatPervasives

include Log.Make(struct let name = "linear" end)
module type Ring = sig
  type t

  val equal : t -> t -> bool
  val add : t -> t -> t
  val mul : t -> t -> t
  val negate : t -> t
  val zero : t
  val one : t
  val pp : Format.formatter -> t -> unit
end

module type Vector = sig
  type t
  type dim
  type scalar

  val equal : t -> t -> bool
  val add : t -> t -> t
  val scalar_mul : scalar -> t -> t

  val zero : t
  val add_term : scalar -> dim -> t -> t
  val of_term : scalar -> dim -> t

  val enum : t -> (scalar * dim) BatEnum.t
  val coeff : dim -> t -> scalar

  val pivot : dim -> t -> scalar * t

  val pp : Format.formatter -> t -> unit
end

module type Context = sig
  val const_typ : const_sym -> typ
  val pp_const : Format.formatter -> const_sym -> unit
  include Smt.TranslationContext
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

module type AbelianGroup = sig
  type t
  val equal : t -> t -> bool
  val add : t -> t -> t
  val negate : t -> t
  val zero : t
end

module AbelianGroupMap (M : Map) (G : AbelianGroup) = struct
  type t = G.t M.t
  type dim = M.key
  type scalar = G.t

  let is_zero x = G.equal x G.zero

  let zero = M.empty

  let add u v =
    let f _ a b =
      match a, b with
      | Some a, Some b ->
        let sum = G.add a b in
        if is_zero sum then None else Some sum
      | Some x, None | None, Some x -> Some x
      | None, None -> assert false
    in
    M.merge f u v

  let add_term coeff v lin =
    if is_zero coeff then lin else begin
      try
        let sum = G.add coeff (M.find v lin) in
        if not (is_zero sum) then M.add v sum lin
        else M.remove v lin
      with Not_found -> M.add v coeff lin
    end

  let coeff x m = try M.find x m with Not_found -> G.zero

  let enum vec = M.enum vec /@ (fun (x,y) -> (y,x))

  let equal = M.equal G.equal

  let compare = M.compare

  let of_term coeff dim = add_term coeff dim zero

  let negate = M.map G.negate

  let pivot dim vec =
    let coeff = M.find dim vec in
    (coeff, M.remove dim vec)
end

module Int = struct
  type t = int [@@deriving show,ord]
  let tag k = k
end
module IntMap = Apak.Tagged.PTMap(Int)
module IntSet = Apak.Tagged.PTSet(Int)

module ZZVector = struct
  include AbelianGroupMap(IntMap)(ZZ)

  let scalar_mul k vec =
    if ZZ.equal k ZZ.one then vec
    else if ZZ.equal k ZZ.zero then IntMap.empty
    else IntMap.map (fun coeff -> ZZ.mul k coeff) vec

  let dot u v =
    BatEnum.fold
      (fun sum (co, i) -> ZZ.add sum (ZZ.mul co (coeff i v)))
      ZZ.zero
      (enum u)

  let pp formatter vec =
    IntMap.values vec
    |> Format.fprintf formatter "[@[%a@]]" (ApakEnum.pp_print_enum ZZ.pp)

  let show = Putil.mk_show pp
end

module QQVector = struct
  include AbelianGroupMap(IntMap)(QQ)

  let scalar_mul k vec =
    if QQ.equal k QQ.one then vec
    else if QQ.equal k QQ.zero then IntMap.empty
    else IntMap.map (fun coeff -> QQ.mul k coeff) vec

  let dot u v =
    BatEnum.fold
      (fun sum (co, i) -> QQ.add sum (QQ.mul co (coeff i v)))
      QQ.zero
      (enum u)

  let pp formatter vec =
    IntMap.values vec
    |> Format.fprintf formatter "[%a]" (ApakEnum.pp_print_enum QQ.pp)

  let show = Putil.mk_show pp
end

module QQMatrix = struct
  module M = AbelianGroupMap(IntMap)(QQVector)
  type t = M.t
  type dim = int
  type scalar = QQ.t

  let scalar_mul k mat =
    if QQ.equal k QQ.one then mat
    else if QQ.equal k QQ.zero then IntMap.empty
    else IntMap.map (fun vec -> QQVector.scalar_mul k vec) mat

  let row = M.coeff
  let add = M.add
  let zero = M.zero
  let equal = M.equal
  let pivot = M.pivot
  let compare = M.compare
  let add_row i vec = M.add_term vec i
  let rows = IntMap.values
  let rowsi = IntMap.enum
  let entry i j mat = QQVector.coeff j (row i mat)

  let add_entry i j k mat =
    add_row i (QQVector.of_term k j) mat

  let add_column i col mat =
    BatEnum.fold
      (fun mat (co,j) -> add_entry j i co mat)
      mat
      (QQVector.enum col)

  let entries mat =
    rowsi mat
    /@ (fun (i, row) -> IntMap.enum row /@ (fun (j, coeff) -> (i, j, coeff)))
    |> BatEnum.concat

  let column_set mat =
    rowsi mat
    |> BatEnum.fold (fun set (_, row) ->
        IntMap.enum row
        |> BatEnum.fold (fun set (j, _) -> IntSet.add j set) set)
      IntSet.empty

  let pp formatter mat =
    let cols = column_set mat in
    let pp_entry row formatter j =
      QQ.pp formatter (QQVector.coeff j row)
    in
    let pp_row formatter row =
      Format.fprintf formatter "[%a]"
        (ApakEnum.pp_print_enum (pp_entry row)) (IntSet.enum cols)
    in
    let pp_sep formatter () =
      Format.fprintf formatter "@\n"
    in
    if equal mat zero then
      Format.pp_print_int formatter 0
    else
      ApakEnum.pp_print_enum ~indent:0 ~pp_sep pp_row formatter (rows mat)

  let show = Putil.mk_show pp
    
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
                 QQVector.add_term (QQVector.dot row col) j res_row)
              QQVector.zero
              (rowsi tr))
           res)
      zero
      (rowsi mat)
end

exception No_solution

let solve_exn mat b =
  let open QQMatrix in
  logf "Solving system:@\nM:  %a@\nb:  %a" pp mat QQVector.pp b;
  let columns = column_set mat in
  let b_column = 1 + (IntSet.fold max columns 0) in
  let mat = add_column b_column b mat in
  let rec reduce finished mat =
    if equal mat zero then
      finished
    else
      let (row_num, _) = IntMap.min_binding mat in
      let (next_row, mat') = pivot row_num mat in
      let column =
        try BatEnum.find (fun i -> i != b_column) (IntMap.keys next_row)
        with Not_found -> raise No_solution
      in
      let (cell, next_row') = QQVector.pivot column next_row in
      let next_row' =
        QQVector.scalar_mul (QQ.negate (QQ.inverse cell)) next_row'
      in
      let f row =
        let (coeff, row') = QQVector.pivot column row in
        QQVector.add
          row'
          (QQVector.scalar_mul coeff next_row')
      in
      reduce ((column,next_row')::finished) (IntMap.map f mat')
  in
  let rr = reduce [] mat in
  let rec backprop soln = function
    | [] -> soln
    | ((lhs, rhs)::rest) ->
      backprop (QQVector.add_term (QQVector.dot soln rhs) lhs soln) rest
  in
  let res =
    backprop (QQVector.of_term QQ.one b_column) rr
    |> pivot b_column
    |> snd
    |> QQVector.negate
  in
  logf "Solution: %a" QQVector.pp res;
  res
    
let solve mat b =
  try Some (solve_exn mat b)
  with No_solution -> None


let vector_right_mul m v =
  m|> IntMap.filter_map (fun _ row ->
      let cell = QQVector.dot row v in
      if QQ.equal cell QQ.zero then None
      else Some cell)

open Syntax
open BatPervasives

include Log.Make(struct let name = "srk.linear" end)

module type AbelianGroup = sig
  type t
  val equal : t -> t -> bool
  val add : t -> t -> t
  val negate : t -> t
  val zero : t
end

module type Ring = sig
  include AbelianGroup
  val mul : t -> t -> t
  val one : t
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
  val coeff : dim -> t -> scalar
  val pivot : dim -> t -> scalar * t
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

  let equal = M.equal G.equal

  let compare = M.compare

  let of_term coeff dim = add_term coeff dim zero

  let negate = M.map G.negate

  let sub u v = add u (negate v)

  let pivot dim vec =
    (coeff dim vec, M.remove dim vec)
end

module RingMap (M : Map) (R : Ring) = struct
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

module IntMap = SrkUtil.Int.Map
module IntSet = SrkUtil.Int.Set

module ZZVector = struct
  include RingMap(IntMap)(ZZ)

  let pp formatter vec =
    let pp_elt formatter (k, v) = Format.fprintf formatter "%d:%a" k ZZ.pp v in
    IntMap.enum vec
    |> Format.fprintf formatter "[@[%a@]]" (SrkUtil.pp_print_enum pp_elt)

  let show = SrkUtil.mk_show pp
  let compare = compare ZZ.compare
end

module QQVector = struct
  include RingMap(IntMap)(QQ)

  let pp formatter vec =
    let pp_elt formatter (k, v) = Format.fprintf formatter "%d:%a" k QQ.pp v in
    IntMap.enum vec
    |> Format.fprintf formatter "[@[%a@]]" (SrkUtil.pp_print_enum pp_elt)

  let show = SrkUtil.mk_show pp
  let compare = compare QQ.compare
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

  let identity = List.fold_left (fun m d -> add_entry d d QQ.one m) zero

  let add_column i col mat =
    BatEnum.fold
      (fun mat (co,j) -> add_entry j i co mat)
      mat
      (QQVector.enum col)

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

  let pp formatter mat =
    let cols = column_set mat in
    let pp_entry row formatter j =
      QQ.pp formatter (QQVector.coeff j row)
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

  let show = SrkUtil.mk_show pp
    
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

  let rational_eigenvalues m =
    let denominator =
      BatEnum.fold (fun d (_, _, entry) ->
          ZZ.lcm d (QQ.denominator entry))
        ZZ.one
        (entries m)
    in
    let dims =
      SrkUtil.Int.Set.union (row_set m) (column_set m)
    in
    let nb_dims = SrkUtil.Int.Set.cardinal dims in
    let m =
      Array.init nb_dims (fun i ->
          Array.init nb_dims (fun j ->
              let (num, den) = QQ.to_zzfrac (entry i j m) in
              Ntl.ZZ.of_mpz (ZZ.div (ZZ.mul num denominator) den)))
    in
    let charpoly = Ntl.ZZMatrix.charpoly m in
    let (_, factors) = Ntl.ZZX.factor charpoly in
    factors |> BatList.filter_map (fun (p, m) ->
        if Ntl.ZZX.degree p == 1 then
          (* p = ax + b *)
          let a = Ntl.ZZ.mpz_of (Ntl.ZZX.get_coeff p 1) in
          let b = Ntl.ZZ.mpz_of (Ntl.ZZX.get_coeff p 0) in
          let eigenvalue =
            QQ.negate (QQ.of_zzfrac b (ZZ.mul a denominator))
          in
          Some (eigenvalue, m)
        else
          None)
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
      let f _ row =
        let (coeff, row') = QQVector.pivot column row in
        let row'' =
          QQVector.add
            row'
            (QQVector.scalar_mul coeff next_row')
        in
        if QQVector.is_zero row'' then
          None
        else
          Some row''
      in
      reduce ((column,next_row')::finished) (IntMap.filter_map f mat')
  in
  let rr = reduce [] mat in
  let rec backprop soln = function
    | [] -> soln
    | ((lhs, rhs)::rest) ->
      backprop (QQVector.add_term (QQVector.dot soln rhs) lhs soln) rest
  in
  let res =
    backprop (QQVector.of_term QQ.one b_column) rr
    |> QQVector.pivot b_column
    |> snd
    |> QQVector.negate
  in
  logf "Solution: %a" QQVector.pp res;
  res

let solve mat b =
  try Some (solve_exn mat b)
  with No_solution -> None

let orient p system =
  let module V = QQVector in
  let rec reduce fin sys =
    match sys with
    | [] -> fin
    | (eq::rest) ->
      if V.equal eq V.zero then
        reduce fin rest
      else
        try
          let (coeff, dim) =
            BatEnum.find (fun (_, dim) -> not (p dim)) (V.enum eq)
          in
          let coeff_inv = QQ.inverse coeff in
          let sub eq' =
            try
              let coeff' = V.coeff dim eq' in
              let k = QQ.negate (QQ.mul coeff_inv coeff') in
              V.add (V.scalar_mul k eq) eq'
            with Not_found -> eq'
          in
          let rhs =
            V.scalar_mul (QQ.negate coeff_inv) (snd (V.pivot dim eq))
          in
          reduce
            ((dim,rhs)::(List.map (fun (dim, rhs) -> (dim, sub rhs)) fin))
            (List.map sub rest)
        with Not_found -> reduce fin rest (* No variable to eliminate *)
  in
  reduce [] system

let vector_right_mul m v =
  m|> IntMap.filter_map (fun _ row ->
      let cell = QQVector.dot row v in
      if QQ.equal cell QQ.zero then None
      else Some cell)

let intersect_rowspace a b =
  (* Create a system lambda_1*A - lambda_2*B = 0.  lambda_1's occupy even
     columns and lambda_2's occupy odd. *)
  let mat_a =
    BatEnum.fold
      (fun mat (i, j, k) -> QQMatrix.add_entry j (2*i) k mat)
      QQMatrix.zero
      (QQMatrix.entries a)
  in
  let mat =
    ref (BatEnum.fold
           (fun mat (i, j, k) -> QQMatrix.add_entry j (2*i + 1) (QQ.negate k) mat)
           mat_a
           (QQMatrix.entries b))
  in
  let c = ref QQMatrix.zero in
  let d = ref QQMatrix.zero in
  let c_rows = ref 0 in
  let d_rows = ref 0 in
  let mat_rows =
    ref (BatEnum.fold (fun m (i, _) -> max m i) 0 (QQMatrix.rowsi (!mat)) + 1)
  in

  (* Loop through the columns col of A/B, trying to find a vector in the
     intersection of the row spaces of A and B and which has 1 in col's entry.
     If yes, add it the linear combinations to C/D, and add a constraint to
     mat that (in all future rows of CA), col's entry is 0.  This ensures that
     the rows of CA are linearly independent. *)
  (* to do: repeatedly solving super systems of the same system of equations
       -- can be made more efficient *)
  (QQMatrix.rowsi (!mat))
  |> (BatEnum.iter (fun (col, _) ->
      let mat' =
        QQMatrix.add_row
          (!mat_rows)
          (QQMatrix.row col mat_a)
          (!mat)
      in
      match solve mat' (QQVector.of_term QQ.one (!mat_rows)) with
      | Some solution ->
        let (c_row, d_row) =
          BatEnum.fold (fun (c_row, d_row) (entry, i) ->
              if i mod 2 = 0 then
                (QQVector.add_term entry (i/2) c_row, d_row)
              else
                (c_row, QQVector.add_term entry (i/2) d_row))
            (QQVector.zero, QQVector.zero)
            (QQVector.enum solution)
        in
        c := QQMatrix.add_row (!c_rows) c_row (!c);
        d := QQMatrix.add_row (!d_rows) d_row (!d);
        mat := mat';
        incr c_rows; incr d_rows; incr mat_rows
      | None -> ()));
  (!c, !d)

let divide_right a b =
  try
    let b_tr = QQMatrix.transpose b in
    let div =
      BatEnum.fold (fun div (i, row) ->
          QQMatrix.add_row i (solve_exn b_tr row) div)
        QQMatrix.zero
        (QQMatrix.rowsi a)
    in
    Some div
  with No_solution -> None

(* Affine expressions over constant symbols.  dim_of_sym, const_dim, and
   sym_of_dim are used to translate between symbols and the dimensions of the
   coordinate space. *)

exception Nonlinear

let const_dim = -1

let sym_of_dim dim =
  if dim >= 0 then Some (symbol_of_int dim)
  else None

let dim_of_sym k = int_of_symbol k

let const_linterm k = QQVector.of_term k const_dim

let linterm_size linterm = BatEnum.count (QQVector.enum linterm)

let const_of_linterm v =
  let (k, rest) = QQVector.pivot const_dim v in
  if QQVector.equal rest QQVector.zero then Some k
  else None

let linterm_of srk term =
  let open QQVector in
  let real qq = of_term qq const_dim in
  let pivot_const = pivot const_dim in
  let qq_of term =
    let (k, rest) = pivot_const term in
    if equal rest zero then k
    else raise Nonlinear
  in
  let nonzero_qq_of term =
    let qq = qq_of term in
    if QQ.equal qq QQ.zero then raise Nonlinear else qq
  in
  let mul x y =
    try scalar_mul (qq_of x) y
    with Nonlinear -> scalar_mul (qq_of y) x
  in
  let alg = function
    | `Real qq -> real qq
    | `App (k, []) -> of_term QQ.one (dim_of_sym k)
    | `Var (_, _) | `App (_, _) -> raise Nonlinear
    | `Add sum -> List.fold_left add zero sum
    | `Mul sum -> List.fold_left mul (real QQ.one) sum
    | `Binop (`Div, x, y) -> scalar_mul (QQ.inverse (nonzero_qq_of y)) x
    | `Binop (`Mod, x, y) -> real (QQ.modulo (qq_of x) (nonzero_qq_of y))
    | `Unop (`Floor, x) -> real (QQ.of_zz (QQ.floor (qq_of x)))
    | `Unop (`Neg, x) -> negate x
    | `Ite (_, _, _) -> raise Nonlinear
  in
  Term.eval srk alg term

let of_linterm srk linterm =
  let open QQVector in
  enum linterm
  /@ (fun (coeff, dim) ->
      match sym_of_dim dim with
      | Some k ->
        if QQ.equal coeff QQ.one then mk_const srk k
        else mk_mul srk [mk_real srk coeff; mk_const srk k]
      | None -> mk_real srk coeff)
  |> BatList.of_enum
  |> mk_add srk

let pp_linterm srk formatter linterm =
  Term.pp srk formatter (of_linterm srk linterm)

let evaluate_linterm interp term =
  (QQVector.enum term)
  /@ (fun (coeff, dim) ->
      match sym_of_dim dim with
      | Some const -> QQ.mul (interp const) coeff
      | None -> coeff)
  |> BatEnum.fold QQ.add QQ.zero

let evaluate_affine m term =
  (QQVector.enum term)
  /@ (fun (coeff, dim) ->
      if dim == const_dim then
        coeff
      else
        QQ.mul (m dim) coeff)
  |> BatEnum.fold QQ.add QQ.zero
